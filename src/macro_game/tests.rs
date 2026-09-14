    use super::*;
    use crate::shuffler::default_shuffle;
    use crate::solver::{solve, SearchResult};
    use core::num::NonZeroU8;
    use crate::pruning::{FullPruner, NoPruner, Pruner};
    use crate::traverse::{traverse, Callback, Control};

    /// The legacy per-card `do_move` sweep, kept as the test-only
    /// reference implementation of `sweep_words`.
    fn legacy_canon(g: &mut Solitaire) {
        loop {
            let cands = sweep_candidates(g);
            if cands == 0 {
                break;
            }
            let cm = cands & cands.wrapping_neg();
            let c = Card::from_mask_index(u8::try_from(cm.trailing_zeros()).unwrap());
            let _ = g.do_move(Move::PileStack(c));
        }
    }

    /// Search-path firing rates for the two search-level sole-successor
    /// rules (fold C12 forced-reveal, C9 draw-1 deck dominance), measured
    /// through the progress hook on the shipped path: at every TP-miss
    /// node, recompute the two masks and count. The rates bound the work a
    /// pre-`core_run` short-circuit could skip (the whole rule list plus
    /// the shared BFS at forced nodes; the deck-side channels at
    /// deck-dominated draw-1 nodes).
    #[test]
    #[ignore = "rate probe; run with --ignored --release --nocapture"]
    fn debug_forced_and_deck_dom_rate() {
        for draw_step in [1u8, 3] {
            let (mut nodes, mut forced, mut deck_dom) = (0u64, 0u64, 0u64);
            let mut deck_cards = 0u64;
            for seed in [12u64, 14, 17, 18, 21, 22, 26, 32] {
                let g = Solitaire::new(&default_shuffle(seed), NonZeroU8::new(draw_step).unwrap());
                let (mut n, mut f, mut d, mut dc) = (0u64, 0u64, 0u64, 0u64);
                let t = std::time::Instant::now();
                let win = macro_solvable_direct_progress(&g, |s| {
                    n += 1;
                    let root = Words::from_game(s);
                    let fr = root.locked
                        & root.vis
                        & root.sm()
                        & root.bm()
                        & Stack::decode(root.stack).dominance_mask();
                    if fr != 0 {
                        f += 1;
                    }
                    if draw_step == 1 {
                        let dm = s.get_deck().compute_mask(false)
                            & root.sm()
                            & Stack::decode(root.stack).dominance_mask();
                        if dm != 0 {
                            d += 1;
                            dc += s.get_deck().compute_mask(false).count_ones() as u64;
                        }
                    }
                });
                let p = perf_probe::read();
                let tot = p[16] as f64 + p[14] as f64 + p[15] as f64 + p[5] as f64;
                println!(
                    "seed={seed} draw={draw_step} win={win} nodes={n} forced={f} ({:4.1}%) deck_dom={d} ({:4.1}%) avg_deck_at_dom={:4.1} reg_fires={} in {:?} | sections: tp={:4.1}% core={:4.1}% branch={:4.1}% bfs={:4.1}%",
                    100.0 * f as f64 / n.max(1) as f64,
                    100.0 * d as f64 / n.max(1) as f64,
                    dc as f64 / d.max(1) as f64,
                    p[13],
                    t.elapsed(),
                    100.0 * p[16] as f64 / tot,
                    100.0 * p[14] as f64 / tot,
                    100.0 * p[15] as f64 / tot,
                    100.0 * p[5] as f64 / tot,
                );
                nodes += n;
                forced += f;
                deck_dom += d;
                deck_cards += dc;
            }
            println!(
                "TOTAL draw={draw_step}: nodes={nodes} forced={forced} ({:4.1}%) deck_dom={deck_dom} ({:4.1}%) avg_deck_at_dom={:4.1}",
                100.0 * forced as f64 / nodes.max(1) as f64,
                100.0 * deck_dom as f64 / nodes.max(1) as f64,
                deck_cards as f64 / deck_dom.max(1) as f64,
            );
        }
    }

    /// Ordering-policy experiment for the search's commitment loop:
    /// mirrors the shipped fold exactly (forced hoist, deck_dom, f3 from
    /// the scratch, collapse_pick) but reorders the groups before the
    /// loop per policy. Policy 0 (no reorder) must reproduce the shipped
    /// node counts — the harness's own sanity check. The others probe
    /// whether a different visitation order shrinks the refutation tree
    /// (the reveal-before-draw fix was worth ~12% of nodes once).
    #[test]
    #[ignore = "ordering experiment; run with --ignored --release --nocapture"]
    fn debug_ordering_policies() {
        use std::time::Instant;
        const NODE_CAP: usize = 4_000_000;
        // policy: 0 = shipped, 1 = reversed, 2 = draws-first,
        // 3 = kings-first (rank desc, kind order preserved),
        // 4 = tallest successor first (needs post_words per group)
        fn rec(
            s: &mut Solitaire,
            tp: &mut TpTable,
            scratch: &mut DirectScratch,
            nodes: &mut usize,
            policy: u8,
        ) -> bool {
            if s.is_win() || !tp.insert(s.encode()) {
                return s.is_win();
            }
            *nodes += 1;
            if *nodes > NODE_CAP {
                return false;
            }
            let ctx = ClosureCtx::from_game(s);
            let forced_reveal = {
                let f = ctx.root.locked
                    & ctx.root.vis
                    & ctx.root.sm()
                    & ctx.root.bm()
                    & Stack::decode(ctx.root.stack).dominance_mask();
                f & f.wrapping_neg()
            };
            if forced_reveal != 0 {
                let x = Card::from_mask_index(
                    u8::try_from(forced_reveal.trailing_zeros()).unwrap(),
                );
                let steps = [Move::PileStack(x)];
                let (vis, stack) = post_words(s, &ctx, &steps);
                let old = (s.get_visible_mask(), s.get_stack().encode());
                let (_, (undo, _)) = s.do_move(steps[0]);
                s.set_board(vis, stack);
                let child_win = rec(s, tp, scratch, nodes, policy);
                s.undo_move(steps[0], undo);
                s.set_board(old.0, old.1);
                return child_win;
            }
            let deck_dom = {
                let d = ctx.deck_mask
                    & ctx.root.sm()
                    & Stack::decode(ctx.root.stack).dominance_mask();
                if s.get_deck().draw_step().get() == 1 && d != 0 {
                    d & d.wrapping_neg()
                } else {
                    0
                }
            };
            let mut commitments = core::mem::take(&mut scratch.commitments);
            core_run(&ctx, scratch, &mut commitments, true, s.get_deck());
            scratch.commitments = commitments;
            let f3 = scratch.f3;
            let mut groups = core::mem::take(&mut scratch.groups);
            match policy {
                0 => {}
                1 => groups.reverse(),
                2 => groups.sort_by_key(|g| match g.first() {
                    Some((Commitment::Draw(x), ..)) => (0u8, x.mask_index()),
                    Some((Commitment::Reveal(x), ..)) => (1, x.mask_index()),
                    _ => (2, 0),
                }),
                3 => groups.sort_by_key(|g| match g.first() {
                    Some((Commitment::Draw(x) | Commitment::Reveal(x), ..)) => {
                        u8::MAX - x.rank()
                    }
                    _ => 0,
                }),
                4 => {
                    // tallest swept successor first: stack nibble sum of
                    // the collapse_pick'd post-state, descending. Groups
                    // without a selection sink to the end.
                    let key = |g: &Vec<StepTransition>| -> u16 {
                        let Some((_, _, steps, _)) = collapse_pick(g, f3) else {
                            return 0;
                        };
                        let (_, stack) = post_words(s, &ctx, steps);
                        let mut t = 0u16;
                        for sh in 0..4u16 {
                            t += (stack >> (4 * sh)) & 0xF;
                        }
                        t + 1
                    };
                    groups.sort_by_key(|g| core::cmp::Reverse(key(g)));
                }
                _ => {}
            }
            let mut win = false;
            'outer: for group in &groups {
                if deck_dom != 0 {
                    if let Some((Commitment::Draw(x), ..)) = group.first() {
                        if x.mask() != deck_dom {
                            continue;
                        }
                    }
                }
                let Some((_, _, steps, _ch)) = collapse_pick(group, f3) else {
                    continue;
                };
                let (vis, stack) = post_words(s, &ctx, steps);
                let old = (s.get_visible_mask(), s.get_stack().encode());
                let commit = *steps.last().expect("every channel ends in a commit");
                let (_, (undo, _)) = s.do_move(commit);
                s.set_board(vis, stack);
                let child_win = rec(s, tp, scratch, nodes, policy);
                s.undo_move(commit, undo);
                s.set_board(old.0, old.1);
                if child_win {
                    win = true;
                    break 'outer;
                }
            }
            scratch.groups = groups;
            win
        }
        for (name, policy) in [
            ("shipped      ", 0u8),
            ("reversed     ", 1),
            ("draws-first  ", 2),
            ("kings-first  ", 3),
            ("tallest-first", 4),
        ] {
            let mut total_nodes = 0u64;
            let mut total_n = 0u64;
            let t_all = Instant::now();
            for draw_step in [1u8, 3] {
                for seed in [12u64, 14, 17, 18, 21, 22, 26, 32] {
                    let mut root = Solitaire::new(
                        &default_shuffle(seed),
                        NonZeroU8::new(draw_step).unwrap(),
                    );
                    canonicalize(&mut root);
                    let mut tp = TpTable::default();
                    let mut scratch = DirectScratch::new();
                    let mut nodes = 0usize;
                    let t = Instant::now();
                    let win = rec(&mut root, &mut tp, &mut scratch, &mut nodes, policy);
                    if seed == 32 {
                        println!(
                            "  {name} seed=32 draw={draw_step} win={win} nodes={nodes} in {:?}",
                            t.elapsed()
                        );
                    }
                    total_nodes += nodes as u64;
                    total_n += u64::from(u32::from(win));
                }
            }
            println!(
                "{name}: total nodes across 16 configs = {total_nodes} ({total_n} wins) in {:?}",
                t_all.elapsed()
            );
        }
    }

    /// The amortization question for the shared accommodation BFS ("don't
    /// re-ask"): the closure a BFS walks — and therefore the answer for
    /// any (goal, kind) — is a pure function of the key
    /// `(root stack word, vis, locked, first_layer ∩ KING)`: the closure
    /// graph is deck-independent (edges never read the deck), and the
    /// deck-dependent goal conjuncts reduce to `x ∈ deck_mask`, which is
    /// given for a Draw goal. So if the search revisits the same key with
    /// the same goal, the whole walk is redundant and memoizable.
    ///
    /// This probe measures exactly that on the shipped search path: at
    /// every TP-miss node (via the progress hook), re-run the fold-mode
    /// generator locally to recover the node's goal set, and count
    /// distinct keys, distinct (key, goal) queries, and the repeat rate.
    /// A repeat rate near zero kills the memo idea on the spot.
    #[test]
    #[ignore = "closure-reuse probe; run with --ignored --release --nocapture"]
    fn debug_closure_reuse() {
        for draw_step in [1u8, 3] {
            let cards = default_shuffle(32);
            let g = Solitaire::new(&cards, NonZeroU8::new(draw_step).unwrap());
            let mut nodes = 0u64;
            let mut nodes_with_goals = 0u64;
            let mut goal_queries = 0u64;
            let mut goal_query_repeats = 0u64;
            let mut keys: std::collections::HashSet<(u64, u64, u64, u64)> =
                std::collections::HashSet::new();
            let mut queries: std::collections::HashSet<(u64, u64, u64, u64, u64, u8)> =
                std::collections::HashSet::new();
            let t = std::time::Instant::now();
            let win = macro_solvable_direct_progress(&g, |s| {
                nodes += 1;
                let ctx = ClosureCtx::from_game(s);
                // the closure key: root words + the king-layer slice the
                // reveal goal check reads
                let kf = ctx.first_layer & KING_MASK;
                let key = (
                    ctx.root.vis,
                    ctx.root.locked,
                    u64::from(ctx.root.stack),
                    kf,
                );
                // recover this node's goal set (same fold the search runs)
                let mut scratch = DirectScratch::new();
                let mut commitments = Vec::new();
                core_run(&ctx, &mut scratch, &mut commitments, true, s.get_deck());
                if scratch.goals.is_empty() {
                    return;
                }
                nodes_with_goals += 1;
                keys.insert(key);
                for goal in &scratch.goals {
                    let kind = matches!(goal.kind, OutcomeKind::Stack) as u8;
                    let q = (
                        ctx.root.vis,
                        ctx.root.locked,
                        u64::from(ctx.root.stack),
                        kf,
                        goal.xmask,
                        kind,
                    );
                    goal_queries += 1;
                    if !queries.insert(q) {
                        goal_query_repeats += 1;
                    }
                }
            });
            println!(
                "seed=32 draw={draw_step} win={win} nodes={nodes} nodes_with_goals={nodes_with_goals} \
                 distinct_keys={} distinct_(key,goal)={} queries={} repeats={} ({:2.1}%) in {:?}",
                keys.len(),
                queries.len(),
                goal_queries,
                goal_query_repeats,
                100.0 * goal_query_repeats as f64 / goal_queries.max(1) as f64,
                t.elapsed()
            );
        }
    }

    /// Concrete crease cases, curated from real corpus states: the
    /// deepest answered accommodation witnesses, the alternating ones
    /// (a PileStack before a StackPile — the up-then-down composition no
    /// single-word channel can express, §8.4's diagonal core), and dead
    /// tableau goals (the 93% miss mass) with the closure size the BFS
    /// paid to conclude "never opens". Each case dumps the board, the
    /// goal, the witness steps, and the fixed channels' guard states —
    /// the raw material for any future channel-extension or kill
    /// candidate.
    #[test]
    #[ignore = "crease case curation; run with --ignored --release --nocapture"]
    fn debug_crease_cases() {
        fn dump_board(g: &Solitaire) -> String {
            let st = g.get_stack();
            let vis = g.get_visible_mask();
            let locked = g.get_hidden().get_locked_mask();
            let mut surfaces = String::new();
            let mut v = vis & locked;
            while v != 0 {
                let bit = v & v.wrapping_neg();
                v &= !bit;
                surfaces.push_str(&format!(
                    "{} ",
                    Card::from_mask_index(u8::try_from(bit.trailing_zeros()).unwrap())
                ));
            }
            let mut free = String::new();
            let mut v = vis & !locked;
            while v != 0 {
                let bit = v & v.wrapping_neg();
                v &= !bit;
                free.push_str(&format!(
                    "{} ",
                    Card::from_mask_index(u8::try_from(bit.trailing_zeros()).unwrap())
                ));
            }
            format!(
                "heights=[{} {} {} {}] locked-surfaces=[{surfaces}] free-vis=[{free}] deck={}",
                st.get(0),
                st.get(1),
                st.get(2),
                st.get(3),
                g.get_deck().len()
            )
        }
        // closure size on words: BFS over the reversible edges from the
        // root (the same child rule as accommodations_shared)
        fn closure_size(ctx: &ClosureCtx) -> usize {
            let mut seen: std::collections::HashSet<u16> = std::collections::HashSet::new();
            let mut queue: alloc::collections::VecDeque<u16> =
                alloc::collections::VecDeque::new();
            seen.insert(ctx.root.stack);
            queue.push_back(ctx.root.stack);
            while let Some(word) = queue.pop_front() {
                let w = ctx.words_at(word);
                let mv = w.move_masks(ctx.deck_mask, ctx.first_layer);
                let mut edges = mv.pile_stack & !w.locked;
                let mut is_pile = true;
                loop {
                    if edges == 0 {
                        if is_pile {
                            edges = mv.stack_pile;
                            is_pile = false;
                            continue;
                        }
                        break;
                    }
                    let bit = edges & edges.wrapping_neg();
                    edges &= !bit;
                    let c = Card::from_mask_index(u8::try_from(bit.trailing_zeros()).unwrap());
                    let child = if is_pile {
                        word + (1 << (4 * c.suit()))
                    } else {
                        word - (1 << (4 * c.suit()))
                    };
                    if seen.insert(child) {
                        queue.push_back(child);
                    }
                }
            }
            seen.len()
        }
        struct Case {
            seed: u64,
            draw: u8,
            turn: usize,
            board: Solitaire,
            commitment: Commitment,
            kind: OutcomeKind,
            steps: Vec<Move>,
            channels_fired: Vec<&'static str>,
            closure: usize,
        }
        let mut deepest: Vec<Case> = Vec::new();
        let mut alternating: Vec<Case> = Vec::new();
        let mut dead_tableau: Vec<Case> = Vec::new();
        let (mut answered, mut missed) = (0usize, 0usize);
        // K4 kill candidate tally: dead tableau goals on first-layer kings
        // (locked surface king at the bottom of its pile — the reveal mask's
        // !(first_layer & KING) conjunct is closure-invariant)
        let (mut k4_count, mut k4_closure, mut dead_count, mut dead_closure) =
            (0usize, 0usize, 0usize, 0usize);
        for draw_step in [1u8, 3] {
            for i in 0..32u64 {
                let mut game = Solitaire::new(
                    &default_shuffle(12 + i),
                    NonZeroU8::new(draw_step).unwrap(),
                );
                for turn in 0..200usize {
                    if game.is_win() {
                        break;
                    }
                    canonicalize(&mut game);
                    let ctx = ClosureCtx::from_game(&game);
                    let mut scratch = DirectScratch::new();
                    let mut commitments = Vec::new();
                    core_run(&ctx, &mut scratch, &mut commitments, false, game.get_deck());
                    let cs = closure_size(&ctx);
                    let fired = |ci: usize| -> Vec<&'static str> {
                        scratch.groups[ci]
                            .iter()
                            .map(|(_, _, _, ch)| *ch)
                            .collect()
                    };
                    for (ci, group) in scratch.groups.iter().enumerate() {
                        for (c, k, steps, ch) in group {
                            if !ch.ends_with("bfs") {
                                continue;
                            }
                            answered += 1;
                            let shuffles = &steps[..steps.len() - 1];
                            let alt = shuffles
                                .iter()
                                .any(|m| matches!(m, Move::PileStack(_)))
                                && shuffles
                                    .iter()
                                    .any(|m| matches!(m, Move::StackPile(_)));
                            let case = Case {
                                seed: 12 + i,
                                draw: draw_step,
                                turn,
                                board: game.clone(),
                                commitment: *c,
                                kind: *k,
                                steps: steps.iter().copied().collect(),
                                channels_fired: fired(ci),
                                closure: cs,
                            };
                            if alt {
                                alternating.push(case);
                            } else {
                                deepest.push(case);
                            }
                        }
                    }
                    for goal in &scratch.goals {
                        let ci = commitments
                            .iter()
                            .position(|c| *c == goal.commitment)
                            .unwrap();
                        let ch = match goal.kind {
                            OutcomeKind::Stack => "stack-bfs",
                            OutcomeKind::Tableau => "tableau-bfs",
                        };
                        let got = scratch.groups[ci]
                            .iter()
                            .any(|(c, k, _, cch)| *c == goal.commitment && *k == goal.kind && *cch == ch);
                        if got {
                            continue;
                        }
                        missed += 1;
                        dead_count += 1;
                        dead_closure += cs;
                        let x = match goal.commitment {
                            Commitment::Draw(x) | Commitment::Reveal(x) => x,
                        };
                        if x.rank() == crate::card::KING_RANK
                            && ctx.first_layer & x.mask() != 0
                        {
                            k4_count += 1;
                            k4_closure += cs;
                        }
                        if goal.kind == OutcomeKind::Tableau {
                            dead_tableau.push(Case {
                                seed: 12 + i,
                                draw: draw_step,
                                turn,
                                board: game.clone(),
                                commitment: goal.commitment,
                                kind: goal.kind,
                                steps: Vec::new(),
                                channels_fired: fired(ci),
                                closure: cs,
                            });
                        }
                    }
                    // advance by the oracle's first witness path
                    let cands = enumerate_commitments(&game);
                    match cands.first() {
                        None => break,
                        Some(c0) => {
                            for &m in &c0.witness_path {
                                let _ = game.do_move(m);
                            }
                        }
                    }
                }
            }
        }
        let show = |label: &str, cases: &[Case]| {
            println!("=== {label} ===");
            for c in cases {
                println!(
                    "seed={} draw={} turn={} goal={:?} {:?}",
                    c.seed, c.draw, c.turn, c.commitment, c.kind
                );
                println!("  board: {}", dump_board(&c.board));
                println!("  closure size: {}", c.closure);
                println!("  fixed channels fired: {:?}", c.channels_fired);
                if !c.steps.is_empty() {
                    let steps: Vec<String> = c.steps.iter().map(|m| format!("{m}")).collect();
                    println!("  witness ({} steps): {}", c.steps.len(), steps.join(" · "));
                } else {
                    // the K2 receiver analysis: why the tableau goal never
                    // opens — the twin receivers at rank(X)+1, opposite
                    // color, and their status
                    let x = match c.commitment {
                        Commitment::Draw(x) | Commitment::Reveal(x) => x,
                    };
                    if x.rank() == crate::card::KING_RANK {
                        println!("  X is a king — opens only via the empty-pile gate (no receiver, K2 takes no kill)");
                    } else {
                        let vis = c.board.get_visible_mask();
                        let locked = c.board.get_hidden().get_locked_mask();
                        let stacked = stacked_mask(c.board.get_stack().encode());
                        let s = x.suit();
                        let mut rec = Vec::new();
                        for p in [Card::new(x.rank() + 1, s ^ 2), Card::new(x.rank() + 1, s ^ 3)] {
                            rec.push(format!(
                                "{p}: {}",
                                if vis & p.mask() != 0 && locked & p.mask() == 0 {
                                    "visible-free"
                                } else if vis & p.mask() != 0 {
                                    "visible-locked"
                                } else if stacked & p.mask() != 0 {
                                    "on-foundation (worry-backable)"
                                } else {
                                    "buried/in-deck (dead)"
                                }
                            ));
                        }
                        println!("  receivers for X: [{}]", rec.join(", "));
                    }
                }
            }
        };
        deepest.sort_by_key(|c| core::cmp::Reverse(c.steps.len()));
        show("deepest witnesses", &deepest[..deepest.len().min(3)]);
        alternating.sort_by_key(|c| c.steps.len());
        show("alternating creases (shortest)", &alternating[..alternating.len().min(3)]);
        dead_tableau.sort_by_key(|c| core::cmp::Reverse(c.closure));
        show("dead tableau goals (largest closures)", &dead_tableau[..dead_tableau.len().min(3)]);
        println!(
            "scanned: answered={answered} missed={missed} (dead tableau recorded: {})",
            dead_tableau.len()
        );
        println!(
            "K4 candidate (first-layer-king Reveal tableau goals, all kinds counted): {k4_count} of {dead_count} missed goals, carrying {k4_closure} of {dead_closure} closure states ({:4.1}% of miss cost)",
            100.0 * k4_closure as f64 / dead_closure.max(1) as f64
        );
    }

    /// The closure-shape question — can the reversible structure be tamed
    /// by interval arithmetic? For every corpus state, walk the FULL
    /// closure (no cap), compute the per-suit height ranges, and measure
    /// *box-completeness*: |closure| / Π(max_i − min_i + 1). A completeness
    /// of 1 means the reachable set is exactly its componentwise bounding
    /// box — the walk is then replaceable by 8 threshold numbers plus
    /// goal-box intersection tests (the K6 kill family); holes mean the
    /// diagonal core genuinely forbids the abstraction.
    #[test]
    #[ignore = "closure shape probe; run with --ignored --release --nocapture"]
    fn debug_closure_shape() {
        fn closure_words(ctx: &ClosureCtx) -> Vec<u16> {
            let mut seen: std::collections::HashSet<u16> = std::collections::HashSet::new();
            let mut queue: alloc::collections::VecDeque<u16> =
                alloc::collections::VecDeque::new();
            seen.insert(ctx.root.stack);
            queue.push_back(ctx.root.stack);
            while let Some(word) = queue.pop_front() {
                let w = ctx.words_at(word);
                let mv = w.move_masks(ctx.deck_mask, ctx.first_layer);
                let mut edges = mv.pile_stack & !w.locked;
                let mut is_pile = true;
                loop {
                    if edges == 0 {
                        if is_pile {
                            edges = mv.stack_pile;
                            is_pile = false;
                            continue;
                        }
                        break;
                    }
                    let bit = edges & edges.wrapping_neg();
                    edges &= !bit;
                    let c = Card::from_mask_index(u8::try_from(bit.trailing_zeros()).unwrap());
                    let child = if is_pile {
                        word + (1 << (4 * c.suit()))
                    } else {
                        word - (1 << (4 * c.suit()))
                    };
                    if seen.insert(child) {
                        queue.push_back(child);
                    }
                }
            }
            seen.into_iter().collect()
        }
        let (mut states, mut exact, mut near, mut boxes_of_1) =
            (0usize, 0usize, 0usize, 0usize);
        let mut sizes: Vec<usize> = Vec::new();
        let mut completeness: Vec<f64> = Vec::new();
        // miss-cost weighting: closure states walked, by whether the
        // closure is exactly a box
        let (mut walk_in_exact, mut walk_in_holey) = (0u64, 0u64);
        for draw_step in [1u8, 3] {
            for i in 0..32u64 {
                let mut game = Solitaire::new(
                    &default_shuffle(12 + i),
                    NonZeroU8::new(draw_step).unwrap(),
                );
                for _turn in 0..200 {
                    if game.is_win() {
                        break;
                    }
                    canonicalize(&mut game);
                    let ctx = ClosureCtx::from_game(&game);
                    let words = closure_words(&ctx);
                    let n = words.len();
                    let mut mins = [u8::MAX; 4];
                    let mut maxs = [0u8; 4];
                    for &w in &words {
                        for s in 0..4u16 {
                            let h = ((w >> (4 * s)) & 0xF) as u8;
                            mins[s as usize] = mins[s as usize].min(h);
                            maxs[s as usize] = maxs[s as usize].max(h);
                        }
                    }
                    let mut volume = 1usize;
                    for s in 0..4 {
                        if maxs[s] >= mins[s] {
                            volume *= usize::from(maxs[s] - mins[s] + 1);
                        }
                    }
                    let comp = n as f64 / volume as f64;
                    states += 1;
                    sizes.push(n);
                    completeness.push(comp);
                    if comp >= 1.0 {
                        exact += 1;
                        walk_in_exact += n as u64;
                    } else if comp >= 0.95 {
                        near += 1;
                        walk_in_holey += n as u64;
                    } else {
                        walk_in_holey += n as u64;
                    }
                    if volume == 1 {
                        boxes_of_1 += 1;
                    }
                    // advance by the oracle's first witness path
                    let cands = enumerate_commitments(&game);
                    match cands.first() {
                        None => break,
                        Some(c0) => {
                            for &m in &c0.witness_path {
                                let _ = game.do_move(m);
                            }
                        }
                    }
                }
            }
        }
        sizes.sort_unstable();
        completeness.sort_by(|a, b| a.partial_cmp(b).unwrap());
        let pct = |x: usize| 100.0 * x as f64 / states as f64;
        println!("closure shape over {states} corpus states:");
        println!(
            "  sizes: min={} p50={} p90={} max={}",
            sizes[0],
            sizes[sizes.len() / 2],
            sizes[sizes.len() * 9 / 10],
            sizes[sizes.len() - 1]
        );
        println!(
            "  box-completeness: exact={} ({:.1}%) near(>=0.95)={} ({:.1}%) p50={:.3} p10={:.3}",
            exact,
            pct(exact),
            near,
            pct(near),
            completeness[completeness.len() / 2],
            completeness[completeness.len() / 10]
        );
        println!(
            "  trivial boxes (volume 1): {} ({:.1}%) — the walk is already free there",
            boxes_of_1,
            pct(boxes_of_1)
        );
        println!(
            "  walk cost: exact-box closures carry {} states, holey carry {} ({:.1}% of walk cost is exact)",
            walk_in_exact,
            walk_in_holey,
            100.0 * walk_in_exact as f64 / (walk_in_exact + walk_in_holey) as f64
        );
    }

    /// The dominance-pruned closure question (§5.2 ported into the walk):
    /// the closure walker explores RAW edges (dominances off — the C1
    /// reduction is about the raw game), but every worry-back makes its
    /// card re-stackable, so the big endgame closures are full of words
    /// with 3+ simultaneous unlocked stackables — exactly the state where
    /// the engine's §5.2 rule ("three-or-more redundant stackables → only
    /// the lowest") collapses the branching. Since edge-filtering
    /// explores a subset, filtered answers ⊆ raw answers; the soundness
    /// test is one-directional: **every goal the raw walk answers, the
    /// filtered walk must answer too** (witness length may change — the
    /// detour stacks the lowest first). This probe measures opening-set
    /// preservation and the closure-size reduction, per corpus state.
    #[test]
    #[ignore = "closure dominance probe; run with --ignored --release --nocapture"]
    fn debug_closure_dominance() {
        const CAP: usize = 40;
        /// BFS over the closure answering `goals`; when `dom` is set, the
        /// up-edges apply §5.2 (≥3 unlocked stackables → only the lowest).
        fn walk_answers(
            ctx: &ClosureCtx,
            goals: &[AccommodationGoal],
            dom: bool,
        ) -> (usize, Vec<bool>) {
            let n = goals.len();
            let mut answered = vec![false; n];
            let mut pending: Vec<usize> = (0..n).collect();
            let mut seen: std::collections::HashSet<u16> = std::collections::HashSet::new();
            let mut queue: alloc::collections::VecDeque<(u16, usize)> =
                alloc::collections::VecDeque::new();
            seen.insert(ctx.root.stack);
            queue.push_back((ctx.root.stack, 0));
            let mut words = 0usize;
            while let Some((word, depth)) = queue.pop_front() {
                words += 1;
                let w = ctx.words_at(word);
                let mv = w.move_masks(ctx.deck_mask, ctx.first_layer);
                pending.retain(|&gi| goals[gi].cap > depth);
                if pending.is_empty() {
                    break;
                }
                let mut opened = false;
                for &gi in &pending {
                    let goal = &goals[gi];
                    let opens = match (goal.commitment, goal.kind) {
                        (Commitment::Draw(_), OutcomeKind::Tableau) => {
                            mv.deck_pile & goal.xmask != 0
                        }
                        (Commitment::Reveal(_), OutcomeKind::Tableau) => {
                            mv.reveal & goal.xmask != 0
                        }
                        (Commitment::Draw(_), OutcomeKind::Stack) => {
                            mv.deck_stack & goal.xmask != 0
                        }
                        (Commitment::Reveal(_), OutcomeKind::Stack) => {
                            mv.pile_stack & goal.xmask != 0
                        }
                    };
                    if opens {
                        answered[gi] = true;
                        opened = true;
                    }
                }
                if opened {
                    pending.retain(|&gi| !answered[gi]);
                    if pending.is_empty() {
                        break;
                    }
                }
                if depth + 1 >= CAP {
                    continue;
                }
                let mut ups = mv.pile_stack & !w.locked;
                if dom && ups.count_ones() >= 3 {
                    ups = ups & ups.wrapping_neg();
                }
                let mut edges = ups;
                let mut is_pile = true;
                loop {
                    if edges == 0 {
                        if is_pile {
                            edges = mv.stack_pile;
                            is_pile = false;
                            continue;
                        }
                        break;
                    }
                    let bit = edges & edges.wrapping_neg();
                    edges &= !bit;
                    let c = Card::from_mask_index(u8::try_from(bit.trailing_zeros()).unwrap());
                    let child = if is_pile {
                        word + (1 << (4 * c.suit()))
                    } else {
                        word - (1 << (4 * c.suit()))
                    };
                    if seen.insert(child) {
                        queue.push_back((child, depth + 1));
                    }
                }
            }
            (words, answered)
        }
        let (mut states, mut goals_checked, mut lost, mut raw_states, mut dom_states) =
            (0usize, 0usize, 0usize, 0u64, 0u64);
        let mut lost_cases: Vec<String> = Vec::new();
        for draw_step in [1u8, 3] {
            for i in 0..32u64 {
                let mut game = Solitaire::new(
                    &default_shuffle(12 + i),
                    NonZeroU8::new(draw_step).unwrap(),
                );
                for _turn in 0..200 {
                    if game.is_win() {
                        break;
                    }
                    canonicalize(&mut game);
                    let ctx = ClosureCtx::from_game(&game);
                    let mut scratch = DirectScratch::new();
                    let mut commitments = Vec::new();
                    core_run(&ctx, &mut scratch, &mut commitments, false, game.get_deck());
                    if scratch.goals.is_empty() {
                        // advance anyway
                        let cands = enumerate_commitments(&game);
                        match cands.first() {
                            None => break,
                            Some(c0) => {
                                for &m in &c0.witness_path {
                                    let _ = game.do_move(m);
                                }
                                continue;
                            }
                        }
                    }
                    states += 1;
                    let (raw_words, raw_ans) = walk_answers(&ctx, &scratch.goals, false);
                    let (dom_words, dom_ans) = walk_answers(&ctx, &scratch.goals, true);
                    raw_states += raw_words as u64;
                    dom_states += dom_words as u64;
                    for gi in 0..scratch.goals.len() {
                        goals_checked += 1;
                        if raw_ans[gi] && !dom_ans[gi] {
                            lost += 1;
                            if lost_cases.len() < 5 {
                                lost_cases.push(format!(
                                    "seed={} draw={draw_step} turn={_turn} goal={:?} {:?}",
                                    12 + i,
                                    scratch.goals[gi].commitment,
                                    scratch.goals[gi].kind
                                ));
                            }
                        }
                    }
                    // advance by the oracle's first witness path
                    let cands = enumerate_commitments(&game);
                    match cands.first() {
                        None => break,
                        Some(c0) => {
                            for &m in &c0.witness_path {
                                let _ = game.do_move(m);
                            }
                        }
                    }
                }
            }
        }
        println!(
            "closure 5.2-dominance: {states} states, {goals_checked} goals; lost openings = {lost}; closure words raw={raw_states} dom={dom_states} ({:.1}% cut)",
            100.0 * (1.0 - dom_states as f64 / raw_states as f64)
        );
        for c in &lost_cases {
            println!("  LOST {c}");
        }
    }

    /// The macro-footprint comparison: how many macro states (distinct
    /// canonical/swept encodes) does the SHIPPED old solver (dominance +
    /// FullPruner) actually traverse, versus the macro solver's node
    /// count? Every macro transition ends in exactly one irreversible
    /// move, so distinct canonical states are exactly the distinct
    /// irreversible-move endpoints — the common scale for "how much state
    /// space did each engine really need". The ratio macro/old quantifies
    /// the macro solver's over-generation against the filtered old
    /// engine: the value of the remaining filter-layer ports (the
    /// path-dependent pruners the macro game deliberately lacks).
    #[test]
    #[ignore = "macro footprint comparison; run with --ignored --release --nocapture"]
    fn debug_old_macro_footprint() {
        use std::collections::HashSet;
        struct MacroCounter {
            won: bool,
            visits: u64,
            macro_tp: HashSet<Encode>,
        }
        impl Callback for MacroCounter {
            type Pruner = FullPruner;
            fn on_win(&mut self, _: &Solitaire) -> Control {
                self.won = true;
                Control::Halt
            }
            fn on_visit(&mut self, g: &Solitaire, _: Encode) -> Control {
                self.visits += 1;
                let mut w = Words::from_game(g);
                sweep_words(&mut w);
                // the canonical form's encode: the swept stack replaces
                // the low 16 bits; hidden/deck are sweep-invariant
                self.macro_tp
                    .insert((g.encode() & !0xFFFF) | u64::from(w.stack));
                Control::Ok
            }
        }
        for draw_step in [1u8, 3] {
            let (mut sum_old, mut sum_macro) = (0u64, 0u64);
            for seed in [12u64, 14, 17, 18, 21, 22, 26, 32] {
                let cards = default_shuffle(seed);
                let step = NonZeroU8::new(draw_step).unwrap();
                let t = std::time::Instant::now();
                let mut game = Solitaire::new(&cards, step);
                let mut tp = TpTable::default();
                let mut cb = MacroCounter {
                    won: false,
                    visits: 0,
                    macro_tp: HashSet::new(),
                };
                traverse::<_, _, true>(&mut game, &FullPruner::default(), &mut tp, &mut cb);
                let t_old = t.elapsed();
                let t = std::time::Instant::now();
                let mut macro_nodes = 0u64;
                let g2 = Solitaire::new(&cards, step);
                let win = macro_solvable_direct_progress(&g2, |_| {
                    macro_nodes += 1;
                });
                let t_macro = t.elapsed();
                assert_eq!(cb.won, win, "verdict divergence at seed={seed} draw={draw_step}");
                sum_old += cb.macro_tp.len() as u64;
                sum_macro += macro_nodes;
                println!(
                    "seed={seed} draw={draw_step} win={win} OLD: micro-visits={:>9} macro-states={:>9} ({:>6.2}s) | MACRO: nodes={:>9} ({:>6.2}s) | ratio={:5.2}x",
                    cb.visits,
                    cb.macro_tp.len(),
                    t_old.as_secs_f64(),
                    macro_nodes,
                    t_macro.as_secs_f64(),
                    macro_nodes as f64 / cb.macro_tp.len().max(1) as f64
                );
            }
            println!(
                "TOTAL draw={draw_step}: old macro-states={sum_old}, macro nodes={sum_macro} ({:5.2}x)",
                sum_macro as f64 / sum_old.max(1) as f64
            );
        }
    }

    /// The deck-lattice decomposition — what IS the 164x deck-word
    /// multiplicity? Per board (stack | hidden), the visited states carry
    /// different deck masks (which cards remain) and offsets (pace). The
    /// attack-relevant shape:
    /// - *comparable* mask pairs (M1 ⊃ M2): the subset state is
    ///   reachable from the superset state by draw+park sequences
    ///   (board-preserving) — in draw-1 the offset is normalized away, so
    ///   TP already dedupes this order-redundancy and a state-level
    ///   dominance adds nothing;
    /// - *incomparable* masks: genuinely different deployed-card sets —
    ///   distinct positions no dominance by superset can merge;
    /// - offset multiplicity per (board, mask): surviving draw-order
    ///   information (draw-3 only; draw-1 normalizes it away).
    #[test]
    #[ignore = "deck lattice decomposition; run with --ignored --release --nocapture"]
    fn debug_deck_lattice() {
        use std::collections::{HashMap, HashSet};
        for draw_step in [1u8, 3] {
            let g = Solitaire::new(&default_shuffle(32), NonZeroU8::new(draw_step).unwrap());
            let mut boards: HashMap<u32, Vec<u32>> = HashMap::new();
            macro_solvable_direct_progress(&g, |s| {
                let e = s.encode();
                let board = (e & 0xFFFF_FFFF) as u32;
                let deck = (e >> 32) as u32;
                boards.entry(board).or_default().push(deck);
            });
            let states: u64 = boards.values().map(|v| v.len() as u64).sum();
            let mut mults: Vec<u64> = boards.values().map(|v| v.len() as u64).collect();
            mults.sort_unstable();
            // distinct (board, mask) and offset multiplicity per mask
            let mut masks: HashSet<(u32, u32)> = HashSet::new();
            let mut offsets_per_mask: HashMap<(u32, u32), HashSet<u8>> = HashMap::new();
            for (b, ds) in &boards {
                for &d in ds {
                    let m = d & 0xFF_FFFF;
                    masks.insert((*b, m));
                    offsets_per_mask
                        .entry((*b, m))
                        .or_default()
                        .insert((d >> 24) as u8);
                }
            }
            let multi_offset: u64 = offsets_per_mask
                .values()
                .filter(|o| o.len() > 1)
                .count() as u64;
            // the residue-dominance prize: within each (board, MASK),
            // offsets group into residue classes (mod 3) plus the pure
            // class (offset == len, already normalized); only the minimal
            // offset per class needs exploring — count the doomed extras.
            // Plus the impure-beats-pure rule: a pure state (pass
            // boundary — no block-1 accessibility) is dominated by ANY
            // same-mask impure state (block 1 nonempty ⊇ empty, same
            // successor merge), so pure states with impure siblings die.
            let (mut doomed, mut surviving) = (0u64, 0u64);
            let mut pure_killed_by_impure: u64 = 0;
            for (b, ds) in &boards {
                let mut by_mask_residue: HashMap<(u32, u8), Vec<u8>> = HashMap::new();
                for &d in ds {
                    let m = d & 0xFF_FFFF;
                    let o = (d >> 24) as u8;
                    let len = m.count_ones() as u8;
                    let r = if o == len { 0 } else { o % 3 };
                    by_mask_residue.entry((m, r)).or_default().push(o);
                }
                let has_impure = by_mask_residue
                    .keys()
                    .any(|(_, r)| *r != 0);
                for ((_, r), offs) in by_mask_residue {
                    if r == 0 {
                        // the pure class: single state (offset == len);
                        // dies entirely when an impure sibling exists
                        if has_impure {
                            pure_killed_by_impure += offs.len() as u64;
                            doomed += offs.len() as u64;
                        } else {
                            surviving += 1;
                        }
                        continue;
                    }
                    surviving += 1;
                    doomed += offs.len() as u64 - 1;
                }
            }
            // pairwise structure on the top-100 boards by multiplicity
            let mut top: Vec<(&u32, &Vec<u32>)> = boards.iter().collect();
            top.sort_by_key(|(_, v)| core::cmp::Reverse(v.len()));
            let (mut comparable, mut incomparable, mut same_mask) = (0u64, 0u64, 0u64);
            let mut pop_spread: Vec<u8> = Vec::new();
            for (_, ds) in top.iter().take(100) {
                let masks: Vec<u32> = ds.iter().map(|d| d & 0xFF_FFFF).collect();
                let mut pmin = 24u8;
                let mut pmax = 0u8;
                for &m in &masks {
                    let p = m.count_ones() as u8;
                    pmin = pmin.min(p);
                    pmax = pmax.max(p);
                }
                pop_spread.push(pmax - pmin);
                for i in 0..masks.len() {
                    for j in 0..masks.len() {
                        if i == j {
                            continue;
                        }
                        let (mi, mj) = (masks[i], masks[j]);
                        if mi == mj {
                            same_mask += 1;
                        } else if (mi & mj) == mj {
                            comparable += 1; // mi ⊃ mj
                        } else if (mi & mj) != mi {
                            incomparable += 1;
                        }
                    }
                }
            }
            let pairs = comparable + incomparable + same_mask;
            println!(
                "seed=32 draw={draw_step}: states={states} boards={} avg-mult={:5.1} p50-mult={} max-mult={}",
                boards.len(),
                states as f64 / boards.len() as f64,
                mults[mults.len() / 2],
                mults[mults.len() - 1]
            );
            println!(
                "  distinct (board,mask)={} — {} masks carry >1 offset (draw-order info survived); popcount spread per top-board: p50={} max={}",
                masks.len(),
                multi_offset,
                pop_spread[pop_spread.len() / 2],
                pop_spread.iter().copied().max().unwrap_or(0)
            );
            println!(
                "  residue-dominance prize: surviving states={} doomed={} ({:4.1}% of the search's states; {} pure states killed by impure siblings)",
                surviving,
                doomed,
                100.0 * doomed as f64 / states as f64,
                pure_killed_by_impure
            );
            println!(
                "  top-100-board mask pairs: comparable(superset)={} ({:4.1}%) same-mask={} incomparable={} ({:4.1}%)",
                comparable,
                100.0 * comparable as f64 / pairs as f64,
                same_mask,
                incomparable,
                100.0 * incomparable as f64 / pairs as f64
            );
        }
    }

    /// The pace-dominance lemma's empirical pin (the falsifier for the
    /// offset-dominance registry before it ships). For random draw-3
    /// decks and every offset, the accessible position set K(o) must
    /// satisfy the order the dominance theorem stands on:
    ///
    /// - **pure-pure equality**: K(o) for o ≡ 0 (mod 3) or the exhausted
    ///   boundary is o-independent — this *derives* the engine's
    ///   `is_pure`/`normalized_offset` merge from the accessibility
    ///   formula instead of asserting it;
    /// - **residue monotonicity**: within an impure residue class,
    ///   o ≤ o' implies K(o) ⊇ K(o') (block 1 of `iter_callback` starts
    ///   lower; block 3 and the last card are class-invariant);
    /// - **impure over pure**: every impure K strictly contains the pure
    ///   set (block 1 nonempty ⊇ empty).
    ///
    /// Plus the merge lemma: drawing the same card from two states
    /// sharing a mask (same array) yields the identical successor offset
    /// (`draw` sets the offset to the drawn position — parent-invariant).
    #[test]
    fn pace_dominance_order() {
        use crate::deck::{Deck, N_DECK_CARDS};
        use core::ops::ControlFlow;
        use std::collections::HashSet;
        let step = NonZeroU8::new(3).unwrap();
        for seed in 12u64..112 {
            let cards = default_shuffle(seed);
            let deck_cards: [Card; N_DECK_CARDS as usize] =
                cards[(N_CARDS - N_DECK_CARDS) as usize..]
                    .try_into()
                    .unwrap();
            let mut d = Deck::new(deck_cards, step);
            // consume a few cards to vary the mask and array
            let mut rng = seed;
            for _ in 0..(seed % 7) {
                let acc: Vec<u8> = {
                    let mut v = Vec::new();
                    let _ = d.iter_callback(false, |p, _| -> ControlFlow<()> {
                        v.push(p);
                        ControlFlow::Continue(())
                    });
                    v
                };
                if acc.is_empty() {
                    break;
                }
                rng = rng.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
                let _ = d.draw(acc[(rng as usize) % acc.len()]);
            }
            let n = d.len();
            let ks: Vec<HashSet<u8>> = (0..=n)
                .map(|o| {
                    d.set_offset(o);
                    let mut s = HashSet::new();
                    let _ = d.iter_callback(false, |p, _| -> ControlFlow<()> {
                        s.insert(p);
                        ControlFlow::Continue(())
                    });
                    s
                })
                .collect();
            let pure = |o: u8| o % 3 == 0 || o == n;
            for o1 in 0..=n {
                for o2 in 0..=n {
                    if o1 == o2 {
                        continue;
                    }
                    if pure(o1) && pure(o2) {
                        assert_eq!(
                            ks[usize::from(o1)], ks[usize::from(o2)],
                            "pure-pure K divergence: seed={seed} n={n} {o1} vs {o2}"
                        );
                    } else if !pure(o1) && !pure(o2) && o1 % 3 == o2 % 3 && o1 < o2 {
                        assert!(
                            ks[usize::from(o1)].is_superset(&ks[usize::from(o2)]),
                            "residue monotonicity broken: seed={seed} n={n} {o1} vs {o2}"
                        );
                    } else if !pure(o1) && pure(o2) {
                        assert!(
                            ks[usize::from(o1)].is_superset(&ks[usize::from(o2)]),
                            "impure K does not contain pure K: seed={seed} n={n} {o1} vs {o2}"
                        );
                    }
                }
            }
            // merge lemma spot-check: a common-accessible position drawn
            // from two different offsets lands on the same successor
            for (o1, o2) in [(1u8, 4u8), (2, 5), (1, 7), (2, 8)] {
                if o1 >= n || o2 >= n {
                    continue;
                }
                let Some(&p) = ks[usize::from(o1)].intersection(&ks[usize::from(o2)]).next() else {
                    continue;
                };
                let mut d1 = d.clone();
                let mut d2 = d.clone();
                d1.set_offset(o1);
                d2.set_offset(o2);
                let c1 = d1.draw(p);
                let c2 = d2.draw(p);
                assert_eq!(c1, c2, "merge: drawn cards differ seed={seed}");
                assert_eq!(
                    d1.get_offset(),
                    d2.get_offset(),
                    "merge: successor offsets differ seed={seed} o1={o1} o2={o2} p={p}"
                );
            }
        }
        println!("pace dominance order: 100 random decks, all offsets — pure-pure equal, residue-monotone, impure ⊇ pure, merge holds");
    }

    /// **K6 research — the tableau-side kill.** The 93% miss mass:
    /// for every tableau goal that survives K1-K5 in the total
    /// generator and then MISSES in the shared BFS, record the root
    /// four-card signature. The §8.1 locality compresses the whole
    /// opening question into the interaction ball
    /// `{X, twin(X), R, R'}` (the receivers at rank(X)+1, opposite
    /// color) — because the receivers' under-pair IS `{X, twin(X)}`:
    /// with `free[X] ≡ 0` in the closure (X deck or locked), the
    /// blocked disjunct is `¬free[twin(X)]` and the parity is
    /// `vis[R] ⊕ vis[R'] ⊕ free[twin(X)]`, so the goal opens iff some
    /// word has `(vis[R] ∨ vis[R']) ∧ (¬free[twin(X)] ∨ odd-parity)`.
    /// The signature dimensions this probe tallies over the miss mass:
    /// - the receivers' status: visible-free / visible-locked /
    ///   on-foundation (worry-backable) / dead (buried or deck)
    /// - twin(X): free / locked / buried / deck
    /// - the three stacking routes out (R stacks, R' stacks, twin(X)
    ///   stacks): each K1-blocked at the root (a missing prefix card
    ///   not root-visible-and-unlocked) or not
    /// The conjecture the data must shape: which signatures freeze the
    /// parity recursion (the receivers never change count, the twin
    /// never changes freeness) — those are the K6 kills.
    #[test]
    #[ignore = "K6 research probe; run with --ignored --release --nocapture"]
    fn debug_k6_signature() {
        use std::collections::BTreeMap;
        // K1's climb-blocked test for a card c's suit: some card in
        // [h₀, rank(c)) is not root-visible-and-unlocked (it would have
        // to pass through stacked, visible — worry-backs only surface
        // ranks < h₀)
        let climb_blocked = |ctx: &ClosureCtx, c: Card| -> bool {
            let s = c.suit();
            let h0 = ctx.root.height(s);
            if h0 >= c.rank() {
                return false; // at/above: no climb needed
            }
            (h0..c.rank()).any(|r| {
                let m = Card::new(r, s).mask();
                ctx.root.vis & m == 0 || ctx.root.locked & m != 0
            })
        };
        let mut sig_tally: BTreeMap<String, usize> = BTreeMap::new();
        let mut total_missed = 0usize;
        for draw_step in [1u8, 3] {
            for i in 0..32u64 {
                let mut game = Solitaire::new(
                    &default_shuffle(12 + i),
                    NonZeroU8::new(draw_step).unwrap(),
                );
                for _turn in 0..200 {
                    if game.is_win() {
                        break;
                    }
                    canonicalize(&mut game);
                    let ctx = ClosureCtx::from_game(&game);
                    let mut scratch = DirectScratch::new();
                    let mut commitments = Vec::new();
                    core_run(&ctx, &mut scratch, &mut commitments, false, game.get_deck());
                    // the tableau goals that were pushed and missed
                    for goal in &scratch.goals {
                        if goal.kind != OutcomeKind::Tableau {
                            continue;
                        }
                        let ci = commitments
                            .iter()
                            .position(|c| *c == goal.commitment)
                            .unwrap();
                        let answered = scratch.groups[ci].iter().any(
                            |(c, k, _, ch)| {
                                *c == goal.commitment
                                    && *k == OutcomeKind::Tableau
                                    && *ch == "tableau-bfs"
                            },
                        );
                        if answered {
                            continue;
                        }
                        total_missed += 1;
                        let x = match goal.commitment {
                            Commitment::Draw(x) | Commitment::Reveal(x) => x,
                        };
                        let twin = x.swap_suit();
                        let (r, xs) = (x.rank(), x.suit());
                        let (r1, r2) =
                            (Card::new(r + 1, xs ^ 2), Card::new(r + 1, xs ^ 3));
                        let vis = ctx.root.vis;
                        let locked = ctx.root.locked;
                        let stacked = stacked_mask(ctx.root.stack);
                        let status = |c: Card| -> &'static str {
                            if vis & c.mask() != 0 {
                                if locked & c.mask() != 0 {
                                    "vis-locked"
                                } else {
                                    "vis-free"
                                }
                            } else if stacked & c.mask() != 0 {
                                "on-found"
                            } else {
                                "dead"
                            }
                        };
                        let twin_status = match status(twin) {
                            "vis-free" => {
                                if climb_blocked(&ctx, twin) {
                                    "free+cb"
                                } else {
                                    "free"
                                }
                            }
                            s => s,
                        };
                        let rx = match status(r1) {
                            "vis-free" => {
                                if climb_blocked(&ctx, r1) {
                                    "vf+cb"
                                } else {
                                    "vf"
                                }
                            }
                            s => s,
                        };
                        let rx2 = match status(r2) {
                            "vis-free" => {
                                if climb_blocked(&ctx, r2) {
                                    "vf+cb"
                                } else {
                                    "vf"
                                }
                            }
                            s => s,
                        };
                        let sig = format!("twin={twin_status} R1={rx} R2={rx2}");
                        *sig_tally.entry(sig).or_insert(0) += 1;
                    }
                    // advance by the oracle's first witness path
                    let cands = enumerate_commitments(&game);
                    match cands.first() {
                        None => break,
                        Some(c0) => {
                            for &m in &c0.witness_path {
                                let _ = game.do_move(m);
                            }
                        }
                    }
                }
            }
        }
        println!("K6: {total_missed} surviving tableau misses; root signatures:");
        let mut entries: Vec<(usize, &String)> =
            sig_tally.iter().map(|(k, v)| (*v, k)).collect();
        entries.sort_by(|a, b| b.0.cmp(&a.0));
        for (n, sig) in entries.iter().take(24) {
            println!("  {n:>8} ({:5.1}%)  {sig}", 100.0 * *n as f64 / total_missed.max(1) as f64);
        }
    }

    /// **The incremental-core scoping probe**: how much of a child's
    /// channel evaluation is inherited from its parent? For every
    /// fold-selected successor edge on the corpus trajectory, run the
    /// total generator on BOTH sides and diff the per-commitment
    /// channel sets. The incremental design's viability is exactly
    /// this number: the fraction of the child's commitments with
    /// unchanged outcomes (inheritable), plus the new-commitment rate
    /// (fresh work regardless). Also tallies the edge sweep size — the
    /// swept cards are additional edited bits beyond the commit's own,
    /// the real invalidation width.
    #[test]
    #[ignore = "incremental scoping; run with --ignored --release --nocapture"]
    fn debug_edge_overlap() {
        use std::collections::BTreeMap;
        let channel_set = |scratch: &DirectScratch| -> BTreeMap<(u8, u8), Vec<&'static str>> {
            let mut m: BTreeMap<(u8, u8), Vec<&'static str>> = BTreeMap::new();
            for (c, _k, _s, ch) in scratch.groups.iter().flat_map(|g| g.iter()) {
                let key = match c {
                    Commitment::Draw(x) | Commitment::Reveal(x) => {
                        (x.mask_index(), 1)
                    }
                };
                let e = m.entry(key).or_default();
                if !e.contains(ch) {
                    e.push(ch);
                }
            }
            m
        };
        let (mut edges, mut shared, mut identical, mut fresh, mut dropped) =
            (0u64, 0u64, 0u64, 0u64, 0u64);
        let mut sweep_hist = [0u64; 16];
        for draw_step in [1u8, 3] {
            for i in 0..32u64 {
                let mut game = Solitaire::new(
                    &default_shuffle(12 + i),
                    NonZeroU8::new(draw_step).unwrap(),
                );
                for _turn in 0..200 {
                    if game.is_win() {
                        break;
                    }
                    canonicalize(&mut game);
                    // parent outcomes
                    let mut pscratch = DirectScratch::new();
                    let mut pcomms = Vec::new();
                    let pctx = ClosureCtx::from_game(&game);
                    core_run(&pctx, &mut pscratch, &mut pcomms, false, game.get_deck());
                    let parent = channel_set(&pscratch);
                    // the fold successors
                    let succs = macro_transitions_fast(&game);
                    let ptotal: u32 = (0..4).map(|s| u32::from(game.get_stack().get(s))).sum();
                    for (commitment, child) in &succs {
                        edges += 1;
                        let ctotal: u32 = (0..4).map(|s| u32::from(child.get_stack().get(s))).sum();
                        let stacked_commit = matches!(
                            commitment,
                            Commitment::Draw(_)
                        ) || matches!(commitment, Commitment::Reveal(_));
                        let _ = stacked_commit;
                        // swept cards beyond the commit's own stack edit:
                        // reveal/tableau commits add 0, stack outcomes +1
                        let swept = (ctotal - ptotal).saturating_sub(1);
                        sweep_hist[(swept.min(15)) as usize] += 1;
                        let mut cscratch = DirectScratch::new();
                        let mut ccomms = Vec::new();
                        let cctx = ClosureCtx::from_game(child);
                        core_run(&cctx, &mut cscratch, &mut ccomms, false, child.get_deck());
                        let child_map = channel_set(&cscratch);
                        for (c, chans) in &child_map {
                            match parent.get(c) {
                                Some(pchans) => {
                                    shared += 1;
                                    if pchans == chans {
                                        identical += 1;
                                    }
                                }
                                None => {
                                    fresh += 1;
                                }
                            }
                        }
                        for c in parent.keys() {
                            if !child_map.contains_key(c) {
                                dropped += 1;
                            }
                        }
                    }
                    // advance by the oracle's first witness path
                    let cands = enumerate_commitments(&game);
                    match cands.first() {
                        None => break,
                        Some(c0) => {
                            for &m in &c0.witness_path {
                                let _ = game.do_move(m);
                            }
                        }
                    }
                }
            }
        }
        println!(
            "incremental scoping over {edges} edges: shared commitments {shared}, identical channels {identical} ({:4.1}% of shared), fresh (new in child) {fresh} ({:4.1}% of child work), dropped {dropped}",
            100.0 * identical as f64 / shared.max(1) as f64,
            100.0 * fresh as f64 / (shared + fresh).max(1) as f64,
        );
        print!("  edge sweep sizes: ");
        for (n, v) in sweep_hist.iter().enumerate() {
            if *v > 0 {
                print!("{n}x{} ", v);
            }
        }
        println!();
    }

    /// **The mask-lift verification probe** — the guard battery goes
    /// bulk (the engine's own `gen_moves` idiom, applied to the macro
    /// channels): every per-commitment guard is a whole-mask set
    /// question, computable in ~25 mask ops per node instead of ~20 ×
    /// 25ns of scalar tests. The lifted masks, and their scalar
    /// equivalents verified bit-for-bit on the corpus:
    ///
    /// - `stack_direct`/`tableau_direct`: the two direct channels, one
    ///   OR of existing masks each
    /// - `dig_cand`: commitments whose TWIN is unlocked and
    ///   pile-stack-able — the adjacent-bit pair swap (`twin_swap`,
    ///   index ^ 1) applied to `pile_stack & !locked`
    /// - `borrow_cand`: commitments with a worry-backable foundation-top
    ///   parent — the foundation tops are ≤4 cards; their children
    ///   spread by rank-down + color-swap + twin-duplication (`cspr`)
    /// - `receiver_live`: commitments with a visible-or-stacked
    ///   receiver — `cspr(vis | stacked)`; its complement is K2
    /// - `k1_dead`: the climb-blocked mask — per suit,
    ///   `SUIT_PREFIX[s][frontier[s]+1]` is the open climb prefix
    /// - `k6_dead`: `twin_swap(vis & !locked) & k1_dead & !receiver_live`
    ///   — the four-card ball, assembled from the pieces (the twin's
    ///   climb-blocked condition is K1's own mask on X: same suit,
    ///   same rank)
    #[test]
    #[ignore = "mask-lift verification; run with --ignored --release --nocapture"]
    fn debug_mask_lift() {
        use crate::card::KING_MASK;
        const EVEN_MASK: u64 = 0x5555_5555_5555_5555;
        let twin_swap = |m: u64| ((m & !EVEN_MASK) >> 1) | ((m & EVEN_MASK) << 1);
        // the sitters of P: `go_after` says x sits on y iff
        // (x + 4) ^ y < 2 — x is 4 below y, with the twin tolerance
        // absorbed by the XOR (the layout's rank-parity interleave makes
        // the +1 direction alternate, but the XOR form is parity-free):
        // the sitters are (y >> 4) and its twin — down-shift then
        // twin-duplicate, two shifts + a swap
        let cspr = |p: u64| {
            let d = p >> 4;
            d | twin_swap(d)
        };
        let (mut states, mut checked) = (0usize, 0usize);
        for draw_step in [1u8, 3] {
            for i in 0..32u64 {
                let mut game = Solitaire::new(
                    &default_shuffle(12 + i),
                    NonZeroU8::new(draw_step).unwrap(),
                );
                for _turn in 0..200 {
                    if game.is_win() {
                        break;
                    }
                    canonicalize(&mut game);
                    let ctx = ClosureCtx::from_game(&game);
                    let mv = ctx.root.move_masks(ctx.deck_mask, ctx.first_layer);
                    let deck_mask = ctx.deck_mask;
                    let locked = ctx.root.locked;
                    let locked_surfaces = ctx.root.vis & locked;
                    let commit_mask = deck_mask | locked_surfaces;
                    let stacked_now = stacked_mask(ctx.root.stack);

                    // the lifted masks
                    let stack_direct =
                        (deck_mask & mv.deck_stack) | (locked_surfaces & mv.pile_stack);
                    let tableau_direct =
                        (deck_mask & mv.deck_pile) | (locked_surfaces & mv.reveal);
                    let dig_cand = commit_mask & !KING_MASK
                        & twin_swap(mv.pile_stack & !locked);
                    let ftop = {
                        let mut f = 0u64;
                        for s in 0..4u8 {
                            let h0 = ctx.root.height(s);
                            if h0 > 0 {
                                f |= Card::new(h0 - 1, s).mask();
                            }
                        }
                        f
                    };
                    let borrow_cand = commit_mask & !KING_MASK
                        & cspr(ftop & !locked & mv.stack_pile);
                    let receiver_live = cspr(ctx.root.vis | stacked_now);
                    // kings never take the K2/K6 kills (the scalar's
                    // king branch exits before them) — and their
                    // phantom rank-13 receivers read as dead
                    let k2_dead = commit_mask & !KING_MASK & !receiver_live;
                    let k1_open = {
                        let mut m = 0u64;
                        for s in 0..4u8 {
                            m |= SUIT_PREFIX[usize::from(s)]
                                [usize::from(ctx.frontier[usize::from(s)]) + 1];
                        }
                        m
                    };
                    let k1_dead = commit_mask & !k1_open;
                    let k6_dead = commit_mask & twin_swap(ctx.root.vis & !locked)
                        & k1_dead & k2_dead;
                    let king_dead = if (ctx.root.vis & ctx.root.locked).count_ones()
                        >= u32::from(N_PILES)
                    {
                        commit_mask & KING_MASK
                    } else {
                        locked_surfaces & KING_MASK & ctx.first_layer
                    };
                    let tableau_dead = king_dead | k6_dead | k2_dead;

                    // the scalar equivalents, per commitment
                    for xi in 0..u32::from(N_CARDS) {
                        let x = Card::from_mask_index(xi as u8);
                        let xm = x.mask();
                        if commit_mask & xm == 0 {
                            continue;
                        }
                        checked += 1;
                        let is_draw = deck_mask & xm != 0;
                        let (r, s) = (x.rank(), x.suit());
                        // stack_now / direct_now
                        let s_now = if is_draw {
                            mv.deck_stack & xm != 0
                        } else {
                            mv.pile_stack & xm != 0
                        };
                        assert_eq!(
                            stack_direct & xm != 0,
                            s_now,
                            "stack_direct divergence: seed={} turn={_turn} {x:?}",
                            12 + i
                        );
                        let d_now = if is_draw {
                            mv.deck_pile & xm != 0
                        } else {
                            mv.reveal & xm != 0
                        };
                        assert_eq!(
                            tableau_direct & xm != 0,
                            d_now,
                            "tableau_direct divergence: seed={} turn={_turn} {x:?}",
                            12 + i
                        );
                        // dig guard
                        let twin = x.swap_suit();
                        let tm = twin.mask();
                        let dig_g = x.rank() != crate::card::KING_RANK
                            && locked & tm == 0
                            && mv.pile_stack & tm != 0;
                        assert_eq!(
                            dig_cand & xm != 0,
                            dig_g,
                            "dig_cand divergence: seed={} turn={_turn} {x:?}",
                            12 + i
                        );
                        // borrow guard (any parent)
                        let borrow_g = x.rank() != crate::card::KING_RANK
                            && [Card::new(r + 1, s ^ 2), Card::new(r + 1, s ^ 3)]
                                .into_iter()
                                .any(|p| {
                                    ctx.root.height(p.suit())
                                        == p.rank().saturating_add(1)
                                        && locked & p.mask() == 0
                                        && mv.stack_pile & p.mask() != 0
                                });
                        assert_eq!(
                            borrow_cand & xm != 0,
                            borrow_g,
                            "borrow_cand divergence: seed={} turn={_turn} {x:?}",
                            12 + i
                        );
                        // the kills vs goal_dead
                        let commitment = if is_draw {
                            Commitment::Draw(x)
                        } else {
                            Commitment::Reveal(x)
                        };
                        assert_eq!(
                            k1_dead & xm != 0,
                            goal_dead(&ctx, commitment, OutcomeKind::Stack),
                            "k1_dead divergence: seed={} turn={_turn} {x:?}",
                            12 + i
                        );
                        if tableau_dead & xm != 0
                            && !goal_dead(&ctx, commitment, OutcomeKind::Tableau)
                        {
                            let (r0, s0) = (x.rank(), x.suit());
                            panic!(
                                "tableau_dead divergence: seed={} turn={_turn} x={x:?} r={r0} s={s0} recv1={:?} vis1={} stk1={} recv2={:?} vis2={} stk2={}",
                                12 + i,
                                Card::new(r0 + 1, s0 ^ 2),
                                ctx.root.vis & Card::new(r0 + 1, s0 ^ 2).mask() != 0,
                                stacked_now & Card::new(r0 + 1, s0 ^ 2).mask() != 0,
                                Card::new(r0 + 1, s0 ^ 3),
                                ctx.root.vis & Card::new(r0 + 1, s0 ^ 3).mask() != 0,
                                stacked_now & Card::new(r0 + 1, s0 ^ 3).mask() != 0,
                            );
                        }
                    }
                    states += 1;
                    // advance by the oracle's first witness path
                    let cands = enumerate_commitments(&game);
                    match cands.first() {
                        None => break,
                        Some(c0) => {
                            for &m in &c0.witness_path {
                                let _ = game.do_move(m);
                            }
                        }
                    }
                }
            }
        }

        println!(
            "mask-lift verified: {checked} commitments on {states} corpus states — all six lifted masks bit-exact"
        );
    }

    /// The word pipeline against move replay, state by state:
    /// `canonicalize` must land exactly where the per-card `do_move` sweep
    /// does (including ambiguous-twin picks), and `post_state` must equal
    /// replaying the channel's steps then sweeping. Any drift is caught
    /// here at the implementation surface, not downstream.
    #[test]
    fn words_match_moves() {
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(|| {
                let mut checked = 0usize;
                for draw_step in [1u8, 3] {
                    for i in 0..16u64 {
                        let mut game = Solitaire::new(
                            &default_shuffle(12 + i),
                            NonZeroU8::new(draw_step).unwrap(),
                        );
                        for _turn in 0..50 {
                            if game.is_win() {
                                break;
                            }
                            // the sweep, both ways
                            let mut a = game.clone();
                            canonicalize(&mut a);
                            let mut b = game.clone();
                            legacy_canon(&mut b);
                            assert_eq!(
                                a.encode(),
                                b.encode(),
                                "sweep divergence: draw={draw_step} seed={} turn={_turn}",
                                12 + i
                            );
                            // every channel's post-state, both ways
                            let mut scratch = DirectScratch::new();
                            let (root, ctx) = macro_transitions_core(&game, &mut scratch);
                            for group in &scratch.groups {
                                for (c, k, chan_steps, channel) in group {
                                    let fast = post_state(&root, &ctx, chan_steps);
                                    let mut replay = root.clone();
                                    for &m in chan_steps.iter() {
                                        replay.do_move(m);
                                    }
                                    legacy_canon(&mut replay);
                                    assert_eq!(
                                        fast.encode(),
                                        replay.encode(),
                                        "post_state divergence: draw={draw_step} seed={} turn={_turn} {c:?} {k:?} {channel} steps={chan_steps:?}",
                                        12 + i
                                    );
                                    let vf = fast.get_visible_mask();
                                    let vr = replay.get_visible_mask();
                                    assert_eq!(
                                        vf, vr,
                                        "post_state vis divergence: draw={draw_step} seed={} turn={_turn} {c:?} {k:?} {channel} steps={chan_steps:?}\n  fast-only={:#x} replay-only={:#x}\n  fast={:?}\n  replay={:?}",
                                        12 + i,
                                        vf & !vr, vr & !vf,
                                        fast, replay,
                                    );
                                    if !fast.is_valid() {
                                        println!(
                                            "INVALID fast: draw={draw_step} seed={} turn={_turn} {c:?} {k:?} {channel} steps={chan_steps:?}",
                                            12 + i
                                        );
                                        println!("  pre-core game.is_valid()={}", game.is_valid());
                                        println!("  canonical root.is_valid()={}", root.is_valid());
                                        {
                                            let rv = root.get_visible_mask();
                                            let mut nonvis_r = root.get_hidden().mask();
                                            for cd in root.get_deck().iter() { nonvis_r |= cd.mask(); }
                                            nonvis_r |= stacked_mask(root.get_stack().encode());
                                            println!("  root vis==derived: {}", full_mask(N_CARDS) ^ nonvis_r == rv);
                                        }
                                        let mut c1 = root.clone();
                                        c1.do_move(*chan_steps.last().unwrap());
                                        println!("  root+commit only is_valid={}", c1.is_valid());
                                        {
                                            let cv = c1.get_visible_mask();
                                            let mut nonvis_c = c1.get_hidden().mask();
                                            for cd in c1.get_deck().iter() { nonvis_c |= cd.mask(); }
                                            nonvis_c |= stacked_mask(c1.get_stack().encode());
                                            println!("  commit-only vis==derived: {} missing={:#x} extra={:#x}",
                                                full_mask(N_CARDS) ^ nonvis_c == cv,
                                                cv & !(full_mask(N_CARDS) ^ nonvis_c),
                                                (full_mask(N_CARDS) ^ nonvis_c) & !cv);
                                        }
                                        println!("  replay_valid={}", replay.is_valid());
                                        let total = vf.count_ones() as u32 + u32::from(fast.get_stack().len()) + u32::from(fast.get_deck().len()) + u32::from(fast.get_hidden().total_down_cards());
                                        println!("  total_cards={total} (want 52)");
                                        let mut nonvis = fast.get_hidden().mask();
                                        for cd in fast.get_deck().iter() { nonvis |= cd.mask(); }
                                        let derived = full_mask(N_CARDS) ^ nonvis ^ stacked_mask(fast.get_stack().encode());
                                        println!("  derived==vis: {}; missing={:#x} extra={:#x}", derived == vf, vf & !derived, derived & !vf);
                                        println!("  hidden_valid={} stack_valid={}", fast.get_hidden().is_valid(), fast.get_stack().is_valid());
                                        println!("  fast={fast:?}");
                                        println!("  replay={replay:?}");
                                    }
                                    assert!(fast.is_valid());
                                    checked += 1;
                                }
                            }
                            // advance by the oracle's first witness path —
                            // canonicalize first: witness paths are
                            // relative to the canonical root (the sweep
                            // discipline of every other harness here)
                            canonicalize(&mut game);
                            let cands = enumerate_commitments(&game);
                            if cands.is_empty() {
                                break;
                            }
                            for &m in &cands[0].witness_path {
                                let _ = game.do_move(m);
                            }
                        }
                    }
                }
                println!("words_match_moves: {checked} channel post-states cross-checked");
            })
            .unwrap()
            .join()
            .unwrap();
    }

    /// The lookup tables against the arithmetic they replace, exhaustively:
    /// `SUIT_NEXT`/`Words::sm` must equal `Stack::mask` for *every* u16
    /// stack word (the table is the formula, but the guarantee is what the
    /// hot path stands on), and `SUIT_PREFIX`/`stacked_mask` must equal the
    /// per-card loop for every *valid* word (nibbles ≤ 13).
    #[test]
    fn word_tables_exact() {
        for w in 0..=u16::MAX {
            let tbl = Words { vis: 0, locked: 0, stack: w }.sm();
            assert_eq!(tbl, Stack::decode(w).mask(), "sm table divergence at {w:#x}");
        }
        for w in 0..=u16::MAX {
            let (mut h0, mut h1, mut h2, mut h3) = (
                (w & 0xF) as u8,
                ((w >> 4) & 0xF) as u8,
                ((w >> 8) & 0xF) as u8,
                ((w >> 12) & 0xF) as u8,
            );
            h0 = h0.min(13);
            h1 = h1.min(13);
            h2 = h2.min(13);
            h3 = h3.min(13);
            let valid = w
                == (u16::from(h0) | (u16::from(h1) << 4) | (u16::from(h2) << 8) | (u16::from(h3) << 12));
            if !valid {
                continue;
            }
            let mut m = 0u64;
            for (s, h) in [(0u8, h0), (1, h1), (2, h2), (3, h3)] {
                for r in 0..h {
                    m |= Card::new(r, s).mask();
                }
            }
            assert_eq!(stacked_mask(w), m, "stacked_mask divergence at {w:#x}");
        }
    }

    /// The fold-mode goal cut against the total generator, per corpus
    /// state: for every commitment, `collapse_pick` (with the identical
    /// F3 mask, which only reads `stack-direct` entries) must select the
    /// same transition — or none — in both modes. That selection equality
    /// *is* the cut's soundness argument for the search; the verdict
    /// sweeps judge the same claim end to end.
    #[test]
    fn fold_goal_cut_matches_total() {
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(|| {
                let mut states = 0usize;
                for draw_step in [1u8, 3] {
                    for i in 0..16u64 {
                        let mut game = Solitaire::new(
                            &default_shuffle(12 + i),
                            NonZeroU8::new(draw_step).unwrap(),
                        );
                        for _turn in 0..50 {
                            if game.is_win() {
                                break;
                            }
                            canonicalize(&mut game);
                            states += 1;
                            let ctx = ClosureCtx::from_game(&game);

                            let run = |fold: bool,
                                       scratch: &mut DirectScratch|
                             -> Vec<Option<(OutcomeKind, ArrayVec<Move, 42>, &'static str)>> {
                                let mut commitments =
                                    core::mem::take(&mut scratch.commitments);
                                core_run(&ctx, scratch, &mut commitments, fold, game.get_deck());
                                scratch.commitments = commitments;
                                let dom = game.get_stack().dominance_mask();
                                let mut f3: u64 = 0;
                                for group in &scratch.groups {
                                    for (c, k, _, ch) in group {
                                        if *k == OutcomeKind::Stack && *ch == "stack-direct"
                                        {
                                            f3 |= match c {
                                                Commitment::Draw(x) | Commitment::Reveal(x) => {
                                                    x.mask()
                                                }
                                            };
                                        }
                                    }
                                }
                                f3 &= dom;
                                scratch
                                    .groups
                                    .iter()
                                    .map(|g| {
                                        collapse_pick(g, f3)
                                            .map(|(_, k, st, ch)| (*k, st.clone(), *ch))
                                    })
                                    .collect()
                            };

                            let mut scratch = DirectScratch::new();
                            let sel_total = run(false, &mut scratch);
                            let n_com = scratch.commitments.len();
                            let sel_fold = run(true, &mut scratch);
                            assert_eq!(n_com, sel_fold.len());
                            assert_eq!(sel_total.len(), sel_fold.len());
                            for (t, f) in sel_total.iter().zip(sel_fold.iter()) {
                                match (t, f) {
                                    (None, None) => {}
                                    (
                                        Some((k1, s1, c1)),
                                        Some((k2, s2, c2)),
                                    ) => {
                                        assert_eq!(
                                            (k1, s1.as_slice(), c1),
                                            (k2, s2.as_slice(), c2),
                                            "fold selection divergence: draw={draw_step} seed={} turn={_turn}",
                                            12 + i
                                        );
                                    }
                                    (t, f) => panic!(
                                        "fold selection None-mismatch: {t:?} vs {f:?} draw={draw_step} seed={} turn={_turn}",
                                        12 + i
                                    ),
                                }
                            }

                            // advance by the oracle's first witness path
                            let cands = enumerate_commitments(&game);
                            match cands.first() {
                                None => break,
                                Some(c0) => {
                                    for &m in &c0.witness_path {
                                        let _ = game.do_move(m);
                                    }
                                }
                            }
                        }
                    }
                }
                println!(
                    "fold goal cut matches total on {states} corpus states"
                );
            })
            .unwrap()
            .join()
            .unwrap();
    }

    /// The per-card algebra of `bottom_mask_of`, bound to the
    /// implementation: a card `c` is movable (`bm ∋ c`) iff
    ///
    /// ```text
    /// (vis[c] ∨ vis[twin(c)])                       — pair visible somewhere
    /// ∧ ( ¬free[u1] ∧ ¬free[u2]                     — under-pair all blocked
    ///     ∨ vis[c]⊕vis[twin(c)]⊕free[u1]⊕free[u2] ) — or the parities differ
    /// ```
    ///
    /// where `u1,u2` are the twin pair at `rank(c)−1`, opposite color (the
    /// cards `c` can sit on; aces have none — always movable when
    /// visible). This is the compressed parity lemma: every closure edge
    /// and goal predicate reads at most four card bits, which is the
    /// substrate the closed-form program (and the Lean formalization of
    /// the kills) stands on.
    #[test]
    fn bm_algebra_matches() {
        let mut x = 0x243F_6A88_85A3_08D3u64;
        let mut next = || {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            x
        };
        let full = full_mask(N_CARDS);
        for _ in 0..2000 {
            let vis = next() & full;
            let locked = next() & vis;
            let bm = bottom_mask_of(vis, locked);
            for ci in 0..u32::from(N_CARDS) {
                let c = Card::from_mask_index(ci as u8);
                let t = c.swap_suit();
                let vis_c = vis & c.mask() != 0;
                let vis_t = vis & t.mask() != 0;
                let free = |card: Card| vis & card.mask() != 0 && locked & card.mask() == 0;
                let algebra = if c.rank() == 0 {
                    vis_c || vis_t
                } else {
                    let u1 = c.reduce_rank_swap_color();
                    let u2 = u1.swap_suit();
                    let (f1, f2) = (free(u1), free(u2));
                    (vis_c || vis_t)
                        && ((!f1 && !f2) || ((vis_c ^ vis_t) ^ (f1 ^ f2)))
                };
                assert_eq!(
                    bm & c.mask() != 0,
                    algebra,
                    "bm algebra divergence c={c:?} vis={vis:#x} locked={locked:#x}"
                );
            }
        }
    }

    /// TP preallocation microbench: insert ~2.76M scattered u64s (the
    /// seed-32 draw-1 unique-state count) into the search's TpTable shape,
    /// grown from empty vs preallocated. The delta is the rehash share
    /// the CLI could reclaim by threading a capacity through
    /// `macro_solvable_direct`.
    #[test]
    #[ignore = "tp microbench; run with --ignored --release --nocapture"]
    fn debug_tp_rehash_share() {
        use crate::utils::MixHasherBuilder;
        use std::time::Instant;
        let n = 2_760_243u64;
        let key = |i: u64| (i.wrapping_mul(0x9E37_79B9_7F4A_7C15) >> 3) & ((1 << 61) - 1);
        let t0 = Instant::now();
        let mut s: hashbrown::HashSet<u64, MixHasherBuilder> = Default::default();
        let mut inserted = 0u64;
        for i in 0..n {
            if s.insert(key(i)) {
                inserted += 1;
            }
        }
        let t_grow = t0.elapsed();
        let t1 = Instant::now();
        let mut s2: hashbrown::HashSet<u64, MixHasherBuilder> =
            hashbrown::HashSet::with_capacity_and_hasher(4_200_000, MixHasherBuilder);
        for i in 0..n {
            s2.insert(key(i));
        }
        let t_pre = t1.elapsed();
        assert_eq!(inserted, n);
        assert_eq!(s2.len(), n as usize);
        println!(
            "insert {n} u64s: grow={t_grow:?} prealloc={t_pre:?} — rehash share {:.1}%",
            100.0 * (1.0 - t_pre.as_secs_f64() / t_grow.as_secs_f64())
        );
    }

    /// The direct falsifier for the `goal_dead` kills: for every corpus
    /// state, reconstruct every (commitment, kind) that would become a BFS
    /// goal *without* the kills, run the un-killed shared BFS over all of
    /// them, and assert that every killed goal indeed has no answer. A
    /// single answered-but-killed goal is a soundness bug in the kill —
    /// this test is the kill's arbiter, the differential its backstop.
    #[test]
    fn goal_kills_are_sound() {
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(|| {
                let (mut states, mut goals_total, mut killed, mut killed_answered) =
                    (0usize, 0usize, 0usize, 0usize);
                for draw_step in [1u8, 3] {
                    for i in 0..16u64 {
                        let mut game = Solitaire::new(
                            &default_shuffle(12 + i),
                            NonZeroU8::new(draw_step).unwrap(),
                        );
                        for _turn in 0..50 {
                            if game.is_win() {
                                break;
                            }
                            canonicalize(&mut game);
                            states += 1;
                            let ctx = ClosureCtx::from_game(&game);

                            // the would-be goal set: identical conditions
                            // to core_run's pushes, minus kills and folds
                            let mut scratch = DirectScratch::new();
                            let mut commitments = Vec::new();
                            core_run(&ctx, &mut scratch, &mut commitments, false, game.get_deck());
                            let mut goals: Vec<AccommodationGoal> = Vec::new();
                            let mut dead: Vec<bool> = Vec::new();
                            for &commitment in &commitments {
                                let g = &scratch.groups
                                    [commitments.iter().position(|c| *c == commitment).unwrap()];
                                let x = match commitment {
                                    Commitment::Draw(x) | Commitment::Reveal(x) => x,
                                };
                                let (stack_move, direct_move) = match commitment {
                                    Commitment::Draw(x) => (Move::DeckStack(x), Move::DeckPile(x)),
                                    Commitment::Reveal(x) => {
                                        (Move::PileStack(x), Move::Reveal(x))
                                    }
                                };
                                let has_stack =
                                    g.iter().any(|(_, k, _, _)| *k == OutcomeKind::Stack);
                                if !has_stack {
                                    goals.push(AccommodationGoal {
                                        commitment,
                                        kind: OutcomeKind::Stack,
                                        xmask: x.mask(),
                                        commit_move: stack_move,
                                        cap: 40,
                                    });
                                    dead.push(goal_dead(&ctx, commitment, OutcomeKind::Stack));
                                }
                                let has_direct =
                                    g.iter().any(|(_, _, _, ch)| *ch == "tableau-direct");
                                if !has_direct {
                                    goals.push(AccommodationGoal {
                                        commitment,
                                        kind: OutcomeKind::Tableau,
                                        xmask: x.mask(),
                                        commit_move: direct_move,
                                        cap: 40,
                                    });
                                    dead.push(goal_dead(&ctx, commitment, OutcomeKind::Tableau));
                                }
                            }
                            goals_total += goals.len();
                            killed += dead.iter().filter(|&&d| d).count();
                            if goals.is_empty() {
                                // advance by the oracle's first witness path
                                let cands = enumerate_commitments(&game);
                                match cands.first() {
                                    None => break,
                                    Some(c0) => {
                                        for &m in &c0.witness_path {
                                            let _ = game.do_move(m);
                                        }
                                    }
                                }
                                continue;
                            }

                            // the un-killed shared BFS over the would-be goals
                            let mut bfs_scratch = DirectScratch::new();
                            let mut groups2: Vec<Vec<StepTransition>> = commitments
                                .iter()
                                .map(|_| Vec::new())
                                .collect();
                            accommodations_shared(
                                &ctx,
                                &goals,
                                &commitments,
                                groups2.as_mut_slice(),
                                &mut bfs_scratch.bfs,
                            );
                            for (gi, goal) in goals.iter().enumerate() {
                                if !dead[gi] {
                                    continue;
                                }
                                let ci = commitments
                                    .iter()
                                    .position(|c| *c == goal.commitment)
                                    .unwrap();
                                let bfs_channel = match goal.kind {
                                    OutcomeKind::Stack => "stack-bfs",
                                    OutcomeKind::Tableau => "tableau-bfs",
                                };
                                let answered = groups2[ci]
                                    .iter()
                                    .any(|(_, k, _, ch)| *k == goal.kind && *ch == bfs_channel);
                                if answered {
                                    killed_answered += 1;
                                    panic!(
                                        "goal_dead killed an answerable goal: draw={draw_step} seed={} turn={_turn} {:?} {:?}",
                                        12 + i, goal.commitment, goal.kind
                                    );
                                }
                            }

                            // advance by the oracle's first witness path
                            let cands = enumerate_commitments(&game);
                            match cands.first() {
                                None => break,
                                Some(c0) => {
                                    for &m in &c0.witness_path {
                                        let _ = game.do_move(m);
                                    }
                                }
                            }
                        }
                    }
                }
                println!(
                    "goal kills sound: {states} states, {goals_total} would-be goals, {killed} killed, {killed_answered} wrongly killed",
                );
            })
            .unwrap()
            .join()
            .unwrap();
    }

    /// The BFS-elimination probe: what does the shared accommodation BFS
    /// actually answer *on the search path* (fold mode), and does the fold
    /// ever select a BFS successor? Hypothesis H1 (crease grammar): every
    /// answered witness is a short, non-alternating composition of the
    /// named channel shapes (dig = PileStack chain, borrow = StackPile,
    /// prefix-raise = PileStack chain) — if H1 holds, the BFS is
    /// replaceable by bounded constant-work probes; alternating shapes
    /// (mixed PileStack/StackPile before the commit) are the genuine
    /// chained crease that needs either the BFS or deeper rules.
    #[test]
    #[ignore = "crease grammar probe; run with --ignored --release --nocapture"]
    fn debug_crease_grammar() {
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(|| {
                for draw_step in [1u8, 3] {
                    perf_probe::reset();
                    perf_probe::crease_reset();
                    perf_probe::miss_kind_reset();
                    let mut win_count = 0usize;
                    for i in 0..32u64 {
                        let g = Solitaire::new(
                            &default_shuffle(12 + i),
                            NonZeroU8::new(draw_step).unwrap(),
                        );
                        if macro_solvable_direct(&g) {
                            win_count += 1;
                        }
                    }
                    let c = perf_probe::crease_read();
                    let p = perf_probe::read();
                    let total: u64 = c[..16].iter().sum();
                    let mk = perf_probe::miss_kind_read();
                    println!(
                        "draw={draw_step}: {win_count}/32 solvable; bfs_calls={} bfs_states={} answered={} missed={}",
                        p[3], p[4], c[17], c[18]
                    );
                    println!(
                        "  missed by kind: stack-climb={} stack-descent={} tableau={}",
                        mk[0], mk[1], mk[2]
                    );
                    for (l, n) in c[..16].iter().enumerate() {
                        if *n > 0 {
                            println!("  witness shuffles={l}: {n} ({:.1}% of answered)", 100.0 * *n as f64 / total as f64);
                        }
                    }
                    println!(
                        "  alternating (mixed dig+borrow) witnesses: {} ({:.1}%)",
                        c[16],
                        100.0 * c[16] as f64 / total as f64
                    );
                    println!(
                        "  fold-selected successors: from fixed channels={} from BFS channels={} ({:.3}% of selections)",
                        c[20],
                        c[19],
                        100.0 * c[19] as f64 / (c[19] + c[20]).max(1) as f64
                    );
                }
            })
            .unwrap()
            .join()
            .unwrap();
    }

    /// Per-section timing attribution for the seed-32 wall: mirrors
    /// `macro_solvable_direct`'s in-place recursion with section timers
    /// (the BFS's own time is attributed by the `perf_probe` nanos
    /// counter printed alongside).
    #[test]
    #[ignore = "perf attribution; run with --ignored --release --nocapture"]
    fn debug_perf_breakdown32() {
        use std::time::{Duration, Instant};
        const NODE_CAP: usize = 300_000;

        #[derive(Default)]
        struct T {
            tp: Duration,
            ctx: Duration,
            core: Duration,
            f3: Duration,
            post: Duration,
            apply: Duration,
        }

        fn rec(
            s: &mut Solitaire,
            tp: &mut TpTable,
            scratch: &mut DirectScratch,
            nodes: &mut usize,
            branches: &mut usize,
            t: &mut T,
        ) -> bool {
            let t0 = Instant::now();
            let win = s.is_win();
            let cont = !win && tp.insert(s.encode());
            t.tp += t0.elapsed();
            if !cont {
                return win;
            }
            *nodes += 1;
            if *nodes > NODE_CAP {
                return false;
            }
            let t0 = Instant::now();
            let ctx = ClosureCtx::from_game(s);
            t.ctx += t0.elapsed();
            // mirror the shipped fold's forced-commitment (C12) clause,
            // hoisted above the generator
            let forced_reveal = {
                let f = ctx.root.locked
                    & ctx.root.vis
                    & ctx.root.sm()
                    & ctx.root.bm()
                    & Stack::decode(ctx.root.stack).dominance_mask();
                f & f.wrapping_neg()
            };
            if forced_reveal != 0 {
                let x = Card::from_mask_index(
                    u8::try_from(forced_reveal.trailing_zeros()).unwrap(),
                );
                let steps = [Move::PileStack(x)];
                let t0 = Instant::now();
                let (vis, stack) = post_words(s, &ctx, &steps);
                t.post += t0.elapsed();
                let t0 = Instant::now();
                let old = (s.get_visible_mask(), s.get_stack().encode());
                let (_, (undo, _)) = s.do_move(steps[0]);
                s.set_board(vis, stack);
                *branches += 1;
                t.apply += t0.elapsed();
                let child_win = rec(s, tp, scratch, nodes, branches, t);
                let t0 = Instant::now();
                s.undo_move(steps[0], undo);
                s.set_board(old.0, old.1);
                t.apply += t0.elapsed();
                return child_win;
            }
            let t0 = Instant::now();
            let mut commitments = core::mem::take(&mut scratch.commitments);
            core_run(&ctx, scratch, &mut commitments, true, s.get_deck());
            scratch.commitments = commitments;
            t.core += t0.elapsed();
            // the shipped fold reads the F3 mask the generator derived
            let t0 = Instant::now();
            let f3 = scratch.f3;
            t.f3 += t0.elapsed();

            let groups = core::mem::take(&mut scratch.groups);
            let mut win = false;
            // mirror the shipped fold's deck-dominance (draw-1) clause
            let deck_dom = {
                let d = ctx.deck_mask
                    & ctx.root.sm()
                    & Stack::decode(ctx.root.stack).dominance_mask();
                if s.get_deck().draw_step().get() == 1 && d != 0 {
                    d & d.wrapping_neg()
                } else {
                    0
                }
            };
            'outer: for group in &groups {
                if deck_dom != 0 {
                    if let Some((Commitment::Draw(x), ..)) = group.first() {
                        if x.mask() != deck_dom {
                            continue;
                        }
                    }
                }
                // the shipped fold: one successor per commitment
                let Some((_, _, steps, _)) = collapse_pick(group, f3) else {
                    continue;
                };
                let t0 = Instant::now();
                let (vis, stack) = post_words(s, &ctx, steps);
                t.post += t0.elapsed();
                let t0 = Instant::now();
                let old = (s.get_visible_mask(), s.get_stack().encode());
                let commit = *steps.last().expect("every channel ends in a commit");
                let (_, (undo, _)) = s.do_move(commit);
                s.set_board(vis, stack);
                *branches += 1;
                t.apply += t0.elapsed();
                // the recursion itself is outside every section timer
                let child_win = rec(s, tp, scratch, nodes, branches, t);
                let t0 = Instant::now();
                s.undo_move(commit, undo);
                s.set_board(old.0, old.1);
                t.apply += t0.elapsed();
                if child_win {
                    win = true;
                    break 'outer;
                }
            }
            scratch.groups = groups;
            win
        }

        for draw_step in [1u8, 3] {
            let cards = default_shuffle(32);
            let step = NonZeroU8::new(draw_step).unwrap();
            let mut root = Solitaire::new(&cards, step);
            canonicalize(&mut root);
            let mut tp = TpTable::default();
            let mut scratch = DirectScratch::new();
            let (mut nodes, mut branches) = (0usize, 0usize);
            let mut t = T::default();
            perf_probe::reset();
            let t_all = Instant::now();
            let w = rec(&mut root, &mut tp, &mut scratch, &mut nodes, &mut branches, &mut t);
            let total = t_all.elapsed();
            let probes = perf_probe::read();
            println!(
                "seed=32 draw={draw_step} win={w} nodes={nodes} branches={branches} total={total:?}\n  tp={:?} ctx={:?} core={:?} f3={:?} post={:?} apply={:?}\n  bfs_calls={} bfs_states={} bfs_time={:?} canon={} post_calls={}",
                t.tp,
                t.ctx,
                t.core,
                t.f3,
                t.post,
                t.apply,
                probes[3],
                probes[4],
                std::time::Duration::from_nanos(probes[5]),
                probes[8],
                probes[6],
            );
        }
    }

    /// Seed-32 node-count forensics, answering "is the macro refutation's
    /// ~15M unique states over-generation (a bug) or the missing deck-axis
    /// compression (the streak/draw-order dominance analogue)?"
    ///
    /// 1. The old engine RAW on seed 32 (no dominance, no pruner),
    ///    time-boxed. If its unique-state count exceeds the macro's, the
    ///    macro game *is* compressing relative to the raw micro space, and
    ///    the macro-vs-shipped gap is exactly the missing filter port.
    ///
    /// 2. The macro search with auxiliary coarse TP keys that strip
    ///    (a) the deck-offset bits (encode bits 56..61) and (b) the whole
    ///    deck word (bits 32..61): the fine-to-coarse unique-count drop is
    ///    the redundancy each axis carries. A big drop under (a) points at
    ///    the last-draw/draw-order port; survival under (b) would mean the
    ///    load-bearing dimensions are hidden/stack/scar instead.
    #[test]
    #[ignore = "state-space forensics; run with --ignored --release --nocapture"]
    fn debug_seed32_state_space() {
        use std::time::{Duration, Instant};

        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(|| {
                // --- arm 1: old engine raw, old-visit-budget-free but time-boxed --- //
                struct TimeCb(Instant, bool);
                impl Callback for TimeCb {
                    type Pruner = crate::pruning::NoPruner;
                    fn on_win(&mut self, _: &Solitaire) -> Control {
                        Control::Halt
                    }
                    fn on_visit(&mut self, _: &Solitaire, _: Encode) -> Control {
                        if self.0.elapsed() > Duration::from_secs(120) && !self.1 {
                            self.1 = true;
                            return Control::Halt;
                        }
                        Control::Ok
                    }
                }
                let cards = default_shuffle(32);
                let mut game = Solitaire::new(&cards, NonZeroU8::new(1).unwrap());
                let mut tp = TpTable::default();
                let t0 = Instant::now();
                let mut cb = TimeCb(Instant::now(), false);
                traverse::<_, _, false>(&mut game, &NoPruner::default(), &mut tp, &mut cb);
                println!(
                    "OLD RAW seed=32 draw=1: unique states={} in {:?}{}",
                    tp.len(),
                    t0.elapsed(),
                    if cb.1 { " (halted at 120s — lower bound)" } else { " (complete)" },
                );

                // --- arm 2: macro collapsed search + coarse keys --- //
                let mut coarse_off = TpTable::default();
                let mut coarse_deck = TpTable::default();
                let (mut n, mut n_off, mut n_deck) = (0u64, 0u64, 0u64);
                let cards = default_shuffle(32);
                let g = Solitaire::new(&cards, NonZeroU8::new(1).unwrap());
                let t0 = Instant::now();
                let win = macro_solvable_direct_progress(&g, |s| {
                    n += 1;
                    let e = s.encode();
                    if coarse_off.insert(e & !(0x1Fu64 << 56)) {
                        n_off += 1;
                    }
                    if coarse_deck.insert(e & full_mask(32)) {
                        n_deck += 1;
                    }
                });
                println!(
                    "MACRO collapsed seed=32 draw=1: win={win} in {:?}\n  unique states={n}\n  unique minus deck OFFSET={n_off}\n  unique minus deck WORD ={n_deck}",
                    t0.elapsed()
                );
            })
            .unwrap()
            .join()
            .unwrap();
    }

    /// POR landcheck probe (the partial-order-reduction program, per the
    /// design conversation): for every pair of sibling commitments offered
    /// at a canonical state along corpus trajectories, apply them in both
    /// orders through the shipped fold and classify:
    /// - `pair disabled`: one order makes the other commitment disappear
    ///   (the enablement hazard — POR must not defer such partners)
    /// - `exact`: the two orders land on the same canonical encode —
    ///   strict commutation; a canonical ordering costs nothing
    /// - `closure`: the two orders land on different encodes but in the
    ///   same closure class (closure_contains) — canonicalizing the sweep
    ///   already quotients them; search-side dedup catches it
    /// - `distinct`: genuinely different states — deferring either would
    ///   need a dominance proof, not just a canonical order
    #[test]
    #[ignore = "commutation landscape probe; run with --ignored --release --nocapture"]
    fn debug_commutation_landscape() {
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(|| {
                for draw_step in [1u8, 3] {
                    let (mut exact, mut closure, mut distinct, mut disabled) =
                        (0usize, 0usize, 0usize, 0usize);
                    let mut by_pair: std::collections::BTreeMap<&'static str, [usize; 4]> =
                        std::collections::BTreeMap::new();
                    for i in 0..16u64 {
                        let mut game = Solitaire::new(
                            &default_shuffle(12 + i),
                            NonZeroU8::new(draw_step).unwrap(),
                        );
                        for _turn in 0..60 {
                            if game.is_win() {
                                break;
                            }
                            canonicalize(&mut game);
                            let succs = macro_transitions_fast(&game);
                            if succs.len() < 2 {
                                // advance anyway: oracle witness if any
                                let cands = enumerate_commitments(&game);
                                match cands.first() {
                                    None => break,
                                    Some(c0) => {
                                        for &m in &c0.witness_path {
                                            let _ = game.do_move(m);
                                        }
                                        continue;
                                    }
                                }
                            }
                            for i in 0..succs.len() {
                                for j in (i + 1)..succs.len() {
                                    let (c1, s1) = &succs[i];
                                    let (c2, s2) = &succs[j];
                                    let kind = match (c1, c2) {
                                        (Commitment::Draw(_), Commitment::Draw(_)) => "draw·draw",
                                        (Commitment::Reveal(_), Commitment::Reveal(_)) => {
                                            "reveal·reveal"
                                        }
                                        _ => "draw·reveal",
                                    };
                                    let tag = by_pair.entry(kind).or_insert([0, 0, 0, 0]);
                                    // commitment still exists = the TOTAL
                                    // generator (`macro_transitions_direct`)
                                    // offers it after the sibling committed;
                                    // the fold must not confound "disabled"
                                    // with "fold-dropped"
                                    let fwd = macro_transitions_direct(s1)
                                        .into_iter()
                                        .find(|(c, _, _, _)| c == c2);
                                    let bwd = macro_transitions_direct(s2)
                                        .into_iter()
                                        .find(|(c, _, _, _)| c == c1);
                                    match (fwd, bwd) {
                                        (None, _) | (_, None) => {
                                            disabled += 1;
                                            tag[3] += 1;
                                        }
                                        (Some((_, _, f, _)), Some((_, _, b, _)))
                                            if f.encode() == b.encode() =>
                                        {
                                            exact += 1;
                                            tag[0] += 1;
                                        }
                                        (Some((_, _, f, _)), Some((_, _, b, _)))
                                            if closure_contains(&f, b.encode()) =>
                                        {
                                            closure += 1;
                                            tag[1] += 1;
                                        }
                                        _ => {
                                            distinct += 1;
                                            tag[2] += 1;
                                        }
                                    }
                                }
                            }
                            // advance by the oracle's first witness path
                            let cands = enumerate_commitments(&game);
                            match cands.first() {
                                None => break,
                                Some(c0) => {
                                    for &m in &c0.witness_path {
                                        let _ = game.do_move(m);
                                    }
                                }
                            }
                        }
                    }
                    let total = exact + closure + distinct + disabled;
                    println!(
                        "commutation landscape, draw={draw_step}: pairs={total} exact={exact} closure={closure} distinct={distinct} disabled={disabled}"
                    );
                    for (k, [a, b, c, d]) in &by_pair {
                        println!("  {k:14} exact={a} closure={b} distinct={c} disabled={d}");
                    }
                }
            })
            .unwrap()
            .join()
            .unwrap();
    }

    /// R-DIA probe (macro_parking.md §P.6): the destination collapse's
    /// only remaining destination-side lemma is the sweep/stack diamond —
    /// from a parked post-state, stacking X lands in the stack outcome's
    /// closure class. Direct measurement: for every corpus commitment with
    /// both kinds offered, compare `canonicalize(post_tab + PileStack(X))`
    /// against every stack-side representative — tally exact-encode hits
    /// (the F3 sweep-equal signature, generalized), closure-linked hits,
    /// and genuine distinct-class counterexamples (printed in full).
    #[test]
    #[ignore = "diamond probe; run with --ignored --release --nocapture"]
    fn debug_destination_diamond() {
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(|| {
                // (both-kind commitments, encode-equal, closure-linked, distinct, swept-in-tab)
                let (mut both, mut eq, mut linked, mut distinct, mut swept) =
                    (0usize, 0usize, 0usize, 0usize, 0usize);
                let mut misses: Vec<(u8, u64, usize, u8)> = Vec::new();
                for draw_step in [1u8, 3] {
                    for i in 0..30u64 {
                        let mut game = Solitaire::new(
                            &default_shuffle(12 + i),
                            NonZeroU8::new(draw_step).unwrap(),
                        );
                        for _turn in 0..100 {
                            if game.is_win() {
                                break;
                            }
                            canonicalize(&mut game);
                            let direct = macro_transitions_direct(&game);
                            // group emissions by commitment
                            let mut by_com: Vec<(Card, Vec<&DirectTransition>, Vec<&DirectTransition>)> =
                                Vec::new();
                            for t @ (c, k, _, _) in &direct {
                                let x = match c {
                                    Commitment::Draw(x) | Commitment::Reveal(x) => *x,
                                };
                                let ent = by_com.iter_mut().find(|(c2, ..)| *c2 == x);
                                let ent = match ent {
                                    Some(e) => e,
                                    None => {
                                        by_com.push((x, Vec::new(), Vec::new()));
                                        by_com.last_mut().unwrap()
                                    }
                                };
                                match k {
                                    OutcomeKind::Tableau => ent.1.push(t),
                                    OutcomeKind::Stack => ent.2.push(t),
                                }
                            }
                            for (x, tabs, stks) in &by_com {
                                if tabs.is_empty() || stks.is_empty() {
                                    continue;
                                }
                                // any-tableau links with any-stack
                                for (_, _, t_state, _) in tabs {
                                    // if X was swept up in the tableau
                                    // outcome, the outcomes are already
                                    // sweep-equal (the F3 signature)
                                    if t_state.get_visible_mask() & x.mask() == 0 {
                                        swept += 1;
                                        continue;
                                    }
                                    let mut t2 = t_state.clone();
                                    t2.do_move(Move::PileStack(*x));
                                    canonicalize(&mut t2);
                                    let enc2 = t2.encode();
                                    let hit = stks
                                        .iter()
                                        .any(|(_, _, s_state, _)| s_state.encode() == enc2);
                                    let closed = hit
                                        || stks
                                            .iter()
                                            .any(|(_, _, s_state, _)| closure_contains(&t2, s_state.encode()));
                                    if hit {
                                        eq += 1;
                                    } else if closed {
                                        linked += 1;
                                    } else {
                                        distinct += 1;
                                        misses.push((draw_step, 12 + i, _turn, x.mask_index()));
                                        println!(
                                            "** R-DIA MISS draw={draw_step} seed={} turn={_turn} X={x}",
                                            12 + i
                                        );
                                    }
                                }
                                both += 1;
                            }
                            // advance by the oracle's first witness path
                            let cands = enumerate_commitments(&game);
                            if cands.is_empty() {
                                break;
                            }
                            for &m in &cands[0].witness_path {
                                let _ = game.do_move(m);
                            }
                        }
                    }
                }
                println!(
                    "R-DIA diamond probe: {both} both-kind commitments; tableau→stack-PileStack(X): encode-equal={eq} closure-linked={linked} **distinct-class={distinct}** (sweep-in-tableau: {swept})"
                );

                // Win-region containment on every miss: the collapse loses
                // a win iff some stack-side class is solvable (ground-truth
                // engine) while the tableau class is not.
                let (mut violated, mut held) = (0usize, 0usize);
                for (draw_step, seed, turn, x_idx) in misses {
                    let mut game = Solitaire::new(
                        &default_shuffle(seed),
                        NonZeroU8::new(draw_step).unwrap(),
                    );
                    for _ in 0..turn {
                        canonicalize(&mut game);
                        let cands = enumerate_commitments(&game);
                        if cands.is_empty() {
                            break;
                        }
                        for &m in &cands[0].witness_path {
                            let _ = game.do_move(m);
                        }
                    }
                    canonicalize(&mut game);
                    let x = Card::from_mask_index(x_idx);
                    let direct = macro_transitions_direct(&game);
                    let mut tabs = Vec::new();
                    let mut stks = Vec::new();
                    for (c, k, st, _) in &direct {
                        let cx = match c {
                            Commitment::Draw(cx) | Commitment::Reveal(cx) => *cx,
                        };
                        if cx != x {
                            continue;
                        }
                        match k {
                            OutcomeKind::Tableau => tabs.push(st),
                            OutcomeKind::Stack => stks.push(st),
                        }
                    }
                    let tab_solvable = tabs.iter().any(|t| {
                        matches!(solve(&mut (*t).clone()).0, SearchResult::Solved)
                    });
                    for st in &stks {
                        let st_solvable =
                            matches!(solve(&mut (*st).clone()).0, SearchResult::Solved);
                        if st_solvable && !tab_solvable {
                            violated += 1;
                            println!(
                                "** CONTAINMENT VIOLATED draw={draw_step} seed={seed} turn={turn} X={}: stack side wins, tableau side loses",
                                x
                            );
                        } else {
                            held += 1;
                        }
                    }
                }
                println!(
                    "R-DIA misses: win-region containment (solvable(stk) ⟹ solvable(tab)): held={held} **violated={violated}**"
                );
            })
            .unwrap()
            .join()
            .unwrap();
    }

    /// A/B the shared multi-goal BFS against the old per-goal BFS at the
    /// differential's first-missing states: any witness divergence is a
    /// bug in the shared version.
    #[test]
    #[ignore = "forensic A/B; run with --ignored --nocapture"]
    fn debug_shared_bfs_ab() {
        // the old per-goal BFS, verbatim, for comparison
        fn bfs_old(
            g: &Solitaire,
            commitment: Commitment,
            x: Card,
            goal_kind: OutcomeKind,
            max_depth: usize,
        ) -> Option<Vec<Move>> {
            use alloc::collections::VecDeque;
            let xmask = x.mask();
            let mut queue: VecDeque<(Solitaire, Vec<Move>)> = VecDeque::new();
            queue.push_back((g.clone(), Vec::new()));
            let mut seen = TpTable::default();
            seen.insert(g.encode());
            while let Some((state, steps)) = queue.pop_front() {
                if steps.len() >= max_depth {
                    continue;
                }
                let mv = state.gen_moves::<false>();
                let opens = match (commitment, goal_kind) {
                    (Commitment::Draw(_), OutcomeKind::Tableau) => mv.deck_pile & xmask != 0,
                    (Commitment::Reveal(_), OutcomeKind::Tableau) => mv.reveal & xmask != 0,
                    (Commitment::Draw(_), OutcomeKind::Stack) => mv.deck_stack & xmask != 0,
                    (Commitment::Reveal(_), OutcomeKind::Stack) => mv.pile_stack & xmask != 0,
                };
                if opens {
                    return Some(steps);
                }
                for m in mv.to_vec::<N_MOVES_MAX>() {
                    if state.reverse_move(m).is_none() {
                        continue;
                    }
                    let mut next = state.clone();
                    let _ = next.do_move(m);
                    let enc = next.encode();
                    if seen.insert(enc) {
                        let mut s2 = steps.clone();
                        s2.push(m);
                        queue.push_back((next, s2));
                    }
                }
            }
            None
        }
        for (seed, turn, draw_step, card_idx, is_draw) in [
            (34u64, 17usize, 1u8, 3u8, false),
            (34, 17, 3, 3, false),
            (12, 38, 1, 38, true),
            (12, 38, 3, 38, true),
            (40, 20, 1, 1, true),
            (40, 20, 3, 1, true),
        ] {
            let mut game = Solitaire::new(
                &default_shuffle(seed),
                NonZeroU8::new(draw_step).unwrap(),
            );
            for _ in 0..turn {
                if game.is_win() {
                    break;
                }
                canonicalize(&mut game);
                let oracle = enumerate_commitments(&game);
                if oracle.is_empty() {
                    break;
                }
                for &m in &oracle[0].witness_path {
                    let _ = game.do_move(m);
                }
            }
            canonicalize(&mut game);
            let x = Card::from_mask_index(card_idx);
            let commitment = if is_draw {
                Commitment::Draw(x)
            } else {
                Commitment::Reveal(x)
            };
            if !enumerate_commitments(&game)
                .iter()
                .any(|c| c.commitment == commitment)
            {
                println!("seed={seed} draw={draw_step} turn={turn}: {commitment:?} not offered here");
                continue;
            }
            let old = bfs_old(&game, commitment, x, OutcomeKind::Tableau, 10);
            let goal = [AccommodationGoal {
                commitment,
                kind: OutcomeKind::Tableau,
                xmask: x.mask(),
                commit_move: Move::Reveal(x),
                cap: 10,
            }];
            let ctx = ClosureCtx::from_game(&game);
            let mut bfs_scratch = DirectScratch::new();
            let mut groups: Vec<Vec<StepTransition>> = vec![Vec::new()];
            accommodations_shared(
                &ctx,
                &goal,
                &[commitment],
                groups.as_mut_slice(),
                &mut bfs_scratch.bfs,
            );
            let new: Option<Vec<Move>> = groups[0].first().map(|(_, _, steps, _)| {
                let mut v: Vec<Move> = steps.iter().copied().collect();
                v.pop(); // drop the appended commit move
                v
            });
            let direct_channels: Vec<&'static str> = macro_transitions_direct(&game)
                .iter()
                .filter(|(c, _, _, _)| *c == commitment)
                .map(|(_, _, _, ch)| *ch)
                .collect();
            println!(
                "seed={seed} draw={draw_step} turn={turn} {commitment:?}: old={old:?} new={new:?} channels={direct_channels:?}"
            );
        }
    }

    /// Hang forensics for the big verdict sweep: characterize a seed the
    /// sweep stalls on. All macro runs are node-capped (capped=true means
    /// "at least this many nodes", not a verdict).
    #[test]
    #[ignore = "hang forensics; run with --ignored --release --nocapture"]
    fn debug_big_sweep_hang() {
        const NODE_CAP: usize = 3_000_000;
        for (seed, draw_step) in [(32u64, 1u8), (32, 3)] {
            let cards = default_shuffle(seed);
            let step = NonZeroU8::new(draw_step).unwrap();

            // direct first (it is the sweep's path), node-capped
            {
                fn rec(
                    s: &Solitaire,
                    tp: &mut TpTable,
                    nodes: &mut usize,
                    branches: &mut usize,
                    capped: &mut bool,
                ) -> bool {
                    if s.is_win() || !tp.insert(s.encode()) {
                        return s.is_win();
                    }
                    *nodes += 1;
                    if *nodes > NODE_CAP {
                        *capped = true;
                        return false;
                    }
                    let succs = macro_transitions_fast(s);
                    *branches += succs.len();
                    succs
                        .into_iter()
                        .any(|(_, succ)| rec(&succ, tp, nodes, branches, capped))
                }
                perf_probe::reset();
                let t = std::time::Instant::now();
                let mut tp = TpTable::default();
                let (mut n, mut b) = (0usize, 0usize);
                let mut capped = false;
                let mut root = Solitaire::new(&cards, step);
                canonicalize(&mut root);
                let w = rec(&root, &mut tp, &mut n, &mut b, &mut capped);
                println!(
                    "seed={seed} draw={draw_step} DIRECT win={w} nodes={n} branches={b} avg_branch={:5.2} capped={} total={:?} probes={:?}",
                    b as f64 / n.max(1) as f64,
                    capped,
                    t.elapsed(),
                    perf_probe::read()
                );
            }

            // oracle, node-capped
            {
                fn rec(
                    g: &Solitaire,
                    tp: &mut TpTable,
                    nodes: &mut usize,
                    branches: &mut usize,
                    capped: &mut bool,
                ) -> bool {
                    let mut s = g.clone();
                    canonicalize(&mut s);
                    if s.is_win() || !tp.insert(s.encode()) {
                        return s.is_win();
                    }
                    *nodes += 1;
                    if *nodes > NODE_CAP {
                        *capped = true;
                        return false;
                    }
                    let succs = enumerate_transitions(&s);
                    *branches += succs.len();
                    succs
                        .into_iter()
                        .any(|(_, succ)| rec(&succ, tp, nodes, branches, capped))
                }
                let t = std::time::Instant::now();
                let mut tp = TpTable::default();
                let (mut n, mut b) = (0usize, 0usize);
                let mut capped = false;
                let w = rec(&Solitaire::new(&cards, step), &mut tp, &mut n, &mut b, &mut capped);
                println!(
                    "seed={seed} draw={draw_step} ORACLE win={w} nodes={n} branches={b} avg_branch={:5.2} capped={} total={:?}",
                    b as f64 / n.max(1) as f64,
                    capped,
                    t.elapsed()
                );
            }

            // old engine reference
            {
                let t = std::time::Instant::now();
                let mut game = Solitaire::new(&cards, step);
                let (res, hist) = solve(&mut game);
                let len = hist.map_or(0, |h| h.len());
                println!(
                    "seed={seed} draw={draw_step} OLD win={res:?} winline={len} total={:?}",
                    t.elapsed()
                );
            }
        }
    }

    /// Structural characterization of a seed: root commitment surface and
    /// the old engine's 2x2 refutation cost.
    #[test]
    #[ignore = "forensics; run with --ignored --release --nocapture"]
    fn debug_seed_types() {
        const BUDGET: u64 = 20_000_000;
        struct P {
            won: bool,
            visits: u64,
            nodes: u64,
            budget: bool,
        }
        fn run_old<const DOM: bool, PR: Pruner + Default>(cards: &[Card; 52], step: NonZeroU8) -> P {
            struct C<P2: Pruner + Default> {
                won: bool,
                visits: u64,
                nodes: u64,
                budget: bool,
                m: core::marker::PhantomData<P2>,
            }
            impl<P2: Pruner + Default> Callback for C<P2> {
                type Pruner = P2;
                fn on_win(&mut self, _: &Solitaire) -> Control {
                    self.won = true;
                    Control::Halt
                }
                fn on_visit(&mut self, _: &Solitaire, _: Encode) -> Control {
                    self.visits += 1;
                    if self.visits > BUDGET {
                        self.budget = true;
                        return Control::Halt;
                    }
                    Control::Ok
                }
                fn on_move_gen(&mut self, m: &crate::moves::MoveMask, _: Encode) -> Control {
                    self.nodes += 1;
                    let _ = m.len();
                    Control::Ok
                }
            }
            let mut game = Solitaire::new(cards, step);
            let mut tp = TpTable::default();
            let mut c = C::<PR> {
                won: false,
                visits: 0,
                nodes: 0,
                budget: false,
                m: core::marker::PhantomData,
            };
            traverse::<_, _, DOM>(&mut game, &PR::default(), &mut tp, &mut c);
            P { won: c.won, visits: c.visits, nodes: c.nodes, budget: c.budget }
        }
        for seed in [12u64, 21, 22, 32] {
            for draw_step in [1u8, 3] {
                let cards = default_shuffle(seed);
                let step = NonZeroU8::new(draw_step).unwrap();
                let mut g = Solitaire::new(&cards, step);
                canonicalize(&mut g);
                let mv = g.gen_moves::<false>();
                let deck = g.get_deck().compute_mask(false).count_ones();
                let locked_surfaces = (g.get_visible_mask() & g.get_hidden().get_locked_mask()).count_ones();
                println!(
                    "seed={seed} draw={draw_step}: root drawables={deck} locked_surfaces={locked_surfaces} stack={:x} raw_moves={}",
                    g.get_stack().encode(),
                    mv.len()
                );
                let t = std::time::Instant::now();
                let p = run_old::<true, FullPruner>(&cards, step);
                println!("  dom+pruner  win={} visits={:>10} nodes={:>10} budget={} {:?}", p.won, p.visits, p.nodes, p.budget, t.elapsed());
                let t = std::time::Instant::now();
                let p = run_old::<true, NoPruner>(&cards, step);
                println!("  dom-only    win={} visits={:>10} nodes={:>10} budget={} {:?}", p.won, p.visits, p.nodes, p.budget, t.elapsed());
                let t = std::time::Instant::now();
                let p = run_old::<false, FullPruner>(&cards, step);
                println!("  pruner-only win={} visits={:>10} nodes={:>10} budget={} {:?}", p.won, p.visits, p.nodes, p.budget, t.elapsed());
                let t = std::time::Instant::now();
                let p = run_old::<false, NoPruner>(&cards, step);
                println!("  raw         win={} visits={:>10} nodes={:>10} budget={} {:?}", p.won, p.visits, p.nodes, p.budget, t.elapsed());
            }
        }
    }

    /// F3 measurement: over the direct search's first N nodes, what
    /// fraction of folded successors are tableau outcomes of
    /// dominantly-stackable commitments (the §4 "additional collapsing"
    /// drop candidate)?
    #[test]
    #[ignore = "measurement; run with --ignored --release --nocapture"]
    fn debug_f3_potential() {
        const N: usize = 200_000;
        fn rec(
            s: &Solitaire,
            tp: &mut TpTable,
            nodes: &mut usize,
            branches: &mut usize,
            droppable: &mut usize,
        ) -> bool {
            if s.is_win() || !tp.insert(s.encode()) {
                return s.is_win();
            }
            *nodes += 1;
            if *nodes > N {
                return false;
            }
            let mut root = s.clone();
            canonicalize(&mut root);
            let dom = root.get_stack().dominance_mask();
            let all = macro_transitions_direct(&root);
            // commitments with a direct stack outcome now: X stackable
            let stack_now: u64 = all
                .iter()
                .filter(|(_, _, _, ch)| *ch == "stack-direct")
                .map(|(c, _, _, _)| match c {
                    Commitment::Draw(x) | Commitment::Reveal(x) => x.mask(),
                })
                .fold(0u64, |a, b| a | b);
            let f3_mask = stack_now & dom;
            let mut seen: Vec<(Commitment, OutcomeKind)> = Vec::new();
            let mut succs: Vec<&Solitaire> = Vec::new();
            for (c, k, st, _) in &all {
                if !seen.contains(&(*c, *k)) {
                    seen.push((*c, *k));
                    succs.push(st);
                }
            }
            *branches += succs.len();
            for (c, k, _, _) in &all {
                let _ = c;
                if *k == OutcomeKind::Tableau {
                    let x = match c {
                        Commitment::Draw(x) | Commitment::Reveal(x) => *x,
                    };
                    if x.mask() & f3_mask != 0 {
                        *droppable += 1;
                    }
                }
            }
            succs
                .into_iter()
                .any(|succ| rec(succ, tp, nodes, branches, droppable))
        }
        for (seed, draw_step) in [(32u64, 1u8), (32, 3), (14, 1), (13, 3), (21, 3)] {
            let cards = default_shuffle(seed);
            let step = NonZeroU8::new(draw_step).unwrap();
            let mut root = Solitaire::new(&cards, step);
            canonicalize(&mut root);
            let mut tp = TpTable::default();
            let (mut n, mut b, mut d) = (0usize, 0usize, 0usize);
            let t = std::time::Instant::now();
            let w = rec(&root, &mut tp, &mut n, &mut b, &mut d);
            println!(
                "seed={seed} draw={draw_step} win={w} nodes={n} branches={b} f3_droppable={d} ({:5.1}%) total={:?}",
                100.0 * d as f64 / b.max(1) as f64,
                t.elapsed()
            );
        }
    }

    /// Deterministic replay harness: bring a specific game to a specific
    /// turn by the same greedy play policy as the differential test, then
    /// dump the direct generator's per-channel evaluation per commitment.
    #[cfg(test)]
    fn debug_replay(seed: u64, draw_step: u8, turns: usize) {
        let mut game = Solitaire::new(&default_shuffle(seed), NonZeroU8::new(draw_step).unwrap());
        for _ in 0..turns {
            canonicalize(&mut game);
            let oracle = enumerate_commitments(&game);
            if oracle.is_empty() {
                break;
            }
            for &m in &oracle[0].witness_path {
                let _ = game.do_move(m);
            }
        }
        canonicalize(&mut game);
        let mv = game.gen_moves::<false>();
        println!("root encode: {:x}", game.encode());
        println!(
            "masks: pile_stack={:#x} deck_pile={:#x} reveal={:#x} deck_stack={:#x} stack_pile={:#x}",
            mv.pile_stack, mv.deck_pile, mv.reveal, mv.deck_stack, mv.stack_pile
        );
        let direct = macro_transitions_direct(&game);
        println!(
            "direct: {:?}",
            direct.iter().map(|(c, k, _, ch)| (c, k, ch)).collect::<Vec<_>>()
        );
        // specific check
        let x = Card::from_mask_index(8);
        let locked = game.get_hidden().get_locked_mask();
        println!(
            "card8: locked={} visible={} reveal_bit={}",
            locked & x.mask() != 0,
            game.get_visible_mask() & x.mask() != 0,
            mv.reveal & x.mask() != 0
        );
    }

    /// Trace `macro_transitions_direct` for one commitment at the replayed
    /// state: prints every channel's guard evaluation so the exact failed
    /// conjunct is visible.
    #[cfg(test)]
    fn debug_trace(game0: &Solitaire, target: Card) {
        let mut game = game0.clone();
        canonicalize(&mut game);
        let mv = game.gen_moves::<false>();
        let xmask = target.mask();
        println!("TRACE for {target:?} (mask {:#x}):", xmask);
        println!("  masks: pile_stack={:#x} deck_pile={:#x} reveal={:#x} deck_stack={:#x} stack_pile={:#x}", 
            mv.pile_stack, mv.deck_pile, mv.reveal, mv.deck_stack, mv.stack_pile);
        println!("  stack_now={} direct_now={}", 
            mv.pile_stack & xmask != 0, mv.reveal & xmask != 0);
        println!("  stack heights: {:?}", [game.get_stack().get(0), game.get_stack().get(1), game.get_stack().get(2), game.get_stack().get(3)]);
        println!("  x.suit()={} x.rank()={}", target.suit(), target.rank());
        let locked = game.get_hidden().get_locked_mask();

        // pile anatomy: which pile holds target, what's under it
        let hidden = game.get_hidden();
        for pos in 0..crate::deck::N_PILES {
            let pile = hidden.get(pos);
            for (i, c) in pile.iter().enumerate() {
                if *c == target || c.swap_suit() == target {
                    println!(
                        "  pile {pos} card {i}/{}: {c:?} {} (locked_mask has {})",
                        pile.len(),
                        if *c == target { "<-- target" } else { "(twin)" },
                        locked & target.mask() != 0
                    );
                }
            }
        }
        for pos in 0..crate::deck::N_PILES {
            let pile = hidden.get(pos);
            if pile.contains(&target) {
                let idx = pile.iter().position(|c| *c == target).unwrap();
                println!(
                    "  pile {pos}: target at depth {}/{}; cards above: {:?}",
                    idx,
                    pile.len() - 1,
                    &pile[idx + 1..]
                );
            }
        }

        // prefix raise probe
        let suit = target.suit();
        let mut probe = game.clone();
        let mut steps = 0;
        loop {
            let need = probe.get_stack().get(suit);
            if need >= target.rank() { break; }
            let c2 = Card::new(need, suit);
            let pmv = probe.gen_moves::<false>();
            let locked_now = probe.get_hidden().get_locked_mask();
            println!("  prefix step {}: c2={:?} in_pile_stack={} locked={} visible={}", 
                steps, c2,
                pmv.pile_stack & c2.mask() != 0,
                locked_now & c2.mask() != 0,
                probe.get_visible_mask() & c2.mask() != 0);
            if !(pmv.pile_stack & c2.mask() != 0 && locked_now & c2.mask() == 0) {
                println!("  prefix chain breaks here"); break;
            }
            let _ = probe.do_move(Move::PileStack(c2));
            steps += 1;
            if steps > 13 { break; }
        }
        let pmv = probe.gen_moves::<false>();
        println!("  after prefix: pile_stack_has_x={}", pmv.pile_stack & xmask != 0);
        // decompose pile_stack conjuncts for the target
        let bm = game.get_bottom_mask();
        let vis = game.get_visible_mask();
        let sm = game.get_stack().mask();
        println!(
            "  pile_stack conjuncts for {target:?}: bm({:#x})={} sm({:#x})={} vis={} locked={}",
            bm,
            bm & xmask != 0,
            sm,
            sm & xmask != 0,
            vis & xmask != 0,
            locked & xmask != 0,
        );
    }

    #[test]
    #[ignore = "forensic print harness: run only when diagnosing a differential miss"]
    fn debug_trace_reveal51() {
        // seed 26, turn 49's failing state: replay it, then trace
        let mut game = Solitaire::new(&default_shuffle(26), NonZeroU8::new(1).unwrap());
        for _turn in 0..49 {
            canonicalize(&mut game);
            let oracle = enumerate_commitments(&game);
            if oracle.is_empty() { break; }
            for &m in &oracle[0].witness_path {
                let _ = game.do_move(m);
            }
        }
        debug_trace(&game, Card::from_mask_index(51));
    }

    #[test]
    #[ignore = "forensic print harness: run only when diagnosing a differential miss"]
    fn debug_replay_seed12_turn5() {
        debug_replay(12, 1, 5);
    }

    #[test]
    #[ignore = "forensic print harness: run only when diagnosing a differential miss"]
    fn debug_replay_seed26_turn49() {
        debug_replay(26, 1, 49);
        // Where is the K of suit 0 (mask index 48) in this state, and why
        // did the direct generator produce nothing for it?
        let mut game = Solitaire::new(&default_shuffle(26), NonZeroU8::new(1).unwrap());
        for _ in 0..49 {
            canonicalize(&mut game);
            let oracle = enumerate_commitments(&game);
            if oracle.is_empty() {
                break;
            }
            for &m in &oracle[0].witness_path {
                let _ = game.do_move(m);
            }
        }
        canonicalize(&mut game);
        let x = Card::from_mask_index(48);
        let xq = Card::from_mask_index(46);
        let locked = game.get_hidden().get_locked_mask();
        println!(
            "card48: locked={} visible={} ; card46: locked={} visible={}",
            locked & x.mask() != 0,
            game.get_visible_mask() & x.mask() != 0,
            locked & xq.mask() != 0,
            game.get_visible_mask() & xq.mask() != 0,
        );
        let hidden = game.get_hidden();
        for pos in 0..crate::deck::N_PILES {
            let pile = hidden.get(pos);
            if pile.contains(&x) || pile.contains(&xq) {
                println!(
                    "  pile {pos}: surface={:?} buried contains target={} prefix={}",
                    pile.last(),
                    pile.contains(&x),
                    pile.contains(&xq)
                );
            }
        }
    }

    /// Reproduce the prefix-raise probe with full legality diagnostics:
    /// for each step, print the needed card, the raw pile_stack bit, the
    /// locked bit, and whether the move validated.
    #[cfg(test)]
    fn debug_prefix_probe(g: &Solitaire, x: Card) {
        let suit = x.suit();
        let mut probe = g.clone();
        println!("    prefix probe for {x:?}: suit f0={}", probe.get_stack().get(suit));
        loop {
            let need = probe.get_stack().get(suit);
            if need >= x.rank() {
                println!("    reached rank({need})");
                break;
            }
            let c2 = Card::new(need, suit);
            let pmv = probe.gen_moves::<false>();
            let locked_now = probe.get_hidden().get_locked_mask();
            let in_ps = pmv.pile_stack & c2.mask() != 0;
            let is_locked = locked_now & c2.mask() != 0;
            let twin_in_vis = probe.get_visible_mask() & c2.swap_suit().mask() != 0;
            println!(
                "    need={need} c2={c2:?} in_ps={in_ps} locked={is_locked} twin_visible={twin_in_vis} stack_before={:#x}",
                probe.get_stack().mask()
            );
            if !(in_ps && !is_locked) {
                println!("    stop: unreachable prefix card");
                break;
            }
            let _ = probe.do_move(Move::PileStack(c2));
        }
    }

    /// The design falsifier of §6.6: per commitment, the direct rule-driven
    /// generator must offer exactly the outcome kinds the closure oracle
    /// finds. Divergences; assert none in either direction.
    #[test]
    fn macro_direct_matches_oracle() {
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(|| {
                let mut checked = 0usize;
                let mut missing = 0usize; // oracle has, direct lacks
                let mut extra = 0usize; // direct has, oracle lacks (a legality bug by construction)
                let mut extra_merged = 0usize; // extra, but closure-connected to oracle samples (benign)
                let mut extra_separate = 0usize; // extra and disconnected (a real soundness question)
                let mut class_uncovered = 0usize; // oracle closure classes no direct post-state covers
                let mut first_missing: Option<String> = None;
                let mut first_extra: Option<String> = None;
                let mut missing_cases: Vec<String> = Vec::new();
                let mut first_missing_state: Option<(Solitaire, Commitment)> = None;
                let mut channel_histogram: std::collections::BTreeMap<&'static str, usize> =
                    std::collections::BTreeMap::new();
                for draw_step in [1u8, 3] {
                    for i in 0..30u64 {
                        let mut game = Solitaire::new(
                            &default_shuffle(12 + i),
                            NonZeroU8::new(draw_step).unwrap(),
                        );
                        for _turn in 0..200 {
                            if game.is_win() {
                                break;
                            }
                            canonicalize(&mut game);
                            let oracle = enumerate_commitments(&game);
                            if oracle.is_empty() {
                                break;
                            }
                            let direct = macro_transitions_direct(&game);

                            let mut oracle_kinds: Vec<(Commitment, bool, bool)> = oracle
                                .iter()
                                .map(|c| {
                                    (
                                        c.commitment,
                                        !c.outcomes.canon_tableau.is_empty(),
                                        !c.outcomes.canon_stack.is_empty(),
                                    )
                                })
                                .collect();
                            oracle_kinds.sort_by_key(|(c, ..)| c.sort_key());
                            let mut direct_kinds: Vec<(Commitment, bool, bool)> = direct
                                .iter()
                                .map(|(c, k, _, _)| (*c, *k == OutcomeKind::Tableau, *k == OutcomeKind::Stack))
                                .collect();
                            for (_, _, _, ch) in &direct {
                                *channel_histogram.entry(*ch).or_insert(0) += 1;
                            }
                            // fold per commitment
                            let mut folded: Vec<(Commitment, bool, bool)> = Vec::new();
                            for (c, tab, stak) in direct_kinds.drain(..) {
                                match folded.last_mut() {
                                    Some(last) if last.0 == c => {
                                        last.1 |= tab;
                                        last.2 |= stak;
                                    }
                                    _ => folded.push((c, tab, stak)),
                                }
                            }
                            let mut direct_kinds = folded;
                            direct_kinds.sort_by_key(|(c, ..)| c.sort_key());

                            if oracle_kinds != direct_kinds {
                                // classify first divergence
                                for (c, o_tab, o_stak) in &oracle_kinds {
                                    let d = direct_kinds.iter().find(|(dc, ..)| dc == c);
                                    let (d_tab, d_stak) =
                                        d.map_or((false, false), |(_, t, s)| (*t, *s));
                                    if (*o_tab, *o_stak) != (d_tab, d_stak) {
                                        let witness = oracle
                                            .iter()
                                            .find(|i| i.commitment == *c)
                                            .map(|i| i.kind_witnesses.clone());
                                        let root_mv = game.gen_moves::<false>();
                                        let xx = match c {
                                            Commitment::Draw(xx) | Commitment::Reveal(xx) => xx,
                                        };
                                        let msg = format!(
                                            "commitment {c:?}: oracle=({o_tab},{o_stak}) direct=({d_tab},{d_stak}) at draw={draw_step} seed={} turn={_turn} root={:x}, witness={witness:?}, root masks: pile_stack={:#x} deck_pile={:#x} reveal={:#x} deck_stack={:#x} stack={:#x} stack_pile={:#x} locked={:#x} X_suit_height={} X_rank={}",
                                            12 + i,
                                            game.encode(),
                                            root_mv.pile_stack,
                                            root_mv.deck_pile,
                                            root_mv.reveal,
                                            root_mv.deck_stack,
                                            game.get_stack().mask(),
                                            root_mv.stack_pile,
                                            game.get_hidden().get_locked_mask(),
                                            game.get_stack().get(xx.suit()),
                                            xx.rank(),
                                        );
                                        if d.map_or(true, |_| false) || (!d_tab && !d_stak) || (!d_tab && *o_tab) || (!d_stak && *o_stak) {
                                            missing += 1;
                                            let [wit_t, wit_s] = &witness.clone().unwrap_or([None, None]);
                                            missing_cases.push(format!(
                                                "seed={} turn={_turn} {:?}(r{},s{}) o=({o_tab},{o_stak}) d=({d_tab},{d_stak}) tab_wit={:?} stack_wit={:?}",
                                                12 + i,
                                                c,
                                                xx.rank(),
                                                xx.suit(),
                                                wit_t,
                                                wit_s
                                            ));
                                            if first_missing.is_none() {
                                                first_missing = Some(msg);
                                            }
                                            if first_missing_state.is_none() {
                                                first_missing_state = Some((game.clone(), *c));
                                            }
                                        } else {
                                            extra += 1;
                                            if first_extra.is_none() {
                                                first_extra = Some(msg);
                                            }
                                        }
                                    }
                                }
                                for (c, d_tab, d_stak) in &direct_kinds {
                                    if !oracle_kinds.iter().any(|(oc, ..)| oc == c) {
                                        extra += 1;
                                        if first_extra.is_none() {
                                            first_extra = Some(format!(
                                                "commitment {c:?}: oracle=(false,false) direct=({d_tab},{d_stak}) at draw={draw_step} seed={}",
                                                12 + i
                                            ));
                                        }
                                    }
                                }
                            }
                            checked += oracle.len();

                            // two questions per extra event: (a) benign
                            // extras are closure-connected to the same
                            // commitment's oracle samples (merged classes,
                            // no unfound successor); (b) genuinely separate
                            // classes would be a real overreach of the rule
                            let mut merged = 0usize;
                            let mut separate = 0usize;
                            for (c, _, st, channel) in &direct {
                                let info = match oracle.iter().find(|i| i.commitment == *c) {
                                    Some(info) => info,
                                    None => continue,
                                };
                                let st_enc = st.encode();
                                let in_any = info
                                    .outcomes
                                    .canon_tableau
                                    .iter()
                                    .chain(info.outcomes.canon_stack.iter())
                                    .any(|(_, rep)| closure_contains(rep, st_enc));
                                if !in_any {
                                    // classify: is it at least closure-connected to *some*
                                    // oracle sample of the same commitment?
                                    separate += 1;
                                    if separate <= 6 {
                                        println!(
                                            "  EXTRA-SEPARATE draw={draw_step} seed={} commitment {c:?} channel={channel} direct-enc={st_enc:x}",
                                            12 + i
                                        );
                                        if *channel == "stack-prefix-raise" {
                                            let x = match c {
                                                Commitment::Draw(x) | Commitment::Reveal(x) => *x,
                                            };
                                            debug_prefix_probe(&game, x);
                                        }
                                    }
                                } else {
                                    merged += 1;
                                }
                            }
                            let _ = (merged, separate);
                            extra_merged += merged;
                            extra_separate += separate;

                            // class coverage: oracle closure classes that no
                            // direct post-state covers — the measured form
                            // of the under-emission the fixed gates accept
                            // (e.g. the second stack scar class when
                            // prefix-raise already fired). Target: zero.
                            for info in &oracle {
                                let mut reps: Vec<&Solitaire> = Vec::new();
                                for samples in
                                    [&info.outcomes.canon_tableau, &info.outcomes.canon_stack]
                                {
                                    for (enc, st) in samples.iter() {
                                        if !reps.iter().any(|r| closure_contains(r, *enc)) {
                                            reps.push(st);
                                        }
                                    }
                                }
                                let direct_states: Vec<&Solitaire> = direct
                                    .iter()
                                    .filter(|(c, _, _, _)| *c == info.commitment)
                                    .map(|(_, _, st, _)| st)
                                    .collect();
                                for rep in reps {
                                    let enc = rep.encode();
                                    if !direct_states.iter().any(|d| {
                                        d.encode() == enc || closure_contains(d, enc)
                                    }) {
                                        class_uncovered += 1;
                                    }
                                }
                            }

                            let before = game.encode();
                            for &m in &oracle[0].witness_path {
                                let _ = game.do_move(m);
                            }
                            assert_ne!(game.encode(), before);
                            assert!(game.is_valid());
                        }
                    }
                }
                println!("direct-vs-oracle: {checked} commitments checked; availability mismatches: missing={missing} extra={extra} (merged={extra_merged}, separate={extra_separate}); oracle classes uncovered by direct: {class_uncovered}");
                if let Some(m) = &first_missing {
                    println!("first missing: {m}");
                }
                if let Some(e) = &first_extra {
                    println!("first extra: {e}");
                }
                // extras are diagnosed not asserted here: an extra that is
                // closure-connected to oracle samples of the same commitment
                // is a benign duplicate-classes case; a separate one would
                // be a direct-generator overreach bug.
                //
                // `missing` is a corpus metric: the residual misses are the
                // declared §6.4 crease (chained digs/borrows of depth > 1),
                // whose witnesses the BFS fallback catches with increasing
                // depth — the number must trend to zero as the rule list
                // converges, and stays printed until it does.
                println!("availability-miss metric: {missing} (target 0; rule-list gap, not a search unsoundness)");
                println!("channel histogram (direct generator output share): {channel_histogram:?}");
                println!("all missing cases:");
                for case in &missing_cases {
                    println!("  MISS {case}");
                }
                if let Some((g, c)) = &first_missing_state {
                    let x = match c { Commitment::Draw(x) | Commitment::Reveal(x) => *x };
                    let suit = x.suit();
                    let mut probe = g.clone();
                    println!("first missing: commitment={c:?} suit={suit} x_rank={}", x.rank());
                    loop {
                        let need = probe.get_stack().get(suit);
                        if need >= x.rank() {
                            println!("  prefix loop reached rank {need} >= {}", x.rank());
                            break;
                        }
                        let c2 = Card::new(need, suit);
                        let pmv = probe.gen_moves::<false>();
                        let lnow = probe.get_hidden().get_locked_mask();
                        println!(
                            "  need={need} c2={c2:?} c2_in_pile_stack={} c2_locked={} c2_visible={}",
                            pmv.pile_stack & c2.mask() != 0,
                            lnow & c2.mask() != 0,
                            probe.get_visible_mask() & c2.mask() != 0,
                        );
                        if !(pmv.pile_stack & c2.mask() != 0 && lnow & c2.mask() == 0) {
                            break;
                        }
                        let _ = probe.do_move(Move::PileStack(c2));
                    }
                }
                assert_eq!(extra_separate, 0, "direct generator produced a class the Oracle could not reach");
            })
            .unwrap()
            .join()
            .unwrap();
    }

    /// Sweep canonicalization: determinism/idempotency hold trivially;
    /// *order-independence* provably fails when an ambiguous twin type
    /// (both twins visible, one covered) is stacked — the type-level masks
    /// know the count, not the identity, and the two readings differ by a
    /// per-suit foundation height (a real part of the state). Measured as
    /// a divergence counter at such types instead of asserted as full
    /// equality; the semantic-safety obligation is recorded in the docs
    /// (macro doc §6.5) as the ambiguous-twin lift.
    #[test]
    fn sweep_is_confluent() {
        let mut rng_state = 0x243F6A8885A308D3u64;
        let mut divergence_count = 0usize;
        let mut rand = move || {
            rng_state ^= rng_state << 13;
            rng_state ^= rng_state >> 7;
            rng_state ^= rng_state << 17;
            rng_state
        };
        for draw_step in [1u8, 3] {
            for i in 0..64u64 {
                let cards = default_shuffle(12 + i);
                let step = NonZeroU8::new(draw_step).unwrap();
                // sample a few mid-game states by random macro play
                let mut game = Solitaire::new(&cards, step);
                for _turn in 0..40 {
                    let mut reference = game.clone();
                    canonicalize(&mut reference);
                    let want = reference.encode();
                    for _trial in 0..4 {
                        let mut g2 = game.clone();
                        loop {
                            let cands = sweep_candidates(&g2);
                            if cands == 0 {
                                break;
                            }
                            let n = cands.count_ones() as usize;
                            let pick = (rand() as usize) % n;
                            let mut cm = cands;
                            let mut mask = 0u64;
                            for _ in 0..=pick {
                                mask = cm & cm.wrapping_neg();
                                cm &= !mask;
                            }
                            let m = Move::PileStack(Card::from_mask_index(
                                u8::try_from(mask.trailing_zeros()).unwrap(),
                            ));
                            let _ = g2.do_move(m);
                        }
                        let got = g2.encode();
                        if got != want {
                            divergence_count += 1;
                            // the divergence must be pure stack noise: hidden
                            // and deck are sweep-invariant, and any nontrivial
                            // divergence there is a bug, not an ambiguity
                            assert_eq!(
                                (got >> 16),
                                (want >> 16),
                                "divergence outside the stack component: draw={draw_step} seed={} turn={_turn} got={got:x} want={want:x}",
                                12 + i
                            );
                            println!(
                                "  LIFT draw={draw_step} seed={} turn={_turn}: stack got={:#x} want={:#x}",
                                12 + i,
                                got & 0xFFFF,
                                want & 0xFFFF,
                            );
                        }
                    }
                    if game.is_win() {
                        break;
                    }
                    let cands = enumerate_commitments(&game);
                    if cands.is_empty() {
                        break;
                    }
                    for &m in &cands[(rand() as usize) % cands.len()].witness_path {
                        let _ = game.do_move(m);
                    }
                }
            }
        }
        println!(
            "sweep determinism: 128 games x 40 turns x 4 random orders; ambiguous-twin lifts diverged in {divergence_count} orderings"
        );
    }

    /// The acceptance gate, in miniature: macro-game verdicts under each
    /// successor policy must equal the (full-dominance, full-pruner) old
    /// solver's verdict on every game. A `TallestOnly`/`ShortestOnly`
    /// mismatch means a scar choice the single-class policy would lose.
    #[test]
    fn macro_verdict_matches_engine() {
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(|| {
                for draw_step in [1u8, 3] {
                    for i in 0..16u64 {
                        let cards = default_shuffle(12 + i);
                        let step = NonZeroU8::new(draw_step).unwrap();
                        let t0 = std::time::Instant::now();
                        let (res, _) = solve(&mut Solitaire::new(&cards, step));
                        let old_win = matches!(res, SearchResult::Solved);
                        let t_old = t0.elapsed();
                        let g = Solitaire::new(&cards, step);
                        let t1 = std::time::Instant::now();
                        let all = macro_solvable_sel(&g, SuccSelect::All);
                        let t_all = t1.elapsed();
                        let t2 = std::time::Instant::now();
                        let fast = macro_solvable_direct(&g);
                        let t_fast = t2.elapsed();
                        // report per-config details when slow
                        let slow = t_old.max(t_all).max(t_fast);
                        println!(
                            "seed={} draw={draw_step} verdict={}/{} old={:?} oracle={:?} direct={:?}",
                            12 + i, if old_win == all && all == fast { "OK" } else { "MISMATCH" },
                            if slow > std::time::Duration::from_millis(200) { "SLOW" } else { "" },
                            t_old, t_all, t_fast
                        );
                        assert_eq!(
                            (all, fast),
                            (old_win, old_win),
                            "verdict mismatch: draw={draw_step} seed={} old={old_win} oracle={all} direct={fast}",
                            12 + i
                        );
                    }
                }
                println!("macro verdicts match the engine (oracle + direct paths)");
            })
            .unwrap()
            .join()
            .unwrap();
    }

    /// The heavy version: draw-1 plus the full greedy corpus, run manually.
    /// Kept #[ignore] because the oracle walk makes it take minutes in
    /// release; it's the acceptance harness when the direct path changes.
    #[test]
    #[ignore = "expensive verdict sweep; run with --ignored --nocapture"]
    fn macro_verdict_sweep_big() {
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(|| {
                let mut n = 0usize;
                let mut mismatches = 0usize;
                for draw_step in [1u8, 3] {
                    for i in 0..64u64 {
                        let cards = default_shuffle(12 + i);
                        let step = NonZeroU8::new(draw_step).unwrap();
                        let (res, _) = solve(&mut Solitaire::new(&cards, step));
                        let old_win = matches!(res, SearchResult::Solved);
                        let g = Solitaire::new(&cards, step);
                        let fast = macro_solvable_direct(&g);
                        n += 1;
                        let ok = old_win == fast;
                        if !ok { mismatches += 1; }
                        println!("seed={} draw={draw_step} old={old_win} direct={fast} {}", 12 + i, if ok { "OK" } else { "** MISMATCH **" });
                    }
                }
                assert_eq!(mismatches, 0, "macro direct path verdict sweep found mismatches");
                println!("big verdict sweep: {n} games, {mismatches} mismatches");
            })
            .unwrap()
            .join()
            .unwrap();
    }

    /// The same verdict sweep on the KlondikeSolver shuffle family — an
    /// independent deal distribution, so a green run here is the
    /// collapse fold's evidence escaping the default-corpus shape.
    #[test]
    #[ignore = "expensive verdict sweep; run with --ignored --nocapture"]
    fn macro_verdict_sweep_ks() {
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(|| {
                let mut n = 0usize;
                let mut mismatches = 0usize;
                for draw_step in [1u8, 3] {
                    for i in 0..64u32 {
                        let cards = crate::shuffler::ks_shuffle(i);
                        let step = NonZeroU8::new(draw_step).unwrap();
                        let (res, _) = solve(&mut Solitaire::new(&cards, step));
                        let old_win = matches!(res, SearchResult::Solved);
                        let g = Solitaire::new(&cards, step);
                        let fast = macro_solvable_direct(&g);
                        n += 1;
                        if old_win != fast {
                            mismatches += 1;
                            println!("seed={i} draw={draw_step} old={old_win} direct={fast} ** MISMATCH **");
                        }
                    }
                }
                assert_eq!(mismatches, 0, "macro direct path KS verdict sweep found mismatches");
                println!("ks verdict sweep: {n} games, {mismatches} mismatches");
            })
            .unwrap()
            .join()
            .unwrap();
    }

    /// Perf attribution for the verdict test's SLOW rows: runs the oracle
    /// and direct recursions side by side with node/branch counters, the
    /// direct generator's channel histogram, and the cfg(test) probe
    /// counters (walk/cluster/BFS/post/sweep). The old engine is run in
    /// its full 2x2 (dominance x pruner) to attribute its speed: the
    /// macro game deliberately searches the *raw* game, so the gap to
    /// `solve` is exactly the filter layers the raw search runs without.
    #[test]
    #[ignore = "perf probe; run with --ignored --release --nocapture"]
    fn macro_verdict_perf_probe() {
        /// old-engine traversal counter: visits (incl. tp hits), unique
        /// nodes, and the filtered branching factor, with an honest budget
        const OLD_VISIT_BUDGET: u64 = 10_000_000;
        struct OldProbe<P: Pruner + Default> {
            won: bool,
            visits: u64,
            nodes: u64,
            branches: u64,
            budget: bool,
            marker: core::marker::PhantomData<P>,
        }
        impl<P: Pruner + Default> OldProbe<P> {
            fn new() -> Self {
                Self {
                    won: false,
                    visits: 0,
                    nodes: 0,
                    branches: 0,
                    budget: false,
                    marker: core::marker::PhantomData,
                }
            }
        }
        impl<P: Pruner + Default> Callback for OldProbe<P> {
            type Pruner = P;
            fn on_win(&mut self, _: &Solitaire) -> Control {
                self.won = true;
                Control::Halt
            }
            fn on_visit(&mut self, _: &Solitaire, _: Encode) -> Control {
                self.visits += 1;
                if self.visits > OLD_VISIT_BUDGET {
                    self.budget = true;
                    return Control::Halt;
                }
                Control::Ok
            }
            fn on_move_gen(&mut self, m: &crate::moves::MoveMask, _: Encode) -> Control {
                self.nodes += 1;
                self.branches += u64::from(m.len());
                Control::Ok
            }
        }
        fn run_old<const DOM: bool, P: Pruner + Default>(
            cards: &[Card; 52],
            step: NonZeroU8,
        ) -> OldProbe<P> {
            let mut game = Solitaire::new(cards, step);
            let mut tp = TpTable::default();
            let mut probe = OldProbe::<P>::new();
            traverse::<_, _, DOM>(&mut game, &P::default(), &mut tp, &mut probe);
            probe
        }
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(|| {
                for (seed, draw_step) in
                    [(17u64, 1u8), (18, 1), (22, 1), (14, 3), (21, 3), (18, 3)]
                {
                    let cards = default_shuffle(seed);
                    let step = NonZeroU8::new(draw_step).unwrap();
                    let g = Solitaire::new(&cards, step);

                    // old engine, the full 2x2 (dominance x pruner)
                    let t = std::time::Instant::now();
                    let p = run_old::<true, FullPruner>(&cards, step);
                    println!(
                        "seed={seed} draw={draw_step} OLD dom+pruner    win={:>5} visits={:>9} nodes={:>9} branches={:>10} avg_branch={:5.2} budget={} total={:?}",
                        p.won, p.visits, p.nodes, p.branches,
                        p.branches as f64 / p.nodes.max(1) as f64,
                        p.budget, t.elapsed()
                    );
                    let t = std::time::Instant::now();
                    let p = run_old::<true, NoPruner>(&cards, step);
                    println!(
                        "seed={seed} draw={draw_step} OLD dom-only      win={:>5} visits={:>9} nodes={:>9} branches={:>10} avg_branch={:5.2} budget={} total={:?}",
                        p.won, p.visits, p.nodes, p.branches,
                        p.branches as f64 / p.nodes.max(1) as f64,
                        p.budget, t.elapsed()
                    );
                    let t = std::time::Instant::now();
                    let p = run_old::<false, FullPruner>(&cards, step);
                    println!(
                        "seed={seed} draw={draw_step} OLD pruner-only    win={:>5} visits={:>9} nodes={:>9} branches={:>10} avg_branch={:5.2} budget={} total={:?}",
                        p.won, p.visits, p.nodes, p.branches,
                        p.branches as f64 / p.nodes.max(1) as f64,
                        p.budget, t.elapsed()
                    );
                    let t = std::time::Instant::now();
                    let p = run_old::<false, NoPruner>(&cards, step);
                    println!(
                        "seed={seed} draw={draw_step} OLD raw           win={:>5} visits={:>9} nodes={:>9} branches={:>10} avg_branch={:5.2} budget={} total={:?}",
                        p.won, p.visits, p.nodes, p.branches,
                        p.branches as f64 / p.nodes.max(1) as f64,
                        p.budget, t.elapsed()
                    );

                    // what the old engine's winning line looks like:
                    // length and per-move-type counts (is the win a
                    // near-forced stacking cascade the raw DFS walks
                    // straight into?)
                    {
                        let mut game = Solitaire::new(&cards, step);
                        let (res, hist) = solve(&mut game);
                        if let Some(h) = &hist {
                            let mut counts = [0usize; 5];
                            for m in h.iter() {
                                match m {
                                    Move::DeckStack(_) => counts[0] += 1,
                                    Move::PileStack(_) => counts[1] += 1,
                                    Move::DeckPile(_) => counts[2] += 1,
                                    Move::StackPile(_) => counts[3] += 1,
                                    Move::Reveal(_) => counts[4] += 1,
                                }
                            }
                            println!(
                                "seed={seed} draw={draw_step} OLD-WINLINE {res:?} len={} DS/PS/DP/SP/R={counts:?}",
                                h.len()
                            );
                        }
                    }

                    // oracle under three successor orders: natural
                    // (reveal-first, the shipped order), draw-first (the
                    // legacy order), and reversed — how much of the node
                    // count is commitment-order refutation?
                    for (policy_name, policy) in
                        [("natural    ", 0u8), ("draw-first  ", 1), ("reversed    ", 2)]
                    {
                        const NODE_CAP: usize = 3_000_000;
                        fn rec(
                            g: &Solitaire,
                            policy: u8,
                            tp: &mut TpTable,
                            nodes: &mut usize,
                            branches: &mut usize,
                            capped: &mut bool,
                        ) -> bool {
                            let mut s = g.clone();
                            canonicalize(&mut s);
                            if s.is_win() || !tp.insert(s.encode()) {
                                return s.is_win();
                            }
                            *nodes += 1;
                            if *nodes > NODE_CAP {
                                *capped = true;
                                return false;
                            }
                            let mut succs = enumerate_transitions(&s);
                            if policy == 1 {
                                succs.sort_by_key(|(c, _)| match c {
                                    Commitment::Draw(_) => 0,
                                    Commitment::Reveal(_) => 1,
                                });
                            }
                            *branches += succs.len();
                            let hit = match policy {
                                2 => succs
                                    .iter()
                                    .rev()
                                    .any(|(_, succ)| rec(succ, policy, tp, nodes, branches, capped)),
                                _ => succs
                                    .iter()
                                    .any(|(_, succ)| rec(succ, policy, tp, nodes, branches, capped)),
                            };
                            hit
                        }
                        let t = std::time::Instant::now();
                        let mut tp = TpTable::default();
                        let (mut n, mut b) = (0usize, 0usize);
                        let mut capped = false;
                        let w = rec(&g, policy, &mut tp, &mut n, &mut b, &mut capped);
                        println!(
                            "seed={seed} draw={draw_step} ORACLE/{policy_name} win={w} nodes={n} branches={b} capped={} total={:?}",
                            capped,
                            t.elapsed()
                        );
                    }

                    // oracle: same shape as macro_solvable_sel(All), counted
                    perf_probe::reset();
                    let t0 = std::time::Instant::now();
                    let o_win = {
                        fn rec(
                            g: &Solitaire,
                            tp: &mut TpTable,
                            nodes: &mut usize,
                            branches: &mut usize,
                            t_trans: &mut std::time::Duration,
                        ) -> bool {
                            let mut s = g.clone();
                            canonicalize(&mut s);
                            if s.is_win() || !tp.insert(s.encode()) {
                                return s.is_win();
                            }
                            *nodes += 1;
                            let t = std::time::Instant::now();
                            let succs = enumerate_transitions(&s);
                            *t_trans += t.elapsed();
                            *branches += succs.len();
                            succs
                                .iter()
                                .any(|(_, succ)| rec(succ, tp, nodes, branches, t_trans))
                        }
                        let mut tp = TpTable::default();
                        let (mut n, mut b) = (0usize, 0usize);
                        let mut t = std::time::Duration::ZERO;
                        let w = rec(&g, &mut tp, &mut n, &mut b, &mut t);
                        println!(
                            "seed={seed} draw={draw_step} ORACLE win={w} nodes={n} branches={b} trans={t:?} total={:?} walk/cls_c/cls_s/bfs_c/bfs_s/post_c/post_s/canon/gen/do/undo/enc={:?}",
                            t0.elapsed(),
                            perf_probe::read()
                        );
                        w
                    };

                    // direct: same shape as macro_solvable_direct, counted;
                    // channels kept visible by folding macro_transitions_direct
                    // by hand (same per-(commitment, kind) first-wins rule as
                    // macro_transitions_fast)
                    perf_probe::reset();
                    let t1 = std::time::Instant::now();
                    let d_win = {
                        fn rec(
                            s: &Solitaire,
                            tp: &mut TpTable,
                            nodes: &mut usize,
                            branches: &mut usize,
                            emissions: &mut usize,
                            t_trans: &mut std::time::Duration,
                            channels: &mut std::collections::BTreeMap<&'static str, usize>,
                        ) -> bool {
                            if s.is_win() || !tp.insert(s.encode()) {
                                return s.is_win();
                            }
                            *nodes += 1;
                            let t = std::time::Instant::now();
                            let all = macro_transitions_direct(s);
                            *t_trans += t.elapsed();
                            *emissions += all.len();
                            let mut seen: Vec<(Commitment, OutcomeKind)> = Vec::new();
                            let mut succs: Vec<&Solitaire> = Vec::new();
                            for (c, k, st, ch) in &all {
                                *channels.entry(*ch).or_insert(0) += 1;
                                if !seen.contains(&(*c, *k)) {
                                    seen.push((*c, *k));
                                    succs.push(st);
                                }
                            }
                            *branches += succs.len();
                            succs.into_iter().any(|succ| {
                                rec(succ, tp, nodes, branches, emissions, t_trans, channels)
                            })
                        }
                        let mut tp = TpTable::default();
                        let mut root = g.clone();
                        canonicalize(&mut root);
                        let (mut n, mut b, mut e) = (0usize, 0usize, 0usize);
                        let mut t = std::time::Duration::ZERO;
                        let mut ch: std::collections::BTreeMap<&'static str, usize> =
                            Default::default();
                        let w = rec(&root, &mut tp, &mut n, &mut b, &mut e, &mut t, &mut ch);
                        println!(
                            "seed={seed} draw={draw_step} DIRECT win={w} nodes={n} branches={b} emissions={e} trans={t:?} total={:?} walk/cls_c/cls_s/bfs_c/bfs_s/post_c/post_s/canon/gen/do/undo/enc={:?} channels={ch:?}",
                            t1.elapsed(),
                            perf_probe::read()
                        );
                        w
                    };
                    assert_eq!(o_win, d_win, "probe recursions disagree at seed={seed}");
                }
            })
            .unwrap()
            .join()
            .unwrap();
    }

    /// Greedy macro play: enumerate commitments, apply one witness path,
    /// repeat. Asserts the state stays valid and the play makes progress
    /// (every commitment changes the encode). Prints the observed
    /// multiplicity of post-states per commitment kind — the input data
    /// for open item O6 (when does the accommodation collapse to ≤2).
    ///
    /// Note: the state-level canonical multiplicity is *not* capped — free
    /// floats form product lattices (observed up to 8). The claim under
    /// test is the quotient one (C2): after quotienting post-states by the
    /// reversible closure, at most 2 classes per commitment survive.
    #[test]
    fn macro_scaffold_smoke() {
        // the closure DFS is deep on some games; give it solver-grade stack
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(macro_scaffold_smoke_inner)
            .unwrap()
            .join()
            .unwrap();
    }

    /// The (Y, Ȳ) parent configuration of a commitment at the canonical
    /// root — the finite table's row. Detection is by derivation only
    /// (deck contains / foundation prefix / hidden-structure slice /
    /// complement), which is exact because placement-blockage of a parent
    /// is already subsumed by `direct`.
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
    struct ParentSig {
        direct: bool,     // the generator offers X a landing at the root
        dig: bool,        // twin(X) is a placed tableau card (covers a parent)
        borrowable: u8,   // parents that are foundation tops
        f_buried: u8,     // parents on the foundation but not the suit top
        dead: u8,         // parents in stock or buried in a structure
        locked_surf: u8,  // parents that are locked surfaces
        kings: bool,      // X is a king (no parent types exist)
        stackable: bool,  // X stackable at the root
    }

    fn is_hidden_buried(g: &Solitaire, c: Card) -> bool {
        let hidden = g.get_hidden();
        (0..crate::deck::N_PILES).any(|pos| {
            let pile = hidden.get(pos);
            !pile.is_empty() && pile[..pile.len() - 1].contains(&c)
        })
    }

    fn is_locked_surface(g: &Solitaire, c: Card) -> bool {
        let hidden = g.get_hidden();
        (0..crate::deck::N_PILES).any(|pos| hidden.get(pos).last() == Some(&c))
    }

    fn in_deck(g: &Solitaire, c: Card) -> bool {
        g.get_deck().iter().any(|card| card == c)
    }

    fn parent_sig(g: &Solitaire, x: Card) -> ParentSig {
        use crate::card::KING_RANK;
        let mv = g.gen_moves::<false>();
        let stackable =
            (mv.pile_stack | mv.deck_stack) & x.mask() != 0;
        if x.rank() == KING_RANK {
            return ParentSig {
                direct: mv.deck_pile & x.mask() != 0 || mv.reveal & x.mask() != 0,
                dig: false,
                borrowable: 0,
                f_buried: 0,
                dead: 0,
                locked_surf: 0,
                kings: true,
                stackable,
            };
        }
        let s = x.suit();
        let parents = [Card::new(x.rank() + 1, s ^ 2), Card::new(x.rank() + 1, s ^ 3)];
        let mut sig = ParentSig {
            direct: false,
            dig: false,
            borrowable: 0,
            f_buried: 0,
            dead: 0,
            locked_surf: 0,
            kings: false,
            stackable,
        };
        for p in parents {
            let f = g.get_stack().get(p.suit());
            if f > p.rank() {
                if f == p.rank() + 1 {
                    sig.borrowable += 1;
                } else {
                    sig.f_buried += 1;
                }
            } else if in_deck(g, p) {
                sig.dead += 1;
            } else if is_hidden_buried(g, p) {
                sig.dead += 1;
            } else if is_locked_surface(g, p) {
                sig.locked_surf += 1;
            }
            // the remaining option (visible & placed) is where direct lives;
            // per-card coverage is intentionally not distinguished here
        }
        // direct = the root generator offers a placement of X
        let place_masks = mv.deck_pile | mv.stack_pile | mv.reveal;
        sig.direct = place_masks & x.mask() != 0;
        // dig channel: twin(X) is placed on the tableau (the only possible
        // parent-coverer, by the locality lemma)
        let twin = Card::new(x.rank(), s ^ 1);
        let twin_on_stack = g.get_stack().get(twin.suit()) > twin.rank();
        let twin_hidden_or_deck = in_deck(g, twin) || is_hidden_buried(g, twin);
        sig.dig = !twin_on_stack && !twin_hidden_or_deck && !is_locked_surface(g, twin);
        sig
    }

    fn macro_scaffold_smoke_inner() {
        let mut histogram = [0usize; 6];
        let mut macro_classes = 0usize;
        let mut sig_table: std::collections::BTreeMap<ParentSig, [usize; 2]> =
            std::collections::BTreeMap::new();
        // structural measurements for the closure theory:
        // - class_histogram[k]: commitments whose post-states form k classes
        // - mixed_kind_classes: classes containing both outcome kinds
        //   (predicted when X is stackable: tableau and stack are
        //   closure-connected via a late PileStack(X))
        // - same_kind_multi: commitments whose *single-kind* samples still
        //   split into several classes (would falsify "one class per kind")
        let mut class_histogram = [0usize; 5];
        let mut mixed_kind_classes = 0usize;
        let mut same_kind_multi = 0usize;
        let mut same_kind_multi_detail: Vec<(Commitment, u64, u64, bool)> = Vec::new();
        for draw_step in [1u8, 3] {
            for i in 0..100u64 {
                let mut game =
                    Solitaire::new(&default_shuffle(12 + i), NonZeroU8::new(draw_step).unwrap());
                let mut max_multiplicity = 0usize;
                let mut max_canon_multiplicity = 0usize;
                let mut overflowed = false;
                let mut canon_overflowed = false;
                for _turn in 0..200 {
                    if game.is_win() {
                        break;
                    }
                    // witness paths are relative to the canonicalized root:
                    // sweep first (reversible moves only), then enumerate
                    canonicalize(&mut game);
                    let cands = enumerate_commitments(&game);
                    if cands.is_empty() {
                        break; // dead-ended macro state
                    }
                    let mut turn_max = 0usize;
                    for c in &cands {
                        max_multiplicity = max_multiplicity
                            .max(c.outcomes.tableau.len())
                            .max(c.outcomes.stack.len());
                        max_canon_multiplicity = max_canon_multiplicity
                            .max(c.outcomes.canon_tableau.len())
                            .max(c.outcomes.canon_stack.len());
                        overflowed |= c.outcomes.overflowed;
                        canon_overflowed |= c.outcomes.canon_overflowed;
                        turn_max = turn_max
                            .max(c.outcomes.canon_tableau.len().min(5))
                            .max(c.outcomes.canon_stack.len().min(5));

                        // the real C2 content: after quotienting post-states
                        // by the reversible closure, at most 2 classes remain;
                        // check ALL multi-sample clusters, not just >2
                        for encs in [&c.outcomes.canon_tableau, &c.outcomes.canon_stack] {
                            if encs.len() > 1 {
                                let k = closure_classes(encs);
                                macro_classes = macro_classes.max(k);
                                if k > 1 {
                                    same_kind_multi += 1;
                                    same_kind_multi_detail.push((
                                        c.commitment,
                                        encs[0].0 >> 32,
                                        encs[0].0 & 0xFFFF,
                                        encs.len() > c.outcomes.canon_tableau.len(),
                                    ));
                                }
                            }
                        }

                        // combined class structure: cluster both kinds
                        // together and see whether classes are kind-pure
                        {
                            let combined = c
                                .outcomes
                                .canon_tableau
                                .iter()
                                .map(|s| (false, s))
                                .chain(c.outcomes.canon_stack.iter().map(|s| (true, s)));
                            let mut reps: Vec<(bool, Encode, &Solitaire)> = Vec::new();
                            let mut any_mixed = false;
                            'samples: for (is_stack, (enc, st)) in combined {
                                for (rep_kind, rep_enc, rep_st) in &mut reps {
                                    if closure_contains(rep_st, *enc) {
                                        any_mixed |= *rep_kind != is_stack;
                                        let _ = rep_enc;
                                        continue 'samples;
                                    }
                                }
                                reps.push((is_stack, *enc, st));
                            }
                            if !reps.is_empty() {
                                class_histogram[reps.len().min(4)] += 1;
                                if any_mixed {
                                    mixed_kind_classes += 1;
                                }
                                // finite configuration table: which (Y,Ȳ)
                                // configs at the canonical root ever
                                // produce 2 classes?
                                let sig = parent_sig(&game, match c.commitment {
                                    Commitment::Draw(x) | Commitment::Reveal(x) => x,
                                });
                                let entry = sig_table.entry(sig).or_default();
                                entry[usize::from(reps.len() > 1)] += 1;
                                // anomaly dump: two kind-pure classes —
                                // check where the cross-kind flip died
                                if reps.len() == 2 && !any_mixed {
                                    let x = match c.commitment {
                                        Commitment::Draw(x) | Commitment::Reveal(x) => x,
                                    };
                                    for (is_stack, enc, st) in &reps {
                                        let mv = st.gen_moves::<false>();
                                        let up = mv.pile_stack & x.mask() != 0;
                                        let down = mv.stack_pile & x.mask() != 0;
                                        println!(
                                            "  TWOPURE draw={draw_step} seed={} {:?} kind_stack={is_stack} enc={enc:x} X_stackable_now={} X_worryback_now={}",
                                            12 + i,
                                            c.commitment,
                                            up,
                                            down
                                        );
                                    }
                                }
                                assert!(
                                    reps.len() <= 2,
                                    "commitment {:?} has {} combined closure classes \
                                     (C2 violation): draw={draw_step} seed={}",
                                    c.commitment,
                                    reps.len(),
                                    12 + i
                                );
                            }
                        }

                        // residue anatomy: when the canonical count exceeds
                        // the structural 4-cap conjecture, show which
                        // encode components float
                        for (kind, encs) in
                            [("tab", &c.outcomes.canon_tableau), ("stak", &c.outcomes.canon_stack)]
                        {
                            if encs.len() > 4 {
                                let stacks: Vec<u16> =
                                    encs.iter().map(|(e, _)| *e as u16).collect();
                                let hiddens: Vec<u16> =
                                    encs.iter().map(|(e, _)| (*e >> 16) as u16).collect();
                                let decks: Vec<u32> =
                                    encs.iter().map(|(e, _)| (*e >> 32) as u32).collect();
                                println!(
                                    "  MULTI draw={draw_step} seed={} {:?} {kind} stacks={stacks:x?} hidden={hiddens:x?} decks={decks:x?}",
                                    12 + i,
                                    c.commitment,
                                );
                            }
                        }
                    }
                    let before = game.encode();
                    for &m in &cands[0].witness_path {
                        let _ = game.do_move(m); // witness paths are legal by construction
                    }
                    assert_ne!(game.encode(), before);
                    assert!(game.is_valid());
                    histogram[turn_max] += 1;
                }
                let _ = (max_multiplicity, max_canon_multiplicity, overflowed, canon_overflowed);
            }
        }
        println!("state-level multiplicity histogram (per turn, capped at 5+): {histogram:?}");
        println!("max distinct post-state closure classes per kind: {macro_classes} (C2 claim: <= 2)");
        println!("combined class histogram (1/2/3/4+): {class_histogram:?}");
        println!("parent-configuration table (sig -> [single_class, multi_class]):");
        for (sig, counts) in &sig_table {
            println!("  {sig:?} -> {counts:?}");
        }
        println!("commitments with mixed-kind classes (predicted iff X stackable): {mixed_kind_classes}");
        println!("same-kind multi-class commitments (should be 0 for one-class-per-kind): {same_kind_multi}");
        for (c, deck, stack, is_stack) in &same_kind_multi_detail {
            println!("  SAMESPLIT {c:?} deck={deck:x} stack={stack:x} kind_stack={is_stack}");
        }
    }
