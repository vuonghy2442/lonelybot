use hashbrown::HashSet;

use crate::{
    moves::{Move, MoveMask},
    pruning::Pruner,
    state::{Encode, Solitaire},
    utils::MixHasherBuilder,
};

pub trait TranspositionTable {
    fn clear(&mut self);
    fn insert(&mut self, value: Encode) -> bool;
}

#[derive(PartialEq, Eq, Debug)]
pub enum Control {
    Halt,
    Skip,
    Ok,
}

pub trait Callback {
    type Pruner: Pruner;

    /// Compile-time gate for Phase-0 falsifier instrumentation
    /// (docs/pruning_dominance_interaction.md §7, items 6-8). When `false`
    /// (the default) every hook below is eliminated at compile time.
    const INSTRUMENT: bool = false;

    fn on_win(&mut self, game: &Solitaire) -> Control;

    fn on_visit(&mut self, _game: &Solitaire, _encode: Encode) -> Control {
        Control::Ok
    }

    fn on_backtrack(&mut self, _game: &Solitaire, _encode: Encode) -> Control {
        Control::Ok
    }

    fn on_move_gen(&mut self, _move_list: &MoveMask, _encode: Encode) -> Control {
        Control::Ok
    }

    fn on_do_move(
        &mut self,
        _game: &Solitaire,
        _m: Move,
        _encode: Encode,
        _pruner: &Self::Pruner,
    ) -> Control {
        Control::Ok
    }

    fn on_undo_move(&mut self, _m: Move, _encode: Encode, _res: &Control) {}

    /// P1 (decisive): the fully filtered move set (`gen_moves::<true>` after
    /// the pruner) is empty while the raw generator offers moves. Every
    /// composition deadlock claimed impossible by a reordering rescue passes
    /// through this event; a hit on a winnable game is a counterexample.
    /// `dom` is the set after the dominance cascade, before the pruner;
    /// `raw` is the unfiltered set.
    fn on_filtered_empty(&mut self, _game: &Solitaire, _dom: &MoveMask, _raw: &MoveMask) {}

    /// P2: a `Reveal` that empties a pile (`ExtraInfo::RevealEmpty`) has
    /// just been played; the king-fill question of the interaction doc's
    /// flagship example (§4) lives at the child state. (Deliberately keyed
    /// to the literal `Reveal`, matching what rule 6.2 matches.)
    fn on_reveal_empty(&mut self, _game: &Solitaire, _m: Move) {}
}

pub type TpTable = HashSet<Encode, MixHasherBuilder>;
impl TranspositionTable for TpTable {
    fn clear(&mut self) {
        self.clear();
    }
    fn insert(&mut self, value: Encode) -> bool {
        self.insert(value)
    }
}

// it guarantee to return the state of g back into normal state
// DOMINANCE=false disables the §5 dominance cascade (the 2x2 ground-truth
// ablation of the soundness analysis drives both configurations).
pub fn traverse<T: TranspositionTable, C: Callback, const DOMINANCE: bool>(
    game: &mut Solitaire,
    prune_info: &C::Pruner,
    tp: &mut T,
    callback: &mut C,
) -> Control {
    if game.is_win() {
        return callback.on_win(game);
    }

    let encode = game.encode();

    match callback.on_visit(game, encode) {
        Control::Halt => return Control::Halt,
        Control::Skip => return Control::Skip,
        Control::Ok => {}
    }

    if !tp.insert(encode) {
        return Control::Ok;
    }

    let dom_list = game.gen_moves::<DOMINANCE>();

    let move_list = dom_list.filter(&prune_info.prune_moves(game));

    if C::INSTRUMENT && move_list.is_empty() {
        // P1: pruned-and-dominated empty while raw play exists
        let raw = game.gen_moves::<false>();
        if !raw.is_empty() {
            callback.on_filtered_empty(game, &dom_list, &raw);
        }
    }

    match callback.on_move_gen(&move_list, encode) {
        Control::Halt => return Control::Halt,
        Control::Skip => return Control::Skip,
        Control::Ok => {}
    }

    let res = move_list.iter_moves(|m| {
        match callback.on_do_move(game, m, encode, prune_info) {
            Control::Halt => return core::ops::ControlFlow::Break(()),
            Control::Skip => return core::ops::ControlFlow::Continue(()),
            Control::Ok => {}
        }

        let (rev_m, (undo, extra)) = game.do_move(m);

        if C::INSTRUMENT
            && matches!(m, Move::Reveal(_))
            && matches!(extra, crate::state::ExtraInfo::RevealEmpty)
        {
            callback.on_reveal_empty(game, m);
        }

        let new_prune_info = prune_info.update(m, rev_m, extra);

        let res = traverse::<_, _, DOMINANCE>(game, &new_prune_info, tp, callback);

        game.undo_move(m, undo);
        callback.on_undo_move(m, encode, &res);

        if res == Control::Halt {
            core::ops::ControlFlow::Break(())
        } else {
            core::ops::ControlFlow::Continue(())
        }
    });

    if res.is_break() {
        return Control::Halt;
    }

    callback.on_backtrack(game, encode)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::card::Card;
    use crate::moves::N_MOVES_MAX;
    use crate::pruning::{FullPruner, NoPruner, Pruner};
    use crate::shuffler::default_shuffle;
    use crate::state::Solitaire;
    use core::num::NonZeroU8;

    /// Per-traversal verdict probe with a visit budget. `Unknown` is
    /// honest: budget exhaustion, not a verdict.
    #[derive(Clone, Copy, PartialEq, Eq, Debug)]
    enum Verdict {
        Win,
        Lose,
        Unknown,
    }

    const VISIT_BUDGET: u64 = 100_000;

    struct VerdictLog<P> {
        won: bool,
        visits: u64,
        marker: core::marker::PhantomData<P>,
    }

    impl<P: Pruner + Default> Default for VerdictLog<P> {
        fn default() -> Self {
            Self { won: false, visits: 0, marker: core::marker::PhantomData }
        }
    }

    impl<P: Pruner + Default> Callback for VerdictLog<P> {
        type Pruner = P;

        fn on_visit(&mut self, _game: &Solitaire, _encode: Encode) -> Control {
            self.visits += 1;
            if self.visits > VISIT_BUDGET {
                return Control::Halt;
            }
            Control::Ok
        }

        fn on_win(&mut self, _game: &Solitaire) -> Control {
            self.won = true;
            Control::Halt
        }
    }

    fn run_config<const DOM: bool, P: Pruner + Default>(cards: &[Card; 52], step: NonZeroU8) -> Verdict {
        let mut game = Solitaire::new(cards, step);
        let mut tp = TpTable::default();
        let mut log = VerdictLog::<P>::default();
        traverse::<_, _, DOM>(&mut game, &P::default(), &mut tp, &mut log);
        if log.won {
            Verdict::Win
        } else if log.visits > VISIT_BUDGET {
            Verdict::Unknown
        } else {
            Verdict::Lose
        }
    }

    /// Phase 0, the decisive shape (interaction doc §7 items 1-2): the 2x2
    /// verdict ablation. The first draft instrumented *dead branches*
    /// ("filtered move set empty" while raw moves exist), which turned out
    /// to be the norm of any losing search — ~129k events over 1.7M visited
    /// states — and therefore cannot be a soundness signal; the verdict
    /// level is the right level. **Any game where the shipped configuration
    /// (FullPruner + dominance) says Lose while a less-filtered
    /// configuration finds Win within the same budget is a candidate
    /// soundness bug.** Budget Unknowns are recorded, not judged.
    #[test]
    fn phase0_verdict_ablation() {
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(|| {
                let mut unknowns = 0usize;
                let mut games_run = 0usize;
                for draw_step in [1u8, 3] {
                    for i in 0..60u64 {
                        let cards = default_shuffle(12 + i);
                        let step = NonZeroU8::new(draw_step).unwrap();

                        // the shipped configuration
                        let full = run_config::<true, FullPruner>(&cards, step);
                        // isolates the pruner's claim
                        let no_prune = run_config::<true, NoPruner>(&cards, step);
                        // isolates the dominance cascade
                        let no_dom = run_config::<false, FullPruner>(&cards, step);
                        // the (expensive) reference: neither filter layer
                        let ground = run_config::<false, NoPruner>(&cards, step);

                        for (name, v) in [
                            ("NoPruner", no_prune),
                            ("NoDominance", no_dom),
                            ("GroundTruth", ground),
                        ] {
                            if v == Verdict::Unknown {
                                unknowns += 1;
                            }
                            assert!(
                                !(full == Verdict::Lose && v == Verdict::Win),
                                "soundness witness: draw={draw_step} seed={} full=Lose but {name}=Win",
                                12 + i
                            );
                        }
                        games_run += 1;
                    }
                }
                println!(
                    "phase0 verdict ablation: {games_run} games x 2 draws, ablation budget-Unknowns: {unknowns}"
                );
            })
            .unwrap()
            .join()
            .unwrap();
    }

    /// Mirror of `FullPruner`'s last_draw update rule, replayed over the
    /// recorded path. Kept as an honest recomputation: if it ever diverges
    /// from `instrument_last_draw()`, the harness itself is unsound.
    fn mirror_last_draw(ld: Option<Card>, m: Move) -> Option<Card> {
        match m {
            Move::DeckPile(c) => Some(c),
            Move::StackPile(c) if !ld.is_some_and(|cc| c.go_after(Some(cc))) => ld,
            _ => None,
        }
    }

    /// P3 (interaction doc §7 item 8; detailed spec in last_draw_rules.md
    /// §6). For states inside a `last_draw` streak, every move killed by
    /// the streak rules *alone* must keep an explicit witness: the same
    /// move present in the generator at the streak's start state (the state
    /// just before the streak's first draw). A miss is exactly the R1/R2
    /// counterexample shape.
    #[derive(Default)]
    struct StreakAudit {
        /// (state-at-entry, move-taken-from-it) for the current DFS path
        path: Vec<(Solitaire, Move)>,
        audited: std::collections::HashSet<Encode>,
        /// (state encode, killed move, streak-start encode)
        misses: Vec<(Encode, Move, Encode)>,
        visits: u64,
        /// per-streak-start cache of the closure-enabled mask sets
        closure_cache: std::collections::HashMap<Encode, (u64, u64)>,
    }

    /// The set of (pile_stack bits, reveal bits) reachable from `s0` through
    /// reversible moves only — the chain-witness the streak rules actually
    /// rely on: e.g. a mid-streak `StackPile(u)` can make `x` stackable for
    /// the first time, and the rescue of a killed `PileStack(x)` is the
    /// pre-streak ordering `SP(u); PS(x); DP(d)`, which exists iff
    /// `PileStack(x)` appears somewhere in the closure of the streak start.
    fn closure_enabled_masks(s0: &Solitaire) -> (u64, u64) {
        fn rec(g: &mut Solitaire, tp: &mut TpTable, acc: &mut (u64, u64)) {
            if !tp.insert(g.encode()) {
                return;
            }
            let mv = g.gen_moves::<false>();
            acc.0 |= mv.pile_stack;
            acc.1 |= mv.reveal;
            for m in mv.to_vec::<N_MOVES_MAX>() {
                if g.reverse_move(m).is_some() {
                    let (_, (undo, _)) = g.do_move(m);
                    rec(g, tp, acc);
                    g.undo_move(m, undo);
                }
            }
        }
        let mut acc = (0u64, 0u64);
        rec(&mut s0.clone(), &mut TpTable::default(), &mut acc);
        acc
    }

    impl StreakAudit {
        fn audit(&mut self, game: &Solitaire, pruner: &FullPruner) {
            if !self.audited.insert(game.encode()) {
                return;
            }
            let Some(d) = pruner.instrument_last_draw() else {
                return; // not a streak state
            };

            // replay the path to find the streak's start
            let mut mirror = None;
            let mut start = None;
            for (idx, (_st, mv)) in self.path.iter().enumerate() {
                let prev = mirror;
                mirror = mirror_last_draw(mirror, *mv);
                if prev.is_none() && mirror.is_some() {
                    start = Some(idx);
                }
            }
            // the harness's own soundness check (cheap, always on)
            assert_eq!(mirror, pruner.instrument_last_draw());
            let Some(s0_idx) = start else {
                return; // pathological: streak without a first draw
            };
            let s0 = &self.path[s0_idx].0;

            let dom = game.gen_moves::<true>();
            let (rule, streak, cycle) = pruner.explain(game);
            // killed by the streak rules and by nothing else
            let k_ps = dom.pile_stack & streak.pile_stack & !rule.pile_stack & !cycle.pile_stack;
            let k_rv = dom.reveal & streak.reveal & !rule.reveal & !cycle.reveal;
            let killed = MoveMask {
                pile_stack: k_ps,
                reveal: k_rv,
                ..MoveMask::default()
            };

            // the witness may live anywhere in the streak start's
            // reversible closure (a mid-streak worry-back can create
            // stackability that no pre-streak state had — the rescue is the
            // pre-streak shuffle chain, not the move at s0 itself)
            let (closure_ps, closure_rv) = *self
                .closure_cache
                .entry(s0.encode())
                .or_insert_with(|| closure_enabled_masks(s0));
            let dom0 = s0.gen_moves::<true>();
            let raw0 = s0.gen_moves::<false>();
            for m in killed.to_vec::<N_MOVES_MAX>() {
                let witnessed = match m {
                    // the drawn card's own pile-stack is design-exempt:
                    // DeckStack(d) stays unrestricted during a streak and
                    // reaches the same encode (Claim B, last_draw_rules §5)
                    Move::PileStack(c) if c == d => true,
                    Move::PileStack(c) => {
                        dom0.pile_stack & c.mask() != 0 || closure_ps & c.mask() != 0
                    }
                    Move::Reveal(c) => raw0.reveal & c.mask() != 0 || closure_rv & c.mask() != 0,
                    _ => true, // the streak rules touch only those two families
                };
                if !witnessed {
                    self.misses.push((game.encode(), m, s0.encode()));
                }
            }
        }
    }

    impl Callback for StreakAudit {
        type Pruner = FullPruner;

        fn on_visit(&mut self, _game: &Solitaire, _encode: Encode) -> Control {
            self.visits += 1;
            if self.visits > VISIT_BUDGET {
                return Control::Halt;
            }
            Control::Ok
        }

        fn on_win(&mut self, _game: &Solitaire) -> Control {
            Control::Halt
        }

        fn on_do_move(
            &mut self,
            game: &Solitaire,
            m: Move,
            _encode: Encode,
            pruner: &FullPruner,
        ) -> Control {
            self.audit(game, pruner);
            self.path.push((game.clone(), m));
            Control::Ok
        }

        fn on_undo_move(&mut self, _m: Move, _encode: Encode, _res: &Control) {
            self.path.pop();
        }
    }

    #[test]
    fn phase0_streak_witnesses() {
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(|| {
                let mut log = StreakAudit::default();
                let mut flagged_games = 0usize;
                for draw_step in [1u8, 3] {
                    for i in 0..60u64 {
                        let cards = default_shuffle(12 + i);
                        let step = NonZeroU8::new(draw_step).unwrap();
                        let before = log.misses.len();
                        let mut game = Solitaire::new(&cards, step);
                        let mut tp = TpTable::default();
                        log.visits = 0;
                        traverse::<_, _, true>(&mut game, &FullPruner::default(), &mut tp, &mut log);
                        if log.misses.len() > before {
                            // a witnessless kill only matters if it flips a
                            // verdict — check this game by ablation now
                            flagged_games += 1;
                            let full = run_config::<true, FullPruner>(&cards, step);
                            let ground = run_config::<false, NoPruner>(&cards, step);
                            assert!(
                                !(full == Verdict::Lose && ground == Verdict::Win),
                                "P3 verdict flip: draw={draw_step} seed={} full={full:?} ground={ground:?}",
                                12 + i
                            );
                        }
                    }
                }
                println!(
                    "P3 streak-witness audit: {} audited states, {} witnessless kills, {} flagged games (all verdict-consistent)",
                    log.audited.len(),
                    log.misses.len(),
                    flagged_games
                );
                for (enc, m, s0) in log.misses.iter().take(8) {
                    println!("  P3 candidate at {enc:x}: {m:?} without streak-start witness (start {s0:x})");
                }
                // P3 events are *candidates*, not verdicts: the assertion
                // lives inside the loop (any flag flips a verdict => fail).
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
