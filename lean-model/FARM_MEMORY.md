# FARM_MEMORY — the prover agents' shared quirks & syntax ledger

Append-only shared memory for all farm agents. Protocol:

- READ this whole file before writing any proof.
- APPEND your discoveries at session end: one `## <file> — <topic>`
  block, dated, ≤ 15 lines. If the append fails (tail changed), re-read
  and retry. Do not rewrite others' entries.
- Record: syntax gotchas, core-lemma names that exist / don't exist,
  reusable proof recipes, wrong FARM routes (with the counterexample),
  reusable helper lemmas you proved, statement repairs you made.
- Do NOT edit FARM.md (the orchestrator's ledger). Never run any git
  command. Another agent may commit work in parallel — never revert
  anything.

## Verification protocol (orchestrator)

- Per-file check from `lean-model/`: `lake env lean Klondike/<File>.lean`
  — success = exit 0 + no `declaration uses 'sorry'` warning for YOUR
  declarations. Never run `lake build` from an agent (lock contention);
  the orchestrator does full builds between waves.
- A `sorry` inside a def's field is reported at the def's NAME line,
  not at the sorry's line.
- Citing a lemma whose proof is still `sorry` does NOT propagate the
  sorry-warning to your theorem: all statements are already in the
  oleans, so later-wave proofs may cite earlier-wave lemmas before
  their proofs land.
- Lake's cache can lie ("0 jobs" while an olean is missing). If in
  doubt: `lake clean && lake build`.

## Theorems.lean — defeq notes (2026-09-12)

- `flipAll_eq_relabelTwin` was plain `rfl`: `Relabel.twin.card ≡
  Card.flipSuit` componentwise-defeq; differing `Board.inj` proof
  fields are bridged by proof irrelevance. Expect the same defeqs for
  `Move.relabel` vs `Move.flipMove` (Wave 3's `apply_relabel`).
- `Suit.flipPair_color` is `@[simp]` and rfl-provable: the twin
  `coherent` field was `intro s s'; simp`, no 16-case bash needed.

## Cycle.lean — the removeAt recipe (2026-09-12)

- Expose structure: `simp only [removeAt]`; then `rw [if_pos h, ...]`
  chains resolve the cursor guards — INNER if-rewrites must come before
  outer guards whose conditions mention them. All guard facts are
  `omega` havs from `i < j < cursor`.
- `removeIdx_comm` is phrased `removeIdx (removeIdx l i) j = removeIdx
  (removeIdx l (j+1)) i` — instantiate the second index at `j - 1`,
  rewrite `j - 1 + 1 = j` by `omega`.
- `drawTo_comm_modAdjacent`'s wrap case (`j = 0`, `i = len - 1`) is NOT
  covered by `removeAt_comm` (it needs `i < j`): rotate/normalize the
  indices first, then apply; `rotate_add` is `@[simp]`.
- `drawTo_nonadjacent_diverge`: end cursors are exactly `j - 1` vs `i`
  as computed in `removeAt_comm` — reuse the `hcards` reasoning.

## Bridge.lean — parsing gotchas + engine facts (2026-09-12)

- Multi-field `{x with f := v, ...}` must start its first field on its
  own line (sepBy1Indent anchors at the first field's column).
- `⟨{x with ...}, ...⟩` (structure instance inside an anonymous
  constructor) does not parse — bind it via `have`/`let`, or pin the
  metavariable with a `rfl`-slot `_`.
- `rcases` flat patterns follow only the RIGHT ∧/∃ spine; left-side
  conjuncts need explicit nested slots; excess trailing slots are
  silently dropped.
- Core lemmas that exist (no Mathlib in this project):
  `List.getElem?_eq_some_iff`, `List.getElem?_eq_none_iff`,
  `List.getElem?_eq_none`.
- `noDupCards` draw-index uniqueness pattern:
  `(List.getElem?_eq_some_iff.mp hc).1` gives the index bound, then
  `hnd i₁ i₂` pins `i₁ = i₂`.
- PROVEN & REUSABLE for Wave 7: `eStep_offset`, `eRun_offset`,
  `isWin_offset` (offset-blindness of the engine). The "trailing draws
  shift only the offset" clause of `toEngine_lifts` is exactly these.
- STATEMENT REPAIR (accepted by orchestrator): `eStep_deckStack_unique`
  gained `(hnd : noDupCards e.order)` — without it, a duplicated order
  gives two draw indices, hence two offsets. Mirrors `deckPile`'s
  signature. No downstream users existed.

## Progress.lean — run_append recipe + trace hazard (2026-09-12)

- `run_append` PROVEN (first try, exit 0): `revert st; induction l₁`
  (Bridge's `eRun_offset` pattern — sidesteps `generalizing` re-intro
  ambiguity), then `intro st` per case. nil: `rfl` alone (append/run/
  bind all iota-reduce). cons: `simp only [List.cons_append,
  State.run]` exposes BOTH matches on `st.apply m` (equations fire
  only on constructor-headed lists, so inner `st'.run ms` is safe);
  `cases st.apply m` + `rfl` / `exact ih st'` — defeq closes the
  unreduced matches, no bind lemmas needed.
- HAZARD for `run_eq_trace_last` (analytical, NOT yet prover-confirmed):
  `State.trace`'s `none` arm yields `st :: []`, so for ANY st, m with
  `st.apply m = none`: `run [m] = none` but `(trace [m]).getLast? =
  some st` — the theorem looks UNSOUND as stated. A dying play needs
  an EMPTY trace for the statement to hold. Downstream `solvable_*`
  only use winning plays (unaffected). ESCALATED to orchestrator.

## Realizability.lean — Fits repair + realizable_of_wf (2026-09-12)

- STATEMENT REPAIR (needs sign-off): dropped `bd.legalEdges ∧` from
  `Board.Fits` — UNSOUND for `realizable_of_wf`: WF's third conjunct
  lets a topHidden boundary card also be visible, so legalEdges'
  canSitOn demand is unprovable. Witness (analytic): standard deal,
  depths p1:1/others 0, board {inl p1 ↦ ♥2, inr ♥2 ↦ ♥3} is WF, yet
  ♥3 has no legalEdges-legal seat in any board over {♥2,♥3} ⇒
  Realizable FALSE. Fits = the WF third conjunct; no downstream users.
- `realizable_of_wf`: bd := st.board, Fits ← `(hwf.2.2.1 b c hb).2`,
  image ← `fun _ => rfl`; `topHidden a` ≡ take/getLast? (δ), bare
  Bool `canSitOn c d` coerces to `= true` — `exact` accepts both.
- `apply_realizable` = `apply_wf` + `realizable_of_wf` (Move.lean).

## Progress.lean — trace repaired + reveal recipe (2026-09-12)

- TRACE DEF REPAIRED (orchestrator-approved): cons moved into the `some`
  arm — dying plays now yield `[]`. Old shape was prover-confirmed
  broken (dies-at-first: `run [m] = none`, `(trace [m]).getLast? =
  some st`; scratch witness: empty deal/board/stock, cursor 0).
- RESIDUAL (prover-confirmed via temp in-file rfl's): dies-LATER plays
  still break `run_eq_trace_last` — `[draw, dying]` gives trace
  `[st]`, run `none`. Needs death-propagation (`match st'.trace ms
  with | [] => [] | rest => st :: rest`) or an iff-form statement.
  Winning plays unaffected; escalated to orchestrator.
- `apply_reveal_totalDepth_lt` PROVEN. Inversion recipe: `simp only
  [State.apply] at h` then `simp only [State.applyReveal] at h` (both
  unfold body-match defs), then per discriminant `cases hX : e` +
  `rw [hXs] at h` + `simp at h`. KEY QUIRKS: `rw` does NOT iota-reduce
  matches — the next discriminant sits under the arm binder (a fresh
  FVar), so the next `rw` fails unless `simp at h` reduced first;
  `cases h : e` never rewrites hypotheses. Tail: `hpos` from
  `findFirst_mem` + `take 0`/`getLast? []` contradiction (plain
  `simp at hta` closes it), then `cases a <;> simp [Anchor.all,
  map_cons, map_nil, sum_cons, sum_nil] <;> omega` — full `simp` is
  REQUIRED: `simp only` skips ite ground-eval (left `if p1 = p0`
  atoms that stumped omega).

## Board.lean — Wave 1 complete; sorryAx propagation gotcha (2026-09-12)

- Board.lean FULLY proven (exit 0, zero warnings). New reusable
  helpers: `attach_inj`, `mapBy_inj`, `Base.flipBase_flipBase`.
- SORRY PROPAGATION: a `sorry` in a def's FIELD rides into any theorem
  whose proof term EMBEDS the def's literal — `subst`/`rw at h`/
  `split at h` all embed it (implicit args of Eq.rec/congrArg), even
  though provable. Citing the sorry'd CONSTANT is safe; embedding the
  LITERAL is not. Fix the field first.
- Multi-line `by` inside a structure instance does NOT parse: prove a
  standalone lemma and cite it from the field.
- Attach-lemma pattern: `unfold attach at h; split at h` ×2 (dite
  binders arrive inaccessible — `constructor <;> assumption` reaches
  them); `rw [Option.some.injEq] at h; subst h; exact update_self/
  update_ne`; `rw [dif_pos h.1, dif_pos h.2]` has no beta trouble.
- Core 4.30 confirmed present: `Option.map_eq_some_iff`,
  `decide_eq_true`, `of_decide_eq_true` (and `dif_pos` as rw).

## Progress.lean — trace death-propagation + run_eq_trace_last (2026-09-12)

- TRACE DEF (2nd repair, orchestrator option (a), APPLIED): `some`
  arm now `match st'.trace ms with | [] => [] | rest => st :: rest`
  — dying yields `[]` at ANY depth; winning traces unchanged.
- `run_eq_trace_last` PROVEN (first try): `revert st; induction
  play` + `intro st` per case (Bridge pattern). nil: `rfl`. cons:
  `simp only [State.run, State.trace]` exposes both matches on
  `st.apply m`; `cases st.apply m` (substitutes GOAL discriminants
  — unlike hypotheses, run_append precedent); some-branch needs
  FULL `simp` first to iota-reduce the outer matches (else the next
  discriminant sits under the arm binder); then `cases htr :
  st'.trace ms` + `have ih' := ih st'; rw [htr] at ih'; exact ih'`
  — defeq closes both arms.
- REUSABLE core fact (prover-confirmed): `List.getLast? (a :: b ::
  l) ≡ (b :: l).getLast?` by plain `rfl` — the cons-arm crux.

## Progress.lean — deckPile/deckStack shortens (2026-09-13)

- `apply_deckPile_shortens` + `apply_deckStack_shortens` PROVEN.
  ROUTE IMPROVEMENT: NO WF hypothesis needed (statements have none!)
  — the move's own success pins the index: `st.stock.prev = some c'`
  unfolds (`simp only [Cycle.prev] at hp`), `split at hp` cases the
  cursor-0 guard, else-arm gives `cards[cursor-1]? = some c'`, and
  `(List.getElem?_eq_some_iff.mp hp).1` yields `cursor - 1 < length`;
  then `Cycle.removeIdx_length` + `omega` (after a `show` to the
  `removeIdx` form — proj-of-literal defeq).
- BIG QUIRK (time-saver): full `simp at h` on
  `(if c then some A else none) = some st'` DECOMPOSES it to
  `c ∧ (A = st')` (absurd else auto-discharged) — do NOT hand-split
  the ite. `split at h` then handles any remaining MATCH cleanly
  (per-arm equations; the guard-conjunct is simp's, not split's);
  finish with `obtain ⟨-, h'⟩ := h; subst h'`. The deckStack arm has
  no match — obtain directly after simp.
- `simp only [State.applyDeckPile]` / `[State.applyDeckStack]`
  unfold body-match defs fine (same as applyReveal).

## Move.lean — apply_wf UNSOUND: two prover-confirmed holes (2026-09-13)

- HOLE 1 (reveal): `applyReveal` leaves trigger c on the now-VISIBLE
  r; WF's inr-clause grandfathers only topHidden bases — the boundary
  moved below r ⇒ c→r needs `canSitOn c r` (no guard). Witness:
  standard deal, depths a.toIdx, board {inr ♥2 ↦ ♥3}, fresh stock ⇒
  st.WF; reveal ♥3 legal; successor (depths p1 = 0, edge ♥3→inr ♥2)
  fails both disjuncts. Hits any pile ≥ 2 cards (reachable too).
- HOLE 2 (deckPile; deckStack same shape): WF pins Deal.WF's stock
  but never the STATE's cycle — [♥4,♥4] cursor 2, {inr ♥A ↦ ♠5},
  depths 1 is WF; deckPile ♥4 (inr ♠5) legal ⇒ ♥4 visible + a copy
  stays ⇒ isVis-clause broken. Both: scratch exit 0, only
  propext+Quot.sound. apply_realizable & Wave 4 boundedPlay BLOCKED.
- Repairs (in State.WF, sign-off needed): += `noDupCards
  st.stock.cards`; inr-clause += deal-adjacency grandfather (∃a t
  rest, piles a = t ++ d :: c :: rest) — the latter breaks
  aboveOf_rank_grading/legalEdges as stated. Other 4 cases believed
  true (draw = Nat.mod_le; canPlace guards feed clause 3).
- RECIPE: falsify ground states by pure `decide` — `(st.apply m).
  isSome = true`, successor as `(st.apply m).getD st`, then per-clause
  decides (topOf/bottomOf/topHidden/canSitOn all kernel-compute).

## Move.lean — landed WF repair: #1/#2 closed; #3/#4 residual (2026-09-13)

- LANDED: inr-clause += deal-adjacency; WF += noDupCards st.stock.cards
  — my witnesses #1 (♥3) and #2 (dup cycle) are closed.
- HOLE #3 (reveal, prover-confirmed): disjunct 1 (topHidden) carries
  no adjacency — {inr ♥2 ↦ ♠9} (♠9 dealt in p6) on p1's boundary is
  WF via disjunct 1 alone; reveal ♠9 ⇒ edge ♠9→inr ♥2 fails all 3
  disjuncts. FIX: DELETE disjunct 1 — subsumed by 2 for reachable
  states (initial edges adjacent; moves attach only canPlace-legal;
  reveal's new r→d₂ edge is deal-adjacent).
- HOLE #4 (reveal, prover-confirmed): state stock never tied to the
  deal — stock ⟨[♥2, ♠9], 1⟩ + {inr ♥2 ↦ ♥3} is WF; reveal ♥3 ⇒ ♥2
  visible with posOf ♥2 = some 0. FIX: WF += ∀ c ∈ st.stock.cards,
  c ∈ st.deal.stock (deck moves: sublist; reveal reads it here).
- Scratch ApplyWfCounter2.lean, exit 0, propext+Quot.sound only. With
  both deltas all 7 arms analyzed sound; reveal's r→d₂ edge needs
  take/getLast?/reverse-head? list lemmas.

## Progress.lean — Wave 0 COMPLETE: the two ≤ bashes (2026-09-13)

- `apply_totalDepth_le` + `apply_stockLen_le` PROVEN — ALL Wave 0
  Progress items done (7/7; only the 5 later-wave sorries remain).
- 7-way bash recipe: per arm `simp only [State.apply,
  State.applyX] at h` + the cases/rw/simp cascade; arms that don't
  touch the measure end `obtain ⟨-, h'⟩ := h; subst h'; exact
  Nat.le_of_eq rfl` (proj-of-literal defeq carries it; even draw's
  stock, via rotate's `cards := c.cards`). reveal arm: cite
  `Nat.le_of_lt (apply_reveal_totalDepth_lt h)`; deck arms in the
  stockLen proof: cite the shortens. pileStack's two-discriminant
  match: cases BOTH discriminants (the `some`-first-discriminant case
  commits to the catchall without the second).
- QUIRK: `split at h` bullets follow the DEF'S ARM ORDER, not the
  constructor order — applyPilePile's attach match lists `some`
  before `none` (bullet-1 = good), applyDeckPile lists `none` first
  (bullet-1 = bad). Read the def's arms before writing split bullets.
- FORWARD-REFERENCE gotcha: same-file citations need the cited
  theorem EARLIER (Lean has no forward refs) — deck-shortens sat
  after `apply_stockLen_le` ⇒ "unknown identifier"; relocated them
  above it (fine — verification is by NAME, not line).

## Move.lean — WF2 landed: #3/#4 closed, #5 residual; helper kit in (2026-09-13)

- LANDED: topHidden disjunct deleted; membership conjunct added
  (replacing noDupCards). Witnesses #1-#4 closed.
- HOLE #5 (deckPile/deckStack, prover-confirmed, ApplyWfCounter3.lean,
  exit 0, propext+Quot.sound): membership does not see multiplicity —
  state stock [♢3, ♢3] (both copies of a deal-STOCK card, so membership
  holds) with board {inr ♠3 ↦ ♠4}: `deckPile ♢3 (inr ♠4)` legal ⇒ ♢3
  visible with a copy surviving ⇒ isVis-clause broken. FIX: RESTORE
  `noDupCards st.stock.cards` ADDITIONALLY (witness #2's dup was of a
  pile card — membership kills that one, not this).
- LANDED in Move.lean (compile-clean, WF-independent): Rank.toIdx_inj;
  Cycle.{findFirstIdx_eq_none, findFirstIdx_mem (needs [DecidableEq α]),
  posOf_eq_none, posOf_mem, getElem?_removeIdx, mem_removeIdx,
  notMem_removeIdx_self}; head?_reverse_eq_getLast?;
  head?_of_take_single; Deal.{flatMap_piles_length, piles_stock_disj}.
- Reveal crux VALIDATED (RevealCrux.lean, axiom-clean): topHidden =
  some r + boundary head? = some d₂ ⇒ ∃ t rest, piles a = t ++ d₂ ::
  r :: rest. GOTCHA: `show` on take_append_drop FAILS (not defeq) and
  rw-ing its symm corrupts the RHS's drop-argument — go via
  `(take_append_drop _ _).symm.trans ?_` instead.

## Progress.lean — Wave 4: play_cut_loop + cycle theorem (2026-09-13)

- `play_cut_loop` + `play_self_is_shuffle` PROVEN, with three new
  REUSABLE helpers (cited by later waves): `run_totalDepth_le`,
  `run_stockLen_le` (run-level monotonicity, induction on play), and
  `run_commit_measures` (a commit in a successful play strictly
  advances a measure by the end). KEY ROUTE FACT: the naive
  "sub-play returns to own start" induction FAILS (sub-plays return to
  the ORIGINAL start, not their own) — carry a measure-DISJUNCTION
  through the induction instead; then play_self = helper + irrefl.
- `++` is LEFT-associative here (4.30, rfl-confirmed): `π₁ ++ π₂ ++ π₃`
  is `(π₁ ++ π₂) ++ π₃` — `run_append` chains must split at the TOP
  append, and explicit-arg `rw [run_append st (π₁ ++ π₂) π₃]` (my
  right-assoc guess) fails to match.
- `have h : (a >>= fun x => f x) = e` NEEDS the outer parens: the
  lambda body otherwise swallows `= e` (do-notation parse error).
- `cases hb : m.isCommit` substitutes the GOAL: false-arm goal is
  `false = false` (`rfl`, NOT `exact hb`); true-arm `true = false`
  (close via `absurd hlt (Nat.lt_irrefl _)`).
- LINTER: unused theorem binder — `clear` does NOT silence it; `have
  := hwf` does. `hwf` is VESTIGIAL in `play_self_is_shuffle` (the
  measures need no WF) — statement could drop it (orchestrator's
  call). The `have := hwf` line covers it meanwhile.
- HOUSEKEEPING: the deck-shortens relocation had accidentally
  swallowed play_self's doc comment — restored (minus its TODO).

## Initial.lean — initial_wf proven (orchestrator, 2026-09-13)

- FILE FULLY PROVEN (initial_wf + 8 helpers). `initialBoard` refactored
  defeq-preservingly into `initBase`/`initStep` (named fold pieces) —
  the file's `decide` examples re-verified behavior. Reusable helpers
  now in-tree: `initStep_topOf`/`initFold_topOf`/`initialBoard_topOf`
  (the fold spec: every top is some pile's top dealt card),
  `decompose_last` (length k+2, [k]? = some u, last = c ⇒ l = t ++ u ::
  c :: []), `mem_of_getLast`, `noDupCards_append_right`.
- EQUATION-CASES SUBSTITUTES THE GOAL: `cases h : e` replaces `e` in
  the goal — if the THEOREM STATEMENT contains the scrutinee (e.g.
  `getLast?` in the conclusion), the goal's copy becomes the pattern
  (`some top`), so the final witness must prove `some top = some c`,
  not the original form. Check the goal before assembling witnesses.
- BINDER TRAP (extends the Move.lean note): after `rw [hgt] at h`
  where hgt : opt = some top, the arm's pattern variable stays BOUND —
  `rw [hat] at h` cannot find `bd.attach (initBase d a) top` (it is
  the ARM's top, not the free top). ESCAPE: `have h2 : <reduced type>
  := h` — the defeq cast iota-reduces the match, substituting the free
  top into the body; then rw works on h2.
- PIPE NOTATION: `have h : x |>.f = true := e` FAILS to parse (the
  parser ends the type at `.f` and demands `:=` at `=`). Use explicit
  parens: `have h : (x).f = true := e`.
- `obtain ⟨...⟩ := hd` CONSUMES hd (clears it) — keep a copy
  (`have hdw := hd` or re-assemble `⟨hlen, hstock, hnd⟩`) before
  passing it to later lemmas.
- Anonymous-constructor slot COUNT errors show up as "expected type
  ∀ ... is not an inductive type" — count the ?_s against the conjunct
  count (WF now has NINE).
- `List.getElem?_eq_none_iff` is the iff name (`_eq_none` alone is not
  a constant). `of_decide_eq_true` + `omega` kills `decide (x < 0)`.
- Move.lean's Deal-namespace helpers: cite as `Deal.piles_stock_disj`,
  `Deal.flatMap_piles_length`; Cycle ones as `Cycle.posOf_eq_none`…
- `(State.initial d s).deal.piles a` displays unreduced: rw fails on
  `d.piles a` patterns until a `show`/defeq-cast normalizes the goal.

## Move.lean — WF2 landed: #3/#4 closed, #5 residual; helper kit in (2026-09-13)

- (Move agent's entry — see above for the five-witness history; the
  ninth WF conjunct `noDupCards st.stock.cards` was restored by the
  orchestrator after witness #5: membership is a SET condition — a
  deal-stock card duplicated in the cycle passes it. BOTH stock
  conjuncts are needed; neither subsumes the other.)

## Progress.lean — solvable_iff_distinctTrace PROVEN (2026-09-13)

- LANDED with 5 reusable helpers (Wave 4's boundedPlay should reuse):
  `run_cons_inv` (successful cons ⇒ apply/run/trace-cons bundle),
  `run_split` (run_append corollary: A++B succeeds, A reaches s ⇒ B
  goes s→w), `run_take_trace` (THE WORKHORSE: `run play = some w →
  i ≤ play.length → st.run (play.take i) = (st.trace play)[i]?`),
  `trace_length_succ` (trace length = play.length + 1),
  `solvable_distinct_aux` (length induction: distinct-trace witness;
  ¬allDistinct → classical ∃-repeat → take/drop split → play_cut_loop
  → strictly shorter). Loop-extraction chain: `List.take_add` +
  `take_append_drop` decompose; `run_take_trace` at i and j + the
  repeat `trace[i]? = trace[j]?` give the return-to-start via
  `run_split`.
- QUIRKS: `by_contra` is NOT core — `apply Classical.byContradiction;
  intro h` (by_cases IS core). `List.take_add` is FULLY IMPLICIT —
  type-ascribe the have. `cases hm : st.apply m` also rewrites the
  GOAL's `st.apply m` (refine slot becomes `rfl`). Forward reference
  AGAIN (play_cut_loop sat after its citer) — relocated. `hwf`
  vestigial here too (`have := hwf`). omega INGESTS ∃-hypotheses via
  choose (seen in error dumps) and needs `State.trace` unfolded
  (`simp only [State.trace, ...]`) before literal-length reasoning.




## Theorems.lean — roundtrip + draw_full_cycle PROVEN (orchestrator, 2026-09-13)

- `pileStack_stackPile_roundtrip` + `draw_full_cycle` LANDED (by hand).
  New reusable: `Board.ext_topOf` (same topOf ⇒ equal boards — funext +
  proof irrelevance; added to Board.lean).
- STATEMENT REPAIR (accepted): `draw_full_cycle`'s cursor bound weakened
  `≤` was FALSE — cursor = length (len > 0) rotates to 0, not back (only
  states never produced by rotate sit there; rotate lands strictly
  below). Repair: strict `<`. No downstream users.
- NAMESPACE TRAP: a theorem named `Board.foo` written INSIDE
  `namespace Board` becomes `Board.Board.foo`. Watch the declaration's
  file position when adding cross-file helpers.
- THE INVERSION RECIPE (Progress agent's, confirmed again): to unpack
  `h : st.apply m = some st'` for a move whose body is
  `if guard then match X with ... else none`: (1) `simp only
  [State.apply, applyXxx] at h`; (2) `cases hX : X with` + `rw [hX] at
  h` for each discriminant (defeq-cast via `have h' : <reduced> := h`
  when the arm binder traps the pattern); (3) FULL `simp at h` then
  decomposes the remaining `(if C then some A else none) = some st'`
  into the guard ∧ arm-equation — `obtain ⟨-, h'⟩ := h; subst h'`.
  Do NOT hand-split the ite: `split at h` leaves the goal open in both
  branches (bullets must each close the MAIN goal) and the display is
  confusing.
- `if c.suit = c.suit then A else B` does NOT whnf-reduce for symbolic
  suit (derived DecidableEq match is stuck): use `rw [if_pos rfl]` /
  `rw [if_neg h]` instead of `show`-defeq casts. Same for any
  symbolic-condition ite.
- Structure-literal projections (`{LIT}.field`) reduce under simp but
  block `rw`: normalize with `show`/defeq-cast first. `cases h : e` with
  e a projection-literal still needs `rw [h] at h-other` manually.
- `{s with f := s.f, ...} = s` closes by rw's auto-rfl (eta) — trailing
  `rfl` after such a rw errors with "No goals".
- After ANY Board.lean/Move.lean edit, the dependents' oleans go
  stale: `lake env lean` then fails with "Unknown constant" — run
  `lake build Klondike` (it cascades) before re-verifying consumers.

## Theorems.lean — relabelBy DEF REPAIRED (orchestrator, 2026-09-13)

- DEF BUG (analytic counterexample): `State.relabelBy`'s board probed
  at `Sum.map id r.card` — for the group's non-involutive elements
  (suit 4-cycles, e.g. h↦s↦d↦c↦h, all Relabel-valid), the relabeled
  guard `topOf (inr (r.card c))` reads `st.topOf (inr (r.card (r.card
  c)))` ≠ `st.topOf (inr c)` — conjugation (`apply_relabel`) is FALSE
  as defined. Heights/stock already used the inverse direction; only
  the board was wrong.
- REPAIR: probe at the inverse — new `Relabel.cardInv` (card-level
  inverse: `⟨r.suitInv c.suit, c.rank⟩`), `board.topOf := fun b =>
  (st.board.topOf (Sum.map id r.cardInv b)).map r.card`. New lemmas:
  `Relabel.cardInv_card` (cardInv ∘ card = id via left_inv),
  `Relabel.cardInv_inj` (base-level injectivity via right_inv),
  `Relabel.relabelBy_inj` (the matching law — KILLS the def-field
  sorry; standalone-lemma pattern).
- `flipAll_eq_relabelTwin` survives as `rfl` (twin is involutive:
  suitInv = suit, so both directions coincide).
- TYPE TRAP: `Sum.map id r.suitInv` is ill-typed over `Base = Sum
  Anchor Card` (suitInv : Suit → Suit) — the inverse must be
  card-level. Check argument TYPES before writing Sum.maps.
- Downstream of the repair: `apply_relabel`/`solvable_relabel` should
  now be provable (guards translate via cardInv_card + left_inv);
  Move.relabel keeps probing FORWARD (r.onBase) — the two directions
  cancel: cardInv ∘ onBase = id.

## ERGONOMICS REFRACTORING LANDED (2026-09-13)

- **TIER 1 — the move inversions** (Move.lean, after legal_pileStack_iff):
  `apply_draw_iff`, `apply_reveal_iff`, `apply_deckPile_iff`,
  `apply_deckStack_iff`, `apply_pileStack_iff`, `apply_stackPile_iff`,
  `apply_pilePile_iff` — one shape lemma per move: guards as flat
  conjunctions + the successor literal. Future consumers open with
  `rw [apply_X_iff] at h; obtain ⟨...⟩` instead of the case bash.
  BACKWARD-pattern that works: `rw [hst]; simp only [State.apply,
  applyXxx, <guard-eqs>]; split · rfl · rename_i hcond; simp
  [<guard-facts>] at hcond` (shape-agnostic — no if_pos conjunct
  guessing; the ite's condition may surface pre-normalized as True).
  FORWARD-pattern: per discriminant `cases h : e` + `rw [h] at h`
  (+ `simp at h` to iota past arm-binders when the pattern binds),
  final `simp at h` decomposes the ite-vs-some into `guards ∧ (arm =
  st')`.
- **NEW GOAL-SUBSTITUTION RULE (refined)**: `cases h : e` abstracts
  `e` under binders too, but ONLY terms without locally-bound
  variables — in an iff-RHS with `∃ r a bd, …`, a conjunct scrutinee
  free of bound vars gets substituted (witness `rfl`), one mentioning
  a bound var does not (witness the original hypothesis). Check the
  slot's expected type before writing witnesses.
- **TIER 2 (as lemmas, not defs)**: `heights_bump_self/_ne`,
  `heights_drop_self/_ne`, `depths_step_self/_ne` — @[simp], firing
  on the exact with-update literal shapes. DECISION: no
  `bumpHeight`-style defs — changing apply's bodies would churn every
  landed proof's literal matches for no extra power; the lemmas give
  the canonical rewrite targets.
- **TIER 3 — WF's named conjuncts** (State.lean): `depths_le`,
  `board_edges`, `vis_off_cycle`, `found_off_cycle`, `heights_le`,
  `cursor_le`, `stock_wf` (bundles noDup + membership); `WF` is now
  the 8-conjunct chain. `intro`/`show` whnf through the defs
  transparently — existing proofs needed only the slot-count fix and
  the stock-bullet merge; `realizable_of_wf`'s `⟨_,_,hmatch,_⟩`
  right-spine absorption survived unchanged (board_edges is still
  the third conjunct).
- **INCIDENT REPORT**: a PowerShell splice truncated Move.lean (Measure
  -Line undercounted; the tail past `piles_stock_disj` was lost from
  the working tree) — recovered from `git show HEAD` (UTF-8 console
  encoding required: `[Console]::OutputEncoding =
  [Text.Encoding]::UTF8` FIRST) + in-context text. LESSON: never slice
  files by measured line counts; use marker-based splits, and
  `[System.IO.File]::ReadAllText/WriteAllText` for content-preserving
  edits. Verify `git diff --stat` matches expectations after scripted
  file surgery.

## Pace.lean (wave 8, the draw pacing) — paid-for facts

- **Machine divergence, resolved**: `Cycle.drawTo` wraps the cursor
  `mod length` (rotate can never reach `cursor = len`), while
  deck.rs's `draw` saturates there. The two agree on the MASK
  everywhere: at a saturated cursor the leading lane is empty (its
  positions must be >= cursor-1 = len-1), so both machines reduce to
  top-lane UNION last; and a last-position draw is a max-remaining
  draw, whose successor never uses the leading lane. Consequence:
  `cursor_after` is stated with `% length` (the wrap case is the
  max-draw) - do NOT repair it to the unwrapped form.
- **Membership, not list equality**: `maskPos` concatenates
  lane1 ++ [last] ++ lane2, so the list is NOT sorted and
  `maskPos c 1 _ = List.range _` is FALSE as equality. The step-1
  degeneration is stated by membership. Check any statement about
  `maskPos` in the same form.
- **No `Monad List` in core** (the syntax card's blind spot hit):
  do-notation over List fails with `expected type is not a monad
  application`. Use `flatMap` chains:
  `(List.range n).flatMap fun n => (List.range (n+2)).flatMap fun c => ...`.
- **#eval of a def in a sorry-carrying module is fine** when the def
  itself is axiom-clean - check with `#print axioms Pace.maskPos`
  (=> [propext, Quot.sound]) before trusting an evaluation abort.
- **Port check (paid)**: `python/pace_port_check.py` regenerates a
  #eval grid (n <= 9, cursor <= n+1 including saturated, step 1..4)
  and diffs Lean's `maskPos` against deck_sim's machine:
  260 states, 0 mismatches. Rerun after any edit to `maskPos`.

## Pace.lean follow-up (2026-09-13) — the divergence resolved in the
## machine, not the statement

The earlier entry's advice (""do NOT repair cursor_after to the
unwrapped form"") is OBSOLETE. The wrap lived in the OLD
`Cycle.drawTo` (rotate-based, cursor mod length); it was replaced
by the deck.rs-literal jump `{ cy with cursor := i + 1 }` — the
cursor now saturates at `length` exactly like deck.rs's
`set_offset`, the mask agrees everywhere on the invariant domain,
and `cursor_after` is EXACT with no mod:
`c''.cursor = c.cards.idxOf w - rBelow c.cards pre w`.
`dealOnce` (the `offset_once` port: clamp at the pass end, wrap
from the end) completes the machine.

The statement repairs that came with it (recorded in FARM.md wave 8):
`hcur : cursor <= length` on the three mask-reading theorems (past
`len + 1` the wrapped lane leaks positions — the port-check grid's
`n + 1` upper edge is exactly the last leak-free cursor), and
`noDupCards` on `pos_shift` (a duplicated card draws twice via
`posOf` finding the second copy while `rBelow` counts by
`idxOf` — over-counting the shift).

## apply_wf PROVEN (orchestrator, 2026-09-13)

- THE KEYSTONE. All 7 arms, ~500 lines, alongside 4 new helpers:
  `bottomOf_isSome_attach` (base-survival through attach), `bottomOf_detach_ne`
  (base-search unchanged off the detached card), `removeIdx_of_length_le`,
  `noDupCards_removeIdx` (with the top-level `by_cases i < length` split — the
  user-supplied fix), `hidden_split`/`hidden_single`/`hidden_parent_dealt`
  (reveal's crux: hidden = pre ++ [d, r] → dealt-adjacency),
  `mem_of_getLast''` (local copy — Initial's is upstream),
  `Cycle.dealOnce_cursor_le` (their agent's new rotation).
- `apply_realizable` = `realizable_of_wf (apply_wf ...)` — one line.
- LESSONS this proof: (1) `subst` on `x = binder` may eliminate the THEOREM
  binder — prefer `rw [h]` on hypotheses / goals; (2) after `cases b`, use
  `Sum.inr d` explicitly — the binder is gone; (3) `Bool.and_eq_true` is an
  Eq-of-Props — the usable form is `Bool.and_eq_true_iff.mp`; (4) after the
  outer `refine ⟨bottomOf-proof, ?_⟩` closes the ∧, the inner block gets the
  MATCH alone — `obtain ⟨-, hleg⟩` + `cases`, no second refine; (5) give
  `mem_removeIdx` EXPLICIT l i — the `_ _` metavars mis-unify through the
  `.cards` projection; (6) stuck-ite state projections (dealOnce) need the
  simp lemma (`dealOnce_cards`) or a show into the def's body before defeq
  transfers; (7) heights-update slots: state the `hon` bound against the raw
  `if`-form and `rw [if_pos/if_neg] at hon` — never name the eliminated `st'`.
