import Orig.TwinExchange

/-!
# Orig — the WF merge walls

## The subsumption packaging (the doctrine, recorded not defined)

The user's doctrine (FUTURES-ORIG §1.8): the old cleanliness layer
`visClean` — invented to kill the crafted states of the w15merge
refutation — COLLAPSES at the physical state to `WF` plus one
corollary, which is recorded here and deliberately NOT packaged as a
predicate: **at a `WF` state, every visible fit is `runOK`'s content,
by definition.**  The three dirt families the old layer guarded are
unstatable or inert under the conservation invariant's own conjuncts
(`Orig/State.lean:232`): phantom cards die at the `cardCount` census,
foundation-passed strays die at the found-prefix conjunct, in-pile
braids die at `runOK`.  No `CleanVis`/`VisCleanO` predicate is
defined in this file: its job is to prove the dirt *content* dies at
`WF` — the two merge walls — not to re-introduce a cleanliness layer.

## The two walls

The physical translations of the old engine impossibles
`merge_impossible_of_visClean` and
`merge_rooted_impossible_of_visClean`
(`Klondike/Restriction.lean:1289`, `:1360` — read as a route map
only, NEVER imported, never cited, every line re-proved physically,
zero engine vocabulary).  The shape guarded is the w15merge corner
(`witnesses/OrigExchangeWitness.lean` — the live exhibit: at the
deliberately non-WF `xA`, the braided helix run `[♥5, ♥7, ♠6]` wins
the game THROUGH the merge, its head `♥5` landing on the other
thread's cargo top `♣6` — the two threads fusing into one pile).

The FIT-LADDER CONTRADICTION (the witness header's rank chain,
classified once here): a legal thread demands its cargo fit its seat
(`z + 1 = t` in rank) and — through `runOK`, read on the `aboveIn`
slot laws — every card strictly above the run root `c` sit strictly
below it (`t + 1 ≤ c` for a passed seat); the merge landing demands
the root itself fit the other cargo stack (`c + 1 = d`, `d ≤ z'`),
with the cargos of twin rank (`z' + 1 = t.twin`).  The fit closure
cycles `t + 2 ≤ t - 1`: rank-impossible for legal edges.  At `WF`
there is no rank realization — the braided slice of the witness
(two ranks off its interior edge, `runOK` a `WF` conjunct but never
a step guard) is unstatable, and the merge corner is DEAD before any
exchange row is stated.

* `merge_impossible_of_WF` — the PASSING wall: a `tabToTab` whose
  run passes a twin seat (either twin strictly above the root, on a
  settled pile) cannot fire onto either cargo's stack — the base may
  be the cargo `z` itself, a card seated above `z` in `z`'s pile, the
  other cargo `z'`, or a card seated above `z'` in its pile (the old
  corners' four landing arms).
* `merge_rooted_impossible_of_WF` — the ROOTED wall: the same wall
  when the lifted run IS the seat (`c = t`, the merged seat at the
  root — the passing form's `aboveIn`-passage premise is vacuous
  there, so the corner needs its own arithmetic), landing strictly
  above the other cargo.

The dividends at work: (b) `runOK` per pile (`Orig/State.lean:126`)
— the rank chains; plus the `canPlace` guard arithmetic
(`Orig/State.lean:170`: the `inl` branch demands king + empty — a
cargo-top landing is never `inl`; the `inr` branch demands a live
pile top and the tableau fit on it — that fit is the ladder's third
rung).  The found-prefix conjunct (a) and the `cardCount` census (c)
are not consulted: the rank-ladder arithmetic alone is closed, which
sharpen the doctrine honestly — the merge corner dies at
`runOK`-alone; the phantom and found disciplines are owed by other
corners of the collapse, not these two.

The falsification bet, resolved honestly: the walls STAND.  Each
candidate move into the shape violates a guard under the dividends,
and every invalidating case below is omega/rank-grade, constructively
decided per guard branch — zero excluded middle, zero choice (the
ite-splits-plus-omega idiom throughout).  The boundary is exact: the
witness `xA` satisfies every SHAPE premise of the passing wall and
its merge move does fire — only `WF` fails (the braided edge, the
phantom strays; probed externally, never committed), which is
precisely the line the doctrine draws.

Consumers: the both-occupied mirroring engine (the exchange
simulation's residual corners — it consumes exactly these two heads,
as the old simulation consumed the two engine lemmas) and any count
lane that needs the merge corner dead.  Everything else is private
kit (the aboveIn descent lemma and the step-guard readers),
farm-normal re-derivations, dedup-marked against `Orig.TwinExchange`
/ `Orig.Integrity` at a later tidy card.

Discipline: zero `sorry`, zero `native_decide`, zero
`Classical.choice`.  Axiom targets `[propext]` /
`[propext, Quot.sound]` (per-lemma external probe audits, never
committed).
-/

/-! ## The private reader kit -/

/-- `fromCard` nonempty means the cut card is a member. -/
private theorem fromCard_mem_of_ne {y : Card} : ∀ {l : List Card},
    fromCard y l ≠ [] → y ∈ l
  | [], h => absurd (show fromCard y [] = [] from rfl) h
  | x :: xs, h => by
      cases hd : decide (y = x) with
      | true =>
          have hEq : y = x := of_decide_eq_true hd
          rw [hEq]
          exact List.mem_cons_self ..
      | false =>
          have hne : y ≠ x := by
            intro hcon
            have hdt := decide_eq_true hcon
            rw [hd] at hdt
            exact absurd hdt (by simp)
          rw [fromCard_cons_ne xs (fun hc => hne hc.symm)] at h
          exact List.mem_cons_of_mem x (fromCard_mem_of_ne h)

/-- One rung up is one rank down, iterated: in a legal run every card
strictly above the head sits strictly below the head in rank (the old
clean-stacks descent, re-proved physically as arithmetic on adjacent
`canSitOn` edges). -/
private theorem rank_lt_of_runHead : ∀ (y : Card) (S : List Card),
    runOK (y :: S) = true → ∀ (x : Card), x ∈ S →
    x.rank.toIdx + 1 ≤ y.rank.toIdx := by
  intro y S
  induction S generalizing y with
  | nil => intro _ x hx; cases hx
  | cons w S' ih =>
      intro hr x hx
      rw [runOK_cons_cons, Bool.and_eq_true_iff] at hr
      obtain ⟨h1, h2⟩ := hr
      have hstep : w.rank.toIdx + 1 = y.rank.toIdx :=
        ((canSitOn_eq w y).mp h1).1
      rcases List.mem_cons.mp hx with heq | hx'
      · rw [heq]
        omega
      · have ih' := ih w h2 x hx'
        omega

/-- The `aboveIn` descent: at a settled pile, every card strictly
above `y` sits strictly below `y` in rank — the in-pile ladder leg. -/
private theorem rank_lt_of_aboveIn {l : List Card} {x y : Card}
    (hr : runOK l = true) (hmem : x ∈ aboveIn y l) :
    x.rank.toIdx + 1 ≤ y.rank.toIdx := by
  have hFCne : fromCard y l ≠ [] := by
    intro hc
    have hne : aboveIn y l ≠ [] := by
      intro hcon
      rw [hcon] at hmem
      cases hmem
    rw [show aboveIn y l = (fromCard y l).tail from rfl, hc] at hne
    exact hne rfl
  have hy : y ∈ l := fromCard_mem_of_ne hFCne
  have hsplit : l = below y l ++ y :: aboveIn y l := below_aboveIn_split hy
  have hrun : runOK (y :: aboveIn y l) = true :=
    ((runOK_append_exact y (below y l) (aboveIn y l)).mp
      (by rw [← hsplit]; exact hr)).2
  exact rank_lt_of_runHead y (aboveIn y l) hrun x hmem

/-- A seated cargo fits its seat: at a settled pile, a `z` sitting
directly above `t` (the `aboveIn` head slot) fits `t` by the very
`runOK` leg it lives on — with the strict rank step the ladder
reads. -/
private theorem rank_step_of_seated {t z : Card} {S l : List Card}
    (hr : runOK l = true) (h : aboveIn t l = z :: S) :
    z.rank.toIdx + 1 = t.rank.toIdx := by
  have hFCne : fromCard t l ≠ [] := by
    intro hc
    rw [show aboveIn t l = (fromCard t l).tail from rfl, hc] at h
    exact absurd h (by simp)
  have hy : t ∈ l := fromCard_mem_of_ne hFCne
  have hsplit : l = below t l ++ t :: aboveIn t l := below_aboveIn_split hy
  rw [h] at hsplit
  rw [hsplit] at hr
  exact ((canSitOn_eq z t).mp
    (runOK_joint_of_splice (pre := below t l) (rest := S) hr)).1

/-- The `tabToTab` step branch, read raw (a private step-shape copy;
dedup-marked against Orig.TwinExchange's own). -/
private theorem step_tabToTab_eq (st : State) (c : Card) (b : Base) :
    st.step (Move.tabToTab c b) =
      (match st.pileHolding c with
       | none => none
       | some a =>
           if st.canPlace c b then
             match fromCard c (st.piles a).faceUp with
             | [] => none
             | run =>
                 some ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                   (below c (st.piles a).faceUp))).putRun run b)
           else none) := rfl

/-- A firing `tabToTab` passed the placement guard. -/
private theorem step_tabToTab_canPlace {st st' : State} {c : Card} {b : Base}
    (h : st.step (Move.tabToTab c b) = some st') : st.canPlace c b = true := by
  rw [step_tabToTab_eq] at h
  cases hh : st.pileHolding c with
  | none => rw [hh] at h; simp at h
  | some a =>
      rw [hh] at h
      cases hp : st.canPlace c b with
      | false => rw [hp] at h; simp at h
      | true => rfl

private theorem canPlace_inr_of_true {st : State} {c d : Card}
    (h : st.canPlace c (Sum.inr d) = true) : canSitOn c d = true := by
  rw [canPlace_inr_eq] at h
  cases hh : st.pileOfTop d with
  | none => rw [hh] at h; simp at h
  | some k => rw [hh] at h; exact h

/-! ## The walls -/

/-- **The passing merge is impossible at `WF` states** — the first
merge wall, the physical translation of the old engine's
`merge_impossible_of_visClean` (`Klondike/Restriction.lean:1289`),
re-proved here with zero engine imports.

The merge shape, physically (the w15merge live exhibit made abstract):
two twin threads are seated — a cargo `z` directly above its seat
`t` in one pile, a cargo `z'` directly above `t`'s twin in another —
and a `tabToTab` fires whose run passes a twin seat (either seat
strictly above the run root `c`, on a settled pile) while LANDING on
a cargo stack: on `z` itself, on a card above `z` in `z`'s pile, on
`z'` itself, or on a card above `z'` in its pile.

The FIT-LADDER CONTRADICTION: the landing fit demands the root one
rank UNDER the base (`c + 1 = d`); the cargo joints demand each cargo
one rank under its seat (`z + 1 = t`, `z' + 1 = t.twin`, the twins of
one rank); the in-pile descent demands the passed seat strictly below
the root (`t + 1 ≤ c`) and any card above a cargo strictly below that
cargo.  The closure cycles `t + 2 ≤ t - 1` — rank-impossible, so the
move the witness exhibits has no `WF` realization: each candidate move
into the shape violates a guard (the `inl` branch is a non-cargo
landing by its king-and-empty demand; the `inr` branch must
twin-fit a live pile top, and that fit is the contradiction).

All invalidating cases are omega/rank-grade, constructively decided
per guard branch. -/
theorem merge_impossible_of_WF {st st' : State} {a a' a₁ : Anchor}
    {t z z' c : Card} {Sa Sa' : List Card} {b : Base}
    (hwf : st.WF)
    (h₀ : aboveIn t (st.piles a).faceUp = z :: Sa)
    (h₀' : aboveIn t.twin (st.piles a').faceUp = z' :: Sa')
    (hstep : st.step (Move.tabToTab c b) = some st')
    (hmerge : t ∈ aboveIn c (st.piles a₁).faceUp ∨
      t.twin ∈ aboveIn c (st.piles a₁).faceUp)
    (hland : ∃ d : Card, b = Sum.inr d ∧
      (d = z ∨ d ∈ aboveIn z (st.piles a).faceUp ∨
       d = z' ∨ d ∈ aboveIn z' (st.piles a').faceUp)) :
    False := by
  obtain ⟨-, hr, -, -⟩ := hwf
  have htt : t.twin.rank.toIdx = t.rank.toIdx :=
    congrArg Rank.toIdx (Card.twin_rank t)
  have hzfit : z.rank.toIdx + 1 = t.rank.toIdx :=
    rank_step_of_seated (hr a) h₀
  have hz'fit : z'.rank.toIdx + 1 = t.twin.rank.toIdx :=
    rank_step_of_seated (hr a') h₀'
  have hcp := step_tabToTab_canPlace hstep
  obtain ⟨d, rfl, hd⟩ := hland
  have hsit : c.rank.toIdx + 1 = d.rank.toIdx :=
    ((canSitOn_eq c d).mp (canPlace_inr_of_true hcp)).1
  rcases hmerge with hmem | hmem
  · have hseat : t.rank.toIdx + 1 ≤ c.rank.toIdx :=
      rank_lt_of_aboveIn (hr a₁) hmem
    rcases hd with rfl | hdz | rfl | hdz'
    · omega
    · have hdea : d.rank.toIdx + 1 ≤ z.rank.toIdx :=
        rank_lt_of_aboveIn (hr a) hdz
      omega
    · omega
    · have hdea' : d.rank.toIdx + 1 ≤ z'.rank.toIdx :=
        rank_lt_of_aboveIn (hr a') hdz'
      omega
  · have hseat : t.twin.rank.toIdx + 1 ≤ c.rank.toIdx :=
      rank_lt_of_aboveIn (hr a₁) hmem
    rcases hd with rfl | hdz | rfl | hdz'
    · omega
    · have hdea : d.rank.toIdx + 1 ≤ z.rank.toIdx :=
        rank_lt_of_aboveIn (hr a) hdz
      omega
    · omega
    · have hdea' : d.rank.toIdx + 1 ≤ z'.rank.toIdx :=
        rank_lt_of_aboveIn (hr a') hdz'
      omega

/-- **The twin-rooted merge is impossible at `WF` states** — the
second merge wall, the physical translation of the old engine's
`merge_rooted_impossible_of_visClean`
(`Klondike/Restriction.lean:1360`), re-proved here with zero engine
imports.

The rooted variant: the lifted run IS the seat itself (`c = t` — the
run root is the twin seat, no card of the run sits below it), and the
landing is on the OTHER cargo's stack, strictly above the other cargo
`z'` (the merged seat at the deal root).

Arithmetic: the landing fit demands the seat-root one rank UNDER the
landing base (`t + 1 = d`); the other cargo's joint demands `z'` one
rank under the twin seat (`z' + 1 = t.twin = t`); the `aboveIn`
descent demands the landing base strictly BELOW that other cargo
(`d + 1 ≤ z'`).  The closure cycles `t + 2 ≤ t - 1` again — omega,
rank-grade, constructive in both guard branches. -/
theorem merge_rooted_impossible_of_WF {st st' : State} {a' : Anchor}
    {t z' c : Card} {Sa' : List Card} {b : Base}
    (hwf : st.WF)
    (h₀' : aboveIn t.twin (st.piles a').faceUp = z' :: Sa')
    (hstep : st.step (Move.tabToTab c b) = some st')
    (hc : c = t)
    (hland : ∃ d : Card, b = Sum.inr d ∧
      d ∈ aboveIn z' (st.piles a').faceUp) :
    False := by
  obtain ⟨-, hr, -, -⟩ := hwf
  have hz'fit : z'.rank.toIdx + 1 = t.twin.rank.toIdx :=
    rank_step_of_seated (hr a') h₀'
  have htt : t.twin.rank.toIdx = t.rank.toIdx :=
    congrArg Rank.toIdx (Card.twin_rank t)
  have hcp := step_tabToTab_canPlace hstep
  obtain ⟨d, rfl, hd⟩ := hland
  have hsit : c.rank.toIdx + 1 = d.rank.toIdx :=
    ((canSitOn_eq c d).mp (canPlace_inr_of_true hcp)).1
  rw [hc] at hsit
  have hdea : d.rank.toIdx + 1 ≤ z'.rank.toIdx :=
    rank_lt_of_aboveIn (hr a') hd
  omega
