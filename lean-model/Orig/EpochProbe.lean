import Orig.ForkStateSB

/-!
# Orig.EpochProbe — THE EPOCH TWO-CELL PROBE

Decide-grade evidence for the no-lock pairClass story: one cell per
epoch direction, every row a kernel-decided fact under a `theorem`
wrapper, zero sorry.

* **CELL ONE (§§1-2) — the upward confinement validation.**  The
  S-craft rebuilt on a permissive board (`up0`: the pair {5♥, 5♦}
  geometry plus a foreign island hosting the black-3 and a foreign
  seat-ok 6♥ — the upward marathon's door material), then the
  licensed climb walked state by state: `up1` (raise 5♥), `up2`
  (raise 6♠), `up3` (raise the foreign 6♥) — and the STALL: from
  `up3` on, NO card in the universe carries a live S-license.  The
  twin-side door (4♣ vacating so 5♦ can raise) is audited shut at
  every milestone: the cover's landing lattice — rank-5 red tops, or
  a king's empty anchor — is decide-empty from `up1` onward.
* **CELL TWO (§§3-5) — the downward pull craft, the decisive one.**
  The pull-permissive board (`down0`: spades at THREE so 5♠ is
  unfounded anchor material, clubs down at one so the black-3 cargo
  is rank-locked, the {5♥, 5♦} pair live, BOTH black-5 anchors
  hosted as pile tops).  The walk: pull 4♥ onto the 5♠ anchor
  (`down1`), pull 4♦ onto the 5♣ anchor (`down2`), slide the
  island's 3♣ onto the landed 4♦ (`down3`).  The verdict row is
  decided at both club rungs: the first-try clubs-at-2 board FAILS
  (the seated 3♣ is next-up live — the offender row is on record),
  the iterated clubs-at-1 board lands `forkStateSB down3 = true`
  with witness 4♥ — a genuine rank-4 fork on the same dealt economy.
  The connection row then prices the class: the pull legs ARE
  reversible (their mirrors are licensed re-founds, rfl-witnessed
  each way) — but the dressing slide is an audited COMMITMENT (a
  revealing slide over a nonempty hidden island; its one-move mirror
  is decide-dead at the landing), so the rank-4 fork sits behind a
  one-way door the reversible class cannot pass — the no-lock
  pairClass theorem survives this probe (decide-grade).

The instrument is `Orig.ForkStateSB`'s census (`forkStateSB` with
its `forkStateSB_true_iff` bridge); the setoid/journey kit comes
transitively with it (`sameOrbitSetoid`, `ShufflePlayW`,
`reversibleAtW`, and the banked `journey_tabToTab_never_reveal`).
-/

/-! ## §0. The private kit -/
/- The house card-maker (each probe file carries its own). -/
private def crd (s : Suit) (r : Rank) : Card := ⟨s, r⟩

/- A suit's foundation prefix at height `n` (the craft's `found`). -/
private def takeUp (s : Suit) (n : Nat) : List Card := s.upCards.take n

/- Oracle step helper (dead-hand plays are construction bugs; the
step theorems below throw — the SProbe/ForkStateUniqGate pattern). -/
private def stepD (st : State) (m : Move) : State :=
  match st.step m with
  | none => st
  | some s' => s'

/-! ## §1. CELL ONE — the permissive up-board

The S-craft geometry, rungs ♠ 5 / ♥ 4 / ♦ 4 / ♣ 2 (the SProbe
`hmap`), with the doors handed material: p1 is the CLUB ISLAND
hosting the black-3 (3♣ flipped bare over its hidden club deck — its
own lift is seat-barred, but as door material it waits for a red-4
top to dress), and p6 is the FOREIGN SEAT pile [7♠, 6♥] — the
seat-ok 6♥ that will climb when hearts opens to it.  The census
still folds the {5♥, 5♦} pair: 6♠ stays sealed (its 6♣ twin buried
under the repaired twin's seat), the island's 3♣ dies at the seat
bar, the foreign 6♥ is next-up-dead at hearts 4. -/

private def H5 : Card := crd .heart .five
private def D5 : Card := crd .diamond .five
private def H7 : Card := crd .heart .seven
private def S6 : Card := crd .spade .six
private def C6 : Card := crd .club .six
private def C4 : Card := crd .club .four
private def C3 : Card := crd .club .three
private def S7 : Card := crd .spade .seven
private def H6 : Card := crd .heart .six

/-- The up-craft rungs: ♠ 5, ♥ 4, ♦ 4, ♣ 2. -/
private def hmapU : Suit → Nat
  | .heart => 4 | .diamond => 4 | .spade => 5 | .club => 2

/-- **THE UP-BOARD `up0`**: p0 = [7♥, 6♠, 5♥] (the witness topping
its own blocking cargo); p2 = [6♣, 5♦, 4♣] (the repaired twin under
its unfounded-not-next-up cover — the mate channel open at the
witness); p1 = the club island ⟨[5♣, 8♣, …, K♣], [3♣]⟩ (the black-3
parked seat-barred); p6 = ⟨[], [7♠, 6♥]⟩ (the foreign seat-ok six);
p3/p4/p5 hidden-only sinks; stock [7♣], waste [J♦], drawStep 1. -/
private def up0 : State where
  found := fun s => takeUp s (hmapU s)
  piles := fun a => match a with
    | .p0 => ⟨[], [H7, S6, H5]⟩
    | .p1 => ⟨[crd .club .five, crd .club .eight, crd .club .nine,
               crd .club .ten, crd .club .jack, crd .club .queen,
               crd .club .king], [C3]⟩
    | .p2 => ⟨[], [C6, D5, C4]⟩
    | .p3 => ⟨[crd .spade .eight, crd .spade .nine, crd .spade .ten,
               crd .spade .jack, crd .spade .queen, crd .spade .king], []⟩
    | .p4 => ⟨[crd .heart .eight, crd .heart .nine, crd .heart .ten,
               crd .heart .jack, crd .heart .queen, crd .heart .king], []⟩
    | .p5 => ⟨[crd .diamond .six, crd .diamond .seven, crd .diamond .eight,
               crd .diamond .nine, crd .diamond .ten, crd .diamond .queen,
               crd .diamond .king], []⟩
    | .p6 => ⟨[], [S7, H6]⟩
  stock := [crd .club .seven]
  waste := [crd .diamond .jack]
  drawStep := 1

private theorem up0_wf_found : ∀ s : Suit, ∃ n, up0.found s = s.upCards.take n := by
  intro s
  cases s with
  | spade => exact ⟨5, rfl⟩
  | heart => exact ⟨4, rfl⟩
  | diamond => exact ⟨4, rfl⟩
  | club => exact ⟨2, rfl⟩

private theorem up0_wf_runs : ∀ a : Anchor, runOK (up0.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

private theorem up0_wf_count : ∀ c ∈ Card.universe, up0.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

/-- The up-board is `WF` (all four clauses, kernel-decided). -/
private theorem up0_wf : up0.WF :=
  ⟨up0_wf_found, up0_wf_runs, up0_wf_count, by decide⟩

/-- **THE PERMISSIVE BOARD STILL FORKS** — the census folds the
{5♥, 5♦} pair verbatim (the island and the foreign seat stay dead). -/
theorem up0_fork : forkStateSB up0 = true := by decide

theorem up0_forkState : forkState up0 := (forkStateSB_true_iff up0_wf).mp up0_fork

/-- The witness is the vanilla-live 5♥ (rfl-fold of the search). -/
theorem up0_witness : forkWitnessSB up0 = some H5 := by rfl

/-- The ledger: the pair lives (the vanilla witness, the S-live
covered twin through the mate channel's twin-topping exit); the
sealed 6♠, the island's 3♣, and the foreign 6♥ are all dead. -/
theorem up0_ledger :
    canRaiseSB up0 H5 = true ∧ canRaiseSB up0 D5 = true ∧
      canRaiseSB up0 S6 = false ∧ canRaiseSB up0 C3 = false ∧
      canRaiseSB up0 H6 = false :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- **THE MATE CHANNEL AT THE ORIGIN** — at `up0` the cover's one
reversible landing exists: 4♣'s run onto the witness's top (the
SProbe `slideM` door, recorded here as the bar's opening). -/
theorem up0_mateOpen : up0.canPlace C4 (Sum.inr H5) = true := by decide

/-! ## §2. CELL ONE — the upward walk, and the stall

The licensed climb, one `decide` row per milestone: raise the
witness 5♥ (`up1`, hearts → 5, the parent 6♠ exposed), raise the
exposed next-up 6♠ (`up2`, spades → 6), raise the foreign 6♥ (`up3`,
hearts → 6, the pile-D seat laid bare).  From `up3` on the strong
census is DEAD ON EVERY CARD IN THE UNIVERSE — the marathon stalls. -/

/-- `up1`: the witness raised to its foundation (the SProbe
`cellRa` step, on the permissive board). -/
private def up1 : State := stepD up0 (Move.tabToFound H5)

/-- `up2`: the exposed parent 6♠ raised to spades (the spade rung 6). -/
private def up2 : State := stepD up1 (Move.tabToFound S6)

/-- `up3`: the foreign 6♥ raised to hearts (hearts 6, the foreign
seat laid bare at p6 = [7♠]). -/
private def up3 : State := stepD up2 (Move.tabToFound H6)

/-- The milestones fire exactly as claimed (the stepD chains are
kernel-reductions, one `rfl` each — the ForkStateUniqGate climb rows). -/
theorem up1_step : State.step up0 (Move.tabToFound H5) = some up1 := by rfl
theorem up2_step : State.step up1 (Move.tabToFound S6) = some up2 := by rfl
theorem up3_step : State.step up2 (Move.tabToFound H6) = some up3 := by rfl

private theorem up1_wf_found : ∀ s : Suit, ∃ n, up1.found s = s.upCards.take n := by
  intro s
  cases s with
  | spade => exact ⟨5, rfl⟩
  | heart => exact ⟨5, rfl⟩
  | diamond => exact ⟨4, rfl⟩
  | club => exact ⟨2, rfl⟩

private theorem up1_wf_runs : ∀ a : Anchor, runOK (up1.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

private theorem up1_wf_count : ∀ c ∈ Card.universe, up1.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

private theorem up1_wf : up1.WF :=
  ⟨up1_wf_found, up1_wf_runs, up1_wf_count, by decide⟩

private theorem up2_wf_found : ∀ s : Suit, ∃ n, up2.found s = s.upCards.take n := by
  intro s
  cases s with
  | spade => exact ⟨6, rfl⟩
  | heart => exact ⟨5, rfl⟩
  | diamond => exact ⟨4, rfl⟩
  | club => exact ⟨2, rfl⟩

private theorem up2_wf_runs : ∀ a : Anchor, runOK (up2.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

private theorem up2_wf_count : ∀ c ∈ Card.universe, up2.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

private theorem up2_wf : up2.WF :=
  ⟨up2_wf_found, up2_wf_runs, up2_wf_count, by decide⟩

private theorem up3_wf_found : ∀ s : Suit, ∃ n, up3.found s = s.upCards.take n := by
  intro s
  cases s with
  | spade => exact ⟨6, rfl⟩
  | heart => exact ⟨6, rfl⟩
  | diamond => exact ⟨4, rfl⟩
  | club => exact ⟨2, rfl⟩

private theorem up3_wf_runs : ∀ a : Anchor, runOK (up3.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

private theorem up3_wf_count : ∀ c ∈ Card.universe, up3.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

/-- The stall endpoint is `WF` (kernel-decided, all four clauses). -/
private theorem up3_wf : up3.WF :=
  ⟨up3_wf_found, up3_wf_runs, up3_wf_count, by decide⟩

/-- **MILESTONE 1, NO RE-PIN**: mid-climb the census is dead (the two
live sixes are suit-strangers: 6♣ under the twin, 6♦ hidden). -/
theorem up1_forkSB : forkStateSB up1 = false := by decide

/-- The licensed follow-ups at `up1`: the exposed parent 6♠ and the
foreign 6♥ are both live (the marathon's next two doors). -/
theorem up1_live :
    canRaiseSB up1 S6 = true ∧ canRaiseSB up1 H6 = true :=
  ⟨by decide, by decide⟩

/-- **MILESTONE 2, NO RE-PIN**: the census dead after the spade climb. -/
theorem up2_forkSB : forkStateSB up2 = false := by decide

/-- The 6♥ still licensed; the bare 7♥ at p0 already waits dead
(hearts at 5 — its turn never comes licensed). -/
theorem up2_live :
    canRaiseSB up2 H6 = true ∧ canRaiseSB up2 H7 = false :=
  ⟨by decide, by decide⟩

/-- **MILESTONE 3, NO RE-PIN**: still dead after the foreign climb. -/
theorem up3_forkSB : forkStateSB up3 = false := by decide

/-- **THE STALL, both seat bars decided**: the next-up 7♥ (hearts 6,
topping the emptied p0) and the next-up 7♠ (spades 6, topping the
emptied foreign seat) are SEAT-BARRED — bare non-kings over empty
hidden decks, no under-seat left to license them. -/
theorem up3_seatbars :
    canRaiseSB up3 H7 = false ∧ canRaiseSB up3 S7 = false :=
  ⟨by decide, by decide⟩

/-- **THE UP-CELL VERDICT ROW: THE MARATHON STALLS AT `up3`** — no
card of the 52 carries a live S-license (the full-universe
per-card fold, kernel-decided). -/
theorem up3_stalls : ∀ c ∈ Card.universe, canRaiseSB up3 c = false := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

/-! ### The twin-side door, audited shut at every milestone

For the twin 5♦ to raise, its cover 4♣ must first vacate — and a
run headed by 4♣ lands only on a rank-5 RED top (5♥ or 5♦) or, as a
king, an empty anchor (which 4♣ is not).  Once the witness founds
(`up1`), 5♥ is gone from the piles forever and 5♦ stays buried
under the cover — the landing lattice is decide-empty at every
milestone, and the twin's own S-license (covered, exit through the
twin's pile-top) dies with the witness's departure. -/

theorem up1_cover :
    (∀ z ∈ Card.universe, up1.canPlace C4 (Sum.inr z) = false) ∧
      (∀ a : Anchor, up1.canPlace C4 (Sum.inl a) = false) ∧
        canRaiseSB up1 D5 = false := by
  refine ⟨?_, ?_, by decide⟩
  · intro z _
    rcases z with ⟨s, r⟩
    cases s <;> cases r <;> decide
  · intro a
    cases a <;> decide

theorem up2_cover :
    (∀ z ∈ Card.universe, up2.canPlace C4 (Sum.inr z) = false) ∧
      (∀ a : Anchor, up2.canPlace C4 (Sum.inl a) = false) ∧
        canRaiseSB up2 D5 = false := by
  refine ⟨?_, ?_, by decide⟩
  · intro z _
    rcases z with ⟨s, r⟩
    cases s <;> cases r <;> decide
  · intro a
    cases a <;> decide

/-- **THE FINAL TWIN-DOOR AUDIT (`upCovered`)**: at the stall
endpoint the cover's landing lattice is empty and the twin's
S-license is dead — the 4♣ can never vacate, so 5♦ can never
raise: the confinement is TOTAL, decided over the whole universe. -/
theorem up_covered :
    (∀ z ∈ Card.universe, up3.canPlace C4 (Sum.inr z) = false) ∧
      (∀ a : Anchor, up3.canPlace C4 (Sum.inl a) = false) ∧
        canRaiseSB up3 D5 = false := by
  refine ⟨?_, ?_, by decide⟩
  · intro z _
    rcases z with ⟨s, r⟩
    cases s <;> cases r <;> decide
  · intro a
    cases a <;> decide

/-! ## §3. CELL TWO — the downward pull craft, FIRST TRY (clubs at 2)

The pull-permissive geometry: spades at rung THREE (so 5♠ is
UNFOUNDED board material — a potential black-5 anchor), clubs at 2,
the {5♥, 5♦} pair live exactly as the S-craft seats it, BOTH
black-5 anchors hosted as pile tops — p3 = [6♥, 5♠] and
p4 = [6♦, 5♣] — reachable material for `foundToTab` landings;
the island p1 hosts the black-3 (3♣ over hidden clubs, seat-barred);
every other candidate card census-dead (4♠ stock-resident, the rest
next-up-dead by the rung arithmetic).  The walk pulls 4♥ and 4♦
down onto the anchors and slides the island's 3♣ onto the landed
4♦ — and the verdict row FAILS: at clubs 2 the seated 3♣ is
NEXT-UP LIVE (the offender, on record) — the census-kill that
dies on landing. -/

private def S4 : Card := crd .spade .four
private def S5 : Card := crd .spade .five
private def C5 : Card := crd .club .five
private def D4 : Card := crd .diamond .four
private def H4 : Card := crd .heart .four
private def D6 : Card := crd .diamond .six

/-- The first-try rungs: ♠ 3, ♥ 4, ♦ 4, ♣ 2. -/
private def hmapV : Suit → Nat
  | .heart => 4 | .diamond => 4 | .spade => 3 | .club => 2

/-- **THE FIRST-TRY DOWN-BOARD `downV0`**: p0 = [7♥, 6♠, 5♥] (6♠
board-seated cargo, its rung unmattered); p2 = [6♣, 5♦, 4♣] (the
twin under its cover); p3 = [6♥, 5♠] and p4 = [6♦, 5♣] (the two
black-5 anchor piles, junk-residue seats); p1 = the club island
⟨[7♣ …, K♣], [3♣]⟩; p5 = the spade sink; p6 = the heart/diamond
sink; stock [4♠] (the spade next-up, stock-resident and dead);
waste [J♦]; drawStep 1. -/
private def downV0 : State where
  found := fun s => takeUp s (hmapV s)
  piles := fun a => match a with
    | .p0 => ⟨[], [H7, S6, H5]⟩
    | .p1 => ⟨[crd .club .seven, crd .club .eight, crd .club .nine,
               crd .club .ten, crd .club .jack, crd .club .queen,
               crd .club .king], [C3]⟩
    | .p2 => ⟨[], [C6, D5, C4]⟩
    | .p3 => ⟨[], [H6, S5]⟩
    | .p4 => ⟨[], [D6, C5]⟩
    | .p5 => ⟨[crd .spade .seven, crd .spade .eight, crd .spade .nine,
               crd .spade .ten, crd .spade .jack, crd .spade .queen,
               crd .spade .king], []⟩
    | .p6 => ⟨[crd .heart .eight, crd .heart .nine, crd .heart .ten,
               crd .heart .jack, crd .heart .queen, crd .heart .king,
               crd .diamond .seven, crd .diamond .eight, crd .diamond .nine,
               crd .diamond .ten, crd .diamond .queen, crd .diamond .king], []⟩
  stock := [S4]
  waste := [crd .diamond .jack]
  drawStep := 1

private theorem downV0_wf_found : ∀ s : Suit, ∃ n, downV0.found s = s.upCards.take n := by
  intro s
  cases s with
  | spade => exact ⟨3, rfl⟩
  | heart => exact ⟨4, rfl⟩
  | diamond => exact ⟨4, rfl⟩
  | club => exact ⟨2, rfl⟩

private theorem downV0_wf_runs : ∀ a : Anchor, runOK (downV0.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

private theorem downV0_wf_count : ∀ c ∈ Card.universe, downV0.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

/-- The first-try board is `WF`. -/
private theorem downV0_wf : downV0.WF :=
  ⟨downV0_wf_found, downV0_wf_runs, downV0_wf_count, by decide⟩

/-- **THE FIRST-TRY BASE IS A GENUINE FORK** — the census folds the
{5♥, 5♦} pair (4♠ stock-dead, the island's 3♣ seat-barred). -/
theorem downV0_fork : forkStateSB downV0 = true := by decide

theorem downV0_forkState : forkState downV0 :=
  (forkStateSB_true_iff downV0_wf).mp downV0_fork

theorem downV0_witness : forkWitnessSB downV0 = some H5 := by rfl

/-- The first-try ledger: the pair lives; the spade next-up and the
island's black-3 are dead. -/
theorem downV0_ledger :
    canRaiseSB downV0 H5 = true ∧ canRaiseSB downV0 D5 = true ∧
      canRaiseSB downV0 S4 = false ∧ canRaiseSB downV0 C3 = false :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- `downV1`: the first pull — 4♥ off the hearts foundation onto
the 5♠ anchor's top. -/
private def downV1 : State := stepD downV0 (Move.foundToTab H4 (Sum.inr S5))

/-- `downV2`: the second pull — 4♦ onto the 5♣ anchor. -/
private def downV2 : State := stepD downV1 (Move.foundToTab D4 (Sum.inr C5))

/-- `downV3`: the dressing — the island's 3♣ slid onto the landed
4♦. -/
private def downV3 : State := stepD downV2 (Move.tabToTab C3 (Sum.inr D4))

theorem downV1_step :
    State.step downV0 (Move.foundToTab H4 (Sum.inr S5)) = some downV1 := by rfl
theorem downV2_step :
    State.step downV1 (Move.foundToTab D4 (Sum.inr C5)) = some downV2 := by rfl
theorem downV3_step :
    State.step downV2 (Move.tabToTab C3 (Sum.inr D4)) = some downV3 := by rfl

private theorem downV1_wf_found : ∀ s : Suit, ∃ n, downV1.found s = s.upCards.take n := by
  intro s
  cases s with
  | spade => exact ⟨3, rfl⟩
  | heart => exact ⟨3, rfl⟩
  | diamond => exact ⟨4, rfl⟩
  | club => exact ⟨2, rfl⟩

private theorem downV1_wf_runs : ∀ a : Anchor, runOK (downV1.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

private theorem downV1_wf_count : ∀ c ∈ Card.universe, downV1.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

private theorem downV1_wf : downV1.WF :=
  ⟨downV1_wf_found, downV1_wf_runs, downV1_wf_count, by decide⟩

private theorem downV2_wf_found : ∀ s : Suit, ∃ n, downV2.found s = s.upCards.take n := by
  intro s
  cases s with
  | spade => exact ⟨3, rfl⟩
  | heart => exact ⟨3, rfl⟩
  | diamond => exact ⟨3, rfl⟩
  | club => exact ⟨2, rfl⟩

private theorem downV2_wf_runs : ∀ a : Anchor, runOK (downV2.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

private theorem downV2_wf_count : ∀ c ∈ Card.universe, downV2.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

private theorem downV2_wf : downV2.WF :=
  ⟨downV2_wf_found, downV2_wf_runs, downV2_wf_count, by decide⟩

private theorem downV3_wf_found : ∀ s : Suit, ∃ n, downV3.found s = s.upCards.take n := by
  intro s
  cases s with
  | spade => exact ⟨3, rfl⟩
  | heart => exact ⟨3, rfl⟩
  | diamond => exact ⟨3, rfl⟩
  | club => exact ⟨2, rfl⟩

private theorem downV3_wf_runs : ∀ a : Anchor, runOK (downV3.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

private theorem downV3_wf_count : ∀ c ∈ Card.universe, downV3.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

private theorem downV3_wf : downV3.WF :=
  ⟨downV3_wf_found, downV3_wf_runs, downV3_wf_count, by decide⟩

/-- **MID-WALK 1, DEAD**: the pulled 4♥ tops the spade anchor — and
the covered twin is still S-live (its exit rides the WITNESS's
still-standing top) — two live cards, no pair. -/
theorem downV1_forkSB : forkStateSB downV1 = false := by decide

theorem downV1_live :
    canRaiseSB downV1 H4 = true ∧ canRaiseSB downV1 D5 = true :=
  ⟨by decide, by decide⟩

/-- **MID-WALK 2, DEAD — the orientation pin dies**: both pulled
fours top their anchors and are VANILLA-live; the S-census sees
{4♥, 4♦} but no witness (each twin's vanilla lift kills the
pin) — the dressed epoch cannot fork here. -/
theorem downV2_forkSB : forkStateSB downV2 = false := by decide

theorem downV2_pin :
    canRaiseB downV2 H4 = true ∧ canRaiseB downV2 D4 = true :=
  ⟨by decide, by decide⟩

/-- **THE FIRST-TRY VERDICT: FALSE** — after the dressing slide the
census is dead: the seated 3♣ (now topping the dressed sandwich at
[6♦, 5♣, 4♦, 3♣], its seat long since non-bare) is NEXT-UP LIVE at
clubs 2 — a third live card no fork pair covers. -/
theorem downV3_forkSB : forkStateSB downV3 = false := by decide

/-- **THE OFFENDER, ON RECORD**: the dressed 3♣ itself carries a
live S-license at the first-try board (the seat kill that worked at
the bare island is dead on landing — `canRaiseSB` decides it). -/
theorem downV3_offender : canRaiseSB downV3 C3 = true := by decide

/-! ## §4. CELL TWO — the iterated board (clubs at 1), the verdict TRUE

The offender's seat cannot be re-killed (a landed card on a dressed
sandwich always seats), but its RUNG can: dropping the club
foundation to ONE — 2♣ demoted to stock-resident dead material —
rank-locks the 3♣ at every milestone of the walk (idx 2 ≠ rung 1),
so the dressing slide hands the census EXACTLY the {4♥, 4♦} pair at
`down3`.  Everything else is verbatim the first-try economy: the
anchors, the island, the sinks, the stock's spade next-up. -/

private def S3 : Card := crd .spade .three
private def C2 : Card := crd .club .two

/-- The iterated rungs: ♠ 3, ♥ 4, ♦ 4, ♣ 1 (the club column opened
below the black-3 — the rank-lock kill). -/
private def hmapD : Suit → Nat
  | .heart => 4 | .diamond => 4 | .spade => 3 | .club => 1

/-- **THE DOWN-BOARD `down0`**: the first-try economy with the club
foundation at one and 2♣ moved to the stock (both census-dead there
at rung 1); all seven piles verbatim the first-try layout. -/
private def down0 : State where
  found := fun s => takeUp s (hmapD s)
  piles := fun a => match a with
    | .p0 => ⟨[], [H7, S6, H5]⟩
    | .p1 => ⟨[crd .club .seven, crd .club .eight, crd .club .nine,
               crd .club .ten, crd .club .jack, crd .club .queen,
               crd .club .king], [C3]⟩
    | .p2 => ⟨[], [C6, D5, C4]⟩
    | .p3 => ⟨[], [H6, S5]⟩
    | .p4 => ⟨[], [D6, C5]⟩
    | .p5 => ⟨[crd .spade .seven, crd .spade .eight, crd .spade .nine,
               crd .spade .ten, crd .spade .jack, crd .spade .queen,
               crd .spade .king], []⟩
    | .p6 => ⟨[crd .heart .eight, crd .heart .nine, crd .heart .ten,
               crd .heart .jack, crd .heart .queen, crd .heart .king,
               crd .diamond .seven, crd .diamond .eight, crd .diamond .nine,
               crd .diamond .ten, crd .diamond .queen, crd .diamond .king], []⟩
  stock := [S4, C2]
  waste := [crd .diamond .jack]
  drawStep := 1

private theorem down0_wf_found : ∀ s : Suit, ∃ n, down0.found s = s.upCards.take n := by
  intro s
  cases s with
  | spade => exact ⟨3, rfl⟩
  | heart => exact ⟨4, rfl⟩
  | diamond => exact ⟨4, rfl⟩
  | club => exact ⟨1, rfl⟩

private theorem down0_wf_runs : ∀ a : Anchor, runOK (down0.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

private theorem down0_wf_count : ∀ c ∈ Card.universe, down0.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

/-- The iterated board is `WF`. -/
private theorem down0_wf : down0.WF :=
  ⟨down0_wf_found, down0_wf_runs, down0_wf_count, by decide⟩

/-- **THE ITERATED BASE IS A GENUINE FORK** — the census folds the
{5♥, 5♦} pair verbatim (the rank-lock silences the black-3; the 2♣
is stock-resident and dead). -/
theorem down0_fork : forkStateSB down0 = true := by decide

theorem down0_forkState : forkState down0 :=
  (forkStateSB_true_iff down0_wf).mp down0_fork

theorem down0_witness : forkWitnessSB down0 = some H5 := by rfl

/-- The iterated ledger: the pair lives; BOTH club candidates (the
island's 3♣ and the demoted 2♣) and the spade next-up are dead. -/
theorem down0_ledger :
    canRaiseSB down0 H5 = true ∧ canRaiseSB down0 D5 = true ∧
      canRaiseSB down0 S4 = false ∧ canRaiseSB down0 C3 = false ∧
        canRaiseSB down0 C2 = false :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- `down1`: the first pull — 4♥ off hearts onto the 5♠ anchor. -/
private def down1 : State := stepD down0 (Move.foundToTab H4 (Sum.inr S5))

/-- `down2`: the second pull — 4♦ onto the 5♣ anchor. -/
private def down2 : State := stepD down1 (Move.foundToTab D4 (Sum.inr C5))

/-- `down3`: the dressing — the island's 3♣ slid onto the landed
4♦ (the new sandwich dressed: [6♦, 5♣, 4♦, 3♣]). -/
private def down3 : State := stepD down2 (Move.tabToTab C3 (Sum.inr D4))

theorem down1_step :
    State.step down0 (Move.foundToTab H4 (Sum.inr S5)) = some down1 := by rfl
theorem down2_step :
    State.step down1 (Move.foundToTab D4 (Sum.inr C5)) = some down2 := by rfl
theorem down3_step :
    State.step down2 (Move.tabToTab C3 (Sum.inr D4)) = some down3 := by rfl

private theorem down1_wf_found : ∀ s : Suit, ∃ n, down1.found s = s.upCards.take n := by
  intro s
  cases s with
  | spade => exact ⟨3, rfl⟩
  | heart => exact ⟨3, rfl⟩
  | diamond => exact ⟨4, rfl⟩
  | club => exact ⟨1, rfl⟩

private theorem down1_wf_runs : ∀ a : Anchor, runOK (down1.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

private theorem down1_wf_count : ∀ c ∈ Card.universe, down1.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

private theorem down1_wf : down1.WF :=
  ⟨down1_wf_found, down1_wf_runs, down1_wf_count, by decide⟩

private theorem down2_wf_found : ∀ s : Suit, ∃ n, down2.found s = s.upCards.take n := by
  intro s
  cases s with
  | spade => exact ⟨3, rfl⟩
  | heart => exact ⟨3, rfl⟩
  | diamond => exact ⟨3, rfl⟩
  | club => exact ⟨1, rfl⟩

private theorem down2_wf_runs : ∀ a : Anchor, runOK (down2.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

private theorem down2_wf_count : ∀ c ∈ Card.universe, down2.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

private theorem down2_wf : down2.WF :=
  ⟨down2_wf_found, down2_wf_runs, down2_wf_count, by decide⟩

private theorem down3_wf_found : ∀ s : Suit, ∃ n, down3.found s = s.upCards.take n := by
  intro s
  cases s with
  | spade => exact ⟨3, rfl⟩
  | heart => exact ⟨3, rfl⟩
  | diamond => exact ⟨3, rfl⟩
  | club => exact ⟨1, rfl⟩

private theorem down3_wf_runs : ∀ a : Anchor, runOK (down3.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

private theorem down3_wf_count : ∀ c ∈ Card.universe, down3.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

/-- The dressed endpoint is `WF` (all four clauses, kernel-decided). -/
private theorem down3_wf : down3.WF :=
  ⟨down3_wf_found, down3_wf_runs, down3_wf_count, by decide⟩

/-- **MID-WALK 1, DEAD** (as the first try): the pulled 4♥ and the
witness-topped twin both live, no pair. -/
theorem down1_forkSB : forkStateSB down1 = false := by decide

theorem down1_live :
    canRaiseSB down1 H4 = true ∧ canRaiseSB down1 D5 = true :=
  ⟨by decide, by decide⟩

/-- **MID-WALK 2, DEAD — the pin still dies**: both fours
vanilla-live, no witness — the dressing epoch has not forked yet. -/
theorem down2_forkSB : forkStateSB down2 = false := by decide

theorem down2_pin :
    canRaiseB down2 H4 = true ∧ canRaiseB down2 D4 = true :=
  ⟨by decide, by decide⟩

/-- **THE VERDICT ROW: TRUE AT CLUBS 1** — after the dressing slide
the census folds the {4♥, 4♦} pair: the pulled four tops the spade
anchor (vanilla-live), the OTHER pulled four sits COVERED under the
rank-locked black-3 (S-live through the twin's topping, vanilla-dead)
— a genuine rank-4 fork on the same dealt economy. -/
theorem down3_forkSB : forkStateSB down3 = true := by decide

/-- **THE WITNESS NAMED**: the SB search folds to the pulled 4♥
(rank 4 — the epoch's downward pair). -/
theorem down3_witness : forkWitnessSB down3 = some H4 := by rfl

/-- **BANKED: the rank-4 fork**, predicate grade, bridge-lifted. -/
theorem down_fork : forkState down3 := (forkStateSB_true_iff down3_wf).mp down3_forkSB

/-- The pair pins at the epoch's both ends: the rank-5 pair sits at
its rungs at `down0`, the rank-4 pair at `down3` — the walked pair
rank is four, one below the base's five. -/
theorem down_pins :
    rungAt down0 Suit.heart = H5.rank.toIdx ∧
      rungAt down0 Suit.diamond = H5.rank.toIdx ∧
        rungAt down3 Suit.heart = H4.rank.toIdx ∧
          rungAt down3 Suit.diamond = H4.rank.toIdx :=
  ⟨by rfl, by rfl, by rfl, by rfl⟩

/-- **THE DRESSED LEDGER**: exactly the pair lives — witness 4♥
vanilla-live; the covered 4♦ S-live but VANILLA-DEAD (the pin
restored by the dressing — compare `down2_pin`); the dressed 3♣
(dead by the club rank-lock at idx 2 ≠ 1); the old pair (5♥, 5♦)
dead at the dropped rungs; the stock residents dead. -/
theorem down3_ledger :
    canRaiseSB down3 H4 = true ∧ canRaiseSB down3 D4 = true ∧
      canRaiseB down3 D4 = false ∧
        canRaiseSB down3 C3 = false ∧
          canRaiseSB down3 H5 = false ∧ canRaiseSB down3 D5 = false ∧
            canRaiseSB down3 S4 = false ∧ canRaiseSB down3 C2 = false :=
  ⟨by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩

/-! ### The pulled-fit alternative, on record

Every PULLED cover self-pollutes: a pulled card is next-up at its own
landing BY CONSTRUCTION (its pull drops its rung to its index), so
dressing the 4♦ with the pulled 3♠ instead of the island's 3♣ puts
THREE live cards on the census — decided dead here, one edit away
from the island route the iteration lands. -/

/-- The alternative dressing: the foundation-top 3♠ pulled straight
onto the landed 4♦. -/
private def downAlt : State := stepD down2 (Move.foundToTab S3 (Sum.inr D4))

theorem downAlt_step :
    State.step down2 (Move.foundToTab S3 (Sum.inr D4)) = some downAlt := by rfl

/-- **THE PULLED-FIT SELF-POLLUTES**: at its landing the pulled 3♠
is next-up live (spades dropped 3 → 2 at idx 2) — the census sees
{3♠, 4♥, 4♦}, three live cards, no fork. -/
theorem downAlt_pollutes :
    forkStateSB downAlt = false ∧ canRaiseSB downAlt S3 = true :=
  ⟨by decide, by decide⟩

/-! ### The reversible dilation, and the one-way door

The two pulls are reversible (each one-move mirror is a licensed
re-found at the landing), so `down0` and `down2` are macro-class
mates through the two-leg witness shuffles — and the class's pulled
end is FORKLESS (`down2_forkSB`).  The final leg — the dressing
slide — is the door: a REVEALING slide over a nonempty hidden
island (the banked monotone-table jury `journey_tabToTab_never_reveal`),
whose one-move mirror is decide-dead anyway (the island's revealed
7♣ top is no red-4 seat for the run, and the emptied-anchor
recourse is king-only).  The rank-4 fork is REAL but sits behind
the commitment: the reversible class cannot reach it. -/

/-- The licensed mirror: the pulled 4♥ re-founds from its landed
top (the SProbe `cellRa_raised` equation, run backwards). -/
private theorem down1_mirror :
    State.step down1 (Move.tabToFound H4) = some down0 := by
  have hstep : State.step down1 (Move.tabToFound H4) =
      some (stepD down1 (Move.tabToFound H4)) := by rfl
  have hxEq : stepD down1 (Move.tabToFound H4) = down0 := by
    refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
    · cases σ <;> rfl
    · cases a <;> rfl
    · rfl
    · rfl
    · rfl
  rw [hstep, hxEq]

/-- The licensed mirror: the pulled 4♦ re-founds from its landed
top, back to the first-pull position. -/
private theorem down2_mirror :
    State.step down2 (Move.tabToFound D4) = some down1 := by
  have hstep : State.step down2 (Move.tabToFound D4) =
      some (stepD down2 (Move.tabToFound D4)) := by rfl
  have hxEq : stepD down2 (Move.tabToFound D4) = down1 := by
    refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
    · cases σ <;> rfl
    · cases a <;> rfl
    · rfl
    · rfl
    · rfl
  rw [hstep, hxEq]

/-- Each pull leg is reversible by its one-move mirror. -/
private theorem revPullA :
    reversibleAtW down0 (Move.foundToTab H4 (Sum.inr S5)) :=
  ⟨down1, [Move.tabToFound H4], down1_step, run_one down1_mirror⟩

private theorem revPullB :
    reversibleAtW down1 (Move.foundToTab D4 (Sum.inr C5)) :=
  ⟨down2, [Move.tabToFound D4], down2_step, run_one down2_mirror⟩

/-- Each re-found leg is reversible the other way, by its pull. -/
private theorem revFoundB :
    reversibleAtW down2 (Move.tabToFound D4) :=
  ⟨down1, [Move.foundToTab D4 (Sum.inr C5)], down2_mirror, run_one down2_step⟩

private theorem revFoundA :
    reversibleAtW down1 (Move.tabToFound H4) :=
  ⟨down0, [Move.foundToTab H4 (Sum.inr S5)], down1_mirror, run_one down1_step⟩

/-- The forward witness shuffle: `down0 → down2` through the pulls. -/
private theorem downFwd : ShufflePlayW down0
    [Move.foundToTab H4 (Sum.inr S5), Move.foundToTab D4 (Sum.inr C5)] down2 :=
  .cons revPullA down1_step (.cons revPullB down2_step (.nil down2))

/-- The backward witness shuffle: `down2 → down0` through the
licensed re-founds. -/
private theorem downBwd : ShufflePlayW down2 [Move.tabToFound D4, Move.tabToFound H4] down0 :=
  .cons revFoundB down2_mirror (.cons revFoundA down1_mirror (.nil down0))

/-- **THE REVERSIBLE DILATION IS CERTIFIED** — `down0` and `down2`
are macro-class mates through the fully-audited two-leg pull journey
(each leg's `reversibleAtW` witness rides a `rfl`-verified step
both ways). -/
theorem down_classPulls : sameOrbitSetoid.r down0 down2 :=
  ⟨[Move.tabToFound D4, Move.tabToFound H4], downBwd,
    [Move.foundToTab H4 (Sum.inr S5), Move.foundToTab D4 (Sum.inr C5)], downFwd⟩

/-- **THE DRESSING SLIDE IS A COMMITMENT** — theorem-grade: a
revealing slide (the whole run leaves the island, the hidden deck
loses a card for good — the banked monotone-table jury). -/
theorem down_slide_irr :
    ¬ reversibleAtW down2 (Move.tabToTab C3 (Sum.inr D4)) :=
  journey_tabToTab_never_reveal down3_step
    (show down2.pileHolding C3 = some Anchor.p1 from by rfl)
    (show below C3 (down2.piles Anchor.p1).faceUp = [] from by rfl)
    (show (down2.piles Anchor.p1).hidden ≠ [] from by decide)

/-- The island's post-slide shape: the reveal exposed 7♣ as the
island's top (the seat the mirror would need — and it is no red-4
for the returning run). -/
theorem down3_island :
    (down3.piles .p1).faceUp = [crd .club .seven] ∧
      (down3.piles .p4).faceUp = [D6, C5, D4, C3] :=
  ⟨rfl, rfl⟩

/-- **ONE-WAY DOOR, BOTH BARS DECIDED**: the 3♣'s complete landing
lattice at the dressed board — over the whole universe, its ONLY
landing is the witness's top 4♥ (the escape hop, which lands
ELSEWHERE); the island's revealed 7♣ refuses the run, the emptied
recourse would be king-only (and the island is not empty anyway),
and the found-route is dead by the rank-lock (not next-up).  The
mirror of the dressing slide is decide-dead at the landing. -/
theorem down_mirrorDead :
    (∀ z ∈ Card.universe, down3.canPlace C3 (Sum.inr z) = (decide (z = H4))) ∧
      down3.canPlace C3 (Sum.inr (crd .club .seven)) = false ∧
        down3.nextUp C3 = false := by
  refine ⟨?_, by decide, by decide⟩
  intro z _
  rcases z with ⟨s, r⟩
  cases s <;> cases r <;> decide

/-! ## §5. The connection ledger — the two forks, priced

The downward refutation attempt produced TWO genuine forks on ONE
dealt economy — rank 5 at the base (`down0`, witness 5♥), rank 4 at
the dressed board beyond the pulls (`down3`, witness 4♥) — and the
class accounting that prices them: the reversible dilation FROM the
base reaches only the FORKLESS `down2` (`down_classPulls`,
`down2_forkSB`), while the one leg separating the rank-4 fork from
that class is an audited COMMITMENT (`down_slide_irr`, the
decide-dead mirror beside it). -/

/-- **THE DOWN-PAIR LEDGER** — decide-grade: two forkStates of
different pair ranks on the same economy, the reversible class
between them ENDING FORKLESS, and the dressing leg a one-way door:
the no-lock pairClass theorem's downward counterexample FAILS to
be same-class at this grade — the theorem survives the probe. -/
theorem down_pair :
    forkState down0 ∧ forkState down3 ∧
      forkWitnessSB down0 = some H5 ∧ forkWitnessSB down3 = some H4 ∧
        H4.rank.toIdx + 1 = H5.rank.toIdx ∧
          forkStateSB down2 = false ∧
            sameOrbitSetoid.r down0 down2 ∧
              ¬ reversibleAtW down2 (Move.tabToTab C3 (Sum.inr D4)) :=
  ⟨down0_forkState, down_fork, down0_witness, down3_witness,
    by decide, down2_forkSB, down_classPulls, down_slide_irr⟩

/-- **THE CONNECTION VERDICT** (`down_class`): what the epoch's
same-class story earns — the pulls are reversible class legs, the
dressing is not; the rank-4 fork lives outside the certified class. -/
theorem down_class :
    sameOrbitSetoid.r down0 down2 ∧ ¬ reversibleAtW down2 (Move.tabToTab C3 (Sum.inr D4)) :=
  ⟨down_classPulls, down_slide_irr⟩

/-! ## §6. The census summary — one theorem per verdict, pure decides -/

theorem EpochProbe_up0 : forkStateSB up0 = true := up0_fork
theorem EpochProbe_up1 : forkStateSB up1 = false := up1_forkSB
theorem EpochProbe_up2 : forkStateSB up2 = false := up2_forkSB
theorem EpochProbe_up3 : forkStateSB up3 = false := up3_forkSB
theorem EpochProbe_downV0 : forkStateSB downV0 = true := downV0_fork
theorem EpochProbe_downV3 : forkStateSB downV3 = false := downV3_forkSB
theorem EpochProbe_down0 : forkStateSB down0 = true := down0_fork
theorem EpochProbe_down1 : forkStateSB down1 = false := down1_forkSB
theorem EpochProbe_down2 : forkStateSB down2 = false := down2_forkSB
theorem EpochProbe_down3 : forkStateSB down3 = true := down3_forkSB

/-- **THE TWO-CELL LEDGER**: the upward marathon stalls with every
license dead; the downward craft banks a rank-4 fork whose dressing
leg is a commitment — the no-lock pairClass theorem survives this
probe at decide grade. -/
theorem EpochProbe_verdicts :
    (∀ c ∈ Card.universe, canRaiseSB up3 c = false) ∧
      forkStateSB down3 = true ∧
        forkWitnessSB down3 = some H4 ∧
          forkWitnessSB down0 = some H5 ∧
            ¬ reversibleAtW down2 (Move.tabToTab C3 (Sum.inr D4)) :=
  ⟨up3_stalls, down3_forkSB, down3_witness, down0_witness, down_slide_irr⟩

/-! ### The audit battery

Fresh heads `#print axioms`-audited — every row lands in the
allowed grades: the decide rows at `[propext]` (the elaborated
decide instances), the table-jury irreversibility and the
bridge-lifted class rows at `[propext, Quot.sound]` — zero
`Classical.choice`, zero sorry. -/

#print axioms up0_fork
#print axioms up0_ledger
#print axioms up1_forkSB
#print axioms up2_forkSB
#print axioms up3_forkSB
#print axioms up3_stalls
#print axioms up_covered
#print axioms downV0_fork
#print axioms downV3_forkSB
#print axioms downV3_offender
#print axioms down0_fork
#print axioms down3_forkSB
#print axioms down3_witness
#print axioms down_fork
#print axioms down_pins
#print axioms down3_ledger
#print axioms downAlt_pollutes
#print axioms down_classPulls
#print axioms down_slide_irr
#print axioms down_mirrorDead
#print axioms down_pair
#print axioms down_class
#print axioms EpochProbe_verdicts
