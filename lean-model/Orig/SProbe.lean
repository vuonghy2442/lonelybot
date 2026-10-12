import Orig.ForkStateSB
import Orig.ConjugateProof

/-!
# Orig.SProbe — the strong forkState census, decide-grade

The evidence base for the confinement/conjugate/ladder conjectures:
crafted boards, every row a `decide`-verified fact under a `theorem`
wrapper, zero sorry, zero proof machinery beyond deciding.  The
instrument is `forkStateSB` (with `forkStateSB_true_iff`) and the
§7 computable `conjugateForkStateS`.
-/

/-! ## §1. The S-craft — the G2 skeleton repaired to strong grade -/

private def crd (s : Suit) (r : Rank) : Card := ⟨s, r⟩

/-- The fork pair {5♥, 5♦}: the vanilla-live witness 5♥, the covered twin. -/
private def H5 : Card := crd .heart .five
private def D5 : Card := crd .diamond .five
/-- The witness's p0 fuselage and the sealed channel's principals. -/
private def H7 : Card := crd .heart .seven
private def S6 : Card := crd .spade .six
private def C6 : Card := crd .club .six
private def C4 : Card := crd .club .four
/-- The dead phase pair. -/
private def C7 : Card := crd .club .seven
private def JD : Card := crd .diamond .jack

/-- The crafted rungs: ♠ 5, ♥ 4, ♦ 4, ♣ 2 (at clubs 2 the 4♣ cover is
unfounded-not-next-up — the seat repair's cover is itself saturated). -/
private def hmap : Suit → Nat
  | .heart => 4 | .diamond => 4 | .spade => 5 | .club => 2

/-- **THE S-CRAFT `cell`**: p0 = [7♥, 6♠, 5♥] (the witness topping its
own blocking cargo, the black next-up 6♠ buried directly beneath it);
p2 = [6♣, 5♦, 4♣] (the twin REPAIRED: seated on the buried 6♣ — so
pair-live AND the 6♠→6♣ free channel sealed — covered by the fitting
unfounded-not-next-up cargo 4♣); p1/p3/p4/p5 hidden-only sinks; p6
empty; stock [7♣], waste [J♦], drawStep 1. -/
private def cell : State where
  found := fun s => s.upCards.take (hmap s)
  piles := fun a => match a with
    | .p0 => ⟨[], [H7, S6, H5]⟩
    | .p2 => ⟨[], [C6, D5, C4]⟩
    | .p1 => ⟨[crd .club .three, crd .club .five, crd .club .eight,
               crd .club .nine, crd .club .ten, crd .club .jack,
               crd .club .queen, crd .club .king], []⟩
    | .p3 => ⟨[crd .spade .seven, crd .spade .eight, crd .spade .nine,
               crd .spade .ten, crd .spade .jack, crd .spade .queen,
               crd .spade .king], []⟩
    | .p4 => ⟨[crd .heart .six, crd .heart .eight, crd .heart .nine,
               crd .heart .ten, crd .heart .jack, crd .heart .queen,
               crd .heart .king], []⟩
    | .p5 => ⟨[crd .diamond .six, crd .diamond .seven, crd .diamond .eight,
               crd .diamond .nine, crd .diamond .ten, crd .diamond .queen,
               crd .diamond .king], []⟩
    | .p6 => ⟨[], []⟩
  stock := [C7]
  waste := [JD]
  drawStep := 1

/-- The craft reads exactly as dealt: witness top, cargo cover, buried 6♣. -/
private theorem cell_wf_found : ∀ s : Suit, ∃ n, cell.found s = s.upCards.take n := by
  intro s
  cases s with
  | spade => exact ⟨5, rfl⟩
  | heart => exact ⟨4, rfl⟩
  | diamond => exact ⟨4, rfl⟩
  | club => exact ⟨2, rfl⟩

private theorem cell_wf_runs : ∀ a : Anchor, runOK (cell.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

private theorem cell_wf_count : ∀ c ∈ Card.universe, cell.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

/-- The craft is `WF` (all four clauses, kernel-decided). -/
private theorem cell_wf : cell.WF :=
  ⟨cell_wf_found, cell_wf_runs, cell_wf_count, by decide⟩

/-- **THE S-CRAFT IS A STRONG FORKSTATE** — the decidable census folds a
witness row (the certified decide row). -/
theorem cell_fork : forkStateSB cell = true := by decide

/-- The iff-certificate: the decide row, lifted to the predicate. -/
theorem cell_forkState : forkState cell := (forkStateSB_true_iff cell_wf).mp cell_fork

/-- The SB witness search names the vanilla-live witness 5♥ (rfl-fold of
the certified search). -/
theorem cell_witness : forkWitnessSB cell = some H5 := by rfl

/-- The repair, clause by clause: the twin 5♦ over its 6♣ seat beneath
the 4♣ cargo. -/
theorem cell_fours_live : canRaiseSB cell H5 = true ∧ canRaiseSB cell D5 = true :=
  ⟨by decide, by decide⟩

/-- **THE G2 LEAK SEALED**: the exposed channel 6♠→6♣ is dead at the
S-license — the twin exit needs a topping 6♣, and 6♣ is buried under
the twin (the decide-verifiable leak orthogonality). -/
theorem cell_six_dead : canRaiseSB cell S6 = false := by decide

/-- The seal's seat: 6♣ sits under the twin, never a pile top. -/
theorem cell_buriedC6 : cell.pileOfTop C6 = none ∧ (cell.piles .p2).top = some C4 :=
  ⟨rfl, rfl⟩

/-! ## §2. The contrast — the OLD G2 cell, strong-fork FALSE

The G2 falsifier board verbatim (rungs ♠5/♥4/♦4/♣3, the bare-bottom
twin, 6♣ topping the landing host): weak-grade fork yet strong-grade
dead — the same shape the S-craft repairs, ten rows apart. -/

private def S7 : Card := crd .spade .seven
private def D7 : Card := crd .diamond .seven

/-- The old G2 rungs: ♠ 5, ♥ 4, ♦ 4, ♣ 3. -/
private def hmapV : Suit → Nat
  | .heart => 4 | .diamond => 4 | .spade => 5 | .club => 3

/-- THE OLD G2 `cellV`: witness 5♥ on [7♥, 6♠]; 6♣ TOPS p1 (the leak's
landing host live); the twin 5♦ BARE at p2 over empty hidden — the
seat bar kills its S-license. -/
private def cellV : State where
  found := fun s => s.upCards.take (hmapV s)
  piles := fun a => match a with
    | .p0 => ⟨[], [H7, S6, H5]⟩
    | .p1 => ⟨[], [D7, C6]⟩
    | .p2 => ⟨[], [D5]⟩
    | .p3 => ⟨[crd .club .king, crd .club .queen], []⟩
    | .p4 => ⟨[crd .heart .king, crd .heart .queen, crd .heart .jack,
               crd .heart .ten, crd .heart .nine, crd .heart .eight,
               crd .heart .six], []⟩
    | .p5 => ⟨[crd .diamond .king, crd .diamond .queen, crd .diamond .jack,
               crd .diamond .ten, crd .diamond .nine, crd .diamond .eight,
               crd .diamond .six], []⟩
    | .p6 => ⟨[crd .spade .king, crd .spade .queen, crd .spade .jack,
               crd .spade .ten, crd .spade .nine, crd .spade .eight,
               crd .club .five, crd .club .seven, crd .club .eight,
               crd .club .nine, crd .club .ten, crd .club .jack], []⟩
  stock := [S7, C4]
  waste := []
  drawStep := 1

private theorem cellV_wf_found : ∀ s : Suit, ∃ n, cellV.found s = s.upCards.take n := by
  intro s
  cases s with
  | spade => exact ⟨5, rfl⟩
  | heart => exact ⟨4, rfl⟩
  | diamond => exact ⟨4, rfl⟩
  | club => exact ⟨3, rfl⟩

private theorem cellV_wf_runs : ∀ a : Anchor, runOK (cellV.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

private theorem cellV_wf_count : ∀ c ∈ Card.universe, cellV.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

/-- The old G2 craft is `WF` (kernel-decided). -/
private theorem cellV_wf : cellV.WF :=
  ⟨cellV_wf_found, cellV_wf_runs, cellV_wf_count, by decide⟩

/-- **THE CONTRAST VERDICT**: the old G2 cell is strong-fork DEAD — the
decidable census rejects it (the two falsifier mechanisms below). -/
theorem cellV_forkSB : forkStateSB cellV = false := by decide

/-- The leak, on record: 6♠ is S-live at the old board — the free slide
`tabToTab 5♥ (inr 6♣)` channel's decidable certificate. -/
theorem cellV_leak_live : canRaiseSB cellV S6 = true := by decide

/-- The bare twin, on record: the old board's seat repair is absent —
5♦ is S-dead (bare-bottom non-king, no slide can ever seat it). -/
theorem cellV_twin_dead : canRaiseSB cellV D5 = false := by decide

/-- The old board WAS a weak forkState — the §7 computable weak check
decides true at it (weak✓/strong✗, the G2 residue in one row). -/
theorem cellV_weakfork : forkStateB cellV = true := by decide

theorem cellV_weakforkState : weakForkState cellV := (forkStateB_iff cellV).mp cellV_weakfork

/-! ## §3. The conjugate orbit — the computable §7 function on the S-craft

`conj1 := conjugateForkStateS cell` FIRES: raise the witness 5♥, slide
the twin's whole covered segment [5♦, 4♣] onto the exposed 6♠, pull
5♥ back onto the twin's exposed seat 6♣ — the twins trade physical
POSITIONS, the license stays with 5♥, and the second iterate returns
`cell` verbatim: the orbit is a genuine 2-CYCLE. -/

/-- First iterate of the computable conjugate. -/
def conj1 : State := conjugateForkStateS cell

/-- THE PHYSICAL SWAP, kernel-folded: the twin 5♦ now sits on 6♠ covered
by its cargo 4♣; the witness 5♥ now tops the twin's old seat 6♣. -/
theorem conj1_swap :
    (conj1.piles .p0).faceUp = [H7, S6, D5, C4] ∧
    (conj1.piles .p2).faceUp = [C6, H5] := ⟨rfl, rfl⟩

/-- The conjugate endpoint is a strong forkState (the decide census). -/
theorem conj1_fork : forkStateSB conj1 = true := by decide

/-- The SB witness names the same 5♥ at the swapped endpoint. -/
theorem conj1_witness : forkWitnessSB conj1 = some H5 := by rfl

/-- The tuple-invariance: the conjugate is net-flat — every rung
survives the round trip (per-suit kernel fold). -/
theorem conj1_rungs : ∀ σ : Suit, rungAt conj1 σ = rungAt cell σ := by
  intro σ
  cases σ <;> rfl

/-- The phase record survives the composite (all three legs write
foundations and piles only). -/
theorem conj1_phase :
    conj1.stock = cell.stock ∧ conj1.waste = cell.waste ∧
      conj1.drawStep = cell.drawStep := ⟨rfl, rfl, rfl⟩

/-- The iterate genuinely moved: its p0 differs from `cell`'s. -/
private theorem conj1_ne : conj1 ≠ cell := by
  intro h
  have hp0 : (cell.piles .p0).faceUp = [H7, S6, D5, C4] := by
    rw [← h]
    exact conj1_swap.1
  exact absurd hp0 (by decide)

/-- The §7 correctness certificate, decided down to its moved arm: the
iterate fulfills the corrected composite AND a (checked) weakForkState. -/
theorem conj1_correct :
    conjugateForkState cell conj1 ∧ weakForkState conj1 :=
  (conjugateForkStateS_correct cell).elim (fun h => absurd h conj1_ne) id

/-- Second iterate: back home. -/
def conj2 : State := conjugateForkStateS conj1

/-- **THE 2-CYCLE**: two applications return `cell` exactly — the
pointwise reads are one `rfl` each (the composite's write records
collapse at every concrete suit/anchor). -/
theorem conj2_cycle : conj2 = cell := by
  refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
  · cases σ <;> rfl
  · cases a <;> rfl
  · rfl
  · rfl
  · rfl

/-- The home stake is the same strong fork (the reuse rides the cycle). -/
theorem conj2_fork : forkStateSB conj2 = true := by
  rw [conj2_cycle]
  exact cell_fork

theorem conj2_witness : forkWitnessSB conj2 = some H5 := by
  rw [conj2_cycle]
  exact cell_witness

/-- Third iterate: returns to `conj1` — the period, on record. -/
def conj3 : State := conjugateForkStateS conj2

theorem conj3_returns : conj3 = conj1 := by
  show conjugateForkStateS conj2 = conj1
  rw [conj2_cycle]
  rfl

theorem conj3_fork : forkStateSB conj3 = true := by
  rw [conj3_returns]
  exact conj1_fork

/-- **THE ORBIT PATTERN**: the computable conjugation is a period-2
involution on the S-craft board — `conj2` is `cell`, `conj3` is
`conj1`. -/
theorem conj_orbit_pattern :
    conjugateForkStateS (conjugateForkStateS cell) = cell := conj2_cycle

/-! ### The S-mate by hand (the one-leg cousin)

`slideM`: the twin's cover 4♣ slides ONTO the witness's top — the twin
5♦ now tops its seat pile, the witness is covered directly by the
fitting cargo.  One reversible `tabToTab` each way; the detection
survives with the witness FLIPPED to 5♦. -/

/-- Oracle step helper (dead-hand plays are construction bugs; the
step theorems below throw). -/
private def stepD (st : State) (m : Move) : State :=
  match st.step m with
  | none => st
  | some s' => s'

private def slideM : State := stepD cell (Move.tabToTab C4 (Sum.inr H5))

/-- The one-leg mate fires: 4♣'s run slides onto the witness's top. -/
private theorem slideM_step :
    State.step cell (Move.tabToTab C4 (Sum.inr H5)) = some slideM := by rfl

/-- The mate undoes by its one-move mirror: 4♣ slides back onto the
exposed twin (now a top); the pointwise reads are `rfl`s. -/
private theorem slideM_undo :
    State.step slideM (Move.tabToTab C4 (Sum.inr D5)) = some cell := by
  have hstep : State.step slideM (Move.tabToTab C4 (Sum.inr D5)) =
      some (stepD slideM (Move.tabToTab C4 (Sum.inr D5))) := by rfl
  have hxEq : stepD slideM (Move.tabToTab C4 (Sum.inr D5)) = cell := by
    refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
    · cases σ <;> rfl
    · cases a <;> rfl
    · rfl
    · rfl
    · rfl
  rw [hstep, hxEq]

/-- The slid mate is a strong forkState (the decide census at the
one-leg endpoint). -/
theorem slideM_fork : forkStateSB slideM = true := by decide

/-- **THE WITNESS FLIP**: the census names the twin 5♦ at the mate. -/
theorem slideM_witness : forkWitnessSB slideM = some D5 := by rfl

/-- The flip's licence ledger: the twin now raises vanilla (over its
6♣ seat), the witness is vanilla-blocked (under the 4♣ cargo) yet
S-live through the free leg. -/
theorem slideM_ledger :
    canRaiseB slideM D5 = true ∧ canRaiseB slideM H5 = false ∧
      canRaiseSB slideM H5 = true := ⟨by decide, by decide, by decide⟩

/-! ## §4. The ladder cells — the cascade epochs

`cellRa`: the S-craft with ONE `tabToFound 5♥` applied — the witness
raised to its foundation, the parent 6♠ exposed.  The confinement
verdict, decided: NO immediate re-pinning — the exposed 6♠ is
vanilla-live but alone; the twin 5♦'s exit channel died WITH the
witness's departure (no topping 5♥ anywhere), and the {6♥, 6♦}
heirs are still buried.  `cellRa6`: the same raise plus ONE seat-ok
foreign 6♥ planted on its own 7♠ seat — still no fork: the two live
sixes are suit-strangers, and 6♦/6♣ stay dead. -/

private def H6 : Card := crd .heart .six
private def D6 : Card := crd .diamond .six

/-- The raised-witness rungs: ♠ 5, ♥ 5, ♦ 4, ♣ 2. -/
private def hmapRa : Suit → Nat
  | .heart => 5 | .diamond => 4 | .spade => 5 | .club => 2

/-- **THE RAISED CELL `cellRa`**: the S-craft after one `tabToFound 5♥`
— heart rung 5, p0 bare to [7♥, 6♠], everything else verbatim. -/
private def cellRa : State where
  found := fun s => s.upCards.take (hmapRa s)
  piles := fun a => match a with
    | .p0 => ⟨[], [H7, S6]⟩
    | .p2 => ⟨[], [C6, D5, C4]⟩
    | .p1 => ⟨[crd .club .three, crd .club .five, crd .club .eight,
               crd .club .nine, crd .club .ten, crd .club .jack,
               crd .club .queen, crd .club .king], []⟩
    | .p3 => ⟨[crd .spade .seven, crd .spade .eight, crd .spade .nine,
               crd .spade .ten, crd .spade .jack, crd .spade .queen,
               crd .spade .king], []⟩
    | .p4 => ⟨[crd .heart .six, crd .heart .eight, crd .heart .nine,
               crd .heart .ten, crd .heart .jack, crd .heart .queen,
               crd .heart .king], []⟩
    | .p5 => ⟨[crd .diamond .six, crd .diamond .seven, crd .diamond .eight,
               crd .diamond .nine, crd .diamond .ten, crd .diamond .queen,
               crd .diamond .king], []⟩
    | .p6 => ⟨[], []⟩
  stock := [C7]
  waste := [JD]
  drawStep := 1

/-- The craft IS the one-tabToFound image of `cell` (the pointwise
reads are `rfl`s). -/
private theorem cellRa_raised :
    State.step cell (Move.tabToFound H5) = some cellRa := by
  have hstep : State.step cell (Move.tabToFound H5) =
      some (stepD cell (Move.tabToFound H5)) := by rfl
  have hxEq : stepD cell (Move.tabToFound H5) = cellRa := by
    refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
    · cases σ <;> rfl
    · cases a <;> rfl
    · rfl
    · rfl
    · rfl
  rw [hstep, hxEq]

private theorem cellRa_wf_found : ∀ s : Suit, ∃ n, cellRa.found s = s.upCards.take n := by
  intro s
  cases s with
  | spade => exact ⟨5, rfl⟩
  | heart => exact ⟨5, rfl⟩
  | diamond => exact ⟨4, rfl⟩
  | club => exact ⟨2, rfl⟩

private theorem cellRa_wf_runs : ∀ a : Anchor, runOK (cellRa.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

private theorem cellRa_wf_count : ∀ c ∈ Card.universe, cellRa.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

private theorem cellRa_wf : cellRa.WF :=
  ⟨cellRa_wf_found, cellRa_wf_runs, cellRa_wf_count, by decide⟩

/-- **THE LADDER VERDICT (a): NO IMMEDIATE RE-PIN** — the raised cell
is strong-fork dead (the decide census). -/
theorem cellRa_forkSB : forkStateSB cellRa = false := by decide

/-- The raised rung and the bare parent, on record. -/
theorem cellRa_shape :
    rungAt cellRa Suit.heart = 5 ∧ (cellRa.piles .p0).faceUp = [H7, S6] :=
  ⟨rfl, rfl⟩

/-- The exposed parent is now vanilla-live — checked-next, alone. -/
theorem cellRa_parent_live : canRaiseSB cellRa S6 = true := by decide

/-- **THE CONFINEMENT**: the twin's exit channel died with the
witness's departure — no topping 5♥ anywhere (it sits founded), so
the pair's covered member is S-dead at the raised cell. -/
theorem cellRa_twin_dead : canRaiseSB cellRa D5 = false := by decide

/-- The {6♥, 6♦} heirs remain buried: 6♥ is hidden-only at p4. -/
theorem cellRa_heir_dead : canRaiseSB cellRa H6 = false := by decide

/-- **THE RAISED CELL `cellRa6`**: `cellRa` plus ONE seat-ok foreign 6♥
planted on its own 7♠ seat at p3 (7♠ surfacing from its hidden sink). -/
private def cellRa6 : State where
  found := fun s => s.upCards.take (hmapRa s)
  piles := fun a => match a with
    | .p0 => ⟨[], [H7, S6]⟩
    | .p2 => ⟨[], [C6, D5, C4]⟩
    | .p3 => ⟨[crd .spade .eight, crd .spade .nine,
               crd .spade .ten, crd .spade .jack, crd .spade .queen,
               crd .spade .king], [S7, H6]⟩
    | .p1 => ⟨[crd .club .three, crd .club .five, crd .club .eight,
               crd .club .nine, crd .club .ten, crd .club .jack,
               crd .club .queen, crd .club .king], []⟩
    | .p4 => ⟨[crd .heart .eight, crd .heart .nine,
               crd .heart .ten, crd .heart .jack, crd .heart .queen,
               crd .heart .king], []⟩
    | .p5 => ⟨[crd .diamond .six, crd .diamond .seven, crd .diamond .eight,
               crd .diamond .nine, crd .diamond .ten, crd .diamond .queen,
               crd .diamond .king], []⟩
    | .p6 => ⟨[], []⟩
  stock := [C7]
  waste := [JD]
  drawStep := 1

private theorem cellRa6_wf_found : ∀ s : Suit, ∃ n, cellRa6.found s = s.upCards.take n := by
  intro s
  cases s with
  | spade => exact ⟨5, rfl⟩
  | heart => exact ⟨5, rfl⟩
  | diamond => exact ⟨4, rfl⟩
  | club => exact ⟨2, rfl⟩

private theorem cellRa6_wf_runs : ∀ a : Anchor, runOK (cellRa6.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

private theorem cellRa6_wf_count : ∀ c ∈ Card.universe, cellRa6.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

private theorem cellRa6_wf : cellRa6.WF :=
  ⟨cellRa6_wf_found, cellRa6_wf_runs, cellRa6_wf_count, by decide⟩

/-- **THE LADDER VERDICT (b): no re-pin even with a live foreign 6♥** —
two sixes of STRANGER suits, nothing pairs; the decide census stays
dead. -/
theorem cellRa6_forkSB : forkStateSB cellRa6 = false := by decide

/-- The foreign 6♥ audit: seat-ok (over its 7♠), vanilla-live —
alongside the exposed 6♠. -/
theorem cellRa6_twoLive :
    canRaiseSB cellRa6 S6 = true ∧ canRaiseSB cellRa6 H6 = true :=
  ⟨by decide, by decide⟩

/-- The decisive deaths: the twins of both live sixes (6♦ hidden-sunk,
6♣ still seated-cargo under the pair's twin) are S-dead — the
{6♥, 6♦} family cannot pin while 6♦ is buried, the {6♠, 6♣} family
cannot pin while 6♣ stays under the twin. -/
theorem cellRa6_familiesDead :
    canRaiseSB cellRa6 D6 = false ∧ canRaiseSB cellRa6 C6 = false :=
  ⟨by decide, by decide⟩

/-! ## §5. The phase repro — the §5b falsifier geometry, decide-grade

The S-craft carries a two-card dead phase load (stock [7♣], waste
[J♦], drawStep 1); one draw rotates the phase while every license
input (foundations, piles) stands — and the STRONG census cannot see
the difference. -/

/-- The one-draw turn of the S-craft: stock emptied, the drawn 7♣
onto the waste top (the phase rotated; foundations and piles
untouched — the falsifier's own §5b shape). -/
private def cellTurn : State :=
  { cell with stock := [], waste := [C7, JD] }

private theorem cellTurn_wf_found : ∀ s : Suit, ∃ n, cellTurn.found s = s.upCards.take n := by
  intro s
  cases s with
  | spade => exact ⟨5, rfl⟩
  | heart => exact ⟨4, rfl⟩
  | diamond => exact ⟨4, rfl⟩
  | club => exact ⟨2, rfl⟩

private theorem cellTurn_wf_runs : ∀ a : Anchor, runOK (cellTurn.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

private theorem cellTurn_wf_count : ∀ c ∈ Card.universe, cellTurn.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

private theorem cellTurn_wf : cellTurn.WF :=
  ⟨cellTurn_wf_found, cellTurn_wf_runs, cellTurn_wf_count, by decide⟩

/-- The turn and its return are literal kernel reductions (the
recycle-deal cycle over the two-card phase load). -/
theorem phase_turn_fwd : State.step cell Move.draw = some cellTurn := by rfl
theorem phase_turn_bwd : State.step cellTurn Move.draw = some cell := by rfl

/-- Draws never write foundations or piles: the rung tuple is fixed
across the turn (per-suit kernel fold). -/
theorem phase_rungs : ∀ σ : Suit, rungAt cellTurn σ = rungAt cell σ := by
  intro σ
  cases σ <;> rfl

/-- The phase record genuinely moved: the turn's waste is not the
cell's. -/
theorem phase_moved : cellTurn.waste ≠ cell.waste := by decide

/-- **PHASE-BLINDNESS**: the strong census holds at the turned board
verbatim (the S-license reads only foundations and piles). -/
theorem cellTurn_forkSB : forkStateSB cellTurn = true := by decide

theorem cellTurn_forkState : forkState cellTurn :=
  (forkStateSB_true_iff cellTurn_wf).mp cellTurn_forkSB

/-! ## §6. The census summary — one theorem per board, pure decides -/

theorem SProbe_cell : forkStateSB cell = true := cell_fork
theorem SProbe_cellV : forkStateSB cellV = false := cellV_forkSB
theorem SProbe_conj1 : forkStateSB conj1 = true := conj1_fork
theorem SProbe_conj2 : forkStateSB conj2 = true := conj2_fork
theorem SProbe_conj3 : forkStateSB conj3 = true := conj3_fork
theorem SProbe_slideM : forkStateSB slideM = true := slideM_fork
theorem SProbe_cellRa : forkStateSB cellRa = false := cellRa_forkSB
theorem SProbe_cellRa6 : forkStateSB cellRa6 = false := cellRa6_forkSB
theorem SProbe_cellTurn : forkStateSB cellTurn = true := cellTurn_forkSB

/-- **THE ORBIT LEDGER**: the conjugation is a period-2 involution on
the S-craft, and the witness census names the orientation at each
strong board (the mate's flip included). -/
theorem SProbe_orbit :
    conjugateForkStateS (conjugateForkStateS cell) = cell ∧
      forkWitnessSB cell = some H5 ∧
      forkWitnessSB conj1 = some H5 ∧
      forkWitnessSB slideM = some D5 :=
  ⟨conj2_cycle, cell_witness, conj1_witness, slideM_witness⟩

/-! ### The audit battery

Fresh heads `#print axioms`-audited — expected `[]` (pure decides) or
`[Quot.sound]` (the ext-split step rows). -/

#print axioms cell_fork
#print axioms cell_forkState
#print axioms cell_witness
#print axioms cell_six_dead
#print axioms cellV_forkSB
#print axioms cellV_weakforkState
#print axioms conj1_fork
#print axioms conj1_correct
#print axioms conj2_cycle
#print axioms conj_orbit_pattern
#print axioms slideM_fork
#print axioms slideM_witness
#print axioms cellRa_forkSB
#print axioms cellRa_twin_dead
#print axioms cellRa6_forkSB
#print axioms cellTurn_forkSB
#print axioms SProbe_orbit
