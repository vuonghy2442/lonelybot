import Orig2.Fork.ForkCrossSuit
import Orig2.Fork.ForkCommuteSlide
import Orig2.Fork.ForkBlocks

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# CrossSuit_Partition — the corridor universe is FOUR faces, not one

READ-ONLY scratch card (`Temp/`).  No source edit, no commit.  Zero `sorry`,
zero `Classical.choice`, zero `native_decide`; battery at the tail.

## The audit that motivated this card

`Orig2/Fork/ForkBlocks.lean` stopped the cross-suit lane at
`Blocks.NoSeatMateCrossSuit` — "the exact surviving shape".  But that
residual (and the `∃`-form `canonical_no_crossSuit_corridor` beneath it)
quantifies only over corridors whose window is **nice**:

* `PullKit.Pullable B d b`  — the pull is already ready at the raise's
  landing `B`;
* `∀ q ∈ γ, SlideFwd.ReadSafe d q` — the window never touches `d`'s read;
* `∀ q ∈ γ, MtnPr.SeatInert b q` — the window never touches the seat.

These three are **hypotheses**, not derived facts.  A corridor of a
minimal saturated play that fails any one of them is simply not covered by
the seat-mate machinery: the swap descent cannot run (the pull is not
ready at `B`, or the pull cannot bubble through the window), so nothing
about it is constrained by the dichotomy.  The `¬Pullable` face is exactly
`SeatPreparedInWindow` of `Temp/CrossSuit_Canonical.lean`: the pull is
not ready at the raise's landing, so the seat is prepared *inside* the
free window.

## What this card proves

* §1 `pullable_of_step` — the pull's own firing *is* `Pullable` at its
  origin (from the step inversion).  So `¬Pullable B d b` means the
  window, not the firing, withheld the seat.
* §2 `foundTop_free_window` — a free window preserves **every** suit's
  foundation top.  So the `¬Pullable` failure cannot live in the
  foundation: `d` tops its column at `B` already.
* §3 `pullable_of_piles_eq` / `piles_ne_of_not_pullable` — `canPlace` is
  pile-determined (`CommuteStep.canPlace_congr_piles`), so with the
  foundation fixed, `¬Pullable B d b` while the pull fires later forces
  **the piles to change across the window**: the seat's availability is
  tableau data.
* §4 `piles_eq_of_draws` / `slide_or_piles_eq` — draws preserve the piles
  (`stepDraw_piles`), so a seat-changing free window **must contain a
  slide**: a draw-only window cannot prepare a seat.  The `¬Pullable`
  face is tableau work, not luck.
* §5 **THE ORACLES** — `readSafeB` / `seatInertB`, the Bool shadows of
  `SlideFwd.ReadSafe` / `MtnPr.SeatInert` with exact iff bridges.  These
  exist for the same reason the repo has `isFreeB` / `isPullB` /
  `isRaiseB`: case-splitting on the window properties without them pulls
  `Classical.choice` through `by_cases`'s fallback, and the axiom battery
  forbids it.
* §6 **THE PARTITION** — `canonical_no_crossSuit_corridor_complete`:
  the corridor universe of the canonical geodesic splits into exactly
  four named faces — `Blocks.NoSeatMateCrossSuit` (theirs: the pull
  ready, the window nice, the cards seat-mates) plus the three complement
  faces below.  With all four dead, the geodesic carries **no** cross-suit
  free corridor at all — with **no** window hypotheses.  The two lanes'
  union is thereby complete: every case of the cross-suit face has a name.

## The three complement faces (named, open)

* `NoWindowPreparedSeat` — no corridor with `¬ Pullable B d b`: the seat is
  never prepared inside the free window (the `SeatPreparedInWindow` face).
* `NoReadUnsafe` — no corridor whose window breaks read-safety for `d`.
* `NoSeatActing` — no corridor whose window breaks seat-inertness for `b`.

Each is exactly the shape of `Blocks.NoInlOrigin` with its own final
hypothesis, so all four residual vacuities compose into the un-hypothesised
statement.
-/

namespace CrossSuitPart

/-! ## §1. The firing is the certificate -/

/-- **THE PULL'S OWN FIRING IS `Pullable` AT ITS ORIGIN.**  From the step
inversion: the top-of-column and the base's acceptance both hold at the
state the pull fires from. -/
theorem pullable_of_step {P C : State} {d : Card} {b : Base}
    (h : State.step P (Move.foundToTab d b) = some C) :
    PullKit.Pullable P d b := by
  obtain ⟨d', htop, hd'd, hcp, -⟩ := step_foundToTab_inv h
  subst hd'd
  exact ⟨htop, hcp⟩

/-! ## §2. A free window fixes every foundation top -/

/-- Free letters avoid every suit (the `AvoidsSuit` catch-all). -/
theorem avoidsSuit_of_free {σ : Suit} {m : Move}
    (h : ValleyElim.FreeMove m) : CrossSuit.AvoidsSuit σ m := by
  rcases h with rfl | ⟨c, b, rfl⟩
  · trivial
  · trivial

/-- **A FREE WINDOW PRESERVES EVERY SUIT'S FOUNDATION TOP.**  Free letters
avoid every suit, so the column transport applies to all four columns:
the window cannot move a card on or off any foundation. -/
theorem foundTop_free_window {Q P : State} {γ : List Move} (σ : Suit)
    (hγ : ShufflePlayW Q γ P) (hfree : ∀ m ∈ γ, ValleyElim.FreeMove m) :
    Q.foundTop σ = P.foundTop σ :=
  (CrossSuit.foundTop_eq_of_avoids hγ
    (fun m hm => avoidsSuit_of_free (hfree m hm))).symm

/-! ## §3. The `¬Pullable` failure is tableau data -/

/-- **PULLABLE TRANSFERS ACROSS PILE-EQUAL STATES.**  `canPlace` is
pile-determined, so with the same piles and the same foundation tops the
pull's guard is unchanged. -/
theorem pullable_of_piles_eq {B P : State} {d : Card} {b : Base}
    (hp : PullKit.Pullable P d b) (htop : ∀ σ : Suit, B.foundTop σ = P.foundTop σ)
    (hpp : B.piles = P.piles) : PullKit.Pullable B d b :=
  ⟨(htop d.suit).trans hp.1, by
    rw [CommuteStep.canPlace_congr_piles hpp d b]; exact hp.2⟩

/-- **THE SEAT-DIFFERENCE.**  If the pull is not ready at the raise's
landing `B` but fires later from `P` through a window that fixed the
foundation tops, then **the piles differ across the window**: the seat's
availability is tableau data, and the window changed it. -/
theorem piles_ne_of_not_pullable {B P : State} {d : Card} {b : Base}
    (hnp : ¬ PullKit.Pullable B d b) (hp : PullKit.Pullable P d b)
    (htop : ∀ σ : Suit, B.foundTop σ = P.foundTop σ) : B.piles ≠ P.piles :=
  fun hpp => hnp (pullable_of_piles_eq hp htop hpp)

/-! ## §4. The seat needs a slide -/

/-- **DRAWS PRESERVE THE PILES.**  A window of only draws changes nothing
on the tableau. -/
theorem piles_eq_of_draws :
    ∀ (γ : List Move) {Q P : State},
      ShufflePlayW Q γ P → (∀ m ∈ γ, m = Move.draw) → Q.piles = P.piles := by
  intro γ
  induction γ with
  | nil => intro Q P hplay _; cases hplay; rfl
  | cons m t ih =>
      intro Q P hplay hall
      have hmd : m = Move.draw := hall m (List.mem_cons_self ..)
      subst hmd
      obtain ⟨S1, -, hstep, hrest⟩ := Bubble.walk_cons_inv hplay
      have h1 : Q.piles = S1.piles := (stepDraw_piles hstep).symm
      have h2 : S1.piles = P.piles :=
        ih hrest (fun x hx => hall x (List.mem_cons_of_mem _ hx))
      exact h1.trans h2

/-- **SLIDE OR PILES-EQUAL.**  A free window either contains a slide, or
it preserves the piles — constructively, with no case split on an
undecidable proposition. -/
theorem slide_or_piles_eq :
    ∀ (γ : List Move) {Q P : State},
      ShufflePlayW Q γ P → Canon.FreeOnly γ →
      (∃ (x : Card) (b' : Base), Move.tabToTab x b' ∈ γ) ∨ Q.piles = P.piles := by
  intro γ
  induction γ with
  | nil => intro Q P hplay _; cases hplay; exact Or.inr rfl
  | cons m t ih =>
      intro Q P hplay hfree
      obtain ⟨S1, -, hstep, hrest⟩ := Bubble.walk_cons_inv hplay
      rcases hfree m (List.mem_cons_self ..) with rfl | ⟨x, b', rfl⟩
      · have h1 : Q.piles = S1.piles := (stepDraw_piles hstep).symm
        rcases ih hrest (fun y hy => hfree y (List.mem_cons_of_mem _ hy)) with
          ⟨x', b', hmem⟩ | h
        · exact Or.inl ⟨x', b', List.mem_cons_of_mem _ hmem⟩
        · exact Or.inr (h1.trans h)
      · exact Or.inl ⟨x, b', List.mem_cons_self ..⟩

/-- **A SEAT-CHANGING FREE WINDOW CONTAINS A SLIDE.**  Draw-only windows
cannot prepare a seat; the `¬Pullable` face is tableau work. -/
theorem slide_of_seat_change {Q P : State} {γ : List Move}
    (hγ : ShufflePlayW Q γ P) (hfree : Canon.FreeOnly γ)
    (hchange : Q.piles ≠ P.piles) :
    ∃ (x : Card) (b' : Base), Move.tabToTab x b' ∈ γ := by
  rcases slide_or_piles_eq γ hγ hfree with h | h
  · exact h
  · exact absurd h hchange

/-! ## §5. The Bool oracles (the house pattern) -/

/-- The Bool shadow of `SlideFwd.ReadSafe`. -/
def readSafeB (z : Card) (q : Move) : Bool :=
  match q with
  | Move.draw => true
  | Move.wasteToFound _ => true
  | Move.wasteToTab _ _ => true
  | Move.tabToFound w => decide (w.suit ≠ z.suit)
  | Move.foundToTab c b => decide (c.suit ≠ z.suit) && decide (b ≠ Sum.inr z)
  | Move.tabToTab c b => decide (c ≠ z) && decide (b ≠ Sum.inr z)

theorem readSafeB_iff (z : Card) (q : Move) :
    readSafeB z q = true ↔ SlideFwd.ReadSafe z q := by
  cases q <;> simp [readSafeB, SlideFwd.ReadSafe]

/-- The Bool shadow of `MtnPr.SeatInert`. -/
def seatInertB (b : Base) (q : Move) : Bool :=
  match q, b with
  | Move.foundToTab _ b', _ => decide (b' ≠ b)
  | Move.wasteToTab _ b', _ => decide (b' ≠ b)
  | Move.tabToTab w b', Sum.inr z => decide (b' ≠ b) && decide (w ≠ z)
  | Move.tabToTab _ b', Sum.inl _ => decide (b' ≠ b)
  | Move.tabToFound w, Sum.inr z => decide (w ≠ z)
  | _, _ => true

theorem seatInertB_iff (b : Base) (q : Move) :
    seatInertB b q = true ↔ MtnPr.SeatInert b q := by
  cases q <;> cases b <;> simp [seatInertB, MtnPr.SeatInert]

theorem readSafeAll_of_bool {d : Card} {γ : List Move}
    (h : γ.all (readSafeB d) = true) : ∀ q ∈ γ, SlideFwd.ReadSafe d q :=
  fun q hq => (readSafeB_iff d q).mp (List.all_eq_true.mp h q hq)

theorem bool_of_readSafeAll {d : Card} {γ : List Move}
    (h : ∀ q ∈ γ, SlideFwd.ReadSafe d q) : γ.all (readSafeB d) = true :=
  List.all_eq_true.mpr (fun q hq => (readSafeB_iff d q).mpr (h q hq))

theorem seatInertAll_of_bool {b : Base} {γ : List Move}
    (h : γ.all (seatInertB b) = true) : ∀ q ∈ γ, MtnPr.SeatInert b q :=
  fun q hq => (seatInertB_iff b q).mp (List.all_eq_true.mp h q hq)

theorem bool_of_seatInertAll {b : Base} {γ : List Move}
    (h : ∀ q ∈ γ, MtnPr.SeatInert b q) : γ.all (seatInertB b) = true :=
  List.all_eq_true.mpr (fun q hq => (seatInertB_iff b q).mpr (h q hq))

/-! ## §6. The partition -/

/-- **COMPLEMENT FACE 1 — THE PREPARED-SEAT FACE.**  No corridor of a
minimal saturated play has `¬ Pullable B d b`: the seat is never prepared
inside the free window.  This is `SeatPreparedInWindow`
(`Temp/CrossSuit_Canonical.lean` §5) at the corridor shape. -/
def NoWindowPreparedSeat : Prop :=
  ∀ (u v : State) (ρ pre γ tail : List Move) (c d : Card) (b : Base) (A B : State),
    u.WF → SSaturated u → SSaturated v → ShufflePlayW u ρ v →
    (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) →
    (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ'.length = ρ.length →
      Canon.inv ρ ≤ Canon.inv ρ') →
    ρ = pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail))) →
    Canon.FreeOnly γ → c.suit ≠ d.suit → ShufflePlayW u pre A →
    State.step A (Move.tabToFound c) = some B →
    ¬ PullKit.Pullable B d b → False

/-- **COMPLEMENT FACE 2 — THE READ-UNSAFE FACE.**  No corridor whose free
window breaks read-safety for the pulled card. -/
def NoReadUnsafe : Prop :=
  ∀ (u v : State) (ρ pre γ tail : List Move) (c d : Card) (b : Base) (A B : State),
    u.WF → SSaturated u → SSaturated v → ShufflePlayW u ρ v →
    (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) →
    (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ'.length = ρ.length →
      Canon.inv ρ ≤ Canon.inv ρ') →
    ρ = pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail))) →
    Canon.FreeOnly γ → c.suit ≠ d.suit → ShufflePlayW u pre A →
    State.step A (Move.tabToFound c) = some B →
    PullKit.Pullable B d b →
    ¬ (∀ q ∈ γ, SlideFwd.ReadSafe d q) → False

/-- **COMPLEMENT FACE 3 — THE SEAT-ACTING FACE.**  No corridor whose free
window breaks seat-inertness for the pull's base. -/
def NoSeatActing : Prop :=
  ∀ (u v : State) (ρ pre γ tail : List Move) (c d : Card) (b : Base) (A B : State),
    u.WF → SSaturated u → SSaturated v → ShufflePlayW u ρ v →
    (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) →
    (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ'.length = ρ.length →
      Canon.inv ρ ≤ Canon.inv ρ') →
    ρ = pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail))) →
    Canon.FreeOnly γ → c.suit ≠ d.suit → ShufflePlayW u pre A →
    State.step A (Move.tabToFound c) = some B →
    PullKit.Pullable B d b →
    (∀ q ∈ γ, SlideFwd.ReadSafe d q) →
    ¬ (∀ q ∈ γ, MtnPr.SeatInert b q) → False

/-- **THE PARTITION — THE TWO LANES' UNION IS COMPLETE.**  With the
seat-mate face dead (`Blocks.NoSeatMateCrossSuit`, the parallel lane's
open residual) AND the three complement faces dead, the canonical geodesic
carries no cross-suit free corridor **at all** — with no window
hypotheses.  Every corridor of the geodesic lands in exactly one of the
four faces: the pull ready at `B` with a nice window (theirs), or one of
the three ways the window can fail to be nice (below).  This closes the
coverage gap the audit found: `Blocks.canonical_no_crossSuit_corridor`
alone does not finish the cross-suit case.

The case split is driven by **decidable data only** — the `canPlace` Bool,
the `foundTop` equation, and the two window oracles — so no
`Classical.choice` is pulled. -/
theorem canonical_no_crossSuit_corridor_complete
    (hseatmate : Blocks.NoSeatMateCrossSuit) (hprep : NoWindowPreparedSeat)
    (hread : NoReadUnsafe) (hact : NoSeatActing)
    (u v : State) (huwf : u.WF) (hu : SSaturated u) (hv : SSaturated v)
    (hcls : sameOrbitSetoid.r u v) :
    ∃ ρ : List Move, ShufflePlayW u ρ v ∧
      (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) ∧
      (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ'.length = ρ.length →
        Canon.inv ρ ≤ Canon.inv ρ') ∧
      ∀ (pre γ tail : List Move) (c d : Card) (b : Base) (A B : State),
        ρ = pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail))) →
        Canon.FreeOnly γ → c.suit ≠ d.suit →
        ShufflePlayW u pre A → State.step A (Move.tabToFound c) = some B → False := by
  obtain ⟨ρ, hplay, hminlen, hmininv, hprop⟩ :=
    Blocks.canonical_geodesic_seatMate u v huwf hu hv hcls
  refine ⟨ρ, hplay, hminlen, hmininv, ?_⟩
  intro pre γ tail c d b A B heq hfree hsu hpre hstepR
  by_cases hcp : B.canPlace d b = true
  · by_cases hft : B.foundTop d.suit = some d
    · have hpull : PullKit.Pullable B d b := ⟨hft, hcp⟩
      by_cases hrdB : γ.all (readSafeB d) = true
      · by_cases hstB : γ.all (seatInertB b) = true
        · have hrd : ∀ q ∈ γ, SlideFwd.ReadSafe d q := readSafeAll_of_bool hrdB
          have hst : ∀ q ∈ γ, MtnPr.SeatInert b q := seatInertAll_of_bool hstB
          obtain ⟨-, -, hsm⟩ := hprop pre γ tail c d b A B heq hfree hsu hpre
            hstepR hpull hrd hst
          exact hseatmate u v ρ pre γ tail c d b A B huwf hu hv hplay hminlen
            hmininv heq hfree hsu hpre hstepR hpull hrd hst hsm
        · have hrd : ∀ q ∈ γ, SlideFwd.ReadSafe d q := readSafeAll_of_bool hrdB
          have hns : ¬(∀ q ∈ γ, MtnPr.SeatInert b q) :=
            fun hall => hstB (bool_of_seatInertAll hall)
          exact hact u v ρ pre γ tail c d b A B huwf hu hv hplay hminlen hmininv
            heq hfree hsu hpre hstepR hpull hrd hns
      · have hnr : ¬(∀ q ∈ γ, SlideFwd.ReadSafe d q) :=
          fun hall => hrdB (bool_of_readSafeAll hall)
        exact hread u v ρ pre γ tail c d b A B huwf hu hv hplay hminlen hmininv
          heq hfree hsu hpre hstepR hpull hnr
    · exact hprep u v ρ pre γ tail c d b A B huwf hu hv hplay hminlen hmininv
        heq hfree hsu hpre hstepR (fun hp => absurd hp.1 hft)
  · exact hprep u v ρ pre γ tail c d b A B huwf hu hv hplay hminlen hmininv
      heq hfree hsu hpre hstepR (fun hp => absurd hp.2 hcp)

end CrossSuitPart

#print axioms CrossSuitPart.pullable_of_step
#print axioms CrossSuitPart.avoidsSuit_of_free
#print axioms CrossSuitPart.foundTop_free_window
#print axioms CrossSuitPart.pullable_of_piles_eq
#print axioms CrossSuitPart.piles_ne_of_not_pullable
#print axioms CrossSuitPart.piles_eq_of_draws
#print axioms CrossSuitPart.slide_or_piles_eq
#print axioms CrossSuitPart.slide_of_seat_change
#print axioms CrossSuitPart.readSafeB_iff
#print axioms CrossSuitPart.seatInertB_iff
#print axioms CrossSuitPart.readSafeAll_of_bool
#print axioms CrossSuitPart.bool_of_readSafeAll
#print axioms CrossSuitPart.seatInertAll_of_bool
#print axioms CrossSuitPart.bool_of_seatInertAll
#print axioms CrossSuitPart.canonical_no_crossSuit_corridor_complete
