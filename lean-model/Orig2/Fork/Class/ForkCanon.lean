import Orig2.Fork.CrossSuit.ForkCrossSuit
import Orig2.Fork.Class.ForkDecide
import Orig2.Fork.Local.ForkPullSwaps
import Orig2.Fork.Split.ForkBaseEnabling
import Orig2.Fork.Class.ForkReadBracket

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkCanon — the canonical (min-`inv`) geodesic

Scratch card.  READ-ONLY on `Orig2/`; no source edit, no commit.  Zero `sorry`,
zero `Classical.choice`, zero `native_decide`; axiom battery at the tail.

## The reframe this card tests

The campaign no longer needs
`MountainGate.MountainAtSplitsDiffering` (a **∀**-claim over geodesics: FALSE at
equal rungs, `Orig2/ForkEqualRungMain.lean`).  It needs
`MtnExists.MountainMinExists` (an **∃**-claim: *some* geodesic between saturated
endpoints carries the mountain shape).  So the question about cross-suit
raise-before-pull pairs is not "does every geodesic avoid it" but "is there a
*canonical* geodesic that avoids it".

This card supplies the canonical-selection machinery and the **exact exchange**
that any such canonical geodesic obeys.

## What is proved (all kernel-checked)

* **§1 the second cost `inv`.**  `inv ρ` counts the pairs `i < j` with
  `ρ[i] = raise c`, `ρ[j] = pull d b`, `c.suit ≠ d.suit` (the *cross-suit*
  inversion count; the same-suit variant is a different lane — it is the
  relocation count and it is *not* removable, `Temp/Pure_Report.md` §4).  The
  definition is a plain fold (`invAux`) with an accumulator of raised suits; no
  choice, no quotient, no `Finset`.
  The exact adjacent identity (`inv_swap_adjacent`): for `c.suit ≠ d.suit`,
  ```text
  inv (pre ++ [pull d b, raise c] ++ post) + 1
    = inv (pre ++ [raise c, pull d b] ++ post).
  ```
  So exchanging an adjacent cross-suit `raise ; pull` into `pull ; raise`
  *decreases `inv` by exactly one*, while (by `CommuteStep.step_comm_raise_pull`)
  the endpoint is unchanged.

* **§2 the canonical geodesic, choice-free.**  Over the finite set of plays of
  the shortest length there is one minimising `inv`
  (`exists_canonical_play`): the bounded scan of `Orig2/Fork/Class/ForkDecide.lean`
  (`allListsOfLen` / `playExistsLen` / `exists_first_le`) applied twice — once
  for the length, once for `inv`.  No `Nat.find`, no well-ordering, no EM.

* **§3 the adjacent exchange.**  In a canonical geodesic an adjacent cross-suit
  `raise c ; pull d b` is **never swappable**
  (`canonical_no_swap`): if both `pull d b` (at the raise's origin) and
  `raise c` (at the pull's image) are legal, `step_comm_raise_pull` produces a
  geodesic of the same length with `inv` one smaller, contradicting §1–§2.

* **§4 the exact obstruction.**  `canonical_blocked` pushes §3 into the two
  concrete alternatives
  ```text
  A.canPlace d b = false   ∨   b = Sum.inr c
  ```
  and `canonical_obstruction` resolves both geometrically: the pull's landing
  site is **the raise's own origin pile** —
  ```text
  b = Sum.inl a                              -- the raise emptied pile `a`
  ∨ b = Sum.inr c                            -- the pull lands on the raised card
  ∨ ∃ z, b = Sum.inr z ∧ A.pileOfTop z = none -- the raise exposed `z` from pile `a`
  ```
  (`A` is the raise's origin, `a` the anchor `c` tops there).  So the
  base-enabling / seat-collision obstruction is exactly "the pull's base is on
  the raise's origin pile", and nothing else survives.

* **§5 the free corridor.**  For the *free* corridor
  `raise c ; (free)* ; pull d b` the pull can be bubbled to adjacency when the
  interior is read-safe for `d` and seat-inert on `b`
  (`bubble_play_of_read`, from `PullKit.pull_moves_left_read`), and bubbling
  across free letters **preserves `inv`** (`inv_bubble`) — free letters are
  neither raises nor pulls.  Hence `canonical_free_corridor_blocked`: in a
  canonical geodesic every cross-suit free-corridor pair is a *blocked* pair of
  §4.  The inner-raise corridor (`raise c ; γ₁ ; raise d ; γ₂ ; pull d b`) is
  **not** reachable this way: the pull would have to cross the inner
  `raise d`, which changes the pulled column's foundation top, so no bubble
  exists — the honest split of `Temp/Pure_Report.md` §2 is confirmed, and the
  inner-raise branch stays open.

  The pull-bubble hypothesis is discharged for **draw-only** interiors
  (`bubble_play_of_read` + `readSafe_draw`, `seatInert_draw`), giving an
  unconditional instance (`canonical_free_corridor_blocked_draw`).

## What is NOT claimed

`inv ρ = 0` (cross-suit vacuity at the canonical geodesic) is **not** proved:
§4 leaves the blocked configurations, whose exclusion is exactly the
saturation content (`SSaturated u`, `SSaturated v`).  What this card changes is
that the residual is no longer "a ∀-statement about all geodesics"; it is the
single geometric configuration of §4 in *one* covering geodesic.
-/

namespace Canon

open ValleyElim
open CommuteStep


/-! ## §1. The second cost: cross-suit inversions -/

/-- Count the entries of `l` satisfying the Boolean `p`. -/
def cnt (p : Suit → Bool) : List Suit → Nat
  | [] => 0
  | s :: t => (if p s then 1 else 0) + cnt p t

theorem cnt_nil (p : Suit → Bool) : cnt p [] = 0 := rfl

theorem cnt_cons (p : Suit → Bool) (s : Suit) (t : List Suit) :
    cnt p (s :: t) = (if p s then 1 else 0) + cnt p t := rfl

theorem cnt_append (p : Suit → Bool) (l₁ l₂ : List Suit) :
    cnt p (l₁ ++ l₂) = cnt p l₁ + cnt p l₂ := by
  induction l₁ with
  | nil => rw [List.nil_append, cnt_nil, Nat.zero_add]
  | cons s t ih => rw [List.cons_append, cnt_cons, cnt_cons, ih]; omega

/-- Inserting a suit in the middle does not change a count. -/
theorem cnt_mid (p : Suit → Bool) (l : List Suit) (s : Suit) (rs : List Suit) :
    cnt p (l ++ s :: rs) = cnt p (s :: (l ++ rs)) := by
  rw [cnt_append, cnt_cons, cnt_cons, cnt_append]
  omega

/-- The suits of the raises of a play, in reverse order of occurrence. -/
def raisedSuits : List Move → List Suit
  | [] => []
  | Move.tabToFound c :: t => c.suit :: raisedSuits t
  | _ :: t => raisedSuits t

theorem raisedSuits_nil : raisedSuits [] = [] := rfl

theorem raisedSuits_raise (c : Card) (t : List Move) :
    raisedSuits (Move.tabToFound c :: t) = c.suit :: raisedSuits t := rfl

theorem raisedSuits_draw (t : List Move) :
    raisedSuits (Move.draw :: t) = raisedSuits t := rfl

theorem raisedSuits_slide (c : Card) (b : Base) (t : List Move) :
    raisedSuits (Move.tabToTab c b :: t) = raisedSuits t := rfl

theorem raisedSuits_wasteToFound (c : Card) (t : List Move) :
    raisedSuits (Move.wasteToFound c :: t) = raisedSuits t := rfl

theorem raisedSuits_wasteToTab (c : Card) (b : Base) (t : List Move) :
    raisedSuits (Move.wasteToTab c b :: t) = raisedSuits t := rfl

theorem raisedSuits_pull (c : Card) (b : Base) (t : List Move) :
    raisedSuits (Move.foundToTab c b :: t) = raisedSuits t := rfl

theorem raisedSuits_append (a b : List Move) :
    raisedSuits (a ++ b) = raisedSuits a ++ raisedSuits b := by
  induction a with
  | nil => rw [List.nil_append, raisedSuits_nil, List.nil_append]
  | cons m t ih =>
      cases m with
      | draw => rw [List.cons_append, raisedSuits_draw, raisedSuits_draw, ih]
      | tabToTab c bb =>
          rw [List.cons_append, raisedSuits_slide, raisedSuits_slide, ih]
      | wasteToFound c =>
          rw [List.cons_append, raisedSuits_wasteToFound, raisedSuits_wasteToFound, ih]
      | wasteToTab c bb =>
          rw [List.cons_append, raisedSuits_wasteToTab, raisedSuits_wasteToTab, ih]
      | tabToFound c =>
          rw [List.cons_append, raisedSuits_raise, raisedSuits_raise, ih]
          rfl
      | foundToTab d bb =>
          rw [List.cons_append, raisedSuits_pull, raisedSuits_pull, ih]

/-- `invAux ρ rs` — the cross-suit inversion count of `ρ`, given the suits
already raised before it in the ambient play. -/
def invAux (ρ : List Move) (rs : List Suit) : Nat :=
  match ρ with
  | [] => 0
  | m :: t =>
      match m with
      | Move.tabToFound c => invAux t (c.suit :: rs)
      | Move.foundToTab d _ => cnt (fun s => decide (s ≠ d.suit)) rs + invAux t rs
      | _ => invAux t rs

theorem invAux_nil (rs : List Suit) : invAux [] rs = 0 := rfl

theorem invAux_raise (c : Card) (t : List Move) (rs : List Suit) :
    invAux (Move.tabToFound c :: t) rs = invAux t (c.suit :: rs) := rfl

theorem invAux_pull (d : Card) (b : Base) (t : List Move) (rs : List Suit) :
    invAux (Move.foundToTab d b :: t) rs =
      cnt (fun s => decide (s ≠ d.suit)) rs + invAux t rs := rfl

theorem invAux_of_free {m : Move} (h : FreeMove m) (t : List Move) (rs : List Suit) :
    invAux (m :: t) rs = invAux t rs := by
  rcases h with rfl | ⟨c, b, rfl⟩ <;> rfl

theorem invAux_wasteToFound (c : Card) (t : List Move) (rs : List Suit) :
    invAux (Move.wasteToFound c :: t) rs = invAux t rs := rfl

theorem invAux_wasteToTab (c : Card) (b : Base) (t : List Move) (rs : List Suit) :
    invAux (Move.wasteToTab c b :: t) rs = invAux t rs := rfl

/-- **THE SECOND COST.**  The number of cross-suit raise-before-pull pairs. -/
def inv (ρ : List Move) : Nat := invAux ρ []

theorem inv_nil : inv [] = 0 := rfl

/-- `invAux` only reads the accumulator through `cnt`. -/
theorem invAux_cnt_congr (ρ : List Move) {rs rs' : List Suit}
    (h : ∀ p : Suit → Bool, cnt p rs = cnt p rs') : invAux ρ rs = invAux ρ rs' := by
  induction ρ generalizing rs rs' with
  | nil => rfl
  | cons m t ih =>
      cases m with
      | draw => exact ih h
      | tabToTab c b => exact ih h
      | wasteToFound c => exact ih h
      | wasteToTab c b => exact ih h
      | tabToFound c =>
          refine ih (fun p => ?_)
          rw [cnt_cons p c.suit rs, cnt_cons p c.suit rs', h p]
      | foundToTab d b =>
          rw [invAux_pull, invAux_pull, h, ih h]

/-- Splitting a play: the second half sees the raises of the first. -/
theorem invAux_append (a b : List Move) (rs : List Suit) :
    invAux (a ++ b) rs = invAux a rs + invAux b (raisedSuits a ++ rs) := by
  induction a generalizing rs with
  | nil => rw [List.nil_append, raisedSuits_nil, List.nil_append, invAux_nil,
      Nat.zero_add]
  | cons m t ih =>
      cases m with
      | draw =>
          rw [List.cons_append, invAux_of_free free_draw (t ++ b) rs,
            invAux_of_free free_draw t rs]
          exact ih rs
      | tabToTab c bb =>
          rw [List.cons_append, invAux_of_free (free_slide c bb) (t ++ b) rs,
            invAux_of_free (free_slide c bb) t rs]
          exact ih rs
      | wasteToFound c =>
          rw [List.cons_append, invAux_wasteToFound c (t ++ b) rs,
            invAux_wasteToFound c t rs]
          exact ih rs
      | wasteToTab c bb =>
          rw [List.cons_append, invAux_wasteToTab c bb (t ++ b) rs,
            invAux_wasteToTab c bb t rs]
          exact ih rs
      | tabToFound c =>
          rw [List.cons_append, invAux_raise, invAux_raise]
          show invAux (t ++ b) (c.suit :: rs)
              = invAux t (c.suit :: rs) + invAux b (c.suit :: (raisedSuits t ++ rs))
          rw [ih (c.suit :: rs)]
          rw [invAux_cnt_congr b (rs := raisedSuits t ++ c.suit :: rs)
            (rs' := c.suit :: (raisedSuits t ++ rs))
            (fun p => cnt_mid p (raisedSuits t) c.suit rs)]
      | foundToTab d bb =>
          rw [List.cons_append, invAux_pull, invAux_pull]
          show cnt (fun s => decide (s ≠ d.suit)) rs + invAux (t ++ b) rs
              = (cnt (fun s => decide (s ≠ d.suit)) rs + invAux t rs)
                + invAux b (raisedSuits t ++ rs)
          rw [ih rs]
          omega

/-- The inversion count splits across an append. -/
theorem inv_append (a b : List Move) :
    inv (a ++ b) = inv a + invAux b (raisedSuits a) := by
  rw [inv, invAux_append, inv]
  rw [List.append_nil]

/-- The two-letter computation at an arbitrary ambient prefix. -/
theorem inv_two (pre post : List Move) (x y : Move) :
    inv (pre ++ ([x, y] ++ post)) =
      inv pre + (invAux [x, y] (raisedSuits pre)
        + invAux post (raisedSuits [x, y] ++ raisedSuits pre)) := by
  rw [inv_append, invAux_append]

/-- Free letters do not change `inv` when a pull crosses them. -/
theorem inv_bubble {q : Move} (hq : FreeMove q) (pre : List Move) (d : Card) (b : Base)
    (post : List Move) :
    inv (pre ++ ([q, Move.foundToTab d b] ++ post)) =
      inv (pre ++ ([Move.foundToTab d b, q] ++ post)) := by
  rcases hq with rfl | ⟨x, bx, rfl⟩
  · have hrs : raisedSuits [Move.draw, Move.foundToTab d b]
        = raisedSuits [Move.foundToTab d b, Move.draw] := by
      rw [raisedSuits_draw, raisedSuits_pull, raisedSuits_pull, raisedSuits_draw]
    rw [inv_two, inv_two, hrs]
    rw [invAux_of_free free_draw [Move.foundToTab d b] (raisedSuits pre),
      invAux_pull d b [] (raisedSuits pre), invAux_nil,
      invAux_pull d b [Move.draw] (raisedSuits pre),
      invAux_of_free free_draw [] (raisedSuits pre), invAux_nil]
  · have hrs : raisedSuits [Move.tabToTab x bx, Move.foundToTab d b]
        = raisedSuits [Move.foundToTab d b, Move.tabToTab x bx] := by
      rw [raisedSuits_slide, raisedSuits_pull, raisedSuits_pull, raisedSuits_slide]
    rw [inv_two, inv_two, hrs]
    rw [invAux_of_free (free_slide x bx) [Move.foundToTab d b] (raisedSuits pre),
      invAux_pull d b [] (raisedSuits pre), invAux_nil,
      invAux_pull d b [Move.tabToTab x bx] (raisedSuits pre),
      invAux_of_free (free_slide x bx) [] (raisedSuits pre), invAux_nil]

/-- The count increment of inserting the (cross-suit) raised suit. -/
theorem cnt_cons_suit_ne (rs : List Suit) (c d : Card) (hsu : c.suit ≠ d.suit) :
    cnt (fun s => decide (s ≠ d.suit)) (c.suit :: rs) =
      1 + cnt (fun s => decide (s ≠ d.suit)) rs := by
  rw [cnt_cons]
  rw [decide_eq_true hsu]
  rfl

/-- **THE ADJACENT IDENTITY.**  Swapping an adjacent cross-suit
`raise c ; pull d b` into `pull d b ; raise c` removes exactly one inversion. -/
theorem inv_swap_adjacent (pre post : List Move) (c d : Card) (b : Base)
    (hsu : c.suit ≠ d.suit) :
    inv (pre ++ ([Move.foundToTab d b, Move.tabToFound c] ++ post)) + 1 =
      inv (pre ++ ([Move.tabToFound c, Move.foundToTab d b] ++ post)) := by
  have hrs : raisedSuits [Move.tabToFound c, Move.foundToTab d b]
      = raisedSuits [Move.foundToTab d b, Move.tabToFound c] := rfl
  rw [inv_two, inv_two, hrs]
  rw [invAux_pull d b [Move.tabToFound c] (raisedSuits pre),
    invAux_raise c [] (raisedSuits pre), invAux_nil,
    invAux_raise c [Move.foundToTab d b] (raisedSuits pre),
    invAux_pull d b [] (c.suit :: raisedSuits pre), invAux_nil,
    cnt_cons_suit_ne (raisedSuits pre) c d hsu]
  omega


/-! ## §2. The canonical geodesic, choice-free -/

/-- "There is a play of length `n` with `inv ≤ K`", decided by brute force over
the symbolic alphabet (never evaluated: `allListsOfLen` is exponential). -/
def invBounded (u v : State) (n K : Nat) : Bool :=
  (DecideKit.allListsOfLen n DecideKit.allMoves).any
    (fun ρ => DecideKit.isPlay u v ρ && decide (inv ρ ≤ K))

theorem invBounded_iff {u v : State} (huwf : u.WF) (n K : Nat) :
    invBounded u v n K = true ↔
      ∃ ρ : List Move, ρ.length = n ∧ ShufflePlayW u ρ v ∧ inv ρ ≤ K := by
  rw [invBounded, List.any_eq_true]
  constructor
  · rintro ⟨ρ, hmem, his⟩
    rw [Bool.and_eq_true] at his
    obtain ⟨hp, hi⟩ := his
    obtain ⟨hlen, -⟩ := (DecideKit.mem_allListsOfLen n DecideKit.allMoves ρ).mp hmem
    exact ⟨ρ, hlen, (DecideKit.isPlay_iff huwf ρ).mp hp, of_decide_eq_true hi⟩
  · rintro ⟨ρ, hlen, hplay, hinv⟩
    refine ⟨ρ, (DecideKit.mem_allListsOfLen n DecideKit.allMoves ρ).mpr
      ⟨hlen, fun m _ => DecideKit.mem_allMoves m⟩, ?_⟩
    rw [Bool.and_eq_true]
    exact ⟨(DecideKit.isPlay_iff huwf ρ).mpr hplay, decide_eq_true hinv⟩

/-- **THE CANONICAL GEODESIC.**  Between same-orbit `WF` states there is a
shortest play whose `inv` is minimal among all shortest plays.  Constructed by
the bounded scan of `DecideKit.exists_first_le` twice (length, then `inv`):
no `Nat.find`, no EM, no choice. -/
theorem exists_canonical_play (u v : State) (huwf : u.WF)
    (hcls : sameOrbitSetoid.r u v) :
    ∃ ρ : List Move, ShufflePlayW u ρ v ∧
      (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) ∧
      (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ'.length = ρ.length →
        inv ρ ≤ inv ρ') := by
  obtain ⟨ρ₀, hρ₀play, hρ₀min⟩ :=
    DecideKit.shortestPlayExists_ungated_choiceFree u v huwf hcls
  have hB : invBounded u v ρ₀.length (inv ρ₀) = true :=
    (invBounded_iff huwf ρ₀.length (inv ρ₀)).mpr ⟨ρ₀, rfl, hρ₀play, Nat.le_refl _⟩
  obtain ⟨K, -, hK, hKmin⟩ :=
    DecideKit.exists_first_le (fun K => invBounded u v ρ₀.length K) (inv ρ₀) hB
  obtain ⟨ρ, hlen, hplay, hinvK⟩ := (invBounded_iff huwf ρ₀.length K).mp hK
  refine ⟨ρ, hplay, ?_, ?_⟩
  · intro ρ' hρ'
    rw [hlen]
    exact hρ₀min ρ' hρ'
  · intro ρ' hρ' hlen'
    have htrue : invBounded u v ρ₀.length (inv ρ') = true :=
      (invBounded_iff huwf ρ₀.length (inv ρ')).mpr
        ⟨ρ', hlen'.trans hlen, hρ', Nat.le_refl _⟩
    have hle : K ≤ inv ρ' := by
      by_cases hcon : inv ρ' < K
      · have hfalse := hKmin (inv ρ') hcon
        rw [hfalse] at htrue
        exact absurd htrue (Bool.false_ne_true)
      · omega
    omega

/-! ## §3. The adjacent exchange -/

/-- The raised card is the raise origin's `d`-foundation top, transported across
the raise (different suits). -/
theorem foundTop_raise_other {A : State} {c d : Card} {a : Anchor}
    (hsu : c.suit ≠ d.suit) (h : (raiseSt A c a).foundTop d.suit = some d) :
    A.foundTop d.suit = some d := by
  unfold State.foundTop at h ⊢
  rw [raiseSt_found_apply, ite_eq_right (Ne.symm hsu)] at h
  exact h

/-- The pull leaves `nextUp c` alone when `c` is not the pulled suit. -/
theorem pullSt_nextUp_ne {st : State} {z : Card} {bz : Base} {c : Card}
    (hsu : c.suit ≠ z.suit) : (pullSt st z bz).nextUp c = st.nextUp c := by
  unfold State.nextUp State.foundHeight
  rw [CommuteStep.pullSt_found_apply, ite_eq_right hsu]

/-- **THE SWAP IS A WITNESS PLAY.**  If the pull is legal at the raise's origin
and the raise is reversible there, and the pull of the other suit is reversible
at its image, then the exchanged two-letter order is a witness play landing at
the same state. -/
theorem swap_raise_pull_witness {A B C : State} {c d : Card} {b : Base}
    (hAwf : A.WF)
    (hrevR : reversibleAtW A (Move.tabToFound c))
    (hstepR : State.step A (Move.tabToFound c) = some B)
    (hrevP : reversibleAtW B (Move.foundToTab d b))
    (hstepP : State.step B (Move.foundToTab d b) = some C)
    (hfoundA : A.foundTop d.suit = some d)
    (hcp : A.canPlace d b = true)
    (hsu : c.suit ≠ d.suit)
    (hbne : b ≠ Sum.inr c) :
    ShufflePlayW A [Move.foundToTab d b, Move.tabToFound c] C := by
  obtain ⟨hnextC, a, hpoC, hsB⟩ := step_tabToFound_inv hstepR
  have hpullA : PullKit.Pullable A d b := ⟨hfoundA, hcp⟩
  have hrevPA : reversibleAtW A (Move.foundToTab d b) :=
    PullKit.reversible_pull_of hAwf hpullA
  have hstepPA : State.step A (Move.foundToTab d b) = some (pullSt A d b) := by
    rw [step_foundToTab_splice hfoundA hcp]; rfl
  have hpileC : (pullSt A d b).pileOfTop c = some a := by
    rw [PullKit.pullSt_pileOfTop_of_ne (st := A) (z := d) (w := c) (bz := b)
      hAwf hfoundA hcp ?_ ?_]
    · exact hpoC
    · intro hcd
      exact hsu (congrArg Card.suit hcd)
    · intro w0 hw0 hcw
      exact hbne (by rw [hcw, hw0])
  have hnextP : (pullSt A d b).nextUp c = true := by
    rw [pullSt_nextUp_ne hsu]; exact hnextC
  have hstepPR : State.step (pullSt A d b) (Move.tabToFound c) =
      some (raiseSt (pullSt A d b) c a) := by
    rw [step_tabToFound_splice hnextP hpileC]; rfl
  have hsq : C = raiseSt (pullSt A d b) c a :=
    CommuteStep.step_comm_raise_pull hAwf hrevR hrevPA hstepR hstepPA hstepP hstepPR
  have hstepPR' : State.step (pullSt A d b) (Move.tabToFound c) = some C := by
    rw [hsq]; exact hstepPR
  have hrevPR : reversibleAtW (pullSt A d b) (Move.tabToFound c) :=
    PullKit.reversible_after_swap hstepR hstepPA hrevR hstepP hrevP hstepPR'
  exact Walk.cons hrevPA hstepPA (Walk.cons hrevPR hstepPR' (Walk.nil _))

/-- **NO SWAPPABLE ADJACENT CROSS-SUIT PAIR IN A CANONICAL PLAY.** -/
theorem canonical_no_swap {u v : State} {pre post : List Move} {c d : Card} {b : Base}
    {A : State}
    (huwf : u.WF) (hplay : ShufflePlayW u (pre ++ (Move.tabToFound c ::
      (Move.foundToTab d b :: post))) v)
    (hpre : ShufflePlayW u pre A)
    (hsu : c.suit ≠ d.suit)
    (hmin : ∀ ρ' : List Move,
      ShufflePlayW u ρ' v →
      ρ'.length = (pre ++ (Move.tabToFound c :: (Move.foundToTab d b :: post))).length →
      inv (pre ++ (Move.tabToFound c :: (Move.foundToTab d b :: post))) ≤ inv ρ')
    (hcp : A.canPlace d b = true) (hbne : b ≠ Sum.inr c) : False := by
  obtain ⟨A', hpre', hrest⟩ := ValleyElim.ShufflePlayW_split hplay pre
    (Move.tabToFound c :: (Move.foundToTab d b :: post)) rfl
  have hAA : A' = A := by
    have h1 := Walk_run (fun st m => reversibleAtW st m) hpre'
    have h2 := Walk_run (fun st m => reversibleAtW st m) hpre
    exact Option.some.inj (h1.symm.trans h2)
  rw [hAA] at hpre' hrest
  obtain ⟨B, hrevR, hstepR, hrest2⟩ := Bubble.walk_cons_inv hrest
  obtain ⟨C, hrevP, hstepP, hpost⟩ := Bubble.walk_cons_inv hrest2
  have hAwf : A.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  obtain ⟨hnextC, a, hpoA, hsB⟩ := step_tabToFound_inv hstepR
  have hfoundB : (raiseSt A c a).foundTop d.suit = some d := by
    obtain ⟨c', htop, hc', -, -⟩ := step_foundToTab_inv hstepP
    rw [hc'] at htop
    rw [hsB] at htop
    exact htop
  have hfoundA : A.foundTop d.suit = some d :=
    foundTop_raise_other hsu hfoundB
  have hswap : ShufflePlayW A [Move.foundToTab d b, Move.tabToFound c] C :=
    swap_raise_pull_witness hAwf hrevR hstepR hrevP hstepP hfoundA hcp hsu hbne
  have hplay' : ShufflePlayW u (pre ++ ([Move.foundToTab d b, Move.tabToFound c] ++ post)) v := by
    have h := ShufflePlayW_append hpre (ShufflePlayW_append hswap hpost)
    simpa only [List.cons_append, List.nil_append, List.append_assoc] using h
  have hid := inv_swap_adjacent pre post c d b hsu
  have hρeq : pre ++ ([Move.tabToFound c, Move.foundToTab d b] ++ post)
      = pre ++ (Move.tabToFound c :: (Move.foundToTab d b :: post)) := rfl
  rw [hρeq] at hid
  have hlen : (pre ++ ([Move.foundToTab d b, Move.tabToFound c] ++ post)).length
      = (pre ++ (Move.tabToFound c :: (Move.foundToTab d b :: post))).length := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hmono := hmin _ hplay' hlen
  omega

/-- **THE ADJACENT OBSTRUCTION.**  In a canonical play, an adjacent cross-suit
`raise c ; pull d b` is blocked: either the pull is not legal at the raise's
origin, or it lands on the raised card `c` itself. -/
theorem canonical_blocked {u v : State} {pre post : List Move} {c d : Card} {b : Base}
    {A : State}
    (huwf : u.WF) (hplay : ShufflePlayW u (pre ++ (Move.tabToFound c ::
      (Move.foundToTab d b :: post))) v)
    (hpre : ShufflePlayW u pre A)
    (hsu : c.suit ≠ d.suit)
    (hmin : ∀ ρ' : List Move,
      ShufflePlayW u ρ' v →
      ρ'.length = (pre ++ (Move.tabToFound c :: (Move.foundToTab d b :: post))).length →
      inv (pre ++ (Move.tabToFound c :: (Move.foundToTab d b :: post))) ≤ inv ρ') :
    A.canPlace d b = false ∨ b = Sum.inr c := by
  by_cases hcp : A.canPlace d b = true
  · by_cases hb : b = Sum.inr c
    · exact Or.inr hb
    · exact (canonical_no_swap huwf hplay hpre hsu hmin hcp hb).elim
  · left
    cases h : A.canPlace d b with
    | false => rfl
    | true => exact absurd h hcp

/-! ## §4. The exact geometry of the obstruction -/

/-- A founded card is no pile top, so `pileOfTop` misses it. -/
theorem pileOfTop_none_of_found {st : State} (hwf : st.WF) {c : Card}
    (htop : st.foundTop c.suit = some c) : st.pileOfTop c = none := by
  have hmem : c ∈ st.found c.suit := by
    unfold State.foundTop at htop
    exact lastOf_mem htop
  cases hpt : st.pileOfTop c with
  | none => rfl
  | some k =>
      exact absurd ((pileOfTop_eq_some_iff hwf).mp hpt)
        (CommuteStep.not_top_of_found hwf hmem k)

/-- The raise can only *empty* the pull's `inl` base by emptying its own pile. -/
theorem canPlace_inl_raise_true {A : State} {c d : Card} {a j : Anchor}
    (hno : A.canPlace d (Sum.inl j) = false)
    (hyes : (raiseSt A c a).canPlace d (Sum.inl j) = true) :
    j = a := by
  by_cases hne : j = a
  · exact hne
  · exfalso
    have hpiles : (raiseSt A c a).piles j = A.piles j := by
      rw [raiseSt_piles_apply, ite_eq_right hne]
    have hsame : (raiseSt A c a).canPlace d (Sum.inl j) = A.canPlace d (Sum.inl j) := by
      rw [canPlace_inl_unfold, canPlace_inl_unfold, hpiles]
    rw [hsame, hno] at hyes
    exact absurd hyes (by simp)

/-- **THE BASE-ENABLING DICHOTOMY.**  If the `inr` base is unavailable at `A`
and available at the raise's image, then it is the raised card itself or a card
the raise exposed (buried at `A`). -/
theorem canPlace_inr_raise_true {A : State} {c d z : Card} {a : Anchor}
    (hno : A.canPlace d (Sum.inr z) = false)
    (hyes : (raiseSt A c a).canPlace d (Sum.inr z) = true) :
    z = c ∨ A.pileOfTop z = none := by
  by_cases hzc : z = c
  · exact Or.inl hzc
  · exact Or.inr (BaseEn.inr_enable_needs_expose (A := A) (C := raiseSt A c a)
      hno hyes).2.1

/-- **THE EXACT OBSTRUCTION.**  In a canonical play an adjacent cross-suit
`raise c ; pull d b` (`c` topping pile `a` at the raise's origin `A`) has its
pull's landing site on the raise's own origin pile:

* `b = inl a` — the raise emptied pile `a`;
* `b = inr c` — the pull lands on the raised card;
* `b = inr z` with `z` buried at `A` — the raise exposed `z` from pile `a`. -/
theorem canonical_obstruction {u v : State} {pre post : List Move} {c d : Card}
    {b : Base} {A : State} {a : Anchor}
    (huwf : u.WF) (hplay : ShufflePlayW u (pre ++ (Move.tabToFound c ::
      (Move.foundToTab d b :: post))) v)
    (hpre : ShufflePlayW u pre A)
    (hsu : c.suit ≠ d.suit)
    (hmin : ∀ ρ' : List Move,
      ShufflePlayW u ρ' v →
      ρ'.length = (pre ++ (Move.tabToFound c :: (Move.foundToTab d b :: post))).length →
      inv (pre ++ (Move.tabToFound c :: (Move.foundToTab d b :: post))) ≤ inv ρ')
    (hpoA : A.pileOfTop c = some a)
    (hyes : (raiseSt A c a).canPlace d b = true) :
    b = Sum.inl a ∨ b = Sum.inr c ∨
      ∃ z : Card, b = Sum.inr z ∧ A.pileOfTop z = none := by
  -- the raise image is `WF`, and `c` is no pile top there
  obtain ⟨A', hpre', hrest⟩ := ValleyElim.ShufflePlayW_split hplay pre
    (Move.tabToFound c :: (Move.foundToTab d b :: post)) rfl
  have hAA : A' = A := by
    have h1 := Walk_run (fun st m => reversibleAtW st m) hpre'
    have h2 := Walk_run (fun st m => reversibleAtW st m) hpre
    exact Option.some.inj (h1.symm.trans h2)
  rw [hAA] at hpre' hrest
  obtain ⟨B, hrevR, hstepR, hrest2⟩ := Bubble.walk_cons_inv hrest
  have hAwf : A.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  obtain ⟨-, a', hpo', hsB0⟩ := step_tabToFound_inv hstepR
  have haa : a' = a := Option.some.inj (hpo'.symm.trans hpoA)
  have hsB : B = raiseSt A c a := by rw [← haa]; exact hsB0
  have hnoneImg : (raiseSt A c a).pileOfTop c = none := by
    have hBtop : B.foundTop c.suit = some c := by
      rw [hsB]; exact BaseEn.foundTop_raiseSt_self A c a
    have hBwf : B.WF := step_wf hAwf hstepR
    have hnoneB : B.pileOfTop c = none := pileOfTop_none_of_found hBwf hBtop
    rw [hsB] at hnoneB
    exact hnoneB
  have hno : A.canPlace d b = false := by
    rcases canonical_blocked huwf hplay hpre hsu hmin with h | hb
    · exact h
    · exfalso
      rw [hb] at hyes
      have hfalse : (raiseSt A c a).canPlace d (Sum.inr c) = false := by
        rw [canPlace_inr_eq, hnoneImg]
      rw [hfalse] at hyes
      exact absurd hyes (by simp)
  rcases hb : b with j | z
  · rw [hb] at hno hyes
    exact Or.inl (congrArg Sum.inl (canPlace_inl_raise_true hno hyes))
  · rw [hb] at hno hyes
    by_cases hzc : z = c
    · exact Or.inr (Or.inl (congrArg Sum.inr hzc))
    · exact Or.inr (Or.inr ⟨z, rfl,
        (canPlace_inr_raise_true hno hyes).resolve_left hzc⟩)

/-! ## §5. The free corridor

A free corridor is `raise c ; (draw | slide)* ; pull d b`.  The pull can be
bubbled left across such a corridor whenever the interior is read-safe for `d`
and seat-inert on `b` (`PullKit.pull_moves_left_read`), and the bubble preserves
`inv` because free letters are neither raises nor pulls. -/

/-- `FreeOnly γ` — every letter of the corridor is free (`draw` or a slide).
(This is `CrossSuit.FreeOnly` of `Temp/Pure_Corridor.lean`, restated locally so
this card imports no `Temp` module.) -/
def FreeOnly (γ : List Move) : Prop := ∀ m ∈ γ, FreeMove m

/-- Moving a pull left across a free window preserves `invAux`. -/
theorem invAux_pull_moves_left {γ : List Move} (hfree : FreeOnly γ) (rs : List Suit)
    (d : Card) (b : Base) (tail : List Move) :
    invAux (γ ++ (Move.foundToTab d b :: tail)) rs =
      invAux (Move.foundToTab d b :: (γ ++ tail)) rs := by
  induction γ generalizing rs with
  | nil => rfl
  | cons q γ' ih =>
      have hq : FreeMove q := hfree q (List.mem_cons_self ..)
      have hfree' : FreeOnly γ' := fun m hm => hfree m (List.mem_cons_of_mem q hm)
      calc invAux (q :: (γ' ++ (Move.foundToTab d b :: tail))) rs
          = invAux (γ' ++ (Move.foundToTab d b :: tail)) rs := invAux_of_free hq _ _
        _ = invAux (Move.foundToTab d b :: (γ' ++ tail)) rs := ih hfree' rs
        _ = cnt (fun s => decide (s ≠ d.suit)) rs + invAux (γ' ++ tail) rs :=
              invAux_pull d b (γ' ++ tail) rs
        _ = cnt (fun s => decide (s ≠ d.suit)) rs + invAux (q :: (γ' ++ tail)) rs := by
              rw [invAux_of_free hq]
        _ = invAux (Move.foundToTab d b :: (q :: (γ' ++ tail))) rs :=
              (invAux_pull d b (q :: (γ' ++ tail)) rs).symm

/-- Moving a pull left across a free window preserves `inv`. -/
theorem inv_pull_moves_left {γ : List Move} (hfree : FreeOnly γ) (pre : List Move)
    (d : Card) (b : Base) (tail : List Move) :
    inv (pre ++ (γ ++ (Move.foundToTab d b :: tail))) =
      inv (pre ++ (Move.foundToTab d b :: (γ ++ tail))) := by
  rw [inv_append, inv_append]
  exact congrArg (fun x => inv pre + x) (invAux_pull_moves_left hfree _ d b tail)

/-- **THE PULL BUBBLE ACROSS A FREE CORRIDOR.**  A witness play
`pre ++ raise c :: γ ++ pull d b :: tail` with `γ` read-safe for `d` and
seat-inert on `b`, and the pull legal at the raise's image, becomes the witness
play `pre ++ raise c :: pull d b :: γ ++ tail`. -/
theorem bubble_play_of_read
    {u v : State} {pre γ tail : List Move} {c d : Card} {b : Base} {A B : State}
    (huwf : u.WF)
    (hplay : ShufflePlayW u
      (pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail)))) v)
    (hpre : ShufflePlayW u pre A)
    (hstepR : State.step A (Move.tabToFound c) = some B)
    (hpullB : PullKit.Pullable B d b)
    (hread : ∀ q ∈ γ, SlideFwd.ReadSafe d q)
    (hseat : ∀ q ∈ γ, MtnPr.SeatInert b q) :
    ShufflePlayW u
      (pre ++ (Move.tabToFound c :: (Move.foundToTab d b :: (γ ++ tail)))) v := by
  -- split at the raise
  obtain ⟨A', hpre', hrest⟩ := ValleyElim.ShufflePlayW_split hplay pre
    (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail))) rfl
  have hAA : A' = A := by
    have h1 := Walk_run (fun st m => reversibleAtW st m) hpre'
    have h2 := Walk_run (fun st m => reversibleAtW st m) hpre
    exact Option.some.inj (h1.symm.trans h2)
  rw [hAA] at hrest hpre'
  obtain ⟨B', hrevR, hstepR', hrest2⟩ := Bubble.walk_cons_inv hrest
  have hBB : B' = B := Option.some.inj (hstepR'.symm.trans hstepR)
  rw [hBB] at hrest2
  have hAwf : A.WF := SatDifferCensus.ShufflePlayW.wf_end hpre' huwf
  have hBwf : B.WF := by
    have h := step_wf hAwf hstepR'
    rw [hBB] at h
    exact h
  -- the bubble
  have hbub : ShufflePlayW B (Move.foundToTab d b :: (γ ++ tail)) v :=
    PullKit.pull_moves_left_read hBwf hpullB hrest2 hread hseat
  have hstepR'' : State.step A (Move.tabToFound c) = some B := hstepR
  exact ShufflePlayW_append hpre (Walk.cons hrevR hstepR'' hbub)

/-- **THE FREE-CORRIDOR EXCHANGE.**  In a canonical play, a cross-suit free
corridor — the pull legal at the raise's image, the interior read-safe for `d`
and seat-inert on `b` — is a *blocked* pair in the sense of §4: the pull is
illegal at the raise's origin, or it lands on the raised card `c`. -/
theorem canonical_free_corridor_blocked
    {u v : State} {pre γ tail : List Move} {c d : Card} {b : Base} {A B : State}
    (huwf : u.WF)
    (hplay : ShufflePlayW u
      (pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail)))) v)
    (hpre : ShufflePlayW u pre A)
    (hstepR : State.step A (Move.tabToFound c) = some B)
    (hpullB : PullKit.Pullable B d b)
    (hfree : FreeOnly γ)
    (hread : ∀ q ∈ γ, SlideFwd.ReadSafe d q)
    (hseat : ∀ q ∈ γ, MtnPr.SeatInert b q)
    (hsu : c.suit ≠ d.suit)
    (hmin : ∀ ρ' : List Move,
      ShufflePlayW u ρ' v →
      ρ'.length = (pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail)))).length →
      inv (pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail)))) ≤ inv ρ') :
    A.canPlace d b = false ∨ b = Sum.inr c := by
  -- the bubbled play
  have hbubPlay : ShufflePlayW u
      (pre ++ (Move.tabToFound c :: (Move.foundToTab d b :: (γ ++ tail)))) v :=
    bubble_play_of_read huwf hplay hpre hstepR hpullB hread hseat
  -- the bubble preserves `inv`
  have hinveq : inv (pre ++ (Move.tabToFound c :: (Move.foundToTab d b :: (γ ++ tail))))
      = inv (pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail)))) := by
    have h := inv_pull_moves_left hfree (pre ++ [Move.tabToFound c]) d b tail
    simpa only [List.cons_append, List.nil_append, List.append_assoc] using h.symm
  -- the bubble preserves length
  have hleneq : (pre ++ (Move.tabToFound c :: (Move.foundToTab d b :: (γ ++ tail)))).length
      = (pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail)))).length := by
    simp only [List.length_append, List.length_cons]
    omega
  -- minimality for the bubbled play
  have hmin' : ∀ ρ' : List Move,
      ShufflePlayW u ρ' v →
      ρ'.length = (pre ++ (Move.tabToFound c :: (Move.foundToTab d b :: (γ ++ tail)))).length →
      inv (pre ++ (Move.tabToFound c :: (Move.foundToTab d b :: (γ ++ tail)))) ≤ inv ρ' := by
    intro ρ' hρ' hlen'
    rw [hinveq]
    exact hmin ρ' hρ' (hlen'.trans hleneq)
  exact canonical_blocked huwf hbubPlay hpre hsu hmin'

/-- A draw is seat-inert. -/
theorem seatInert_draw (b : Base) : MtnPr.SeatInert b Move.draw := by
  cases b <;> exact trivial

/-- **THE DRAW-ONLY CORRIDOR IS UNCONDITIONAL.**  Free corridors whose interior
is entirely draws need no read-safety/seat-inertness hypothesis. -/
theorem canonical_free_corridor_blocked_draw
    {u v : State} {pre γ tail : List Move} {c d : Card} {b : Base} {A B : State}
    (huwf : u.WF)
    (hplay : ShufflePlayW u
      (pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail)))) v)
    (hpre : ShufflePlayW u pre A)
    (hstepR : State.step A (Move.tabToFound c) = some B)
    (hpullB : PullKit.Pullable B d b)
    (hdraw : ∀ q ∈ γ, q = Move.draw)
    (hsu : c.suit ≠ d.suit)
    (hmin : ∀ ρ' : List Move,
      ShufflePlayW u ρ' v →
      ρ'.length = (pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail)))).length →
      inv (pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail)))) ≤ inv ρ') :
    A.canPlace d b = false ∨ b = Sum.inr c := by
  refine canonical_free_corridor_blocked huwf hplay hpre hstepR hpullB ?_ ?_ ?_ hsu hmin
  · intro q hq
    rw [hdraw q hq]
    exact free_draw
  · intro q hq
    rw [hdraw q hq]
    exact SlideFwd.readSafe_draw d
  · intro q hq
    rw [hdraw q hq]
    exact seatInert_draw b

/-- **THE ∃-FORM DELIVERABLE.**  At `WF`, `SSaturated`, same-orbit endpoints
there is a shortest play `ρ` minimizing `inv` among shortest plays, and *in that
play* every cross-suit free corridor is blocked exactly as in §4: the pull is
illegal at the raise's origin, or it lands on the raised card.  This is the
canonical-form statement the strategical reframe asks for. -/
theorem canonical_geodesic_obstruction (u v : State) (huwf : u.WF)
    (hu : SSaturated u) (hv : SSaturated v) (hcls : sameOrbitSetoid.r u v) :
    ∃ ρ : List Move, ShufflePlayW u ρ v ∧
      (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) ∧
      (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ'.length = ρ.length →
        inv ρ ≤ inv ρ') ∧
      ∀ (pre γ tail : List Move) (c d : Card) (b : Base) (A B : State),
        ρ = pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail))) →
        FreeOnly γ → c.suit ≠ d.suit →
        ShufflePlayW u pre A → State.step A (Move.tabToFound c) = some B →
        PullKit.Pullable B d b →
        (∀ q ∈ γ, SlideFwd.ReadSafe d q) →
        (∀ q ∈ γ, MtnPr.SeatInert b q) →
        (A.canPlace d b = false ∨ b = Sum.inr c) := by
  obtain ⟨ρ, hplay, hminlen, hinv⟩ := exists_canonical_play u v huwf hcls
  refine ⟨ρ, hplay, hminlen, hinv, ?_⟩
  intro pre γ tail c d b A B heq hfree hsu hpre hstepR hpullB hread hseat
  have hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v →
      ρ'.length = (pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail)))).length →
      inv (pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail)))) ≤ inv ρ' := by
    intro ρ' hρ' hlen'
    have hρlen : ρ'.length = ρ.length := hlen'.trans (congrArg List.length heq.symm)
    rw [← heq]
    exact hinv ρ' hρ' hρlen
  exact canonical_free_corridor_blocked huwf (heq ▸ hplay) hpre hstepR hpullB
    hfree hread hseat hsu hmin

/-! ## §5.2 The inner-raise corridor: why the same exchange cannot reach it

The second pure-corridor shape is `raise c ; γ₁ ; raise d ; γ₂ ; pull d b`
(`Temp/Pure_Report.md` §2).  To make the *cross-suit* pair `(raise c, pull d)`
adjacent one must bubble the pull left across the inner `raise d` — but no pull
of `d` is legal at the origin of a raise of `d`: there `d` is `nextUp`, hence
(`WF`) not a foundation top, hence not pullable.  So this branch is not reachable
by the free-corridor mechanism and stays a separate residual. -/

/-- At `WF`, a foundation top is not `nextUp` (`foundTop_rank_succ`). -/
theorem nextUp_false_of_foundTop {st : State} (hwf : st.WF) {d : Card}
    (h : st.foundTop d.suit = some d) : st.nextUp d = false := by
  have hsucc := SatDifferCensus.foundTop_rank_succ hwf h
  unfold State.nextUp State.foundHeight rungAt at *
  rw [decide_eq_false_iff_not]
  omega

/-- **THE PULL OF A NEXT-UP CARD IS ILLEGAL.**  In particular no pull of `d` is
legal at the origin of `raise d`; the pull bubble cannot cross an inner raise of
its own card. -/
theorem pull_self_illegal_of_nextUp {X : State} (hXwf : X.WF) {d : Card} {b : Base}
    (hnext : X.nextUp d = true) : State.step X (Move.foundToTab d b) = none := by
  cases h : State.step X (Move.foundToTab d b) with
  | none => rfl
  | some s' =>
      obtain ⟨c', htop, hc', -, -⟩ := step_foundToTab_inv h
      rw [hc'] at htop
      have hfalse : X.nextUp d = false := nextUp_false_of_foundTop hXwf htop
      rw [hnext] at hfalse
      exact absurd hfalse (by simp)

end Canon

/-! ## §6. Axiom battery

Expected: every row `[]`, `[propext]` or `[propext, Quot.sound]` — no
`sorryAx`, no `Classical.choice`, no `Lean.ofReduceBool` (`native_decide`),
no `Classical.em`. -/

#print axioms Canon.cnt_append
#print axioms Canon.cnt_mid
#print axioms Canon.raisedSuits_append
#print axioms Canon.invAux_cnt_congr
#print axioms Canon.invAux_append
#print axioms Canon.inv_append
#print axioms Canon.inv_two
#print axioms Canon.inv_bubble
#print axioms Canon.cnt_cons_suit_ne
#print axioms Canon.inv_swap_adjacent
#print axioms Canon.invBounded_iff
#print axioms Canon.exists_canonical_play
#print axioms Canon.foundTop_raise_other
#print axioms Canon.pullSt_nextUp_ne
#print axioms Canon.swap_raise_pull_witness
#print axioms Canon.canonical_no_swap
#print axioms Canon.canonical_blocked
#print axioms Canon.pileOfTop_none_of_found
#print axioms Canon.canPlace_inl_raise_true
#print axioms Canon.canPlace_inr_raise_true
#print axioms Canon.canonical_obstruction
#print axioms Canon.invAux_pull_moves_left
#print axioms Canon.inv_pull_moves_left
#print axioms Canon.bubble_play_of_read
#print axioms Canon.canonical_free_corridor_blocked
#print axioms Canon.canonical_free_corridor_blocked_draw
#print axioms Canon.canonical_geodesic_obstruction
#print axioms Canon.nextUp_false_of_foundTop
#print axioms Canon.pull_self_illegal_of_nextUp

#check @Canon.inv
#check @Canon.exists_canonical_play
#check @Canon.canonical_blocked
#check @Canon.canonical_obstruction
#check @Canon.canonical_free_corridor_blocked
#check @Canon.canonical_geodesic_obstruction

