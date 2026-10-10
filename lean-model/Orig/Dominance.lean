import Orig.Shuttle
import Orig.Phase
import Orig.Irreversible
import Orig.Classify
import Orig.Reach

/-!
# The original game — the to-foundation dominances

The physical port of method.md §5.1 (forced safe stacking) and §5.3
(draw-1 deck dominance).  The old engine's chapter is
`Klondike/Dominance.lean`; the correspondence is six moves on six:

| old (Klondike) | here (Orig) | remark |
|---|---|---|
| `draw` | `draw` | the physical deal recycles; no cursor |
| `deckStack` | `wasteToFound` | c pinned by `wasteIs` |
| `deckPile` | `wasteToTab` | |
| `pileStack` | `tabToFound` | the §5.1 subject |
| `stackPile` | `foundToTab` | the worry-back |
| `pilePile` | `tabToTab` | first-class runs here |

Two physical dividends change the shape of the statements:

* **no locked-guard** — the reveal is part of the moving move
  (`Pile.afterRunRemoved`), so the old dead-pile witness (a stacked
  card stranding its hidden boundary) is unstateable here;
* **the deal-adjacent residue is geometric** — the R/N split of the
  old §5.1 (returnable base vs the rest) reads here as: the raised
  card's below-run still sits (`tabToFound_undo_under`), the pile
  empties and the card is a king (`tabToFound_undo_bare`), or the
  *bare floor corner* — the below-run is empty and either the reveal
  seated a fresh card or the card is no king.  The first two are
  LANDED (Orig.Irreversible); the third is the file's one §5.1
  residue, the old [GAP] channel-A/B reshape in physical dress.

§5.3 follows the old chapter's layer split — (A) the
stock-as-reserve rotation, (B) the compliant replay, (C) the
rung-discipline normal form — each named below.  The assembly
plumbing is proven; the residues carry their routes.
-/

/-- Keller's safe-automove rung condition, physical form (the old
`safeToStack`, translated through `foundHeight`): a rank-`r` card of
colour `κ` is safe iff both `κ`-colored foundations are built to
`r−2` and both `κ̄`-colored to `r−1`. -/
def safeToFound (st : State) (c : Card) : Bool :=
  Suit.all.all fun σ =>
    if σ.color = c.suit.color
    then decide (c.rank.toIdx ≤ st.foundHeight σ + 2)
    else decide (c.rank.toIdx ≤ st.foundHeight σ + 1)

/-! ## The win transport -/

/-- A win behind a play that runs there: prepending the play lifts
the verdict — the play-level lift of `WinFrom_of_succ`. -/
theorem WinFrom_of_runTo {s s' : State} {play : List Move}
    (h : s.run play = some s') (hs : WinFrom s') : WinFrom s := by
  induction play generalizing s with
  | nil =>
      have heq : s = s' := Option.some.inj h
      rw [heq]
      exact hs
  | cons m rest ih =>
      obtain ⟨t, hstep, hrest⟩ := State.run_cons h
      exact WinFrom_of_succ ⟨m, hstep⟩ (ih hrest)

/-- The undo transport: a reversible witness play from the successor
back to the origin re-lifts the origin's win — the R-cases' common
tail. -/
theorem WinFrom_of_undo {st : State} {m : Move} {s₁ : State}
    (hstep : State.step st m = some s₁) (hw : reversibleAtW st m)
    (hsolv : WinFrom st) : WinFrom s₁ := by
  obtain ⟨s₂, play, hstep2, hback⟩ := hw
  rw [hstep2] at hstep
  have he : s₂ = s₁ := Option.some.inj hstep
  rw [he] at hback
  exact WinFrom_of_runTo hback hsolv

/-! ## Small local kit (dedup at harvest)

`runOK_snoc_sit` and `lastOf_exists` mirror Canonical's private
copies; they are re-proven here so this chapter imports nothing
unmerged.  Promote or delete against the canonical versions when
the chapters merge. -/

/-- A legal run sits each card on the one below: the premise of the
under-seat undo. -/
private theorem runOK_snoc_sit {c : Card} : ∀ {l : List Card}, l ≠ [] →
    runOK (l ++ [c]) = true → ∃ z, lastOf l = some z ∧ canSitOn c z = true := by
  intro l
  induction l with
  | nil => intro hne _; exact absurd rfl hne
  | cons x t ih =>
      intro _ h
      cases t with
      | nil =>
          refine ⟨x, rfl, ?_⟩
          have hexp : runOK (x :: ([] : List Card) ++ [c]) = (canSitOn c x && true) := rfl
          rw [hexp, Bool.and_true] at h
          exact h
      | cons y t' =>
          have hexp : runOK (x :: (y :: t') ++ [c]) =
              (canSitOn y x && runOK ((y :: t') ++ [c])) := rfl
          rw [hexp, Bool.and_eq_true] at h
          obtain ⟨z, hz, hsit⟩ := ih (by simp) h.2
          exact ⟨z, hz, hsit⟩

/-- A nonempty list has a last element. -/
private theorem lastOf_exists : ∀ {l : List Card}, l ≠ [] → ∃ z, lastOf l = some z := by
  intro l
  induction l with
  | nil => intro hne; exact absurd rfl hne
  | cons x t ih =>
      intro _
      cases t with
      | nil => exact ⟨x, rfl⟩
      | cons y t' =>
          obtain ⟨z, hz⟩ := ih (by simp)
          have hll : lastOf (x :: y :: t') = lastOf (y :: t') := rfl
          exact ⟨z, by rw [hll]; exact hz⟩

/-- The chop keeps every card it does not drop. -/
private theorem mem_of_chop : ∀ {l : List Card} {x : Card}, x ∈ chop l → x ∈ l := by
  intro l
  induction l with
  | nil => intro x h; cases h
  | cons y t ih =>
      intro x h
      cases t with
      | nil => cases h
      | cons w t' =>
          show x ∈ y :: w :: t'
          rcases List.mem_cons.1 h with rfl | hrest
          · exact List.mem_cons.2 (Or.inl rfl)
          · exact List.mem_cons.2 (Or.inr (ih hrest))

/-! ## The tabToFound firing shape -/

private theorem tabToFound_fires {st : State} {c : Card} {s₁ : State}
    (hstep : State.step st (Move.tabToFound c) = some s₁) :
    st.nextUp c = true ∧ ∃ a, st.pileOfTop c = some a := by
  by_cases hn : st.nextUp c = true
  · refine ⟨hn, ?_⟩
    cases hp : st.pileOfTop c with
    | none =>
        exfalso
        have hnone : State.step st (Move.tabToFound c) = none := by
          show (if st.nextUp c then
              match st.pileOfTop c with
              | none => none
              | some a => some { st.setFound c.suit (st.found c.suit ++ [c]) with
                  piles := fun a' => if a' = a then
                      Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
                    else st.piles a' }
              else none) = none
          rw [ite_eq_left hn, hp]
        rw [hnone] at hstep
        exact absurd hstep (by simp)
    | some a => exact ⟨a, rfl⟩
  · exfalso
    have hnone : State.step st (Move.tabToFound c) = none := by
      show (if st.nextUp c then
          match st.pileOfTop c with
          | none => none
          | some a => some { st.setFound c.suit (st.found c.suit ++ [c]) with
              piles := fun a' => if a' = a then
                  Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
                else st.piles a' }
          else none) = none
      rw [ite_eq_right hn]
    rw [hnone] at hstep
    exact absurd hstep (by simp)

private theorem tabToFound_shape {st : State} {c : Card} {a : Anchor} {s₁ : State}
    (hstep : State.step st (Move.tabToFound c) = some s₁)
    (hpa : st.pileOfTop c = some a) :
    s₁ = { st.setFound c.suit (st.found c.suit ++ [c]) with
           piles := fun a' => if a' = a then
               Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
             else st.piles a' } := by
  obtain ⟨hnext, -⟩ := tabToFound_fires hstep
  have hstep' : State.step st (Move.tabToFound c) =
      some { st.setFound c.suit (st.found c.suit ++ [c]) with
             piles := fun a' => if a' = a then
                 Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
               else st.piles a' } := by
    show (if st.nextUp c then
        match st.pileOfTop c with
        | none => none
        | some a => some { st.setFound c.suit (st.found c.suit ++ [c]) with
            piles := fun a' => if a' = a then
                Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
              else st.piles a' }
        else none) = some { st.setFound c.suit (st.found c.suit ++ [c]) with
            piles := fun a' => if a' = a then
                Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
              else st.piles a' }
    rw [ite_eq_left hnext, hpa]
  exact ((Option.some.inj (hstep'.symm.trans hstep))).symm

/-! ## §5.1 — the safe tabToFound -/

/-- The R1 search premise at the source's `WF`: after the raise of a
card with a live below-run, the below-run's last card tops the source
pile and tops no other. -/
private theorem pileOfTop_after_tabToFound {st : State} {c z : Card} {k : Anchor}
    {s₁ : State}
    (hwf : st.WF)
    (hz : lastOf (chop (st.piles k).faceUp) = some z)
    (hs : s₁ = { st.setFound c.suit (st.found c.suit ++ [c]) with
           piles := fun a' => if a' = k then
               Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
             else st.piles a' }) :
    s₁.pileOfTop z = some k := by
  have hzmem : z ∈ (st.piles k).faceUp := by
    have h1 : z ∈ chop (st.piles k).faceUp := lastOf_mem hz
    exact mem_of_chop h1
  have hpilek : s₁.piles k = Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp) := by
    rw [hs]
    show (if k = k then
        Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
      else st.piles k) = Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
    rw [ite_eq_left rfl]
  have hpothers : ∀ a', a' ≠ k → s₁.piles a' = st.piles a' := by
    intro a' hne
    rw [hs]
    show (if a' = k then
        Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
      else st.piles a') = st.piles a'
    rw [ite_eq_right hne]
  -- s₁'s pile k tops z (the removal kept the below-run)
  have htops : s₁.topOf k = some z := by
    show lastOf ((s₁.piles k).faceUp) = some z
    rw [hpilek]
    show lastOf (Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)).faceUp = some z
    cases hch : chop (st.piles k).faceUp with
    | nil =>
        rw [hch] at hz
        exact absurd hz (by simp [lastOf])
    | cons x t =>
        have hz' : lastOf (x :: t) = some z := by rw [← hch]; exact hz
        show lastOf (Pile.afterRunRemoved (st.piles k) (x :: t)).faceUp = some z
        rw [show Pile.afterRunRemoved (st.piles k) (x :: t)
            = { (st.piles k) with faceUp := x :: t } from rfl]
        exact hz'
  -- no other pile tops z at st, hence none at s₁
  have hother : ∀ y ∈ Anchor.all, y ≠ k → s₁.topOf y ≠ some z := by
    intro y hy hyne htop
    have hyeq : s₁.piles y = st.piles y := hpothers y hyne
    have htop' : (st.piles y).top = some z := by
      show lastOf ((st.piles y).faceUp) = some z
      rw [← hyeq]
      exact htop
    exact ((mem_faceUp_unique hwf hzmem) (a' := y) hyne).1 (Pile.mem_of_top htop')
  show firstWhere (fun a' => decide (s₁.topOf a' = some z)) Anchor.all = some k
  refine firstWhere_find (Anchor.mem_all k) (by
    show decide (s₁.topOf k = some z) = true
    rw [htops]
    exact decide_eq_true rfl) (fun y hy hyne => decide_false_of_not (fun hcon =>
    hother y hy hyne hcon))

/-- **(N) The bare-floor residue** — §5.1's one open piece, the old
[GAP] channel-A/B reshape in physical dress: the raised card's
below-run is empty, and either the automatic reveal seated the
boundary card (the fresh top is not a fitting base for `c`) or the
card is no king (the emptied pile will not take it back).  The
classical remedy (B&G App. B.1, the safety instances): under
`safeToFound`, every card that could ever sit on `c` is a rank-`r−1`
opposite-colour live tenant with its own foundation already at its
index — the tenant subtree channels through the foundations (channel
A, depth at most two — the safety bounds descend exactly two ranks),
and the worry-backs of `c`'s suit-prefix in the source play are
skipped (channel B — same-colour conjunct).  The divergence is
one-two-step: parks onto `c`'s vacated seat re-home through
`tabToTab` runs; the shuffle-replay template is `RevEqW`
(`Orig/Combine`), the walk agreement `excursionSim`-shaped.
Refute-first target: a bare-floor state where compliancy fails —
every winning play parks onto `c`'s fresh seat before `c`'s suit
climbs past it.  TODO(proof). -/
theorem tabToFound_dominant_of_ground {st : State} {c : Card} {k : Anchor} {s₁ : State}
    (hwf : st.WF) (hsafe : safeToFound st c = true)
    (hk : st.pileOfTop c = some k)
    (hstep : State.step st (Move.tabToFound c) = some s₁)
    (hbare : chop (st.piles k).faceUp = [])
    (hcorner : (st.piles k).hidden ≠ [] ∨ c.rank ≠ Rank.king)
    (hsolv : WinFrom st) : WinFrom s₁ := sorry

/-- **§5.1, physical form**: a legal `tabToFound` of a safe card is
dominant — the win survives the raise.  PROVEN here modulo the single
named residue above: the under-seat case rides the LANDED
`tabToFound_undo_under` (the below-run's last card fits — `runOK`
descent — and tops its pile — the search is unique at `WF`), the
bare-king case rides the LANDED `tabToFound_undo_bare`; both fall to
`WinFrom_of_undo`. -/
theorem tabToFound_safe_dominant {st : State} {c : Card} {s₁ : State}
    (hwf : st.WF) (hsafe : safeToFound st c = true)
    (hstep : State.step st (Move.tabToFound c) = some s₁)
    (hsolv : WinFrom st) : WinFrom s₁ := by
  obtain ⟨hnext, k, hk⟩ := tabToFound_fires hstep
  cases hchop : chop (st.piles k).faceUp with
  | nil =>
      by_cases hking : c.rank = Rank.king
      · by_cases hhidden : (st.piles k).hidden = []
        · exact WinFrom_of_undo hstep
            (tabToFound_undo_bare hstep hk hchop hhidden hking) hsolv
        · exact tabToFound_dominant_of_ground hwf hsafe hk hstep hchop
            (Or.inl hhidden) hsolv
      · exact tabToFound_dominant_of_ground hwf hsafe hk hstep hchop
          (Or.inr hking) hsolv
  | cons x t =>
      have hchne : chop (st.piles k).faceUp ≠ [] := by
        rw [hchop]
        intro h
        exact absurd h (by simp)
      obtain ⟨-, hlastc⟩ := pileOfTop_top hk
      have hfull : (st.piles k).faceUp = chop (st.piles k).faceUp ++ [c] :=
        lastOf_chop hlastc
      have hrok : runOK (chop (st.piles k).faceUp ++ [c]) = true := by
        rw [← hfull]
        exact hwf.runOK_of k
      obtain ⟨z, hz, hsit⟩ := runOK_snoc_sit hchne hrok
      have hs := tabToFound_shape hstep hk
      have hsearch := pileOfTop_after_tabToFound hwf hz hs
      exact WinFrom_of_undo hstep
        (tabToFound_undo_under hstep hk hz hsit hsearch) hsolv

/-! ## §5.3 — the draw-1 deck dominance -/

/-- The draw cycle's content: the stock in draw order, then the waste
read back to front — invariant under dealing and recycling. -/
def cycleOf (st : State) : List Card := st.stock ++ st.waste.reverse

/-- Two states whose piles, foundations, draw step and cycle content
agree — differing at most in how far the cycle has been dealt. -/
def sameCycle (st st' : State) : Prop :=
  st.found = st'.found ∧ st.piles = st'.piles ∧ st.drawStep = st'.drawStep ∧
    cycleOf st = cycleOf st'

/-- c's **exit**: the waste-spending move that takes `c` out of the
cycle for good — the stack arm or the park arm. -/
def Move.leavesWaste (c : Card) : Move → Bool
  | .wasteToFound c' => decide (c' = c)
  | .wasteToTab c' _ => decide (c' = c)
  | _ => false

/-- The only move shape that reads (and drops) `c`'s foundation slot:
a worry-back of `c`'s suit.  (The rung vocabulary is the route map's
own, FUTURES-ORIG §1.) -/
def Move.lowersRung (c : Card) : Move → Bool
  | .foundToTab x _ => decide (x.suit = c.suit)
  | _ => false

/-- The §5.3 compliance (rung discipline): until `c` leaves the
waste, no worry-back of `c`'s suit.  Pre-exit, `c`'s suit cannot
stack (`c` is in the cycle, `WF` uniqueness; its frontier card is
`c` itself), so `foundToTab` of the suit is the only slot-dropper,
and the fronting play stays legal exactly while it is banned. -/
def rungHeldUntilExit (c : Card) : List Move → Prop
  | [] => True
  | m :: π' => (m.leavesWaste c = true) ∨
      ((m.lowersRung c = false) ∧ rungHeldUntilExit c π')

/-! ### The (C) engine's fuel — fires-readers, keepers, and the
two-step worry undo

The (C)-machinery's local kit.  Dedup-marks per piece: the four
fires-readers are adapted from `Orig/Irreversible.lean`'s private
step-inversion rows (and `Orig/Shuttle.lean`'s private
`step_wasteToTab_inv`, `step_foundToTab_eq`); `step_drawStep_keep`
mirrors `Orig/Progress.lean`'s private `step_drawStep` and
`Orig/Phase.lean`'s private `draw_drawStep`; `foundToTab_return` is
restated at the ONE-Move undo shape (the `reversibleAtW` ∃-form of
`foundToTab_undo` / Classify's `foundToTab_reversibleAtW_of_legal_wf`
does not expose the play it constructs, and the adjacent-cancellation
consumes exactly `step s₁ (tabToFound x) = some st`); `setFound_comm`
is a `State.lean` reader-section candidate.  Everything here cites
publics only. -/

/-- A successful `.foundToTab`: the named card is its suit's
foundation top, the placement is legal, and the successor is the
chopped foundation with the card placed. -/
private theorem foundToTab_fires {st : State} {x : Card} {b : Base} {s₁ : State}
    (h : State.step st (Move.foundToTab x b) = some s₁) :
    st.foundTop x.suit = some x ∧ st.canPlace x b = true ∧
      s₁ = (st.setFound x.suit (chop (st.found x.suit))).putCard x b := by
  simp only [State.step] at h
  split at h
  · split at h
    · rename_i _ c' ht hg
      rw [Bool.and_eq_true] at hg
      injection h with hEq
      refine ⟨ht.trans (congrArg some (of_decide_eq_true hg.1)), hg.2, hEq.symm⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- A successful `.wasteToFound`: the guards held, the waste head is
the moved card, and the successor is the raised foundation with the
waste popped. -/
private theorem wasteToFound_fires {st : State} {y : Card} {s₁ : State}
    (h : State.step st (Move.wasteToFound y) = some s₁) :
    st.wasteIs y = true ∧ st.nextUp y = true ∧
      ∃ w', st.waste = y :: w' ∧
        s₁ = { st.setFound y.suit (st.found y.suit ++ [y]) with waste := w' } := by
  simp only [State.step] at h
  split at h
  · rename_i hg
    rw [Bool.and_eq_true] at hg
    split at h
    · rename_i _ v' ws hw
      have hwis := hg.1
      rw [State.wasteIs_cons hw y] at hwis
      have hv : v' = y := of_decide_eq_true hwis
      rw [hv] at hw
      injection h with hEq
      exact ⟨hg.1, hg.2, ws, hw, hEq.symm⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- A successful `.wasteToTab`: the guards held, the waste head is
the moved card, and the successor is the placement with the waste
popped. -/
private theorem wasteToTab_fires {st : State} {y : Card} {b : Base} {s₁ : State}
    (h : State.step st (Move.wasteToTab y b) = some s₁) :
    st.wasteIs y = true ∧ st.canPlace y b = true ∧
      ∃ w', st.waste = y :: w' ∧
        s₁ = { st.putCard y b with waste := w' } := by
  simp only [State.step] at h
  split at h
  · rename_i hg
    rw [Bool.and_eq_true] at hg
    split at h
    · rename_i _ v' ws hw
      have hwis := hg.1
      rw [State.wasteIs_cons hw y] at hwis
      have hv : v' = y := of_decide_eq_true hwis
      rw [hv] at hw
      injection h with hEq
      exact ⟨hg.1, hg.2, ws, hw, hEq.symm⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- A successful `.tabToTab`: the run head's pile was located, the
placement is legal, and the successor is the source pile minus the run
with the run placed. -/
private theorem tabToTab_fires {st : State} {y : Card} {b : Base} {s₁ : State}
    (h : State.step st (Move.tabToTab y b) = some s₁) :
    ∃ a, st.pileHolding y = some a ∧ st.canPlace y b = true ∧
      s₁ = (st.setPile a
          (Pile.afterRunRemoved (st.piles a) (below y (st.piles a).faceUp))).putRun
            (fromCard y (st.piles a).faceUp) b := by
  simp only [State.step] at h
  split at h
  · exact absurd h (by simp)
  · rename_i a hh
    split at h
    · rename_i hcp
      split at h
      · exact absurd h (by simp)
      · rename_i _ hne
        injection h with hEq
        exact ⟨a, hh, hcp, hEq.symm⟩
    · exact absurd h (by simp)

/-- The draw step is permanent: no move in the model re-labels the
draw width.  (Mirrors `Orig/Progress.lean`'s private `step_drawStep`;
re-proven here so this chapter cites publics only.) -/
private theorem step_drawStep_keep {st s₁ : State} {m : Move}
    (h : State.step st m = some s₁) : s₁.drawStep = st.drawStep := by
  cases m with
  | draw =>
      obtain ⟨r, hrec, -, hy⟩ := draw_unfold h
      have hrd : r.drawStep = st.drawStep := by
        rw [← hrec]
        by_cases hst : st.stock = []
        · by_cases hw : st.waste = []
          · rw [recycle_allEmpty st hst hw]
          · rw [recycle_nil st hst hw]
        · rw [recycle_keep st hst]
      have : s₁.drawStep = r.drawStep := by rw [hy]
      rw [this, hrd]
  | wasteToFound y =>
      obtain ⟨-, -, w', -, hs⟩ := wasteToFound_fires h
      rw [hs]
      show (st.setFound y.suit (st.found y.suit ++ [y])).drawStep = st.drawStep
      exact setFound_drawStep st y.suit _
  | wasteToTab y b =>
      obtain ⟨-, -, w', -, hs⟩ := wasteToTab_fires h
      rw [hs]
      show (st.putCard y b).drawStep = st.drawStep
      exact putCard_drawStep st y b
  | tabToFound y =>
      obtain ⟨-, a, ha⟩ := tabToFound_fires h
      rw [tabToFound_shape h ha]
      show (st.setFound y.suit (st.found y.suit ++ [y])).drawStep = st.drawStep
      exact setFound_drawStep st y.suit _
  | foundToTab y b =>
      obtain ⟨-, -, hs⟩ := foundToTab_fires h
      rw [hs]
      have h1 := setFound_drawStep st y.suit (chop (st.found y.suit))
      have h2 := putCard_drawStep (st.setFound y.suit (chop (st.found y.suit))) y b
      rw [h2, h1]
  | tabToTab y b =>
      obtain ⟨a, -, -, hs⟩ := tabToTab_fires h
      rw [hs]
      have h1 := setPile_drawStep st a
        (Pile.afterRunRemoved (st.piles a) (below y (st.piles a).faceUp))
      have h2 := putRun_drawStep
        (st.setPile a (Pile.afterRunRemoved (st.piles a) (below y (st.piles a).faceUp)))
        (fromCard y (st.piles a).faceUp) b
      rw [h2, h1]

/-- Taking at least the whole list takes the whole list. -/
private theorem take_ge_length {α : Type} : ∀ (l : List α) (n : Nat),
    l.length ≤ n → l.take n = l := by
  intro l
  induction l with
  | nil => intro n _; cases n <;> rfl
  | cons x t ih =>
      intro n h
      cases n with
      | zero => exact absurd h (by simp)
      | succ m =>
          show x :: t.take m = x :: t
          exact congrArg (x :: ·) (ih m (by simp at h; omega))

/-- The draw keeps every cycle card somewhere spendable: each card of
the recycled-and-dealt pool lands either in the dealt batch (the new
waste) or in the stock remainder. -/
private theorem draw_inCycle {st s₁ : State} {c : Card}
    (h : State.step st Move.draw = some s₁)
    (hc : c ∈ st.stock ∨ c ∈ st.waste) :
    c ∈ s₁.stock ∨ c ∈ s₁.waste := by
  obtain ⟨r, hrec, hrne, hy⟩ := draw_unfold h
  -- the recycle stage keeps the cycle membership
  have hrc : c ∈ r.stock ∨ c ∈ r.waste := by
    rcases hc with hcs | hcw
    · by_cases hst : st.stock = []
      · exact absurd hcs (by rw [hst]; simp)
      · left; rw [← hrec, recycle_keep st hst]; exact hcs
    · by_cases hst : st.stock = []
      · by_cases hwst : st.waste = []
        · exfalso
          rw [← hrec, recycle_allEmpty st hst hwst] at hrne
          rw [hst] at hrne
          exact absurd rfl hrne
        · left
          have hrr : State.recycle st = { st with stock := st.waste.reverse, waste := [] } :=
            recycle_nil st hst hwst
          rw [← hrec, hrr]
          show c ∈ st.waste.reverse
          exact List.mem_reverse.mpr hcw
      · right; rw [← hrec, recycle_keep st hst]; exact hcw
  -- the deal stage splits the stock into take/drop; both parts stay
  -- spendable (the taken batch reverses onto the new waste)
  have hs : s₁.stock = r.stock.drop r.drawStep := by rw [hy, dealUpTo_eq_take_drop]
  have hw : s₁.waste = (r.stock.take r.drawStep).reverse ++ r.waste := by
    rw [hy, dealUpTo_eq_take_drop]
  rcases hrc with hcs | hcw
  · have hsplit : c ∈ r.stock.take r.drawStep ++ r.stock.drop r.drawStep := by
      rw [List.take_append_drop r.drawStep r.stock]
      exact hcs
    rcases List.mem_append.mp hsplit with hleft | hright
    · right
      rw [hw]
      exact List.mem_append.2 (Or.inl (List.mem_reverse.mpr hleft))
    · left; rw [hs]; exact hright
  · right
    rw [hw]
    exact List.mem_append.2 (Or.inr hcw)

/-- An un-exited rung card blocks the win: with `c` still in the draw
cycle, the foundations cannot be complete — a completed foundation
holds every card of its suit, and `WF` conservation forbids `c` from
being both founded and in the cycle. -/
private theorem inCycle_notisWin {st : State} {c : Card}
    (hwf : st.WF) (hc : c ∈ st.stock ∨ c ∈ st.waste) : st.isWin = false := by
  cases hwin : st.isWin with
  | false => rfl
  | true =>
      exfalso
      have h13 : (st.found c.suit).length = 13 := by
        have hall := (List.all_eq_true).mp hwin
        exact of_decide_eq_true (hall c.suit (Suit.mem_all c.suit))
      obtain ⟨n, hn⟩ := hwf.found_prefix c.suit
      have hmin : (st.found c.suit).length = min n 13 := by
        rw [hn, List.length_take, Suit.upCards_length]
      have hnge : 13 ≤ n := by
        rcases Nat.lt_or_ge n 13 with hlt | hge
        · rw [Nat.min_eq_left (Nat.le_of_lt hlt)] at hmin
          omega
        · exact hge
      have hmem : c ∈ st.found c.suit := by
        have hle : (c.suit.upCards).length ≤ n := by
          rw [Suit.upCards_length]; exact hnge
        rw [hn, take_ge_length _ n hle]
        exact Suit.mem_upCards
      obtain ⟨-, hns, hnw, -⟩ := mem_found_unique hwf hmem
      rcases hc with hcs | hcw
      · exact hns hcs
      · exact hnw hcw

/-- Two foundation writes at distinct suits commute.  (A
`State.lean` reader-section candidate, dedup-marked.) -/
private theorem step_tabToFound_eq {st : State} {c : Card} {k : Anchor}
    (hnext : st.nextUp c = true) (hpo : st.pileOfTop c = some k) :
    State.step st (Move.tabToFound c) =
      some { st.setFound c.suit (st.found c.suit ++ [c]) with
             piles := fun a' => if a' = k then
                 Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
               else st.piles a' } := by
  show (if st.nextUp c then
      match st.pileOfTop c with
      | none => none
      | some a => some { st.setFound c.suit (st.found c.suit ++ [c]) with
          piles := fun a' => if a' = a then
              Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
            else st.piles a' }
      else none) = _
  rw [ite_eq_left hnext, hpo]

/-- **The two-step worry undo.**  At a `WF` state, the adjacent window
`[foundToTab x b; tabToFound x]` is the identity: the restack returns
to the origin in one move, with the foundation restored by the
`chop`-snoc law, the written pile by the round trip of the placement
(`putCard_inr_roundtrip`'s shape), and every other field untouched by
readers.  This is `foundToTab_undo` (Irreversible, private) restated
at the ONE-MOVE shape the adjacent cancellation consumes — the
`reversibleAtW` ∃-form does not expose the constructed play; the
`hnext` arithmetic is Classify's public `wf_found_chop_toIdx`, the
search exactness Integrity's public `pileOfTop_eq_some_iff`. -/
private theorem foundToTab_return {st : State} {x : Card} {b : Base} {s₁ : State}
    (hwf : st.WF) (h : State.step st (Move.foundToTab x b) = some s₁) :
    State.step s₁ (Move.tabToFound x) = some st := by
  obtain ⟨htop, hcp, hs₁⟩ := foundToTab_fires h
  have hwf' : s₁.WF := step_wf hwf h
  have hs₁f : s₁.found x.suit = chop (st.found x.suit) := by
    rw [hs₁, putCard_found, setFound_found_self]
  have hchopidx : (chop (st.found x.suit)).length = x.rank.toIdx :=
    wf_found_chop_toIdx hwf htop
  have hnext : s₁.nextUp x = true := by
    show decide (x.rank.toIdx = (s₁.found x.suit).length) = true
    rw [hs₁f, hchopidx]
    exact decide_eq_true rfl
  have hsnoc : chop (st.found x.suit) ++ [x] = st.found x.suit :=
    (lastOf_chop htop).symm
  -- the foundation with the moved card re-appended is the origin's:
  -- at the moved suit by the snoc law, at every other by the readers
  have hfound : (fun σ => if σ = x.suit then s₁.found x.suit ++ [x] else s₁.found σ)
      = st.found := by
    funext σ
    by_cases hσ : σ = x.suit
    · rw [ite_eq_left hσ, hs₁f, hsnoc, hσ]
    · rw [ite_eq_right hσ]
      show s₁.found σ = st.found σ
      rw [hs₁, putCard_found, setFound_found_ne hσ]
  cases b with
  | inl a =>
      obtain ⟨hempty, -⟩ := canPlace_inl hcp
      obtain ⟨hhid, hface⟩ := (Pile.isEmpty_eq _).mp hempty
      have hstpile : st.piles a = ((⟨[], []⟩ : Pile)) := Pile.ext hhid hface
      have hsk : s₁.piles a = ((⟨[], [x]⟩ : Pile)) := by
        rw [hs₁]
        show ((st.setFound x.suit (chop (st.found x.suit))).putCard x (Sum.inl a)).piles a = _
        rw [putCard_piles_inl]
        show (if a = a then ((⟨[], [x]⟩ : Pile)) else _) = _
        rw [ite_eq_left rfl]
      have hkeep : ∀ a' : Anchor, a' ≠ a → s₁.piles a' = st.piles a' := by
        intro a' hne
        rw [hs₁]
        show ((st.setFound x.suit (chop (st.found x.suit))).putCard x (Sum.inl a)).piles a'
          = st.piles a'
        rw [putCard_piles_inl]
        show (if a' = a then ((⟨[], [x]⟩ : Pile)) else _) = st.piles a'
        rw [ite_eq_right hne, setFound_piles]
      have htops₁ : (s₁.piles a).top = some x := by
        rw [hsk]
        rfl
      have hsrch : s₁.pileOfTop x = some a :=
        (pileOfTop_eq_some_iff hwf').mpr htops₁
      rw [step_tabToFound_eq hnext hsrch]
      refine congrArg some (?_ :
        { s₁.setFound x.suit (s₁.found x.suit ++ [x]) with
          piles := fun a' => if a' = a then
              Pile.afterRunRemoved (s₁.piles a) (chop (s₁.piles a).faceUp)
            else s₁.piles a' } = st)
      apply State.ext
      · exact hfound
      · funext a'
        show (if a' = a then
              Pile.afterRunRemoved (s₁.piles a) (chop (s₁.piles a).faceUp)
            else s₁.piles a') = st.piles a'
        by_cases ha' : a' = a
        · rw [ha', ite_eq_left rfl]
          show Pile.afterRunRemoved (s₁.piles a) (chop (s₁.piles a).faceUp) = st.piles a
          rw [hsk, hstpile]
          rfl
        · rw [ite_eq_right ha']
          exact hkeep a' ha'
      · show s₁.stock = st.stock
        rw [hs₁, putCard_stock, setFound_stock]
      · show s₁.waste = st.waste
        rw [hs₁, putCard_waste, setFound_waste]
      · show s₁.drawStep = st.drawStep
        rw [hs₁, putCard_drawStep, setFound_drawStep]
  | inr z =>
      obtain ⟨k, hz, -⟩ := canPlace_inr hcp
      have hz' : (st.setFound x.suit (chop (st.found x.suit))).pileOfTop z = some k := hz
      obtain ⟨hfkne, -⟩ := pileOfTop_top hz
      have hsk : s₁.piles k = { st.piles k with faceUp := (st.piles k).faceUp ++ [x] } := by
        rw [hs₁]
        show ((st.setFound x.suit (chop (st.found x.suit))).putCard x (Sum.inr z)).piles k = _
        rw [putCard_piles_inr _ _ _ _ hz']
        show (if k = k then
            ({ st.piles k with faceUp := (st.piles k).faceUp ++ [x] } : Pile) else _) = _
        rw [ite_eq_left rfl]
      have hkeep : ∀ a' : Anchor, a' ≠ k → s₁.piles a' = st.piles a' := by
        intro a' hne
        rw [hs₁]
        show ((st.setFound x.suit (chop (st.found x.suit))).putCard x (Sum.inr z)).piles a'
          = st.piles a'
        rw [putCard_piles_inr _ _ _ _ hz']
        show (if a' = k then
            ({ st.piles k with faceUp := (st.piles k).faceUp ++ [x] } : Pile) else _) = st.piles a'
        rw [ite_eq_right hne, setFound_piles]
      have htops₁ : (s₁.piles k).top = some x := by
        rw [hsk]
        exact lastOf_snoc
      have hsrch : s₁.pileOfTop x = some k :=
        (pileOfTop_eq_some_iff hwf').mpr htops₁
      rw [step_tabToFound_eq hnext hsrch]
      refine congrArg some (?_ :
        { s₁.setFound x.suit (s₁.found x.suit ++ [x]) with
          piles := fun a' => if a' = k then
              Pile.afterRunRemoved (s₁.piles k) (chop (s₁.piles k).faceUp)
            else s₁.piles a' } = st)
      apply State.ext
      · exact hfound
      · funext a'
        show (if a' = k then
              Pile.afterRunRemoved (s₁.piles k) (chop (s₁.piles k).faceUp)
            else s₁.piles a') = st.piles a'
        by_cases ha' : a' = k
        · rw [ha', ite_eq_left rfl]
          show Pile.afterRunRemoved (s₁.piles k) (chop (s₁.piles k).faceUp) = st.piles k
          rw [hsk]
          show Pile.afterRunRemoved
              { st.piles k with faceUp := (st.piles k).faceUp ++ [x] }
              (chop ((st.piles k).faceUp ++ [x])) = st.piles k
          rw [chop_snoc, afterRunRemoved_ne hfkne]
        · rw [ite_eq_right ha']
          exact hkeep a' ha'
      · show s₁.stock = st.stock
        rw [hs₁, putCard_stock, setFound_stock]
      · show s₁.waste = st.waste
        rw [hs₁, putCard_waste, setFound_waste]
      · show s₁.drawStep = st.drawStep
        rw [hs₁, putCard_drawStep, setFound_drawStep]

/-- Two foundation writes at distinct suits commute.  (A
`State.lean` reader-section candidate, dedup-marked.) -/
private theorem setFound_comm {st : State} {s₁ s₂ : Suit} {l₁ l₂ : List Card}
    (hne : s₁ ≠ s₂) :
    (st.setFound s₁ l₁).setFound s₂ l₂ = (st.setFound s₂ l₂).setFound s₁ l₁ := by
  apply State.ext
  · funext σ
    show (if σ = s₂ then l₂ else (if σ = s₁ then l₁ else st.found σ)) =
      (if σ = s₁ then l₁ else (if σ = s₂ then l₂ else st.found σ))
    by_cases hs : σ = s₁
    · have hs2 : σ ≠ s₂ := by rw [hs]; exact hne
      rw [ite_eq_right hs2, ite_eq_left hs, ite_eq_left hs]
    · by_cases hs' : σ = s₂
      · rw [ite_eq_left hs', ite_eq_right hs, ite_eq_left hs']
      · rw [ite_eq_right hs', ite_eq_right hs, ite_eq_right hs, ite_eq_right hs']
  · rfl
  · rfl
  · rfl
  · rfl

/-- The `foundToTab` computation: with the foundation top and the
place guard in hand, the step is the chop-back and place.  (A kin of
`Orig/Shuttle.lean`'s private `step_foundToTab_eq`, restated at the
fires-grade this chapter's square consumes.) -/
private theorem step_foundToTab_eq {st : State} {x : Card} {b : Base}
    (htop : st.foundTop x.suit = some x) (hcp : st.canPlace x b = true) :
    State.step st (Move.foundToTab x b) =
      some ((st.setFound x.suit (chop (st.found x.suit))).putCard x b) := by
  show (match st.foundTop x.suit with
      | some c' =>
          if decide (c' = x) && st.canPlace x b then
            some ((st.setFound x.suit (chop (st.found x.suit))).putCard x b)
          else none
      | none => none) = _
  rw [htop]
  show (if decide (x = x) && st.canPlace x b then
      some ((st.setFound x.suit (chop (st.found x.suit))).putCard x b)
    else none) = _
  rw [ite_eq_left (by
    rw [show decide (x = x) = true from decide_eq_true rfl, hcp]
    rfl)]

/-- Placements at twin carriers write the same piles when the
carriers' piles agree.  (The putCard readers, lifted one state up —
the squares' shared channel; a `State.lean`/`Play.lean` reader-section
candidate, dedup-marked.) -/
private theorem putCard_piles_eq_of_eq {A B : State} (hpl : A.piles = B.piles)
    (c : Card) (b : Base) :
    (A.putCard c b).piles = (B.putCard c b).piles := by
  cases b with
  | inl a =>
      rw [putCard_piles_inl, putCard_piles_inl]
      funext a'
      by_cases haa : a' = a
      · rw [ite_eq_left haa, ite_eq_left haa]
      · rw [ite_eq_right haa, ite_eq_right haa]
        show A.piles a' = B.piles a'
        rw [hpl]
  | inr z =>
      have hzEq : A.pileOfTop z = B.pileOfTop z := by
        show firstWhere (fun a' => decide ((A.piles a').top = some z)) Anchor.all =
          firstWhere (fun a' => decide ((B.piles a').top = some z)) Anchor.all
        rw [hpl]
      cases hzA : A.pileOfTop z with
      | none =>
          have hzB : B.pileOfTop z = none := by rw [← hzEq, hzA]
          have hAn : A.putCard c (Sum.inr z) = A := by
            show (match A.pileOfTop z with
              | some k => A.setPile k { A.piles k with faceUp := (A.piles k).faceUp ++ [c] }
              | none => A) = A
            rw [hzA]
          have hBn : B.putCard c (Sum.inr z) = B := by
            show (match B.pileOfTop z with
              | some k => B.setPile k { B.piles k with faceUp := (B.piles k).faceUp ++ [c] }
              | none => B) = B
            rw [hzB]
          show (A.putCard c (Sum.inr z)).piles = (B.putCard c (Sum.inr z)).piles
          rw [hAn, hBn, hpl]
      | some k =>
          have hzB : B.pileOfTop z = some k := by rw [← hzEq, hzA]
          have hAk : A.piles k = B.piles k := by rw [hpl]
          rw [putCard_piles_inr _ _ _ _ hzA, putCard_piles_inr _ _ _ _ hzB]
          funext a'
          by_cases haa : a' = k
          · rw [ite_eq_left haa, ite_eq_left haa, hAk]
          · rw [ite_eq_right haa, ite_eq_right haa]
            show A.piles a' = B.piles a'
            rw [hpl]

/-- The raise's successor at the popped tail — the square's
intermediate, once (local to the square's bookkeeping). -/
private def sq2S (st : State) (y : Card) (w' : List Card) : State :=
  { st.setFound y.suit (st.found y.suit ++ [y]) with waste := w' }

/-- **The window square: `wasteToFound`.**  A foundation raise of
another suit and a c-suit worry-back commute — the raise reads the
waste and writes its own suit's slot; the worry reads the worried
suit's slot and the piles — so both orders land at the SAME
composite.  The raised suit must differ from the worry's own (an
x-suited raiser inside the open window would have to be the restack
itself, pinned by the rung and conservation).  (The spread
residue's route names this square as a paid leg of the window
bubbling; it is the pattern-kernel — the same guard-transfer shape
and the same `putCard_piles_eq_of_eq` channel — for the remaining
squares' cornered statements.) -/
private theorem foundToTab_wasteToFound_square {st : State} {x y : Card} {b : Base}
    {s₁ t : State}
    (hxs : y.suit ≠ x.suit)
    (hf : State.step st (Move.foundToTab x b) = some s₁)
    (hm : State.step s₁ (Move.wasteToFound y) = some t) :
    ∃ s₂, State.step st (Move.wasteToFound y) = some s₂ ∧
      State.step s₂ (Move.foundToTab x b) = some t := by
  obtain ⟨htop, hcp, hs₁⟩ := foundToTab_fires hf
  obtain ⟨hwis, hny, w', hw, ht⟩ := wasteToFound_fires hm
  -- the worry's readers at the two slots
  have hs₁read : ∀ σ, s₁.found σ =
      (if σ = x.suit then chop (st.found x.suit) else st.found σ) := by
    intro σ
    rw [hs₁, putCard_found]
    rfl
  have hs₁p : s₁.piles = (st.putCard x b).piles := by
    rw [hs₁]
    show ((st.setFound x.suit (chop (st.found x.suit))).putCard x b).piles = _
    exact putCard_piles_eq_of_eq (setFound_piles st x.suit (chop (st.found x.suit))) x b
  have hsw : s₁.waste = st.waste := by
    rw [hs₁]
    show ((st.setFound x.suit (chop (st.found x.suit))).putCard x b).waste = _
    rw [putCard_waste, setFound_waste]
  have hwst : st.waste = y :: w' := by rw [← hsw]; exact hw
  -- the raise's guards reread at `st`: the waste is the worry's
  -- verbatim, and the raise's slot shares no suit with the worry
  have hstfy : st.found y.suit = s₁.found y.suit := by
    rw [hs₁]
    show st.found y.suit =
      ((st.setFound x.suit (chop (st.found x.suit))).putCard x b).found y.suit
    rw [putCard_found, setFound_found_ne hxs]
  have hwis' : st.wasteIs y = true := by
    show (match st.waste with
      | [] => false
      | c' :: _ => decide (c' = y)) = true
    rw [hwst]
    exact decide_eq_true rfl
  have hny' : st.nextUp y = true := by
    show decide (y.rank.toIdx = (st.found y.suit).length) = true
    rw [hstfy]
    exact hny
  have hs₁stock : s₁.stock = st.stock := by
    rw [hs₁]
    show ((st.setFound x.suit (chop (st.found x.suit))).putCard x b).stock = _
    rw [putCard_stock, setFound_stock]
  have hs₁ds : s₁.drawStep = st.drawStep := by
    rw [hs₁]
    show ((st.setFound x.suit (chop (st.found x.suit))).putCard x b).drawStep = _
    rw [putCard_drawStep, setFound_drawStep]
  -- the raise fires at `st` with the same waste tail
  have hraise : State.step st (Move.wasteToFound y) =
      some { st.setFound y.suit (st.found y.suit ++ [y]) with waste := w' } := by
    show (if st.wasteIs y && st.nextUp y then
        match st.waste with
        | _ :: cs => some { st.setFound y.suit (st.found y.suit ++ [y]) with waste := cs }
        | [] => none
      else none) = _
    rw [show (st.wasteIs y && st.nextUp y) = true from by rw [hwis', hny']; rfl, hwst]
    rfl
  refine ⟨sq2S st y w', hraise, ?_⟩
  -- the worry's guards reread at the raise's successor
  have hs₂fx : (sq2S st y w').found x.suit = st.found x.suit := by
    show (st.setFound y.suit (st.found y.suit ++ [y])).found x.suit = _
    exact setFound_found_ne (Ne.symm hxs)
  have hs₂read : ∀ σ, (sq2S st y w').found σ
      = (if σ = y.suit then st.found y.suit ++ [y] else st.found σ) := fun _ => rfl
  have htop₂ : (sq2S st y w').foundTop x.suit = some x := by
    show lastOf ((sq2S st y w').found x.suit) = some x
    rw [hs₂fx]
    exact htop
  have hcp₂ : (sq2S st y w').canPlace x b = true := by
    show st.canPlace x b
    exact hcp
  rw [step_foundToTab_eq htop₂ hcp₂, Option.some.injEq]
  apply State.ext
  · funext σ
    rw [putCard_found, ht]
    show (if σ = x.suit then chop ((sq2S st y w').found x.suit) else (sq2S st y w').found σ) =
      (if σ = y.suit then s₁.found y.suit ++ [y] else s₁.found σ)
    rw [hs₂fx, hs₂read σ, hs₁read σ, hs₁read y.suit, ite_eq_right hxs]
    by_cases hσx : σ = x.suit
    · rw [hσx, ite_eq_left rfl, ite_eq_right (Ne.symm hxs), ite_eq_left rfl]
    · by_cases hσy : σ = y.suit
      · rw [hσy, ite_eq_right hxs, ite_eq_left rfl, ite_eq_left rfl]
      · rw [ite_eq_right hσx, ite_eq_right hσy, ite_eq_right hσy, ite_eq_right hσx]
  · funext a'
    have hAT : (((sq2S st y w').setFound x.suit
          (chop ((sq2S st y w').found x.suit))).putCard x b).piles
        = (st.putCard x b).piles := by
        refine putCard_piles_eq_of_eq ?_ x b
        show ((sq2S st y w').setFound x.suit
            (chop ((sq2S st y w').found x.suit))).piles = st.piles
        show (st.setFound y.suit (st.found y.suit ++ [y])).piles = st.piles
        rw [setFound_piles]
    have htp : t.piles a' = (st.putCard x b).piles a' := by
      rw [ht]
      show (s₁.setFound y.suit (s₁.found y.suit ++ [y])).piles a' = (st.putCard x b).piles a'
      rw [setFound_piles, hs₁p]
    show (((sq2S st y w').setFound x.suit (chop ((sq2S st y w').found x.suit))).putCard x b).piles a'
      = t.piles a'
    rw [hAT, ← htp]
  · have hL : (((sq2S st y w').setFound x.suit (chop ((sq2S st y w').found x.suit))).putCard x b).stock
        = st.stock := by
      rw [putCard_stock, setFound_stock]
      show (st.setFound y.suit (st.found y.suit ++ [y])).stock = st.stock
      rw [setFound_stock]
    rw [hL, ht]
    show st.stock = (s₁.setFound y.suit (s₁.found y.suit ++ [y])).stock
    rw [setFound_stock, hs₁stock]
  · have hL : (((sq2S st y w').setFound x.suit (chop ((sq2S st y w').found x.suit))).putCard x b).waste
        = w' := by
      rw [putCard_waste, setFound_waste]
      rfl
    rw [hL, ht]
  · have hL : (((sq2S st y w').setFound x.suit (chop ((sq2S st y w').found x.suit))).putCard x b).drawStep
        = st.drawStep := by
      rw [putCard_drawStep, setFound_drawStep]
      show (st.setFound y.suit (st.found y.suit ++ [y])).drawStep = st.drawStep
      rw [setFound_drawStep]
    rw [hL, ht]
    show st.drawStep = (s₁.setFound y.suit (s₁.found y.suit ++ [y])).drawStep
    rw [setFound_drawStep, hs₁ds]

/-- **(A) The stock-as-reserve lemma, physical form** (B&G §5.4.1's
exception, draw-1): sameCycle twins are the same verdict.  Route:
the replay of a winning play from the twin splices pure draws in
front of each consuming move (`draw` commutes past every board move
and past other draws by the phase table; a `wasteTo*` fires after
enough draws bring its card to hand — at `drawStep = 1` the cycle is
a plain rotation, `dealUpTo 1`); board moves fire verbatim
(`Phase`'s step table: no move but `draw` reads the stock or waste).
TODO(proof). -/
theorem draw1_sameCycle_sameFate {st st' : State}
    (h1 : st.drawStep = 1) (h2 : st'.drawStep = 1)
    (hsc : sameCycle st st') : sameFate st st' := sorry

/-- **(B) The compliant replay**: with `c` stocked next for its
foundation, a compliant winning play front-loads as a win after
dealing `c` out and stacking it.  Safety is not a premise — no case
reads it; the c-bundle passes to each successor on the compliance
alone.  The case ledger, one exchange per first move (an equality
square, or a `sameCycle` transport via (A)):

* `draw` — absorbed: one fewer fronting draw, same landing;
* `tabToFound` / `tabToTab` — equality squares (stock- and
  waste-blind, and the fronted card is elsewhere);
* `foundToTab x b`, x.suit ≠ c.suit — equality square (the slot
  drop and the fronting bump are at distinct suits);
* `wasteToFound x` / `wasteToTab x b`, x ≠ c — the consuming moves:
  the squares land up to `sameCycle` and (A) transports the win;
* the c-exits close without recursion: `wasteToFound c` — the
  fronting IS the play prefix's k+1 deal, so the tail wins verbatim;
  `wasteToTab c b` — the worry-back identity `[fronting,
  foundToTab c b] ≡ [wasteToTab c b]` (the raise-bump is undone by
  the lower; `shuttle_join`'s legs are the pieces).

TODO(proof). -/
theorem draw1_compliant_replay {st : State} {c : Card}
    (hwf : st.WF) (hstep : st.drawStep = 1)
    (hrung : st.nextUp c = true) (hstock : c ∈ st.stock) :
    ∀ π w, rungHeldUntilExit c π → st.run π = some w → w.isWin = true →
      ∃ k s', st.run (List.replicate k Move.draw ++ [Move.wasteToFound c]) = some s' ∧
        WinFrom s' := sorry

/-- The rung pins the card: two next-up cards of one suit are the
same card (the rung is a height, the height is a rank index, and
`Rank.toIdx` separates ranks). -/
private theorem sameRung_eq {st : State} {a b : Card}
    (ha : st.nextUp a = true) (hb : st.nextUp b = true) (hs : a.suit = b.suit) :
    a = b := by
  have hla : a.rank.toIdx = st.foundHeight a.suit := of_decide_eq_true ha
  have hlb : b.rank.toIdx = st.foundHeight b.suit := of_decide_eq_true hb
  rcases a with ⟨as, ar⟩
  rcases b with ⟨bs, br⟩
  have hss : as = bs := hs
  have hrr : ar = br := Rank.toIdx_inj (by rw [hla, hlb, hss])
  rw [hrr, hss]

/-- **(C)'s window-spread residue** — the row's ONE named stub.

The normal-form engine below reduces the compliant-play search to
this shape: a winning play whose FIRST c-suit worry-back — `x` is the
suit's foundation top; the rung bookkeeping pins the whole window to
it — is followed by something OTHER than its own restack.  The stub
owes a compliant winning play from `st` itself.

ROUTE (the whole (ii)+(iii) ledger, staged for the next pass):

* **The window accounting.**  The win founds `c` (`inCycle_notisWin`
  blocks every earlier end state), so `c` leaves the cycle inside
  the remaining play; the only raiser of a dropped c-suit rung is the
  dropped card itself (WF conservation: one card per suit and rank),
  so the restack `tabToFound x` exists in the window — possibly
  AFTER a c-park (`wasteToTab c`) that reads no rung: the straddle
  shape.  A first-passage extraction (the §12.1 `climb_firstPassage`
  family, NOT yet ported to Orig — the recorded gap) locates the
  restack while the window is open.
* **The spread exchanges** (each single square; the worry bubbles
  forward, or dually the restack backward, one move at a time): the
  `wasteToFound y` square (y.suit ≠ x.suit) is LANDED privately in
  this file (`foundToTab_wasteToFound_square`, composite-equal, its
  `putCard_piles_eq_of_eq` channel is the pattern-kernel for the
  rest); the remaining kinds have their no-interference corners,
  not new statements: `draw` reduces to the recycle-triple lemma
  (the draw reads only the stock/waste pair, the worry writes only
  foundations and piles — `draw_unfold` at both states plus the
  three `recycle` readers; the only guarded step is the `dealStock`
  shape); `wasteToTab y b'` / `foundToTab y b'` interfere exactly
  when the segment places onto the worry-created seat (a base
  reading `x`, or a landing pile shadowing the `pileOfTop` search) —
  the storage family below; `tabToFound y` is order-locked when the
  worry's own base is `inr y` (the raise consumed the worry's target
  card); `tabToTab` is cornered when the moved run passes through
  `x`; worry-worry pairs (`foundToTab` of the suit's next card down)
  never square — the second reads the POST-first foundation top
  (LIFO), so a bubble must jump the nested window as a unit, not
  through it.
* **The storage shape — the shared [GAP] family.**  When the segment
  stores onto the worry-created seat, the repair is a reshape, not a
  reordering: the placement re-homes through the foundations.
  `tabToFound_dominant_of_ground` (the (N) stub) is cited BY NAME as
  the bare-floor win-lift the storage prong consumes.  Its slack
  premise — the worried `x` is `safeToFound` at the window, by
  slack one under `safeToFound st c`, the (C) premise — is NOT
  carried here: the engine's clean prefix may spend the slack (an
  other-suit worry-back drops a height bound; `safeToFound` does not
  pass the bundle invariant, which is why (C)'s own statement keeps
  it at the root).  The storage prong must re-derive the slack at
  the window, or this residue earns a recorded premise repair.  As
  stated (no safety premise) the stub's truth rides on the classical
  B&G route; the wave-24 gate for (C) ("a compliant-less corner")
  doubles as this stub's refute gate — see the witness file.
-/
theorem draw1_worry_spread_residue {st : State} {c : Card} {x : Card} {b : Base}
    {s₁ : State} {m₂ : Move} {rest : List Move} {w : State}
    (hwf : st.WF) (hds : st.drawStep = 1) (hrung : st.nextUp c = true)
    (hcyc : c ∈ st.stock ∨ c ∈ st.waste)
    (hx : x.suit = c.suit)
    (hf : State.step st (Move.foundToTab x b) = some s₁)
    (hne : m₂ ≠ Move.tabToFound x)
    (hrun : s₁.run (m₂ :: rest) = some w) (hwin : w.isWin = true) :
    ∃ π v, st.run π = some v ∧ v.isWin = true ∧ rungHeldUntilExit c π := sorry

/-- **The (C) engine.**  Strong induction on the washing play's
length, with the engine bundle `{WF, drawStep = 1, nextUp c, c in
the cycle}` (the public statement's `c ∈ st.stock` is the root
instance; the invariant weakens to the cycle because a draw may deal
`c` into the waste before it is spent — the pre-exit regime).  The
case ledger: the empty play and the one-move worry both die on
`inCycle_notisWin` (an un-exited rung card blocks every win); an
exit head is compliant verbatim; a rung-clean head recurses at the
successor on the transferred bundle; an adjacent worry window
`[foundToTab x b; tabToFound x]` cancels through `foundToTab_return`
and recurses on the two-moves-shorter play; every spread window
routes to `draw1_worry_spread_residue`. -/
private theorem normform_aux : ∀ n : Nat, ∀ (st : State) (c : Card),
    st.WF → st.drawStep = 1 → st.nextUp c = true → (c ∈ st.stock ∨ c ∈ st.waste) →
    ∀ π w, π.length ≤ n → st.run π = some w → w.isWin = true →
      ∃ π' v, st.run π' = some v ∧ v.isWin = true ∧ rungHeldUntilExit c π' := by
  intro n
  induction n with
  | zero =>
      intro st c hwf hds hrung hcyc π w hlen hrun hwin
      cases π with
      | nil =>
          exfalso
          have hr : st.run ([] : List Move) = some st := rfl
          rw [hr] at hrun
          injection hrun with hwst
          rw [← hwst] at hwin
          rw [inCycle_notisWin hwf hcyc] at hwin
          exact Bool.noConfusion hwin
      | cons m rest =>
          exfalso
          simp at hlen
  | succ n ih =>
      intro st c hwf hds hrung hcyc π w hlen hrun hwin
      cases π with
      | nil =>
          exfalso
          have hr : st.run ([] : List Move) = some st := rfl
          rw [hr] at hrun
          injection hrun with hwst
          rw [← hwst] at hwin
          rw [inCycle_notisWin hwf hcyc] at hwin
          exact Bool.noConfusion hwin
      | cons m rest =>
          obtain ⟨s₁, hstep, hrunrest⟩ := State.run_cons hrun
          by_cases hex : m.leavesWaste c = true
          · exact ⟨m :: rest, w, hrun, hwin, Or.inl hex⟩
          · by_cases hrn : m.lowersRung c = true
            · -- the worry sector
              cases m with
              | draw => exact Bool.noConfusion hrn
              | wasteToFound y => exact Bool.noConfusion hrn
              | wasteToTab y b' => exact Bool.noConfusion hrn
              | tabToFound y => exact Bool.noConfusion hrn
              | tabToTab y b' => exact Bool.noConfusion hrn
              | foundToTab x b =>
                  have hx : x.suit = c.suit := of_decide_eq_true hrn
                  cases rest with
                  | nil =>
                      exfalso
                      have hr : s₁.run ([] : List Move) = some s₁ := rfl
                      rw [hr] at hrunrest
                      injection hrunrest with hws
                      rw [← hws] at hwin
                      obtain ⟨-, -, hs₁⟩ := foundToTab_fires hstep
                      have hcyc₁ : c ∈ s₁.stock ∨ c ∈ s₁.waste := by
                        rcases hcyc with hcs | hcw
                        · left
                          rw [hs₁]
                          show c ∈ ((st.setFound x.suit (chop (st.found x.suit))).putCard x b).stock
                          rw [putCard_stock, setFound_stock]
                          exact hcs
                        · right
                          rw [hs₁]
                          show c ∈ ((st.setFound x.suit (chop (st.found x.suit))).putCard x b).waste
                          rw [putCard_waste, setFound_waste]
                          exact hcw
                      rw [inCycle_notisWin (step_wf hwf hstep) hcyc₁] at hwin
                      exact Bool.noConfusion hwin
                  | cons m₂ rest' =>
                      by_cases hrestack : m₂ = Move.tabToFound x
                      · -- the adjacent window cancels; recurse two
                        -- moves shorter at the SAME state
                        subst hrestack
                        obtain ⟨s₂, hstep₂, hrunrest'⟩ := State.run_cons hrunrest
                        have hrtn : State.step s₁ (Move.tabToFound x) = some st :=
                          foundToTab_return hwf hstep
                        rw [hrtn] at hstep₂
                        injection hstep₂ with hs₂st
                        rw [← hs₂st] at hrunrest'
                        have hlen' : rest'.length ≤ n := by
                          simp at hlen
                          omega
                        exact ih st c hwf hds hrung hcyc rest' w hlen' hrunrest' hwin
                      · -- the spread window: the residue
                        exact draw1_worry_spread_residue hwf hds hrung hcyc hx hstep
                          hrestack hrunrest hwin
            · -- the clean sector: transfer the bundle, prepend the head
              have hfalse : m.lowersRung c = false := by
                cases hlb : m.lowersRung c with
                | true => exact absurd hlb hrn
                | false => rfl
              have hwf₁ : s₁.WF := step_wf hwf hstep
              have hds₁ : s₁.drawStep = 1 := by
                rw [step_drawStep_keep hstep, hds]
              -- the per-kind bundle transfers
              have bundle : s₁.nextUp c = true ∧ (c ∈ s₁.stock ∨ c ∈ s₁.waste) := by
                cases m with
                | draw =>
                    have hfc : s₁.found c.suit = st.found c.suit := by
                      rw [stepDraw_found hstep]
                    refine ⟨?_, draw_inCycle hstep hcyc⟩
                    show decide (c.rank.toIdx = (s₁.found c.suit).length) = true
                    rw [hfc]
                    exact hrung
                | wasteToFound y =>
                    obtain ⟨-, hny, w', hw, hs⟩ := wasteToFound_fires hstep
                    -- y ≠ c, or the head would have been the exit
                    have hne : y ≠ c := by
                      intro hcon
                      apply hex
                      show Move.leavesWaste c (Move.wasteToFound y) = true
                      rw [show Move.leavesWaste c (Move.wasteToFound y) = decide (y = c) from rfl,
                        hcon]
                      exact decide_eq_true rfl
                    -- y's suit cannot be c's (the rung pins it), so
                    -- the raise does not touch c's foundation slot
                    have hys : y.suit ≠ c.suit := by
                      intro hcon
                      exact hne (sameRung_eq hny hrung hcon)
                    have hfc : s₁.found c.suit = st.found c.suit := by
                      rw [hs]
                      show (st.setFound y.suit (st.found y.suit ++ [y])).found c.suit = _
                      exact setFound_found_ne (Ne.symm hys)
                    constructor
                    · show decide (c.rank.toIdx = (s₁.found c.suit).length) = true
                      rw [hfc]
                      exact hrung
                    · rcases hcyc with hcs | hcw
                      · left
                        rw [hs]
                        show c ∈ (st.setFound y.suit (st.found y.suit ++ [y])).stock
                        rw [setFound_stock]
                        exact hcs
                      · right
                        rw [hs]
                        show c ∈ w'
                        rw [hw] at hcw
                        rcases List.mem_cons.mp hcw with he | hm
                        · exact absurd he.symm hne
                        · exact hm
                | wasteToTab y b' =>
                    obtain ⟨-, -, w', hw, hs⟩ := wasteToTab_fires hstep
                    have hne : y ≠ c := by
                      intro hcon
                      apply hex
                      show Move.leavesWaste c (Move.wasteToTab y b') = true
                      rw [show Move.leavesWaste c (Move.wasteToTab y b') = decide (y = c) from rfl,
                        hcon]
                      exact decide_eq_true rfl
                    have hfc : s₁.found c.suit = st.found c.suit := by
                      rw [hs]
                      show (st.putCard y b').found c.suit = _
                      rw [putCard_found]
                    constructor
                    · show decide (c.rank.toIdx = (s₁.found c.suit).length) = true
                      rw [hfc]
                      exact hrung
                    · rcases hcyc with hcs | hcw
                      · left
                        rw [hs]
                        show c ∈ (st.putCard y b').stock
                        rw [putCard_stock]
                        exact hcs
                      · right
                        rw [hs]
                        show c ∈ w'
                        rw [hw] at hcw
                        rcases List.mem_cons.mp hcw with he | hm
                        · exact absurd he.symm hne
                        · exact hm
                | tabToFound y =>
                    obtain ⟨hny, a, ha⟩ := tabToFound_fires hstep
                    have hs := tabToFound_shape hstep ha
                    rcases Decidable.em (y.suit = c.suit) with hcon | hcon
                    · exfalso
                      have hyc : y = c := sameRung_eq hny hrung hcon
                      rw [hyc] at ha
                      obtain ⟨-, hlast⟩ := pileOfTop_top ha
                      have hmem : c ∈ (st.piles a).faceUp := lastOf_mem hlast
                      rcases hcyc with hcs | hcw
                      · exact ((mem_stock_unique hwf hcs).1 a).2 hmem
                      · exact ((mem_waste_unique hwf hcw).1 a).2 hmem
                    · have hfc : s₁.found c.suit = st.found c.suit := by
                        rw [hs]
                        show (st.setFound y.suit (st.found y.suit ++ [y])).found c.suit = _
                        exact setFound_found_ne (Ne.symm hcon)
                      constructor
                      · show decide (c.rank.toIdx = (s₁.found c.suit).length) = true
                        rw [hfc]
                        exact hrung
                      · rcases hcyc with hcs | hcw
                        · left
                          rw [hs]
                          show c ∈ (st.setFound y.suit (st.found y.suit ++ [y])).stock
                          rw [setFound_stock]
                          exact hcs
                        · right
                          rw [hs]
                          show c ∈ (st.setFound y.suit (st.found y.suit ++ [y])).waste
                          rw [setFound_waste]
                          exact hcw
                | foundToTab y b' =>
                    obtain ⟨-, hcp, hs⟩ := foundToTab_fires hstep
                    -- clean means the rung fact: y's suit is not c's
                    have hys : y.suit ≠ c.suit := by
                      intro hcon
                      rw [show Move.lowersRung c (Move.foundToTab y b') =
                        decide (y.suit = c.suit) from rfl, hcon] at hfalse
                      exact Bool.noConfusion (hfalse.symm.trans (decide_eq_true rfl))
                    have hfc : s₁.found c.suit = st.found c.suit := by
                      rw [hs]
                      show ((st.setFound y.suit (chop (st.found y.suit))).putCard y b').found c.suit = _
                      rw [putCard_found, setFound_found_ne (Ne.symm hys)]
                    constructor
                    · show decide (c.rank.toIdx = (s₁.found c.suit).length) = true
                      rw [hfc]
                      exact hrung
                    · rcases hcyc with hcs | hcw
                      · left
                        rw [hs]
                        show c ∈ ((st.setFound y.suit (chop (st.found y.suit))).putCard y b').stock
                        rw [putCard_stock, setFound_stock]
                        exact hcs
                      · right
                        rw [hs]
                        show c ∈ ((st.setFound y.suit (chop (st.found y.suit))).putCard y b').waste
                        rw [putCard_waste, setFound_waste]
                        exact hcw
                | tabToTab y b' =>
                    obtain ⟨a, -, -, hs⟩ := tabToTab_fires hstep
                    have hfc : s₁.found c.suit = st.found c.suit := by
                      rw [hs]
                      show ((st.setPile a
                          (Pile.afterRunRemoved (st.piles a) (below y (st.piles a).faceUp))).putRun
                          (fromCard y (st.piles a).faceUp) b').found c.suit = _
                      rw [putRun_found, setPile_found]
                    constructor
                    · show decide (c.rank.toIdx = (s₁.found c.suit).length) = true
                      rw [hfc]
                      exact hrung
                    · rcases hcyc with hcs | hcw
                      · left
                        rw [hs]
                        show c ∈ ((st.setPile a
                            (Pile.afterRunRemoved (st.piles a) (below y (st.piles a).faceUp))).putRun
                            (fromCard y (st.piles a).faceUp) b').stock
                        rw [putRun_stock, setPile_stock]
                        exact hcs
                      · right
                        rw [hs]
                        show c ∈ ((st.setPile a
                            (Pile.afterRunRemoved (st.piles a) (below y (st.piles a).faceUp))).putRun
                            (fromCard y (st.piles a).faceUp) b').waste
                        rw [putRun_waste, setPile_waste]
                        exact hcw
              obtain ⟨hrung₁, hcyc₁⟩ := bundle
              have hlen' : rest.length ≤ n := by
                simp at hlen
                omega
              obtain ⟨π', v, hrun', hwin', hcomp'⟩ :=
                ih s₁ c hwf₁ hds₁ hrung₁ hcyc₁ rest w hlen' hrunrest hwin
              refine ⟨m :: π', v, ?_, hwin', Or.inr ⟨hfalse, hcomp'⟩⟩
              show (match State.step st m with
                | some st' => State.run st' π'
                | none => none) = some v
              rw [hstep]
              exact hrun'

set_option linter.unusedVariables false in
/-- **(C) The normal form**: a winning play exists that keeps the
c-rung until `c` leaves the waste — B&G's safemoves discipline.  Any
pre-exit worry of `c`'s suit is the suit's foundation-top card; its
restack (`tabToFound`) must fire before the suit climbs again, and
the pair is either adjacent (cancel through the foundation round
trip — `tabToFound_undo_under` at the top, or `_bare`) or closes by
the same exchanges as (B)'s squares; the storage shape (a placement
onto the vacated seat) is the bare-floor residue's own assembly at
the worry-created seat — the shared [GAP] family.

PROVEN SKELETON (the (C) farm row, 2026-10-10): the case split is
`normform_aux`'s — the empty play and the lone worry die on the
cycle's win-blockade (`inCycle_notisWin`), an exit head is compliant
verbatim, a clean head recurses on the transferred bundle, and the
adjacent window `[foundToTab x b; tabToFound x]` cancels through the
proven `foundToTab_return` (the two-step worry-undo — the undo
family's round-trip identity at WF), recursing two moves shorter at
the same state.  Every spread window — worry first, a non-restack
second — routes to the ONE named residue `draw1_worry_spread_residue`
above: the residue's route note owns the window accounting (the §12.1
first-passage gap), the window squares (the landed `draw` /
`wasteToFound` privates and the corner-shaped remainder), and the
storage prong's `tabToFound_dominant_of_ground` citation (the (N)
stub — that taint is expected and named).  `hsafe` is consumed by
the residue's storage prong, not by the proven skeleton:
`safeToFound` does not survive an arbitrary clean prefix (an
other-suit worry-back can tighten a height bound), which is why the
engine's invariant carries only the rung-cycle bundle.  (The linter
is silenced below: `hsafe` is a FINAL premise of the statement — the
residue's storage prong consumes it; the proven skeleton does not.)
-/
theorem draw1_compliant_normalForm {st : State} {c : Card}
    (hwf : st.WF) (hstep : st.drawStep = 1)
    (hsafe : safeToFound st c = true)
    (hrung : st.nextUp c = true) (hstock : c ∈ st.stock)
    (hsolv : WinFrom st) :
    ∃ π w, st.run π = some w ∧ w.isWin = true ∧ rungHeldUntilExit c π := by
  obtain ⟨π, w, hrun, hwin⟩ := hsolv
  exact normform_aux π.length st c hwf hstep hrung (Or.inl hstock) π w (Nat.le_refl _)
    hrun hwin

/-- **§5.3, physical form (draw-1)**: with one card per draw, the safe
stack of a stocked rung card can be front-loaded as a plain deal-out
and stack — no play loses by it.  PROVEN given the named stubs (C)
then (B) (with the reserve lemma (A) inside (B)'s transports). -/
theorem stock_dominance_draw1 {st : State} {c : Card}
    (hwf : st.WF) (hstep : st.drawStep = 1)
    (hsafe : safeToFound st c = true)
    (hrung : st.nextUp c = true) (hstock : c ∈ st.stock)
    (hsolv : WinFrom st) :
    ∃ k s', st.run (List.replicate k Move.draw ++ [Move.wasteToFound c]) = some s' ∧
      WinFrom s' := by
  obtain ⟨π, w, hrun, hwin, hcomp⟩ :=
    draw1_compliant_normalForm hwf hstep hsafe hrung hstock hsolv
  exact draw1_compliant_replay hwf hstep hrung hstock π w hcomp hrun hwin
