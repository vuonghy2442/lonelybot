import Orig.Shuttle
import Orig.Phase
import Orig.Irreversible

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

/-! ## (B)'s private development — the nine-case replay engine

The kit below serves `draw1_compliant_replay` only.  The list
surgery and the two deal composites are dedup-marked ports of
`Orig/Phase.lean`'s private orbit strip (`plain_draw_shape`,
`base_draw_shape`, `run_draw_cons`, `run_replicate_append`,
`drain_positions_one`, `base_positions_one`); the spend/board step
inversions are dedup-marked ports of the private copies in
`Orig/Shuttle.lean` and `Orig/Irreversible.lean` (same shapes, same
proof scripts, per the farm's private-isolation convention; they
dedup at merge). -/

/-! ### List surgery -/

/-- Membership as an infix split (the witness shape a stocked or
wasted `c` carries through the induction). -/
private theorem mem_infix_split {α : Type} : ∀ (l : List α) (x : α),
    x ∈ l → ∃ pre post, l = pre ++ x :: post := by
  intro l
  induction l with
  | nil => intro x h; cases h
  | cons y t ih =>
      intro x h
      rcases List.mem_cons.1 h with rfl | hm
      · exact ⟨[], t, rfl⟩
      · obtain ⟨pre, post, heq⟩ := ih x hm
        exact ⟨y :: pre, post, by rw [heq, List.cons_append]⟩

/-- The additive take split (dedup-marked port of `Phase`'s private
`take_drop_add`). -/
private theorem table_take_add {α : Type} :
    ∀ (i j : Nat) (l : List α),
    l.take (i + j) = l.take i ++ (l.drop i).take j := by
  intro i
  induction i with
  | zero => intro j l; simp
  | succ i ih =>
      intro j l
      have hidx : i + 1 + j = i + j + 1 := by omega
      rw [hidx]
      cases l with
      | nil => simp only [List.take_nil, List.drop_nil, List.nil_append]
      | cons a t =>
          show a :: t.take (i + j) = a :: (t.take i ++ (t.drop i).take j)
          exact congrArg (a :: ·) (ih j t)

/-- The additive drop split (dedup-marked port of `Phase`'s private
`drop_drop_add`). -/
private theorem table_drop_add {α : Type} :
    ∀ (i j : Nat) (l : List α),
    (l.drop i).drop j = l.drop (i + j) := by
  intro i
  induction i with
  | zero => intro j l; simp
  | succ i ih =>
      intro j l
      have hidx : i + 1 + j = i + j + 1 := by omega
      rw [hidx]
      cases l with
      | nil => simp only [List.drop_nil]
      | cons a t => exact ih j t

/-- Taking past (or exactly to) the end takes the whole list
(dedup-marked port of `Phase`'s private `take_ge_length`). -/
private theorem table_take_ge {α : Type} : ∀ (l : List α) (n : Nat),
    l.length ≤ n → l.take n = l := by
  intro l
  induction l with
  | nil => intro n _; exact List.take_nil
  | cons a t ih =>
      intro n h
      match n with
      | 0 =>
          exact absurd h (by
            have hx : (a :: t).length = t.length + 1 := rfl
            omega)
      | m + 1 =>
          have hm : t.length ≤ m := by
            have hx : (a :: t).length = t.length + 1 := rfl
            omega
          show a :: t.take m = a :: t
          exact congrArg (a :: ·) (ih m hm)

/-- Dropping past (or exactly to) the end drops to nothing
(dedup-marked port of `Phase`'s private `drop_ge_length`). -/
private theorem table_drop_ge {α : Type} : ∀ (l : List α) (n : Nat),
    l.length ≤ n → l.drop n = [] := by
  intro l
  induction l with
  | nil => intro n _; exact List.drop_nil
  | cons a t ih =>
      intro n h
      match n with
      | 0 =>
          exact absurd h (by
            have hx : (a :: t).length = t.length + 1 := rfl
            omega)
      | m + 1 =>
          exact ih m (by have hx : (a :: t).length = t.length + 1 := rfl; omega)

/-- Taking through a known prefix returns the prefix. -/
private theorem table_take_pre {α : Type} : ∀ (A B : List α),
    (A ++ B).take A.length = A := by
  intro A
  induction A with
  | nil => intro B; rfl
  | cons a t ih => intro B; exact congrArg (a :: ·) (ih B)

/-- Dropping past a known prefix returns the tail (dedup-marked port
of `Phase`'s private `drop_append_prefix`). -/
private theorem table_drop_pre {α : Type} : ∀ (A B : List α),
    (A ++ B).drop A.length = B := by
  intro A
  induction A with
  | nil => intro B; rfl
  | cons a t ih => intro B; exact ih B

/-- The take-side append split below the prefix. -/
private theorem table_take_app_le {α : Type} :
    ∀ (A B : List α) (n : Nat), n ≤ A.length →
    (A ++ B).take n = A.take n := by
  intro A
  induction A with
  | nil =>
      intro B n hn
      have hn0 : n = 0 := by simpa using hn
      subst hn0
      rfl
  | cons a t ih =>
      intro B n hn
      match n with
      | 0 => rfl
      | m + 1 =>
          show a :: (t ++ B).take m = a :: t.take m
          exact congrArg (a :: ·) (ih B m (by
            have hx : (a :: t).length = t.length + 1 := rfl
            omega))

/-- The drop-side append split below the prefix. -/
private theorem table_drop_app_le {α : Type} :
    ∀ (A B : List α) (n : Nat), n ≤ A.length →
    (A ++ B).drop n = A.drop n ++ B := by
  intro A
  induction A with
  | nil =>
      intro B n hn
      have hn0 : n = 0 := by simpa using hn
      subst hn0
      rfl
  | cons a t ih =>
      intro B n hn
      match n with
      | 0 => rfl
      | m + 1 =>
          show (t ++ B).drop m = t.drop m ++ B
          exact ih B m (by have hx : (a :: t).length = t.length + 1 := rfl; omega)

/-- The take-side append split past the prefix. -/
private theorem table_take_app_ge {α : Type} :
    ∀ (A B : List α) (n : Nat), A.length ≤ n →
    (A ++ B).take n = A ++ B.take (n - A.length) := by
  intro A
  induction A with
  | nil =>
      intro B n _
      simp [Nat.sub_zero]
  | cons a t ih =>
      intro B n hn
      match n with
      | 0 =>
          exact absurd hn (by
            have hx : (a :: t).length = t.length + 1 := rfl
            omega)
      | m + 1 =>
          have hsub : m + 1 - (a :: t).length = m - t.length := by
            have hx : (a :: t).length = t.length + 1 := rfl
            omega
          rw [hsub]
          show a :: (t ++ B).take m = a :: (t ++ B.take (m - t.length))
          exact congrArg (a :: ·) (ih B m (by
            have hx : (a :: t).length = t.length + 1 := rfl
            omega))

/-- The drop-side append split past the prefix. -/
private theorem table_drop_app_ge {α : Type} :
    ∀ (A B : List α) (n : Nat), A.length ≤ n →
    (A ++ B).drop n = B.drop (n - A.length) := by
  intro A
  induction A with
  | nil =>
      intro B n _
      simp [Nat.sub_zero]
  | cons a t ih =>
      intro B n hn
      match n with
      | 0 =>
          exact absurd hn (by
            have hx : (a :: t).length = t.length + 1 := rfl
            omega)
      | m + 1 =>
          show (t ++ B).drop m = B.drop ((m + 1) - (t.length + 1))
          have hx : (m + 1) - (t.length + 1) = m - t.length := by omega
          rw [hx]
          exact ih B m (by have h1 : (a :: t).length = t.length + 1 := rfl; omega)

/-! ### The draw composites

Dedup-marked ports of `Orig/Phase.lean`'s private orbit strip
(`plain_draw_shape`, `base_draw_shape`, `run_draw_cons`,
`run_replicate_append`, `drain_positions_one`, `base_positions_one`),
plus the `drawStep = 1` specializations the fronting engine reads. -/

/-- One plain draw (the stock is nonempty, so no recycle fires): the
head card moves stock-to-waste, list-exact. -/
private theorem plain_draw_shape1 {x : State} (hne : x.stock ≠ []) :
    State.step x Move.draw = some
      { x with stock := x.stock.drop x.drawStep,
               waste := (x.stock.take x.drawStep).reverse ++ x.waste } := by
  rw [show State.step x Move.draw = x.stepDraw from rfl, State.stepDraw,
    show State.recycle x = x from recycle_keep x hne,
    dealStock_eq_of_ne_nil x hne, dealUpTo_eq_take_drop]

/-- One pass-end draw (the stock is empty and the waste nonempty, so
the recycle fires): the waste becomes the stock reversed, and one
clipped deal moves back onto the waste. -/
private theorem base_draw_shape1 {x : State} (hstock : x.stock = ([] : List Card))
    (hw : x.waste ≠ []) :
    State.step x Move.draw = some
      { x with stock := x.waste.reverse.drop x.drawStep,
               waste := (x.waste.reverse.take x.drawStep).reverse ++ ([] : List Card) } := by
  have hrne : x.waste.reverse ≠ [] := by
    intro hc
    have hlen := congrArg List.length hc
    rw [List.length_reverse, List.length_nil] at hlen
    obtain ⟨c0, t0, hwcon0⟩ := list_cons_of_ne_nil hw
    have h1 : 1 ≤ x.waste.length := by
      rw [hwcon0, List.length_cons]; omega
    omega
  rw [show State.step x Move.draw = x.stepDraw from rfl, State.stepDraw,
    recycle_nil x hstock hw,
    dealStock_eq_of_ne_nil _ hrne, dealUpTo_eq_take_drop]

/-- One draw followed by the rest of the play (dedup-marked port of
`Phase`'s private `run_draw_cons`). -/
private theorem run_draw_cons1 {x y : State} {rest : List Move}
    (hstep : State.step x Move.draw = some y) :
    x.run (Move.draw :: rest) = y.run rest := by
  show (match State.step x Move.draw with
      | some st' => State.run st' rest
      | none => none) = State.run y rest
  rw [hstep]

/-- Append-glue for pure-draw plays (dedup-marked port of `Phase`'s
private `run_replicate_append`). -/
private theorem run_rep_append1 :
    ∀ (q : Nat) (x z : State) (rest : List Move),
    x.run (List.replicate q Move.draw) = some z →
    x.run (List.replicate q Move.draw ++ rest) = z.run rest := by
  intro q
  induction q with
  | zero =>
      intro x z rest h
      have hx : (some x : Option State) = some z := h
      injection hx with hx2
      rw [← hx2]
      rfl
  | succ q ih =>
      intro x z rest h
      obtain ⟨y, hstep, hrest⟩ := State.run_cons h
      show x.run (Move.draw :: (List.replicate q Move.draw ++ rest)) = z.run rest
      rw [run_draw_cons1 hstep]
      exact ih y z rest hrest

/-- Splitting a successful run at a play split. -/
private theorem run_append_split1 : ∀ (x : State) (A B : List Move) (w : State),
    x.run (A ++ B) = some w → ∃ z, x.run A = some z ∧ z.run B = some w := by
  intro x A
  induction A generalizing x with
  | nil =>
      intro B w h
      exact ⟨x, rfl, h⟩
  | cons m rest ih =>
      intro B w h
      obtain ⟨s₁, hstep, hrest⟩ := State.run_cons h
      obtain ⟨z, hA, hB⟩ := ih s₁ B w hrest
      refine ⟨z, ?_, hB⟩
      show (match State.step x m with
        | some st' => State.run st' rest
        | none => none) = some z
      rw [hstep]
      exact hA

/-- One move runs by stepping it (dedup-marked port of `Shuttle`'s
private `run_one`). -/
private theorem run_one1 {st : State} {m : Move} {s : State}
    (h : State.step st m = some s) :
    st.run [m] = some s := by
  show (match State.step st m with
    | some st' => State.run st' []
    | none => none) = some s
  rw [h]
  rfl

/-- **The drain positions** (dedup-marked port of `Phase`'s private
`drain_positions_one`): from a state whose stock is `l`, `q` draws
— each a full deal of `x.drawStep`, the running offset `n = q *
drawStep` staying within the stock — move exactly those `n` cards
from the stock's front onto the waste's front, list-exact. -/
private theorem drain_positions1 :
    ∀ (q : Nat) (x : State) (n : Nat) (l : List Card),
    0 < x.drawStep → n = q * x.drawStep → n ≤ l.length → x.stock = l →
    x.run (List.replicate q Move.draw) = some
      { x with stock := l.drop n, waste := (l.take n).reverse ++ x.waste } := by
  intro q
  induction q with
  | zero =>
      intro x n l _hd hn _hle hstock
      have hn0 : n = 0 := by
        rw [Nat.zero_mul] at hn
        exact hn
      subst hn0
      show (some x : Option State) = some
        { x with stock := l.drop 0, waste := (l.take 0).reverse ++ x.waste }
      rw [List.drop_zero, List.take_zero, List.reverse_nil, List.nil_append,
        ← hstock]
  | succ q ih =>
      intro x n l hd hn hle hstock
      have hnsm : n = q * x.drawStep + x.drawStep := by
        rw [Nat.succ_mul] at hn
        exact hn
      have hlne : l ≠ [] := by
        intro hc
        have hlen : l.length = 0 := by rw [hc]; simp
        omega
      have hsne : x.stock ≠ [] := by
        intro hc
        apply hlne
        rw [← hstock]
        exact hc
      have hstep : State.step x Move.draw = some
        { x with stock := x.stock.drop x.drawStep,
                 waste := (x.stock.take x.drawStep).reverse ++ x.waste } :=
        plain_draw_shape1 hsne
      have hrep : List.replicate (q + 1) Move.draw
          = Move.draw :: List.replicate q Move.draw := rfl
      rw [hrep, run_draw_cons1 hstep, hstock]
      have hle' : q * x.drawStep ≤ (l.drop x.drawStep).length := by
        have h1 := List.length_drop (i := x.drawStep) (l := l)
        omega
      have hres := ih
        { x with stock := l.drop x.drawStep,
                 waste := (l.take x.drawStep).reverse ++ x.waste }
        (q * x.drawStep) (l.drop x.drawStep) hd rfl hle' rfl
      rw [hres]
      have hSw : (show State from
          { x with stock := l.drop x.drawStep,
                   waste := (l.take x.drawStep).reverse ++ x.waste }).waste
          = (l.take x.drawStep).reverse ++ x.waste := rfl
      rw [hSw]
      have hidx : x.drawStep + q * x.drawStep = n := by omega
      rw [table_drop_add x.drawStep (q * x.drawStep) l, hidx]
      have hmerge : (List.take (q * x.drawStep) (List.drop x.drawStep l)).reverse
            ++ ((List.take x.drawStep l).reverse ++ x.waste)
          = (l.take (x.drawStep + q * x.drawStep)).reverse ++ x.waste := by
        rw [table_take_add, List.reverse_append, List.append_assoc]
      rw [hmerge, hidx]

/-- **The redeal positions** (dedup-marked port of `Phase`'s private
`base_positions_one`): from a pass base (empty stock, nonempty
waste), `k + 1` consecutive draws move exactly that many cards back
onto the waste, list-exact. -/
private theorem base_positions1 :
    ∀ (k : Nat) (x : State),
    x.stock = ([] : List Card) → x.waste ≠ [] → 0 < x.drawStep →
    (k + 1) * x.drawStep ≤ x.waste.length →
    x.run (List.replicate (k + 1) Move.draw) = some
      { x with stock := x.waste.reverse.drop ((k + 1) * x.drawStep),
               waste := (x.waste.reverse.take ((k + 1) * x.drawStep)).reverse
                 ++ ([] : List Card) } := by
  intro k x hstock hw hd hsize
  rw [Nat.succ_mul] at hsize
  have hstep : State.step x Move.draw = some
      { x with stock := x.waste.reverse.drop x.drawStep,
               waste := (x.waste.reverse.take x.drawStep).reverse
                 ++ ([] : List Card) } :=
    base_draw_shape1 hstock hw
  rw [show List.replicate (k + 1) Move.draw
        = Move.draw :: List.replicate k Move.draw from rfl,
    run_draw_cons1 hstep]
  have hle' : k * x.drawStep ≤ (x.waste.reverse.drop x.drawStep).length := by
    have h1 := List.length_drop (i := x.drawStep) (l := x.waste.reverse)
    have h2 : x.waste.reverse.length = x.waste.length := List.length_reverse
    omega
  have hres := drain_positions1 k
    { x with stock := x.waste.reverse.drop x.drawStep,
             waste := (x.waste.reverse.take x.drawStep).reverse
               ++ ([] : List Card) }
    (k * x.drawStep) (x.waste.reverse.drop x.drawStep) hd rfl hle' rfl
  rw [hres]
  have hSw : (show State from
      { x with stock := x.waste.reverse.drop x.drawStep,
               waste := (x.waste.reverse.take x.drawStep).reverse
                 ++ ([] : List Card) }).waste
      = (x.waste.reverse.take x.drawStep).reverse
          ++ ([] : List Card) := rfl
  rw [hSw]
  have hidx : x.drawStep + k * x.drawStep = (k + 1) * x.drawStep := by
    rw [Nat.succ_mul]; omega
  rw [table_drop_add x.drawStep (k * x.drawStep) x.waste.reverse, hidx]
  have hmerge : (List.take (k * x.drawStep)
          (List.drop x.drawStep x.waste.reverse)).reverse
        ++ ((List.take x.drawStep x.waste.reverse).reverse ++ ([] : List Card))
      = ((List.take (x.drawStep + k * x.drawStep) x.waste.reverse).reverse
          ++ ([] : List Card)) := by
    rw [table_take_add, List.reverse_append, List.append_assoc]
  rw [hmerge, hidx]

/-- Replicate's snoc form. -/
private theorem rep_snoc (n : Nat) (m : Move) :
    List.replicate n m ++ [m] = List.replicate (n + 1) m := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have e1 : List.replicate (n + 1) m = m :: List.replicate n m := List.replicate_succ
      have e2 : List.replicate (n + 1 + 1) m = m :: List.replicate (n + 1) m :=
        List.replicate_succ
      rw [e1, List.cons_append, ih, e2]

/-- Replicate addition (the pure-draw plays' split). -/
private theorem rep_add (a : Nat) : ∀ (b : Nat) (m : Move),
    List.replicate (a + b) m = List.replicate a m ++ List.replicate b m := by
  intro b
  induction b with
  | zero =>
      intro m
      have ha : a + 0 = a := Nat.add_zero a
      rw [ha]
      simp
  | succ b ih =>
      intro m
      have hab : a + (b + 1) = (a + b) + 1 := by omega
      have e1 : List.replicate ((a + b) + 1) m
          = List.replicate (a + b) m ++ [m] := (rep_snoc (a + b) m).symm
      have e2 : List.replicate (b + 1) m = List.replicate b m ++ [m] :=
        (rep_snoc b m).symm
      rw [hab, e1, e2, ih, List.append_assoc]

/-- The draw-1 drain: `r` draws from a state whose stock holds at
least `r` cards move exactly `r` stock cards onto the waste's front. -/
private theorem drain_run1 {x : State} (r : Nat) (hds : x.drawStep = 1)
    (hle : r ≤ x.stock.length) :
    x.run (List.replicate r Move.draw) = some
      { x with stock := x.stock.drop r, waste := (x.stock.take r).reverse ++ x.waste } := by
  have hpos : 0 < x.drawStep := by rw [hds]; omega
  have hm : r = r * x.drawStep := by rw [hds, Nat.mul_one]
  exact drain_positions1 r x r x.stock hpos hm hle rfl

/-- The draw-1 pass-base redeal: from an exhausted stock, `1 + m`
draws deal the first `1 + m` recycled cards back onto the waste. -/
private theorem redeal_run1 {x : State} (m : Nat) (hds : x.drawStep = 1)
    (hst : x.stock = ([] : List Card)) (hw : x.waste = [] → False)
    (hle : m + 1 ≤ x.waste.length) :
    x.run (List.replicate (m + 1) Move.draw) = some
      { x with stock := x.waste.reverse.drop (m + 1),
               waste := (x.waste.reverse.take (m + 1)).reverse ++ ([] : List Card) } := by
  have hwne : x.waste ≠ [] := by
    intro hc
    exact hw hc
  have hpos : 0 < x.drawStep := by rw [hds]; omega
  have hcnt : (m + 1) * x.drawStep = m + 1 := by rw [hds, Nat.mul_one]
  have hp := base_positions1 m x hst hwne hpos (by rw [hcnt]; exact hle)
  rw [hcnt] at hp
  exact hp

/-! ### The spend step, in raised form

The `wasteToFound` spend lands on `Shuttle`'s public `raisedMid`
literal — the same shape the worry-back identity's legs use. -/

/-- The waste-top stack, computed: given the waste head and the rung,
the step is the raise. -/
private theorem wtf_step_raised {s : State} {c : Card} {ws : List Card}
    (hw : s.waste = c :: ws) (hng : s.nextUp c = true) :
    State.step s (Move.wasteToFound c) = some (raisedMid s ws c) := by
  have hgt : (s.wasteIs c && s.nextUp c) = true := by
    rw [State.wasteIs_cons hw c, hng]
    simp
  show (if s.wasteIs c && s.nextUp c then
      match s.waste with
      | _ :: ws' => some { s.setFound c.suit (s.found c.suit ++ [c]) with waste := ws' }
      | [] => none
    else none) = some (raisedMid s ws c)
  rw [ite_eq_left hgt, hw]
  rfl

/-! ### Step inversions (dedup-marked ports) -/

/-- A successful `.wasteToFound`: the guard's two halves, and the
splice `s' = raisedMid st ws c`. -/
private theorem step_wtf_inv1 {st : State} {c : Card} {s' : State}
    (h : State.step st (Move.wasteToFound c) = some s') :
    st.wasteIs c = true ∧ st.nextUp c = true ∧
      ∃ ws, st.waste = c :: ws ∧ s' = raisedMid st ws c := by
  simp only [State.step] at h
  split at h
  · rename_i hcond
    rw [Bool.and_eq_true_iff] at hcond
    obtain ⟨hw, hng⟩ := hcond
    refine ⟨hw, hng, ?_⟩
    by_cases hwst : st.waste = []
    · rw [hwst] at h
      simp at h
    · obtain ⟨w', wsl, hcon⟩ := list_cons_of_ne_nil hwst
      have hw'c : w' = c := by
        rw [State.wasteIs_cons hcon c] at hw
        exact of_decide_eq_true hw
      rw [hw'c] at hcon
      simp only [hcon, Option.some.injEq] at h
      exact ⟨wsl, hcon, by rw [h.symm]; rfl⟩
  · simp at h

/-- A successful `.wasteToTab`: guard, nonempty waste, and the
placement with the waste popped (dedup-marked port of `Shuttle`'s
private `step_wasteToTab_inv`). -/
private theorem step_wtt_inv1 {u : State} {c : Card} {b : Base} {s' : State}
    (h : State.step u (Move.wasteToTab c b) = some s') :
    u.wasteIs c = true ∧ u.canPlace c b = true ∧
      ∃ wsl, u.waste = c :: wsl ∧ s' = { u.putCard c b with waste := wsl } := by
  simp only [State.step] at h
  split at h
  · rename_i hcond
    rw [Bool.and_eq_true_iff] at hcond
    obtain ⟨hw, hcp⟩ := hcond
    refine ⟨hw, hcp, ?_⟩
    by_cases hwst : u.waste = []
    · rw [hwst] at h
      simp at h
    · obtain ⟨w', wsl, hcon⟩ := list_cons_of_ne_nil hwst
      have hw'c : w' = c := by
        rw [State.wasteIs_cons hcon c] at hw
        exact of_decide_eq_true hw
      rw [hw'c] at hcon
      simp only [hcon, Option.some.injEq] at h
      exact ⟨wsl, hcon, h.symm⟩
  · simp at h

/-- A successful `.foundToTab` (dedup-marked port of `Irreversible`'s
private `step_foundToTab_inv`). -/
private theorem step_ftt_inv1 {st : State} {c : Card} {b : Base} {s' : State}
    (h : State.step st (Move.foundToTab c b) = some s') :
    st.canPlace c b = true ∧
      s' = (st.setFound c.suit (chop (st.found c.suit))).putCard c b := by
  simp only [State.step] at h
  split at h
  · split at h
    · rename_i c' ht hcond
      rw [Bool.and_eq_true_iff] at hcond
      obtain ⟨hdec, hcp⟩ := hcond
      injection h with hEq
      have hc'c : c' = c := of_decide_eq_true hdec
      refine ⟨hcp, ?_⟩
      rw [← hEq]
    · simp at h
  · simp at h

/-- The `foundToTab` computation (dedup-marked port of `Shuttle`'s
private `step_foundToTab_eq`). -/
private theorem step_foundToTab_eq1 {st : State} {c : Card} {b : Base}
    (hcu : st.foundTop c.suit = some c)
    (hcond : (decide (c = c) && st.canPlace c b) = true) :
    State.step st (Move.foundToTab c b) =
      some ((st.setFound c.suit (chop (st.found c.suit))).putCard c b) := by
  show (match st.foundTop c.suit with
      | some c' =>
        if decide (c' = c) && st.canPlace c b then
          some ((st.setFound c.suit (chop (st.found c.suit))).putCard c b)
        else none
      | none => none) = _
  rw [hcu]
  show (if decide (c = c) && st.canPlace c b then
      some ((st.setFound c.suit (chop (st.found c.suit))).putCard c b)
    else none) =
    some ((st.setFound c.suit (chop (st.found c.suit))).putCard c b)
  rw [ite_eq_left hcond]

/-- The lower leg (dedup-marked port of `Shuttle`'s private
`lower_foundToTab`): from the mid state, `foundToTab c b` fires and
lands exactly on the `wasteToTab c b` successor — the worry-back
identity's second half. -/
private theorem lower_foundToTab1 {u : State} {c : Card} {ws : List Card}
    (hwastee : u.waste = c :: ws)
    {b : Base} {s : State}
    (h : State.step u (Move.wasteToTab c b) = some s) :
    State.step (raisedMid u ws c) (Move.foundToTab c b) = some s := by
  obtain ⟨-, hcp, ws1, hw', hs'⟩ := step_wtt_inv1 h
  rw [hw'] at hwastee
  injection hwastee with _ hws
  cases hws
  subst hs'
  -- the mid state's foundation top is exactly `c`, and its target
  -- guard is read against `u`'s verbatim piles
  have hMfc : (raisedMid u ws c).found c.suit = u.found c.suit ++ [c] := by
    show (if c.suit = c.suit then u.found c.suit ++ [c] else u.found c.suit) = _
    rw [ite_eq_left rfl]
  have hMtop : (raisedMid u ws c).foundTop c.suit = some c := by
    show lastOf ((raisedMid u ws c).found c.suit) = some c
    rw [hMfc]
    exact lastOf_snoc
  have hMcp : (raisedMid u ws c).canPlace c b = true := hcp
  rw [step_foundToTab_eq1 hMtop (by
    rw [show decide (c = c) = true from decide_eq_true rfl, hMcp]
    rfl)]
  -- restore the foundation, then place
  have hchop : chop ((raisedMid u ws c).found c.suit) = u.found c.suit := by
    rw [hMfc, chop_snoc]
  rw [hchop, Option.some.injEq]
  -- the lowered source's found-function and piles are exactly `u`'s
  have hMf : ((raisedMid u ws c).setFound c.suit (u.found c.suit)).found
      = u.found := by
    funext s1'
    show ((raisedMid u ws c).setFound c.suit (u.found c.suit)).found s1'
      = u.found s1'
    by_cases hs1 : s1' = c.suit
    · show (if s1' = c.suit then u.found c.suit
           else (raisedMid u ws c).found s1') = u.found s1'
      rw [ite_eq_left hs1, hs1]
    · show (if s1' = c.suit then u.found c.suit
           else (raisedMid u ws c).found s1') = u.found s1'
      rw [ite_eq_right hs1]
      show (if s1' = c.suit then u.found c.suit ++ [c] else u.found s1') = _
      rw [ite_eq_right hs1]
  have hMsp : ((raisedMid u ws c).setFound c.suit (u.found c.suit)).piles
      = u.piles := rfl
  cases b with
  | inl a2 =>
      apply State.ext
      · exact hMf
      · show (fun a' : Anchor =>
            if a' = a2 then ⟨[], [c]⟩ else
            ((raisedMid u ws c).setFound c.suit (u.found c.suit)).piles a') =
          (fun a' : Anchor => if a' = a2 then ⟨[], [c]⟩ else u.piles a')
        rw [hMsp]
      · rfl
      · rfl
      · rfl
  | inr z2 =>
      simp only [State.canPlace] at hcp
      cases hpo : u.pileOfTop z2 with
      | none =>
          simp only [hpo] at hcp
          exact Bool.noConfusion hcp
      | some k =>
          have hMpo : ((raisedMid u ws c).setFound c.suit (u.found c.suit)).pileOfTop z2
              = some k := by
            show (u.pileOfTop z2 : Option Anchor) = some k
            exact hpo
          rw [putCard_inr_eq hMpo,
            show u.putCard c (.inr z2) =
              u.setPile k { u.piles k with faceUp := (u.piles k).faceUp ++ [c] } from
              putCard_inr_eq hpo]
          apply State.ext
          · exact hMf
          · show (fun a' : Anchor =>
                if a' = k then
                  { ((raisedMid u ws c).setFound c.suit (u.found c.suit)).piles k with
                    faceUp :=
                    (((raisedMid u ws c).setFound c.suit (u.found c.suit)).piles k).faceUp ++ [c] }
                else ((raisedMid u ws c).setFound c.suit (u.found c.suit)).piles a') =
              (fun a' : Anchor =>
                if a' = k then { u.piles k with faceUp := (u.piles k).faceUp ++ [c] }
                else u.piles a')
            rw [hMsp]
          · rfl
          · rfl
          · rfl

/-! ### The two fronting engines -/

/-- The two bump orders agree at distinct suits — the found half of
every exchange square at `x` and `c`. -/
private theorem bump2_comm {f : Suit → List Card} {x c : Card}
    (hne : x.suit ≠ c.suit) :
    (fun s' => if s' = c.suit then f c.suit ++ [c] else
        (if s' = x.suit then f x.suit ++ [x] else f s'))
    = (fun s' => if s' = x.suit then f x.suit ++ [x] else
        (if s' = c.suit then f c.suit ++ [c] else f s')) := by
  funext s'
  by_cases h1 : s' = c.suit
  · subst h1
    rw [ite_eq_left rfl, ite_eq_right (Ne.symm hne), ite_eq_left rfl]
  · by_cases h2 : s' = x.suit
    · subst h2
      rw [ite_eq_right hne, ite_eq_left rfl, ite_eq_left rfl]
    · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h2, ite_eq_right h1]

/-- **The stock fronting engine**: with `c` stocked at depth
`|pre|` in the deal order, `|pre| + 1` draws bring it to hand and
the stack lands on the record state — `c`'s foundation bumped, the
suffix past `c` the new stock, `pre` reversed onto the waste. -/
private theorem front_stock {s : State} {c : Card} {pre post : List Card}
    (hd : s.drawStep = 1) (hng : s.nextUp c = true)
    (hs : s.stock = pre ++ c :: post) :
    s.run (List.replicate (pre.length + 1) Move.draw ++ [Move.wasteToFound c]) =
      some (State.mk (fun s' => if s' = c.suit then s.found c.suit ++ [c] else s.found s')
        s.piles post (pre.reverse ++ s.waste) s.drawStep) := by
  have hls : s.stock.length = pre.length + post.length + 1 := by
    rw [hs, List.length_append, List.length_cons]; omega
  have hle : pre.length + 1 ≤ s.stock.length := by omega
  have hap : s.stock = pre ++ [c] ++ post := by
    rw [hs]
    exact (List.append_assoc pre [c] post).symm
  have hlenA : (pre ++ [c]).length = pre.length + 1 := by
    simp [List.length_append]
  have htake : s.stock.take (pre.length + 1) = pre ++ [c] := by
    rw [hap, ← hlenA]
    exact table_take_pre (pre ++ [c]) post
  have hdrop : s.stock.drop (pre.length + 1) = post := by
    rw [hap, ← hlenA]
    exact table_drop_pre (pre ++ [c]) post
  have hdr : s.run (List.replicate (pre.length + 1) Move.draw) = some
      (State.mk s.found s.piles post ((pre ++ [c]).reverse ++ s.waste) s.drawStep) := by
    have hd0 := drain_run1 (pre.length + 1) hd hle
    rw [hd0]
    refine congrArg some (State.ext rfl rfl ?_ ?_ rfl)
    · rw [hdrop]
    · rw [htake]
  have hw : (State.mk s.found s.piles post ((pre ++ [c]).reverse ++ s.waste) s.drawStep).waste
      = c :: (pre.reverse ++ s.waste) := by
    show ((pre ++ [c]).reverse ++ s.waste) = _
    rw [List.reverse_append]
    simp
  have hstep : State.step
      (State.mk s.found s.piles post ((pre ++ [c]).reverse ++ s.waste) s.drawStep)
      (Move.wasteToFound c) = some
      (raisedMid (State.mk s.found s.piles post ((pre ++ [c]).reverse ++ s.waste) s.drawStep)
        (pre.reverse ++ s.waste) c) :=
    wtf_step_raised hw hng
  rw [run_rep_append1 (pre.length + 1) s _
      [Move.wasteToFound c] hdr, run_one1 hstep]
  rfl

/-- **The waste fronting engine**: with `c` in the waste, `preW`
above it and `postW` below, the fronting is the drain to the pass
base, the recycle-deal, and `|postW|` more deals — landing on the
record state — `c`'s foundation bumped, the cards that were above
`c` back in the stock reversed ahead of it, `postW` the new waste. -/
private theorem front_waste {s : State} {c : Card} {preW postW : List Card}
    (hd : s.drawStep = 1) (hng : s.nextUp c = true)
    (hw : s.waste = preW ++ c :: postW) :
    s.run (List.replicate (s.stock.length + postW.length + 1) Move.draw ++
      [Move.wasteToFound c]) =
      some (State.mk (fun s' => if s' = c.suit then s.found c.suit ++ [c] else s.found s')
        s.piles (preW.reverse ++ s.stock) postW s.drawStep) := by
  have hlw : s.waste.length = preW.length + 1 + postW.length := by
    rw [hw, List.length_append, List.length_cons]; omega
  -- leg one: the drain to the pass base
  have hdr1 : s.run (List.replicate s.stock.length Move.draw) = some
      (State.mk s.found s.piles [] (s.stock.reverse ++ s.waste) s.drawStep) := by
    have hd0 := drain_run1 s.stock.length hd (Nat.le_refl _)
    rw [hd0]
    refine congrArg some (State.ext rfl rfl ?_ ?_ rfl)
    · rw [table_drop_ge _ _ (Nat.le_refl _)]
    · rw [table_take_ge _ _ (Nat.le_refl _)]
  have hst : (State.mk s.found s.piles [] (s.stock.reverse ++ s.waste) s.drawStep).stock
      = ([] : List Card) := rfl
  have hwne : (s.stock.reverse ++ s.waste) = [] → False := by
    intro hc
    have hcm : c ∈ s.waste := by
      rw [hw]; exact List.mem_append.2 (Or.inr List.mem_cons_self)
    have hm : c ∈ (s.stock.reverse ++ s.waste) :=
      List.mem_append.2 (Or.inr hcm)
    rw [hc] at hm
    exact absurd hm (by simp)
  -- the recycled order, left-deep
  have hrev : (s.stock.reverse ++ s.waste).reverse
      = (postW.reverse ++ [c] ++ preW.reverse) ++ s.stock := by
    rw [List.reverse_append, List.reverse_reverse, hw, List.reverse_append,
      List.reverse_cons]
  have hlen : postW.reverse.length = postW.length := by
    simp [List.length_reverse]
  have hlA : postW.length + 1 ≤ (postW.reverse ++ [c]).length := by
    rw [← hlen, List.length_append]; simp
  have hlX : postW.length + 1
      ≤ (postW.reverse ++ [c] ++ preW.reverse).length := by
    rw [← hlen, List.length_append, List.length_append]; simp
  have htak : (s.stock.reverse ++ s.waste).reverse.take (postW.length + 1)
      = postW.reverse ++ [c] := by
    rw [hrev,
      table_take_app_le (postW.reverse ++ [c] ++ preW.reverse) s.stock
        (postW.length + 1) hlX,
      table_take_app_le (postW.reverse ++ [c]) preW.reverse (postW.length + 1) hlA,
      table_take_ge (postW.reverse ++ [c]) (postW.length + 1) (by
        rw [← hlen, List.length_append]; simp)]
  have hdro : (s.stock.reverse ++ s.waste).reverse.drop (postW.length + 1)
      = preW.reverse ++ s.stock := by
    rw [hrev,
      table_drop_app_le (postW.reverse ++ [c] ++ preW.reverse) s.stock
        (postW.length + 1) hlX,
      table_drop_app_le (postW.reverse ++ [c]) preW.reverse (postW.length + 1) hlA,
      table_drop_ge (postW.reverse ++ [c]) (postW.length + 1) (by
        rw [← hlen, List.length_append]; simp),
      List.nil_append]
  have hle2 : postW.length + 1 ≤ (s.stock.reverse ++ s.waste).length := by
    rw [List.length_append, List.length_reverse]
    omega
  -- leg two: the redeal
  have hdr2 : (State.mk s.found s.piles [] (s.stock.reverse ++ s.waste) s.drawStep).run
      (List.replicate (postW.length + 1) Move.draw) = some
      (State.mk s.found s.piles (preW.reverse ++ s.stock) (c :: postW) s.drawStep) := by
    have hdsB : (State.mk s.found s.piles [] (s.stock.reverse ++ s.waste) s.drawStep).drawStep
        = 1 := hd
    have h0 := @redeal_run1 (State.mk s.found s.piles []
        (s.stock.reverse ++ s.waste) s.drawStep) postW.length hdsB hst hwne hle2
    rw [h0]
    refine congrArg some (State.ext rfl rfl ?_ ?_ rfl)
    · show ((s.stock.reverse ++ s.waste).reverse.drop (postW.length + 1)) = _
      rw [hdro]
    · show ((s.stock.reverse ++ s.waste).reverse.take (postW.length + 1)).reverse
          ++ ([] : List Card) = _
      rw [htak, List.reverse_append, List.reverse_reverse, List.append_nil]
      simp
  -- the count splits, the legs glue, the spend fires
  have hc : s.stock.length + postW.length + 1
      = s.stock.length + (postW.length + 1) := by omega
  rw [hc, rep_add, List.append_assoc,
    run_rep_append1 s.stock.length s
      (State.mk s.found s.piles [] (s.stock.reverse ++ s.waste) s.drawStep)
      (List.replicate (postW.length + 1) Move.draw ++ [Move.wasteToFound c]) hdr1,
    run_rep_append1 (postW.length + 1)
      (State.mk s.found s.piles [] (s.stock.reverse ++ s.waste) s.drawStep)
      (State.mk s.found s.piles (preW.reverse ++ s.stock) (c :: postW) s.drawStep)
      [Move.wasteToFound c] hdr2,
    run_one1 (wtf_step_raised (rfl : (State.mk s.found s.piles (preW.reverse ++ s.stock)
        (c :: postW) s.drawStep).waste = c :: postW) hng)]
  rfl

/-! ### The nine-case compliant replay induction (in progress) -/

/-- `isWin` reads the foundation heights alone. -/
private theorem isWin_len {s : State} (σ : Suit) (h : s.isWin = true) :
    (s.found σ).length = 13 := by
  have hall := List.all_eq_true.mp h
  exact of_decide_eq_true (hall σ (Suit.mem_all σ))

/-- The take/drop partition of a deal (dedup-marked port of
`Phase`'s private `take_drop_append`). -/
private theorem table_partition {α : Type} : ∀ (n : Nat) (l : List α),
    l.take n ++ l.drop n = l := by
  intro n
  induction n with
  | zero => intro l; simp
  | succ m ih =>
      intro l
      cases l with
      | nil => rfl
      | cons a t =>
          show (a :: t.take m) ++ (t.drop m) = a :: t
          exact congrArg (a :: ·) (ih t)

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

STATUS (this row's engine kit is landed BELOW, sorry-free; the
nine-case assembly remains).  The landed private strip:

* the list surgery + the `drawStep = 1` deal composites
  (`drain_positions1`/`base_positions1`/`drain_run1`/`redeal_run1`,
  dedup-marked ports of `Phase`'s orbit strip);
* the two **fronting engines `front_stock`/`front_waste`** — the
  k-existence arithmetic made explicit: with `c` stocked at depth
  `|pre|`, `|pre|+1` drains land
  `⟨bump c, stock := suffix past c, waste := pre.reverse ++ old⟩`;
  with `c` wasted (`preW` above, `postW` below), the composite is
  drain-to-pass-base + one recycle-deal + `|postW|` deals, landing
  `⟨bump c, stock := preW.reverse ++ old stock, waste := postW⟩`;
* the spend step in raised form (`wtf_step_raised`,
  `step_wtf_inv1`) and `lower_foundToTab1` — the worry-back
  identity's leg ported from `Shuttle` (the `[wasteToFound c,
  foundToTab c b] ≡ [wasteToTab c b]` closing shape for the
  `wasteToTab c b` exit);
* `bump2_comm` — the two foundation bumps commute at distinct suits
  (the found half of every equality square at `x ≠ c`).

Route corrections for the assembly (probed, refute-first): the `\pi
= []` corner is WF-FREE — `isWin` caps every foundation at 13
while `nextUp c` pins `c.rank.toIdx < 13` against that very height,
so no step-preserved WF is needed anywhere in the induction; the
board-move squares are `draw`-pair syncs (equal stock/waste/drawStep
pairs stay synchronized through any number of draws, then the
bumps commute); the consuming-move square does NOT land up to
`sameCycle` — the two landings differ by a pure-draw ROTATION of
the same cycle (mutually reachable, so the win lifts without any
transport), and a genuine `sameCycle`-vs-(A) transport survives
only in the pristine corner of the waste-form fronting
(`postW = []`: the fronted card's slot is dealt back at the last
recycle, so the twin's cut never re-closes — THIS is the one place
(B) really cites (A)).  TODO(assembly). -/
theorem draw1_compliant_replay {st : State} {c : Card}
    (hwf : st.WF) (hstep : st.drawStep = 1)
    (hrung : st.nextUp c = true) (hstock : c ∈ st.stock) :
    ∀ π w, rungHeldUntilExit c π → st.run π = some w → w.isWin = true →
      ∃ k s', st.run (List.replicate k Move.draw ++ [Move.wasteToFound c]) = some s' ∧
        WinFrom s' := sorry

/-- **(C) The normal form**: a winning play exists that keeps the
c-rung until `c` leaves the waste — B&G's safemoves discipline.  Any
pre-exit worry of `c`'s suit is the suit's foundation-top card; its
restack (`tabToFound`) must fire before the suit climbs again, and
the pair is either adjacent (cancel through the foundation round
trip — `tabToFound_undo_under` at the top, or `_bare`) or closes by
the same exchanges as (B)'s squares; the storage shape (a placement
onto the vacated seat) is the bare-floor residue's own assembly at
the worry-created seat — the shared [GAP] family.  TODO(proof). -/
theorem draw1_compliant_normalForm {st : State} {c : Card}
    (hwf : st.WF) (hstep : st.drawStep = 1)
    (hsafe : safeToFound st c = true)
    (hrung : st.nextUp c = true) (hstock : c ∈ st.stock)
    (hsolv : WinFrom st) :
    ∃ π w, st.run π = some w ∧ w.isWin = true ∧ rungHeldUntilExit c π := sorry

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
