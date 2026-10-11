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

/-! ### The (A) kit — congruence readers, run glue, draw readers

The replay machinery for the reserve lemma below: the per-state field
congruences (over `Orig/Twin.lean`'s public `firstWhere_congr`), the
run glue (`run_step_cons`, `run_replicate_append`) and the draw
readers (`draw_shape_plain`/`_base`, `draw_cycleOf`, `drain_full`),
which mirror `Orig/Phase.lean`'s private copies
(`drain_positions_one` et al.) specialized to `drawStep = 1` —
dedup-marked, promote at harvest. -/

/-- The pile-top read is a piles-field read. -/
private theorem topOf_congr {u v : State} (a : Anchor) (h : u.piles = v.piles) :
    u.topOf a = v.topOf a := by
  show (u.piles a).top = (v.piles a).top
  exact congrArg Pile.top (congrFun h a)

/-- The top-search is a piles-field read. -/
private theorem pileOfTop_congr {u v : State} (z : Card) (h : u.piles = v.piles) :
    u.pileOfTop z = v.pileOfTop z := by
  show firstWhere (fun a => decide (u.topOf a = some z)) Anchor.all = _
  exact firstWhere_congr (p := fun a => decide (u.topOf a = some z))
    (q := fun a => decide (v.topOf a = some z)) (fun a => by rw [topOf_congr a h])
    (l := Anchor.all)

/-- The holding-search is a piles-field read. -/
private theorem pileHolding_congr {u v : State} (c : Card) (h : u.piles = v.piles) :
    u.pileHolding c = v.pileHolding c := by
  show firstWhere (fun a => decide (c ∈ (u.piles a).faceUp)) Anchor.all = _
  exact firstWhere_congr (p := fun a => decide (c ∈ (u.piles a).faceUp))
    (q := fun a => decide (c ∈ (v.piles a).faceUp))
    (fun a => by rw [congrArg Pile.faceUp (congrFun h a)]) (l := Anchor.all)

/-- The placement guard is a piles-field read. -/
private theorem canPlace_congr {u v : State} (c : Card) (b : Base)
    (h : u.piles = v.piles) : u.canPlace c b = v.canPlace c b := by
  cases b with
  | inl a =>
      show ((u.piles a).isEmpty && decide (c.rank = Rank.king))
          = ((v.piles a).isEmpty && decide (c.rank = Rank.king))
      rw [congrArg Pile.isEmpty (congrFun h a)]
  | inr z =>
      show (match u.pileOfTop z with
        | some _ => canSitOn c z | none => false) = _
      rw [pileOfTop_congr z h]
      rfl

/-- The foundation-next read is a found-field read. -/
private theorem nextUp_congr {u v : State} (c : Card) (h : u.found = v.found) :
    u.nextUp c = v.nextUp c :=
  congrArg (fun (f : Suit → List Card) => decide (c.rank.toIdx = (f c.suit).length)) h

/-- The foundation-top read is a found-field read. -/
private theorem foundTop_congr {u v : State} (s : Suit) (h : u.found = v.found) :
    u.foundTop s = v.foundTop s := by
  simp only [State.foundTop]
  rw [congrFun h s]

/-- The win predicate is a found-field read. -/
private theorem isWin_congr {u v : State} (h : u.found = v.found) :
    u.isWin = v.isWin := by
  show (Suit.all.all fun σ => decide ((u.found σ).length = 13)) =
    (Suit.all.all fun σ => decide ((v.found σ).length = 13))
  rw [h]

/-- A foundation update's `found` field, read as the guard function. -/
private theorem setFound_found_eq (st : State) (s : Suit) (l : List Card) :
    (st.setFound s l).found = fun σ => if σ = s then l else st.found σ := rfl

/-- A pile update's `piles` field, read as the guard function. -/
private theorem setPile_piles_eq (st : State) (a : Anchor) (p : Pile) :
    (st.setPile a p).piles = fun a' => if a' = a then p else st.piles a' := rfl

/-- The readers' transfer: the append-write agrees under found equality. -/
private theorem found_append_transfer {s t : State} {c : Card}
    (hf : s.found = t.found) :
    (s.setFound c.suit (s.found c.suit ++ [c])).found =
      (t.setFound c.suit (t.found c.suit ++ [c])).found := by
  rw [setFound_found_eq, setFound_found_eq]
  funext σ
  by_cases hs : σ = c.suit
  · rw [ite_eq_left hs, ite_eq_left hs, congrFun hf c.suit]
  · rw [ite_eq_right hs, ite_eq_right hs, congrFun hf σ]

/-- The readers' transfer: the chop-write agrees under found equality. -/
private theorem found_chop_transfer {s t : State} {c : Card}
    (hf : s.found = t.found) :
    (s.setFound c.suit (chop (s.found c.suit))).found =
      (t.setFound c.suit (chop (t.found c.suit))).found := by
  rw [setFound_found_eq, setFound_found_eq]
  funext σ
  by_cases hs : σ = c.suit
  · rw [ite_eq_left hs, ite_eq_left hs, congrFun hf c.suit]
  · rw [ite_eq_right hs, ite_eq_right hs, congrFun hf σ]

/-- The placement of one card agrees under piles equality. -/
private theorem putCard_piles_congr {s t : State} {c : Card} {b : Base}
    (hp : s.piles = t.piles) :
    (s.putCard c b).piles = (t.putCard c b).piles := by
  cases b with
  | inl a =>
      rw [show s.putCard c (Sum.inl a) = s.setPile a ⟨[], [c]⟩ from rfl,
        show t.putCard c (Sum.inl a) = t.setPile a ⟨[], [c]⟩ from rfl,
        setPile_piles_eq, setPile_piles_eq]
      funext a'
      by_cases ha : a' = a
      · rw [ha, ite_eq_left rfl, ite_eq_left rfl]
      · rw [ite_eq_right ha, ite_eq_right ha, congrFun hp a']
  | inr z =>
      rw [show s.putCard c (Sum.inr z) =
          (match s.pileOfTop z with
            | some k => s.setPile k { s.piles k with faceUp := (s.piles k).faceUp ++ [c] }
            | none => s) from rfl,
        show t.putCard c (Sum.inr z) =
          (match t.pileOfTop z with
            | some k => t.setPile k { t.piles k with faceUp := (t.piles k).faceUp ++ [c] }
            | none => t) from rfl,
        pileOfTop_congr z hp]
      cases hopt : t.pileOfTop z with
      | none => exact hp
      | some k =>
          rw [setPile_piles_eq, setPile_piles_eq]
          funext a'
          by_cases ha : a' = k
          · rw [ha, ite_eq_left rfl, ite_eq_left rfl, congrFun hp k]
          · rw [ite_eq_right ha, ite_eq_right ha, congrFun hp a']

/-- The placement of a run agrees under piles equality. -/
private theorem putRun_piles_congr {s t : State} {r₁ r₂ : List Card} {b : Base}
    (hp : s.piles = t.piles) (hr : r₁ = r₂) :
    (s.putRun r₁ b).piles = (t.putRun r₂ b).piles := by
  cases b with
  | inl a =>
      rw [show s.putRun r₁ (Sum.inl a) = s.setPile a ⟨[], r₁⟩ from rfl,
        show t.putRun r₂ (Sum.inl a) = t.setPile a ⟨[], r₂⟩ from rfl,
        setPile_piles_eq, setPile_piles_eq, hr]
      funext a'
      by_cases ha : a' = a
      · rw [ha, ite_eq_left rfl, ite_eq_left rfl]
      · rw [ite_eq_right ha, ite_eq_right ha, congrFun hp a']
  | inr z =>
      rw [show s.putRun r₁ (Sum.inr z) =
          (match s.pileOfTop z with
            | some k => s.setPile k { s.piles k with faceUp := (s.piles k).faceUp ++ r₁ }
            | none => s) from rfl,
        show t.putRun r₂ (Sum.inr z) =
          (match t.pileOfTop z with
            | some k => t.setPile k { t.piles k with faceUp := (t.piles k).faceUp ++ r₂ }
            | none => t) from rfl,
        pileOfTop_congr z hp, hr]
      cases hopt : t.pileOfTop z with
      | none => exact hp
      | some k =>
          rw [setPile_piles_eq, setPile_piles_eq]
          funext a'
          by_cases ha : a' = k
          · rw [ha, ite_eq_left rfl, ite_eq_left rfl, congrFun hp k]
          · rw [ite_eq_right ha, ite_eq_right ha, congrFun hp a']

/-! ### The (A) kit — the run glue and the draw readers -/

/-- The step projection of `State.run`, one move. -/
private theorem run_step_cons {u u₁ : State} {m : Move} {rest : List Move}
    (h : State.step u m = some u₁) : u.run (m :: rest) = u₁.run rest := by
  show (match State.step u m with
      | some st' => State.run st' rest | none => none) = State.run u₁ rest
  rw [h]

/-- Append-glue for pure-draw prefixes: after `q` draws land at `z`,
the suffix continues from `z`. -/
private theorem run_replicate_append :
    ∀ (q : Nat) (u z : State) (rest : List Move),
    u.run (List.replicate q Move.draw) = some z →
    u.run (List.replicate q Move.draw ++ rest) = z.run rest := by
  intro q
  induction q with
  | zero =>
      intro u z rest h
      have hx : (some u : Option State) = some z := h
      injection hx with hx2
      rw [← hx2]
      rfl
  | succ q ih =>
      intro u z rest h
      obtain ⟨u₁, hstep, hrest⟩ := State.run_cons h
      show u.run (Move.draw :: (List.replicate q Move.draw ++ rest)) = z.run rest
      rw [run_step_cons hstep]
      exact ih u₁ z rest hrest

/-- The plain draw at step 1, exactly: one card off the stock's front,
reversed onto the waste's front. -/
private theorem draw_shape_plain {u : State} {c : Card} {cs : List Card}
    (hds : u.drawStep = 1) (h : u.stock = c :: cs) : State.step u Move.draw = some
      { u with stock := cs, waste := c :: u.waste } := by
  rw [show State.step u Move.draw = State.dealStock (State.recycle u) from rfl,
    show State.recycle u = u from recycle_keep u (by
      rw [h]; exact fun hc => absurd hc (by simp)),
    dealStock_eq_of_ne_nil u (by rw [h]; exact fun hc => absurd hc (by simp)),
    dealUpTo_eq_take_drop, hds, h]
  rfl

/-- The pass-end draw at step 1: the recycled waste's first card comes
back out. -/
private theorem draw_shape_base {u : State} {b : Card} {bs : List Card}
    (hds : u.drawStep = 1) (hst : u.stock = [])
    (hw : u.waste.reverse = b :: bs) :
    State.step u Move.draw = some { u with stock := bs, waste := [b] } := by
  have hne : u.waste ≠ [] := by
    intro hc
    rw [hc, List.reverse_nil] at hw
    exact absurd hw (by simp)
  rw [show State.step u Move.draw = State.dealStock (State.recycle u) from rfl,
    show State.recycle u = { u with stock := u.waste.reverse, waste := [] } from by
      rw [recycle_nil u hst hne, hw],
    hw, dealStock_eq_of_ne_nil _ (by simp),
    dealUpTo_eq_take_drop, hds]
  rfl

/-- A step-1 draw needs only the cycle. -/
private theorem draw_step_fires {u : State} (hds : u.drawStep = 1)
    (hcy : cycleOf u ≠ []) : ∃ u₁, State.step u Move.draw = some u₁ := by
  cases hs : u.stock with
  | cons c cs => exact ⟨_, draw_shape_plain hds hs⟩
  | nil =>
      cases hw : u.waste with
      | nil =>
          exfalso
          exact hcy (by
            rw [show cycleOf u = u.stock ++ u.waste.reverse from rfl, hs, hw]
            rfl)
      | cons x xs =>
          have hrev : u.waste.reverse ≠ [] := by
            intro hc
            have hl : u.waste.length = 0 := by
              have h1 := congrArg List.length hc
              rw [List.length_reverse, List.length_nil] at h1
              exact h1
            rw [hw] at hl
            have h2 : (x :: xs).length = xs.length + 1 := rfl
            omega
          obtain ⟨b, bs, hbs⟩ := list_cons_of_ne_nil hrev
          exact ⟨_, draw_shape_base hds hs hbs⟩

/-- A successful step-1 draw succeeds only over a nonempty cycle. -/
private theorem draw_ne_of_fires {u u₁ : State}
    (h : State.step u Move.draw = some u₁) : cycleOf u ≠ [] := by
  obtain ⟨r, hreq, hrne, -⟩ := draw_unfold h
  cases hs : u.stock with
  | cons c cs =>
      intro hc
      rw [show cycleOf u = u.stock ++ u.waste.reverse from rfl, hs] at hc
      exact absurd hc (by simp)
  | nil =>
      have hwl : u.waste ≠ [] := by
        intro hc0
        have hru : State.recycle u = u := by simp only [State.recycle, hs, hc0]
        rw [hru] at hreq
        rw [← hreq] at hrne
        rw [hs] at hrne
        exact hrne rfl
      intro hc
      obtain ⟨y, ys, hcon⟩ := list_cons_of_ne_nil hwl
      rw [show cycleOf u = u.stock ++ u.waste.reverse from rfl, hs, hcon] at hc
      exact absurd hc (by simp)

/-- **The draw rotation.**  A successful draw at step 1 moves the dealt
cycle's head to its tail — `cycleOf` rotates left, regardless of the
phase (how far the cycle has been dealt). -/
private theorem draw_cycleOf {s s' : State}
    (hds : s.drawStep = 1) (h : State.step s Move.draw = some s') :
    cycleOf s' = (cycleOf s).drop 1 ++ (cycleOf s).take 1 := by
  cases hs : s.stock with
  | cons c cs =>
      rw [draw_shape_plain hds hs] at h
      have heq : s' = { s with stock := cs, waste := c :: s.waste } :=
        (Option.some.inj h).symm
      have hcy : cycleOf s = c :: (cs ++ s.waste.reverse) := by
        show s.stock ++ s.waste.reverse = _
        rw [hs]
        rfl
      rw [heq, hcy]
      show cs ++ (c :: s.waste).reverse
          = (c :: (cs ++ s.waste.reverse)).drop 1
            ++ (c :: (cs ++ s.waste.reverse)).take 1
      rw [show (c :: (cs ++ s.waste.reverse)).drop 1 = cs ++ s.waste.reverse from rfl,
          show (c :: (cs ++ s.waste.reverse)).take 1 = [c] from rfl,
          List.reverse_cons, List.append_assoc]
  | nil =>
      cases hw : s.waste with
      | nil =>
          exfalso
          have hrd : State.recycle s = s := by simp only [State.recycle, hs, hw]
          rw [show State.step s Move.draw = State.dealStock (State.recycle s) from rfl,
              hrd, dealStock_nil s hs] at h
          exact absurd h (by simp)
      | cons x xs =>
          have hrev : s.waste.reverse ≠ [] := by
            intro hc
            have hl : s.waste.length = 0 := by
              have h1 := congrArg List.length hc
              rw [List.length_reverse, List.length_nil] at h1
              exact h1
            rw [hw] at hl
            have h2 : (x :: xs).length = xs.length + 1 := rfl
            omega
          obtain ⟨b, bs, hbs⟩ := list_cons_of_ne_nil hrev
          rw [draw_shape_base hds hs hbs] at h
          have heq : s' = { s with stock := bs, waste := [b] } :=
            (Option.some.inj h).symm
          have hcy : cycleOf s = b :: bs := by
            show s.stock ++ s.waste.reverse = _
            rw [hs, hbs]
            rfl
          rw [heq, hcy]
          show bs ++ [b].reverse = (b :: bs).drop 1 ++ (b :: bs).take 1
          rw [show (b :: bs).drop 1 = bs from rfl,
              show (b :: bs).take 1 = [b] from rfl]
          rfl

/-- **The full drain.**  At step 1, `q` consecutive draws from a
matching stock move exactly its first `q` cards onto the waste,
list-exact (`drain_positions_one` at `drawStep = 1`, the Phase copy's
step-1 specialization). -/
private theorem drain_full : ∀ (q : Nat) (u : State) (l : List Card),
    u.drawStep = 1 → l.length = q → u.stock = l →
    u.run (List.replicate q Move.draw) = some
      { u with stock := l.drop q, waste := (l.take q).reverse ++ u.waste } := by
  intro q
  induction q with
  | zero =>
      intro u l hds hlen hst
      have hl : l = [] := by
        cases l with
        | nil => rfl
        | cons a t =>
            have h1 : (a :: t).length = t.length + 1 := rfl
            rw [hlen] at h1
            omega
      subst hl
      exact congrArg some (State.ext rfl rfl hst rfl rfl)
  | succ q ih =>
      intro u l hds hlen hst
      have hne : l ≠ [] := by
        cases l with
        | cons a t' =>
            show (a :: t') ≠ []
            exact List.cons_ne_nil a t'
        | nil =>
            have h0 : (0 : Nat) = q + 1 := hlen
            exact absurd h0 (by omega)
      obtain ⟨x, t, hl⟩ := list_cons_of_ne_nil hne
      have hsx : u.stock = x :: t := by rw [hst, hl]
      have hstep := draw_shape_plain hds hsx
      rw [show List.replicate (q + 1) Move.draw
            = Move.draw :: List.replicate q Move.draw from rfl,
          run_step_cons hstep]
      have htlen : t.length = q := by
        rw [hl] at hlen
        have h1 : (x :: t).length = t.length + 1 := rfl
        omega
      have hrecv := ih { u with stock := t, waste := x :: u.waste } t hds htlen rfl
      rw [hrecv, hl]
      have hw : (t.take q).reverse ++ (x :: u.waste)
          = ((x :: t).take (q + 1)).reverse ++ u.waste := by
        rw [show (x :: t).take (q + 1) = x :: t.take q from rfl,
            List.reverse_cons, List.append_assoc]
        rfl
      exact congrArg some (State.ext rfl rfl rfl hw rfl)

/-- The presented cycle ends at the waste top. -/
private theorem cycleOf_eq_snoc {u : State} {x : Card} {ws : List Card}
    (h : u.waste = x :: ws) : cycleOf u = (u.stock ++ ws.reverse) ++ [x] := by
  show u.stock ++ u.waste.reverse = _
  rw [h, List.reverse_cons, List.append_assoc]

/-- Two states with equal cycles agree on the waste top. -/
private theorem waste_head_of_cycle {s t : State} {x y : Card} {ws xs : List Card}
    (hu : s.waste = x :: ws) (hv : t.waste = y :: xs)
    (hcy : cycleOf s = cycleOf t) : y = x := by
  have h1 : (s.stock ++ ws.reverse) ++ [x] = (t.stock ++ xs.reverse) ++ [y] := by
    rw [← cycleOf_eq_snoc hu, ← cycleOf_eq_snoc hv, hcy]
  have h2 := congrArg lastOf h1
  rw [lastOf_snoc (front := s.stock ++ ws.reverse),
      lastOf_snoc (front := t.stock ++ xs.reverse)] at h2
  exact (Option.some.inj h2).symm

/-- A successful `wasteToFound`, exactly: guard, the waste top is the
move's own card, the successor's shape. -/
private theorem step_wasteToFound_inv' {u : State} {x : Card} {u₁ : State}
    (h : State.step u (.wasteToFound x) = some u₁) :
    (u.wasteIs x && u.nextUp x) = true ∧ ∃ ws, u.waste = x :: ws ∧
      u₁ = { u.setFound x.suit (u.found x.suit ++ [x]) with waste := ws } := by
  simp only [State.step] at h
  split at h
  · rename_i hg
    split at h
    · rename_i _ y ys hw
      have hg0 : (u.wasteIs x && u.nextUp x) = true := hg
      rw [Bool.and_eq_true, State.wasteIs_cons hw x] at hg
      have hy : y = x := of_decide_eq_true hg.1
      rw [hy] at hw
      exact ⟨hg0, ys, hw, (Option.some.inj h).symm⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- A successful `wasteToTab`, exactly: guard, the waste top is the
move's own card, the successor's shape. -/
private theorem step_wasteToTab_inv' {u : State} {x : Card} {b : Base} {u₁ : State}
    (h : State.step u (.wasteToTab x b) = some u₁) :
    (u.wasteIs x && u.canPlace x b) = true ∧ ∃ ws, u.waste = x :: ws ∧
      u₁ = { u.putCard x b with waste := ws } := by
  simp only [State.step] at h
  split at h
  · rename_i hg
    split at h
    · rename_i _ y ys hw
      have hg0 : (u.wasteIs x && u.canPlace x b) = true := hg
      rw [Bool.and_eq_true, State.wasteIs_cons hw x] at hg
      have hy : y = x := of_decide_eq_true hg.1
      rw [hy] at hw
      exact ⟨hg0, ys, hw, (Option.some.inj h).symm⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- A successful `foundToTab`, exactly: the named card is the top of
its foundation, the placement is legal, the successor is the chopped
foundation with the card placed. -/
private theorem step_foundToTab_inv' {u : State} {x : Card} {b : Base} {u₁ : State}
    (h : State.step u (.foundToTab x b) = some u₁) :
    ∃ c', u.foundTop x.suit = some c' ∧ c' = x ∧ u.canPlace x b = true ∧
      u₁ = (u.setFound x.suit (chop (u.found x.suit))).putCard x b := by
  simp only [State.step] at h
  split at h
  · split at h
    · rename_i _ c' ht hg
      rw [Bool.and_eq_true] at hg
      exact ⟨c', ht, of_decide_eq_true hg.1, hg.2, (Option.some.inj h).symm⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- A successful `tabToTab`, exactly: the run head's pile was located,
the placement is legal, the face-up run from the head is nonempty, and
the successor is the pile-with-run-removed then the run placed. -/
private theorem step_tabToTab_inv' {u : State} {x : Card} {b : Base} {u₁ : State}
    (h : State.step u (.tabToTab x b) = some u₁) :
    ∃ a, u.pileHolding x = some a ∧ u.canPlace x b = true ∧
      fromCard x (u.piles a).faceUp ≠ [] ∧
      u₁ = (u.setPile a (Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp))).putRun
        (fromCard x (u.piles a).faceUp) b := by
  simp only [State.step] at h
  split at h
  · exact absurd h (by simp)
  · rename_i _ a hh
    split at h
    · rename_i hcp
      split at h
      · exact absurd h (by simp)
      · rename_i _ hne
        exact ⟨a, hh, hcp, hne, (Option.some.inj h).symm⟩
    · exact absurd h (by simp)

/-! ### The (A) sink — the transfers and the twin replay -/

/-- Shared tails make equal snoc-appendages (the append-injectivity
worked by induction). -/
private theorem snoc_tail_eq {A B : List Card} {x : Card}
    (h : A ++ [x] = B ++ [x]) : A = B := by
  induction A generalizing B with
  | nil =>
      cases B with
      | nil => rfl
      | cons b bs =>
          rw [List.nil_append, List.cons_append] at h
          exact absurd h (by simp)
  | cons a as ih =>
      cases B with
      | nil =>
          rw [List.cons_append, List.nil_append] at h
          exact absurd h (by simp)
      | cons b bs =>
          rw [List.cons_append, List.cons_append] at h
          injection h with hab htl
          rw [hab]
          exact congrArg (b :: ·) (ih htl)

/-- A successful draw keeps the draw step. -/
private theorem stepDraw_keep_drawStep {u u₁ : State} (h : u.stepDraw = some u₁) :
    u₁.drawStep = u.drawStep := by
  obtain ⟨r, hreq, -, hs'⟩ := draw_unfold h
  rw [hs']
  show r.drawStep = u.drawStep
  rw [← hreq]
  cases hs : u.stock <;> cases hw : u.waste <;>
    simp only [State.recycle, hs, hw]

/-- `putCard`, wherever it lands, writes no foundation. -/
private theorem putCard_found_keep {u : State} {c : Card} {b : Base} :
    (u.putCard c b).found = u.found := by
  cases b with
  | inl a => exact putCard_inl_found c a
  | inr z => exact putCard_inr_found c z

/-- `putRun`, wherever it lands, writes no foundation. -/
private theorem putRun_found_keep {u : State} {run : List Card} {b : Base} :
    (u.putRun run b).found = u.found := by
  cases b with
  | inl a => rfl
  | inr z =>
      rw [show u.putRun run (Sum.inr z) =
          (match u.pileOfTop z with
            | some k => u.setPile k { u.piles k with faceUp := (u.piles k).faceUp ++ run }
            | none => u) from rfl]
      cases u.pileOfTop z with
      | none => rfl
      | some k => rfl

/-- `putRun` keeps the stock, the waste, and the draw step. -/
private theorem putRun_keep {u : State} {run : List Card} {b : Base} :
    (u.putRun run b).stock = u.stock ∧ (u.putRun run b).waste = u.waste ∧
      (u.putRun run b).drawStep = u.drawStep := by
  cases b with
  | inl a => exact ⟨rfl, rfl, rfl⟩
  | inr z =>
      rw [show u.putRun run (Sum.inr z) =
          (match u.pileOfTop z with
            | some k => u.setPile k { u.piles k with faceUp := (u.piles k).faceUp ++ run }
            | none => u) from rfl]
      cases u.pileOfTop z with
      | none => exact ⟨rfl, rfl, rfl⟩
      | some k => exact ⟨rfl, rfl, rfl⟩

/-- The players' transfer of the `tabToFound` pile write. -/
private theorem piles_afterRunRemoved_transfer {s t : State} {a : Anchor}
    (hp : s.piles = t.piles) :
    (fun a' => if a' = a then
        Pile.afterRunRemoved (s.piles a) (chop (s.piles a).faceUp)
      else s.piles a') =
    (fun a' => if a' = a then
        Pile.afterRunRemoved (t.piles a) (chop (t.piles a).faceUp)
      else t.piles a') := by
  funext a'
  by_cases ha : a' = a
  · rw [ha, ite_eq_left rfl, ite_eq_left rfl, congrFun hp a]
  · rw [ite_eq_right ha, ite_eq_right ha, congrFun hp a']

/-- The players' transfer of the `tabToTab` pile write: the located
removal and the placed run agree under piles equality. -/
private theorem piles_setPile_putRun_transfer {s t : State} {c : Card} {a : Anchor}
    {b : Base} (hp : s.piles = t.piles) :
    ((s.setPile a (Pile.afterRunRemoved (s.piles a) (below c (s.piles a).faceUp))).putRun
      (fromCard c (s.piles a).faceUp) b).piles =
    ((t.setPile a (Pile.afterRunRemoved (t.piles a) (below c (t.piles a).faceUp))).putRun
      (fromCard c (t.piles a).faceUp) b).piles := by
  have hpa : s.piles a = t.piles a := congrFun hp a
  have hset : (s.setPile a (Pile.afterRunRemoved (s.piles a) (below c (s.piles a).faceUp))).piles
      = (t.setPile a (Pile.afterRunRemoved (t.piles a) (below c (t.piles a).faceUp))).piles := by
    rw [setPile_piles_eq, setPile_piles_eq]
    funext a'
    by_cases ha : a' = a
    · rw [ha, ite_eq_left rfl, ite_eq_left rfl, hpa]
    · rw [ite_eq_right ha, ite_eq_right ha, congrFun hp a']
  have hrun : fromCard c (s.piles a).faceUp = fromCard c (t.piles a).faceUp := by
    rw [congrArg Pile.faceUp hpa]
  exact putRun_piles_congr hset hrun

/-- **The (A) replay.**  A winning play from `s` is replayed from the
twin `t` (same foundations, same piles, one card per draw, the same
presented cycle) by induction on the play.  Board moves fire verbatim
(their guards read piles and foundations only; the step shapes carry
the writes and the fields in lockstep).  A copied `draw` rotates both
cycles in lockstep (`draw_cycleOf`).  Before a consuming move the twin
either already sits on the same waste top — the top is the cycle's
last card, and the cycles agree — or starts from a full stock, where
draining the whole cycle (`drain_full`) brings the same card to hand
and restores the same cycle minus the consumed card.  The cycle lists
stay equal at every copied move, so the end state's foundations agree
and the twin wins. -/
private theorem draw1_replay : ∀ (π : List Move) (s t : State),
    s.drawStep = 1 → t.drawStep = 1 → s.found = t.found → s.piles = t.piles →
    cycleOf s = cycleOf t → ∀ w, s.run π = some w → w.isWin = true →
    ∃ π' w', t.run π' = some w' ∧ w'.isWin = true := by
  intro π
  induction π with
  | nil =>
      intro s t hds hdt hf hp hcy w hrun hwin
      refine ⟨[], t, rfl, ?_⟩
      have hisW : s.isWin = t.isWin := isWin_congr hf
      have hw : w = s := (Option.some.inj hrun).symm
      rw [hw, hisW] at hwin
      exact hwin
  | cons m rest ih =>
      intro s t hds hdt hf hp hcy w hrun hwin
      obtain ⟨s₁, hstep, hrest⟩ := State.run_cons hrun
      cases m with
      | draw =>
          have hsd : s.stepDraw = some s₁ := hstep
          have hscy : cycleOf s ≠ [] := draw_ne_of_fires hstep
          have htcy : cycleOf t ≠ [] := by rw [← hcy]; exact hscy
          obtain ⟨t₁, htstep⟩ := draw_step_fires hdt htcy
          have htd : t.stepDraw = some t₁ := htstep
          have hf1 : s₁.found = t₁.found := by
            rw [stepDraw_found hsd, stepDraw_found htd, hf]
          have hp1 : s₁.piles = t₁.piles := by
            rw [stepDraw_piles hsd, stepDraw_piles htd, hp]
          have hc1 : cycleOf s₁ = cycleOf t₁ := by
            rw [draw_cycleOf hds hstep, draw_cycleOf hdt htstep, hcy]
          obtain ⟨π', w', hrun', hwin'⟩ :=
            ih s₁ t₁ (by rw [stepDraw_keep_drawStep hsd, hds])
              (by rw [stepDraw_keep_drawStep htd, hdt]) hf1 hp1 hc1 w hrest hwin
          refine ⟨Move.draw :: π', w', ?_, hwin'⟩
          rw [run_step_cons htstep]
          exact hrun'
      | wasteToFound x =>
          obtain ⟨hg, ws, hwaste, hs1shape⟩ := step_wasteToFound_inv' hstep
          rw [Bool.and_eq_true] at hg
          obtain ⟨-, hnext⟩ := hg
          have hdsn : cycleOf s = (s.stock ++ ws.reverse) ++ [x] :=
            cycleOf_eq_snoc hwaste
          cases htw : t.waste with
          | cons y ys =>
              have hyx : y = x := waste_head_of_cycle hwaste htw hcy
              rw [hyx] at htw
              have hvwi : t.wasteIs x = true := by
                rw [State.wasteIs_cons htw x, decide_eq_true (rfl : x = x)]
              have hvnext : t.nextUp x = true := by
                rw [nextUp_congr x hf] at hnext
                exact hnext
              have htstep : State.step t (Move.wasteToFound x) = some
                  { t.setFound x.suit (t.found x.suit ++ [x]) with waste := ys } := by
                show (if t.wasteIs x && t.nextUp x then
                    match t.waste with
                    | _ :: ws₂ => some
                        { t.setFound x.suit (t.found x.suit ++ [x]) with waste := ws₂ }
                    | [] => none
                  else none) = _
                rw [ite_eq_left (by rw [hvwi, hvnext]; rfl), htw]
              have hf1 : s₁.found =
                  { t.setFound x.suit (t.found x.suit ++ [x]) with waste := ys }.found := by
                rw [hs1shape]
                exact found_append_transfer hf
              have hp1 : s₁.piles =
                  { t.setFound x.suit (t.found x.suit ++ [x]) with waste := ys }.piles := by
                rw [hs1shape]
                show s.piles = t.piles
                exact hp
              have hc1 : cycleOf s₁ =
                  cycleOf { t.setFound x.suit (t.found x.suit ++ [x]) with waste := ys } := by
                rw [hs1shape]
                show s.stock ++ ws.reverse = t.stock ++ ys.reverse
                apply snoc_tail_eq (x := x)
                rw [hdsn.symm,
                  show (t.stock ++ ys.reverse) ++ [x] = cycleOf t from
                    (cycleOf_eq_snoc htw).symm, hcy]
              obtain ⟨π', w', hrun', hwin'⟩ :=
                ih s₁ { t.setFound x.suit (t.found x.suit ++ [x]) with waste := ys }
                  (by rw [hs1shape]; exact hds) hdt hf1 hp1 hc1 w hrest hwin
              refine ⟨Move.wasteToFound x :: π', w', ?_, hwin'⟩
              rw [run_step_cons htstep]
              exact hrun'
          | nil =>
              -- the full-stock twin: drain the whole cycle, then consume
              obtain ⟨vt, hvt⟩ : ∃ vt,
                  vt = { t with stock := [], waste := (cycleOf t).reverse } := ⟨_, rfl⟩
              have hdrain : t.run (List.replicate (cycleOf t).length Move.draw)
                  = some vt := by
                have hst : t.stock = cycleOf t := by
                  show t.stock = t.stock ++ t.waste.reverse
                  rw [htw, show ([] : List Card).reverse = [] from rfl, List.append_nil]
                have h0 := drain_full _ t (cycleOf t) hdt rfl hst
                rw [htw, List.take_length, List.append_nil, List.drop_length] at h0
                rw [← hvt] at h0
                exact h0
              have hd : cycleOf t = (s.stock ++ ws.reverse) ++ [x] := by
                rw [← hcy, hdsn]
              have hland : vt.waste = x :: (s.stock ++ ws.reverse).reverse := by
                rw [hvt]
                show (cycleOf t).reverse = _
                rw [hd, List.reverse_append]
                rfl
              have hvwi : vt.wasteIs x = true := by
                rw [State.wasteIs_cons hland x, decide_eq_true (rfl : x = x)]
              have hvtf : vt.found = t.found := by rw [hvt]
              have hvnext : vt.nextUp x = true := by
                rw [nextUp_congr x hvtf, nextUp_congr x hf.symm]
                exact hnext
              have htstep : State.step vt (Move.wasteToFound x) = some
                  { vt.setFound x.suit (vt.found x.suit ++ [x]) with waste := (s.stock ++ ws.reverse).reverse } := by
                show (if vt.wasteIs x && vt.nextUp x then
                    match vt.waste with
                    | _ :: ws₂ => some { vt.setFound x.suit (vt.found x.suit ++ [x]) with waste := ws₂ }
                    | [] => none
                  else none) = _
                rw [ite_eq_left (by rw [hvwi, hvnext]; rfl), hland]
              have hf1 : s₁.found = { vt.setFound x.suit (vt.found x.suit ++ [x]) with waste := (s.stock ++ ws.reverse).reverse }.found := by
                rw [hs1shape, hvt]
                exact found_append_transfer hf
              have hp1 : s₁.piles = { vt.setFound x.suit (vt.found x.suit ++ [x]) with waste := (s.stock ++ ws.reverse).reverse }.piles := by
                rw [hs1shape, hvt]
                show s.piles = t.piles
                exact hp
              have hc1 : cycleOf s₁ = cycleOf { vt.setFound x.suit (vt.found x.suit ++ [x]) with waste := (s.stock ++ ws.reverse).reverse } := by
                rw [hs1shape, hvt]
                show s.stock ++ ws.reverse
                    = (([] : List Card) ++ (s.stock ++ ws.reverse).reverse).reverse
                rw [List.nil_append, List.reverse_reverse]
              have hdst : { vt.setFound x.suit (vt.found x.suit ++ [x]) with waste := (s.stock ++ ws.reverse).reverse }.drawStep = 1 := by
                rw [hvt]
                show t.drawStep = 1
                exact hdt
              obtain ⟨π', w', hrun', hwin'⟩ :=
                ih s₁ { vt.setFound x.suit (vt.found x.suit ++ [x]) with waste := (s.stock ++ ws.reverse).reverse }
                  (by rw [hs1shape]; exact hds) hdst hf1 hp1 hc1 w hrest hwin
              refine ⟨List.replicate (cycleOf t).length Move.draw
                  ++ Move.wasteToFound x :: π', w', ?_, hwin'⟩
              rw [run_replicate_append _ t vt (Move.wasteToFound x :: π') hdrain,
                run_step_cons htstep]
              exact hrun'
      | wasteToTab x b =>
          obtain ⟨hg, ws, hwaste, hs1shape⟩ := step_wasteToTab_inv' hstep
          rw [Bool.and_eq_true] at hg
          obtain ⟨-, hcp⟩ := hg
          have hdsn : cycleOf s = (s.stock ++ ws.reverse) ++ [x] :=
            cycleOf_eq_snoc hwaste
          cases htw : t.waste with
          | cons y ys =>
              have hyx : y = x := waste_head_of_cycle hwaste htw hcy
              rw [hyx] at htw
              have hvwi : t.wasteIs x = true := by
                rw [State.wasteIs_cons htw x, decide_eq_true (rfl : x = x)]
              have hvcp : t.canPlace x b = true := by
                rw [canPlace_congr x b hp] at hcp
                exact hcp
              have htstep : State.step t (Move.wasteToTab x b) = some
                  { t.putCard x b with waste := ys } := by
                show (if t.wasteIs x && t.canPlace x b then
                    match t.waste with
                    | _ :: ws₂ => some { t.putCard x b with waste := ws₂ }
                    | [] => none
                  else none) = _
                rw [ite_eq_left (by rw [hvwi, hvcp]; rfl), htw]
              have hf1 : s₁.found = { t.putCard x b with waste := ys }.found := by
                rw [hs1shape, putCard_found_keep, putCard_found_keep]
                exact hf
              have hp1 : s₁.piles = { t.putCard x b with waste := ys }.piles := by
                rw [hs1shape]
                exact putCard_piles_congr hp
              have hc1 : cycleOf s₁ = cycleOf { t.putCard x b with waste := ys } := by
                rw [hs1shape]
                show (s.putCard x b).stock ++ ws.reverse
                    = (t.putCard x b).stock ++ ys.reverse
                rw [show (s.putCard x b).stock = s.stock from (putCard_keep).2.1,
                    show (t.putCard x b).stock = t.stock from (putCard_keep).2.1]
                apply snoc_tail_eq (x := x)
                rw [hdsn.symm,
                  show (t.stock ++ ys.reverse) ++ [x] = cycleOf t from
                    (cycleOf_eq_snoc htw).symm, hcy]
              obtain ⟨π', w', hrun', hwin'⟩ :=
                ih s₁ { t.putCard x b with waste := ys }
                  (by
                    rw [hs1shape]
                    show (s.putCard x b).drawStep = 1
                    rw [show (s.putCard x b).drawStep = s.drawStep from (putCard_keep).2.2.2]
                    exact hds)
                  (by
                    show (t.putCard x b).drawStep = 1
                    rw [show (t.putCard x b).drawStep = t.drawStep from (putCard_keep).2.2.2]
                    exact hdt) hf1 hp1 hc1 w hrest hwin
              refine ⟨Move.wasteToTab x b :: π', w', ?_, hwin'⟩
              rw [run_step_cons htstep]
              exact hrun'
          | nil =>
              -- the full-stock twin: drain the whole cycle, then consume
              obtain ⟨vt, hvt⟩ : ∃ vt,
                  vt = { t with stock := [], waste := (cycleOf t).reverse } := ⟨_, rfl⟩
              have hdrain : t.run (List.replicate (cycleOf t).length Move.draw)
                  = some vt := by
                have hst : t.stock = cycleOf t := by
                  show t.stock = t.stock ++ t.waste.reverse
                  rw [htw, show ([] : List Card).reverse = [] from rfl, List.append_nil]
                have h0 := drain_full _ t (cycleOf t) hdt rfl hst
                rw [htw, List.take_length, List.append_nil, List.drop_length] at h0
                rw [← hvt] at h0
                exact h0
              have hd : cycleOf t = (s.stock ++ ws.reverse) ++ [x] := by
                rw [← hcy, hdsn]
              have hland : vt.waste = x :: (s.stock ++ ws.reverse).reverse := by
                rw [hvt]
                show (cycleOf t).reverse = _
                rw [hd, List.reverse_append]
                rfl
              have hvwi : vt.wasteIs x = true := by
                rw [State.wasteIs_cons hland x, decide_eq_true (rfl : x = x)]
              have hvcp : vt.canPlace x b = true := by
                rw [canPlace_congr x b hp] at hcp
                rw [← canPlace_congr x b (by rw [hvt] : vt.piles = t.piles)] at hcp
                exact hcp
              have hvtf : vt.found = t.found := by rw [hvt]
              have hvtp : vt.piles = t.piles := by rw [hvt]
              have htstep : State.step vt (Move.wasteToTab x b) = some
                  { vt.putCard x b with waste := (s.stock ++ ws.reverse).reverse } := by
                show (if vt.wasteIs x && vt.canPlace x b then
                    match vt.waste with
                    | _ :: ws₂ => some { vt.putCard x b with waste := ws₂ }
                    | [] => none
                  else none) = _
                rw [ite_eq_left (by rw [hvwi, hvcp]; rfl), hland]
              have hf1 : s₁.found = { vt.putCard x b with waste := (s.stock ++ ws.reverse).reverse }.found := by
                rw [hs1shape, putCard_found_keep, putCard_found_keep, hvtf]
                exact hf
              have hp1 : s₁.piles = { vt.putCard x b with waste := (s.stock ++ ws.reverse).reverse }.piles := by
                rw [hs1shape]
                exact putCard_piles_congr (hp.trans hvtp.symm)
              have hdst1 : { vt.putCard x b with waste := (s.stock ++ ws.reverse).reverse }.drawStep = 1 := by
                show (vt.putCard x b).drawStep = 1
                rw [show (vt.putCard x b).drawStep = vt.drawStep from (putCard_keep).2.2.2,
                    show vt.drawStep = t.drawStep from by rw [hvt]]
                exact hdt
              have hc1 : cycleOf s₁ = cycleOf { vt.putCard x b with waste := (s.stock ++ ws.reverse).reverse } := by
                rw [hs1shape]
                show (s.putCard x b).stock ++ ws.reverse
                    = (vt.putCard x b).stock ++ ((s.stock ++ ws.reverse).reverse).reverse
                rw [show (s.putCard x b).stock = s.stock from (putCard_keep).2.1,
                    show (vt.putCard x b).stock = vt.stock from (putCard_keep).2.1,
                    show vt.stock = ([] : List Card) from by rw [hvt],
                    List.nil_append, List.reverse_reverse]
              obtain ⟨π', w', hrun', hwin'⟩ :=
                ih s₁ { vt.putCard x b with waste := (s.stock ++ ws.reverse).reverse }
                  (by
                    rw [hs1shape]
                    show (s.putCard x b).drawStep = 1
                    rw [show (s.putCard x b).drawStep = s.drawStep from (putCard_keep).2.2.2]
                    exact hds) hdst1 hf1 hp1 hc1 w hrest hwin
              refine ⟨List.replicate (cycleOf t).length Move.draw
                  ++ Move.wasteToTab x b :: π', w', ?_, hwin'⟩
              rw [run_replicate_append _ t vt (Move.wasteToTab x b :: π') hdrain,
                run_step_cons htstep]
              exact hrun'
      | tabToFound x =>
          obtain ⟨hnext, a, hpa⟩ := tabToFound_fires hstep
          have hs1shape := tabToFound_shape hstep hpa
          have hvnext : t.nextUp x = true := by
            rw [nextUp_congr x hf] at hnext
            exact hnext
          have hvpa : t.pileOfTop x = some a := by
            rw [pileOfTop_congr x hp] at hpa
            exact hpa
          have htstep : State.step t (Move.tabToFound x) = some
              { t.setFound x.suit (t.found x.suit ++ [x]) with
                piles := fun a' => if a' = a then
                    Pile.afterRunRemoved (t.piles a) (chop (t.piles a).faceUp)
                  else t.piles a' } := by
            show (if t.nextUp x then
                match t.pileOfTop x with
                | none => none
                | some a' => some
                    { t.setFound x.suit (t.found x.suit ++ [x]) with
                      piles := fun a'' => if a'' = a' then
                          Pile.afterRunRemoved (t.piles a') (chop (t.piles a').faceUp)
                        else t.piles a'' }
                else none) = _
            rw [ite_eq_left hvnext, hvpa]
          have hf1 : s₁.found =
              { t.setFound x.suit (t.found x.suit ++ [x]) with
                piles := fun a' => if a' = a then
                    Pile.afterRunRemoved (t.piles a) (chop (t.piles a).faceUp)
                  else t.piles a' }.found := by
            rw [hs1shape]
            exact found_append_transfer hf
          have hp1 : s₁.piles =
              { t.setFound x.suit (t.found x.suit ++ [x]) with
                piles := fun a' => if a' = a then
                    Pile.afterRunRemoved (t.piles a) (chop (t.piles a).faceUp)
                  else t.piles a' }.piles := by
            rw [hs1shape]
            exact piles_afterRunRemoved_transfer hp
          have hc1 : cycleOf s₁ =
              cycleOf { t.setFound x.suit (t.found x.suit ++ [x]) with
                piles := fun a' => if a' = a then
                    Pile.afterRunRemoved (t.piles a) (chop (t.piles a).faceUp)
                  else t.piles a' } := by
            rw [hs1shape]
            show s.stock ++ s.waste.reverse = t.stock ++ t.waste.reverse
            exact hcy
          obtain ⟨π', w', hrun', hwin'⟩ :=
            ih s₁ { t.setFound x.suit (t.found x.suit ++ [x]) with
                piles := fun a' => if a' = a then
                    Pile.afterRunRemoved (t.piles a) (chop (t.piles a).faceUp)
                  else t.piles a' }
              (by rw [hs1shape]; exact hds) hdt hf1 hp1 hc1 w hrest hwin
          refine ⟨Move.tabToFound x :: π', w', ?_, hwin'⟩
          rw [run_step_cons htstep]
          exact hrun'
      | foundToTab x b =>
          obtain ⟨c', htop, hcc, hcp, hs1shape⟩ := step_foundToTab_inv' hstep
          have hvtop : t.foundTop x.suit = some c' := by
            rw [foundTop_congr x.suit hf] at htop
            exact htop
          have hvcp : t.canPlace x b = true := by
            rw [canPlace_congr x b hp] at hcp
            exact hcp
          have htstep : State.step t (Move.foundToTab x b) = some
              ((t.setFound x.suit (chop (t.found x.suit))).putCard x b) := by
            show (match t.foundTop x.suit with
                | some c₂ =>
                    if decide (c₂ = x) && t.canPlace x b then
                      some ((t.setFound x.suit (chop (t.found x.suit))).putCard x b)
                    else none
                | none => none) = _
            rw [hvtop]
            show ((if (decide (c' = x) && t.canPlace x b) = true then
                    some ((t.setFound x.suit (chop (t.found x.suit))).putCard x b)
                  else none)) = _
            rw [ite_eq_left (by rw [decide_eq_true hcc, hvcp]; rfl)]
          have hf1 : s₁.found =
              ((t.setFound x.suit (chop (t.found x.suit))).putCard x b).found := by
            rw [hs1shape, putCard_found_keep, putCard_found_keep]
            exact found_chop_transfer hf
          have hp1 : s₁.piles =
              ((t.setFound x.suit (chop (t.found x.suit))).putCard x b).piles := by
            rw [hs1shape]
            exact putCard_piles_congr hp
          have hc1 : cycleOf s₁ =
              cycleOf ((t.setFound x.suit (chop (t.found x.suit))).putCard x b) := by
            rw [hs1shape]
            show ((s.setFound x.suit (chop (s.found x.suit))).putCard x b).stock
                ++ ((s.setFound x.suit (chop (s.found x.suit))).putCard x b).waste.reverse
                = ((t.setFound x.suit (chop (t.found x.suit))).putCard x b).stock
                  ++ ((t.setFound x.suit (chop (t.found x.suit))).putCard x b).waste.reverse
            rw [show ((s.setFound x.suit (chop (s.found x.suit))).putCard x b).stock
                    = s.stock from (putCard_keep).2.1,
                show ((s.setFound x.suit (chop (s.found x.suit))).putCard x b).waste
                    = s.waste from (putCard_keep).2.2.1,
                show ((t.setFound x.suit (chop (t.found x.suit))).putCard x b).stock
                    = t.stock from (putCard_keep).2.1,
                show ((t.setFound x.suit (chop (t.found x.suit))).putCard x b).waste
                    = t.waste from (putCard_keep).2.2.1]
            exact hcy
          obtain ⟨π', w', hrun', hwin'⟩ :=
            ih s₁ ((t.setFound x.suit (chop (t.found x.suit))).putCard x b)
              (by
                rw [hs1shape]
                show ((s.setFound x.suit (chop (s.found x.suit))).putCard x b).drawStep = 1
                rw [show ((s.setFound x.suit (chop (s.found x.suit))).putCard x b).drawStep
                        = s.drawStep from (putCard_keep).2.2.2]
                exact hds)
              (by
                show ((t.setFound x.suit (chop (t.found x.suit))).putCard x b).drawStep = 1
                rw [show ((t.setFound x.suit (chop (t.found x.suit))).putCard x b).drawStep
                        = t.drawStep from (putCard_keep).2.2.2]
                exact hdt) hf1 hp1 hc1 w hrest hwin
          refine ⟨Move.foundToTab x b :: π', w', ?_, hwin'⟩
          rw [run_step_cons htstep]
          exact hrun'
      | tabToTab x b =>
          obtain ⟨a, hhld, hcp, hne, hs1shape⟩ := step_tabToTab_inv' hstep
          have hvhld : t.pileHolding x = some a := by
            rw [pileHolding_congr x hp] at hhld
            exact hhld
          have hvcp : t.canPlace x b = true := by
            rw [canPlace_congr x b hp] at hcp
            exact hcp
          have hfr : fromCard x (t.piles a).faceUp ≠ [] := by
            rw [show fromCard x (t.piles a).faceUp = fromCard x (s.piles a).faceUp from by
                rw [congrArg Pile.faceUp (congrFun hp a)]]
            exact hne
          have htstep : State.step t (Move.tabToTab x b) = some
              ((t.setPile a (Pile.afterRunRemoved (t.piles a) (below x (t.piles a).faceUp))).putRun
                (fromCard x (t.piles a).faceUp) b) := by
            show (match t.pileHolding x with
                | none => none
                | some a' =>
                    if t.canPlace x b then
                      match fromCard x (t.piles a').faceUp with
                      | [] => none
                      | run => some
                          ((t.setPile a' (Pile.afterRunRemoved (t.piles a') (below x (t.piles a').faceUp))).putRun
                            run b)
                    else none) = _
            rw [hvhld]
            show ((if t.canPlace x b = true then
                    match fromCard x (t.piles a).faceUp with
                    | [] => none
                    | run => some
                        ((t.setPile a (Pile.afterRunRemoved (t.piles a) (below x (t.piles a).faceUp))).putRun
                          run b)
                  else none)) = _
            rw [ite_eq_left hvcp]
            cases hfx : fromCard x (t.piles a).faceUp with
            | nil =>
                rw [hfx] at hfr
                exact absurd hfr (by simp)
            | cons r1 r2 =>
                rfl
          have hf1 : s₁.found =
              ((t.setPile a (Pile.afterRunRemoved (t.piles a) (below x (t.piles a).faceUp))).putRun
                (fromCard x (t.piles a).faceUp) b).found := by
            rw [hs1shape, putRun_found_keep, putRun_found_keep]
            exact hf
          have hp1 : s₁.piles =
              ((t.setPile a (Pile.afterRunRemoved (t.piles a) (below x (t.piles a).faceUp))).putRun
                (fromCard x (t.piles a).faceUp) b).piles := by
            rw [hs1shape]
            exact piles_setPile_putRun_transfer hp
          have hc1 : cycleOf s₁ =
              cycleOf ((t.setPile a (Pile.afterRunRemoved (t.piles a) (below x (t.piles a).faceUp))).putRun
                (fromCard x (t.piles a).faceUp) b) := by
            rw [hs1shape]
            show ((s.setPile a (Pile.afterRunRemoved (s.piles a) (below x (s.piles a).faceUp))).putRun
                    (fromCard x (s.piles a).faceUp) b).stock
                ++ ((s.setPile a (Pile.afterRunRemoved (s.piles a) (below x (s.piles a).faceUp))).putRun
                    (fromCard x (s.piles a).faceUp) b).waste.reverse
                = ((t.setPile a (Pile.afterRunRemoved (t.piles a) (below x (t.piles a).faceUp))).putRun
                    (fromCard x (t.piles a).faceUp) b).stock
                  ++ ((t.setPile a (Pile.afterRunRemoved (t.piles a) (below x (t.piles a).faceUp))).putRun
                    (fromCard x (t.piles a).faceUp) b).waste.reverse
            rw [show ((s.setPile a (Pile.afterRunRemoved (s.piles a) (below x (s.piles a).faceUp))).putRun
                      (fromCard x (s.piles a).faceUp) b).stock
                    = s.stock from (putRun_keep).1,
                show ((s.setPile a (Pile.afterRunRemoved (s.piles a) (below x (s.piles a).faceUp))).putRun
                      (fromCard x (s.piles a).faceUp) b).waste
                    = s.waste from (putRun_keep).2.1,
                show ((t.setPile a (Pile.afterRunRemoved (t.piles a) (below x (t.piles a).faceUp))).putRun
                      (fromCard x (t.piles a).faceUp) b).stock
                    = t.stock from (putRun_keep).1,
                show ((t.setPile a (Pile.afterRunRemoved (t.piles a) (below x (t.piles a).faceUp))).putRun
                      (fromCard x (t.piles a).faceUp) b).waste
                    = t.waste from (putRun_keep).2.1]
            exact hcy
          obtain ⟨π', w', hrun', hwin'⟩ :=
            ih s₁ ((t.setPile a (Pile.afterRunRemoved (t.piles a) (below x (t.piles a).faceUp))).putRun
              (fromCard x (t.piles a).faceUp) b)
              (by
                rw [hs1shape]
                show ((s.setPile a (Pile.afterRunRemoved (s.piles a) (below x (s.piles a).faceUp))).putRun
                    (fromCard x (s.piles a).faceUp) b).drawStep = 1
                rw [show ((s.setPile a (Pile.afterRunRemoved (s.piles a) (below x (s.piles a).faceUp))).putRun
                      (fromCard x (s.piles a).faceUp) b).drawStep
                        = s.drawStep from (putRun_keep).2.2]
                exact hds)
              (by
                show ((t.setPile a (Pile.afterRunRemoved (t.piles a) (below x (t.piles a).faceUp))).putRun
                    (fromCard x (t.piles a).faceUp) b).drawStep = 1
                rw [show ((t.setPile a (Pile.afterRunRemoved (t.piles a) (below x (t.piles a).faceUp))).putRun
                      (fromCard x (t.piles a).faceUp) b).drawStep
                        = t.drawStep from (putRun_keep).2.2]
                exact hdt) hf1 hp1 hc1 w hrest hwin
          refine ⟨Move.tabToTab x b :: π', w', ?_, hwin'⟩
          rw [run_step_cons htstep]
          exact hrun'

/-- **(A) The stock-as-reserve lemma, physical form** (B&G §5.4.1's
exception, draw-1): sameCycle twins are the same verdict.

Route (PROVEN, the replay refinement of the Klondike mirror
`draw1_cursor_solvable`): an induction on the winning play, replayed
from the twin under the four-field invariant (equal foundations,
equal piles, step one, equal `cycleOf` — the sameCycle fields plus the
cycled phase).  Board moves fire verbatim — no move but `draw` and the
waste consumers reads the stock or waste, and the guards are
found/piles reads, so the successors' fields transfer through the step
shapes.  A copied `draw` rotates both cycles in lockstep
(`draw_cycleOf`: the phase, how far the cycle has been dealt, is
invisible to the presentation).  A consuming `wasteTo*` fires
directly whenever the twin's waste is nonempty — the waste top is the
presented cycle's last card, and the cycles agree — and from a
full-stock twin after splicing `drain_full`: draining the whole cycle
deals its last card out to hand and restores the same cycle, after
which the consumption leaves both threads on the same stripped cycle.
Foundation transfers close the invariant at every step; `isWin` reads
found only, so the twin's replayed play wins. -/
theorem draw1_sameCycle_sameFate {st st' : State}
    (h1 : st.drawStep = 1) (h2 : st'.drawStep = 1)
    (hsc : sameCycle st st') : sameFate st st' := by
  obtain ⟨hfd, hpl, hds, hcy⟩ := hsc
  refine ⟨fun hwin => ?_, fun hwin => ?_⟩
  · obtain ⟨π, w, hrun, hisw⟩ := hwin
    exact draw1_replay π st st' h1 h2 hfd hpl hcy w hrun hisw
  · obtain ⟨π, w, hrun, hisw⟩ := hwin
    exact draw1_replay π st' st h2 h1 hfd.symm hpl.symm hcy.symm w hrun hisw

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
