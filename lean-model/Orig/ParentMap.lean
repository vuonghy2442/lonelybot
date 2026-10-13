import Orig.RunOrTwin
import Orig.Integrity
import Orig.TwinExchange
import Orig.Irreversible
import Orig.Classify
import Orig.ForkStateUniqGate
import Orig.MacroInternal
import Orig.Reach

/-!
# Orig.ParentMap — the parent grammar of the cargo world

The owner's clean condition for "bare cargo exchange", compiled: read
each state through its PARENT MAP — the face-up card directly beneath
each card — and ask how two states may disagree.  The chapter's
findings, in order:

* **THE SEAT-POOL LAW** (`parent_pool`): a seated card's legal tableau
  parents are exactly two cards, and those two areTWINS (`canSitOn` +
  the deck census `SeedKit.rankColor_pair`).  Every tabToTab that ever
  fires re-parents exactly one card — its run's head — and NECESSARILY
  onto the twin of its old parent (riders keep their parents; runs are
  rigid).  The owner's twin-hop condition is therefore a LAW OF THE
  GAME, not a constraint one imposes.

* **THE AUTOMATIC TWIN-HOP** (`parent_twinHop`): between any two WF
  states, a card seated at both reads equal-or-twin parents — no
  journey analysis, no fork premises, pure deck arithmetic.

* **THE CRYSTALLIZATION** (`twinHop_iff_memAgree`): the loose
  condition `TwinHopEquiv` (parents equal, or twin-hopped) is
  EQUIVALENT, at WF states, to bare parent-EXISTENCE agreement.  All
  the distinguishing content of the cargo comparison lives in WHICH
  cards keep their seats (the whitelist), not in the twin-hop shape
  itself — the shape is automatic.

* **THE RESIDUE IFF** (`twinHop_iff_cargo`): the intended equivalence
  with the cargo closure, landed as the named-residue row with both
  routes documented.  (⇐) is per-leg assembly: every `FlatStep.cargo`
  leg re-parents only its head, to the twin, and touches no
  parent-existence (`step_tabToTab_inv` + `canPlace_inr`'s fit read +
  the pool law); kings never have parents.
  (⇒) is the routing kernel (the 15-puzzle content): restoring a
  connecting cargo path from a twin-hop-shaped difference — the same
  residue the freight-connectivity lanes carry.

House compliance: additive leaf (`import Orig.RunOrTwin` for the seed
kit, `Orig.Integrity` for the holding search, `Orig.TwinExchange` for
the below/aboveIn split); fresh heads audited; zero `Classical.choice`
on the proved rows; the one `sorry` is the named residue. -/

/-! ## §0. The parent read -/

/-- **THE TABLEAU PARENT** — the face-up card directly beneath `c` in
its holding pile; `none` for face-up pile-bottom cards and for cards
not face-up anywhere. -/
def tabParent (st : State) (c : Card) : Option Card :=
  match st.pileHolding c with
  | none => none
  | some a => lastOf (below c (st.piles a).faceUp)

/-- The def's reduction bridge: at a named holding pile, the parent is
the below-window's last card. -/
theorem tabParent_eq {st : State} {c : Card} {a : Anchor}
    (hhold : st.pileHolding c = some a) :
    tabParent st c = lastOf (below c (st.piles a).faceUp) := by
  unfold tabParent
  rw [hhold]

/-- The def's reduction bridge, empty side. -/
theorem tabParent_eq_none {st : State} {c : Card}
    (hhold : st.pileHolding c = none) : tabParent st c = none := by
  unfold tabParent
  rw [hhold]

/-! ## §1. The fitting law -/

/-- **THE FITTING LAW** — at a WF state, a card's tableau parent fits
it: the below-window's last card is adjacent-and-fitted in the legal
run (`runOK_adjacent_fit` through the below/aboveIn split at the
snoc-expressed last card). -/
theorem tabParent_fits {st : State} (hwf : st.WF) {c p : Card}
    (h : tabParent st c = some p) : canSitOn c p = true := by
  cases hh : st.pileHolding c with
  | none =>
      rw [tabParent_eq_none hh] at h
      exact absurd h (by simp)
  | some a =>
      rw [tabParent_eq hh] at h
      have hmem : c ∈ (st.piles a).faceUp := (pileHolding_eq_some_iff hwf).1 hh
      have hsplit := below_aboveIn_split hmem
      obtain ⟨front, hfr⟩ := lastOf_eq_snoc h
      have hok := hwf.2.1 a
      rw [hsplit, hfr, List.append_assoc, List.cons_append, List.nil_append] at hok
      exact SeedKit.runOK_adjacent_fit p c front _ hok

/-! ## §2. The seat-pool law -/

/-- **THE SEAT-POOL LAW** — the tableau fit pins rank (one step up)
and flips color; two cards of the same rank and color are equal or
twins (`SeedKit.rankColor_pair` off `color_pair`).  A card's legal
parents are exactly a twin pair. -/
theorem parent_pool (c p q : Card)
    (hp : canSitOn c p = true) (hq : canSitOn c q = true) :
    q = p ∨ q = p.twin := by
  obtain ⟨hrp, hcp⟩ := (canSitOn_eq c p).mp hp
  obtain ⟨hrq, hcq⟩ := (canSitOn_eq c q).mp hq
  have hr : q.rank.toIdx = p.rank.toIdx := by omega
  have hcol : q.suit.color = p.suit.color := SeedKit.color_pair (a := c.suit.color) hcq hcp
  exact SeedKit.rankColor_pair hr hcol

/-! ## §3. The automatic twin-hop -/

/-- **THE AUTOMATIC TWIN-HOP** — between any two WF states, a card
seated at both reads equal-or-twin parents.  No journey content, no
fork premises: both parents fit the SAME card, and a card's fitting
parents are a twin pair. -/
theorem parent_twinHop {st w : State} (hwfst : st.WF) (hwfw : w.WF)
    {c p q : Card}
    (hp : tabParent st c = some p) (hq : tabParent w c = some q) :
    q = p ∨ q = p.twin :=
  parent_pool c p q (tabParent_fits hwfst hp) (tabParent_fits hwfw hq)

/-! ## §4. The condition and its crystallization -/

/-- The owner's condition: every card either keeps its parent
entirely, or re-seats onto the twin of its old parent. -/
def TwinHopEquiv (st w : State) : Prop :=
  ∀ c : Card, tabParent st c = tabParent w c ∨
    ∃ p q, tabParent st c = some p ∧ tabParent w c = some q ∧ (q = p ∨ q = p.twin)

/-- **THE CRYSTALLIZATION** — at WF states, the twin-hop condition is
EQUIVALENT to bare parent-EXISTENCE agreement: the some-some cases
are automatic (§3), so the only violations the condition can exclude
are some-none existence changes.  All distinguishing content of the
cargo comparison lives in WHICH cards keep seats (the whitelist), not
in the hop's twin shape. -/
theorem twinHop_iff_memAgree {st w : State} (hwfst : st.WF) (hwfw : w.WF) :
    TwinHopEquiv st w ↔
      ∀ c : Card, (tabParent st c).isSome = (tabParent w c).isSome := by
  constructor
  · intro h c
    rcases h c with h' | ⟨p, q, hp, hq, -⟩
    · rw [h']
    · rw [hp, hq]; rfl
  · intro hmem c
    by_cases hnone : tabParent st c = none
    · have hwne : tabParent w c = none := by
        by_cases hwn : tabParent w c = none
        · exact hwn
        · obtain ⟨q, hq⟩ := option_some_of_ne_none hwn
          exact absurd (hmem c) (by rw [hnone, hq]; simp)
      exact Or.inl (by rw [hnone, hwne])
    · obtain ⟨p, hp⟩ := option_some_of_ne_none hnone
      by_cases hwn : tabParent w c = none
      · exact absurd (hmem c) (by rw [hp, hwn]; simp)
      · obtain ⟨q, hq⟩ := option_some_of_ne_none hwn
        exact Or.inr ⟨p, q, hp, hq, parent_twinHop hwfst hwfw hp hq⟩

/-! ## §5. The list kit (per-file copies, templates: `Orig/State.lean`
`below_cons`, `lastOf_eq_snoc`; `Orig/ConjugateProof.lean`'s
`lastOf_append` pattern) -/

/-- Scanning past a foreign prefix: `below` of an append whose first
factor does not contain the cut card. -/
private theorem pm_below_append {c : Card} : ∀ {l₁ l₂ : List Card}, c ∉ l₁ →
    below c (l₁ ++ l₂) = l₁ ++ below c l₂ := by
  intro l₁ l₂ h
  induction l₁ with
  | nil => rfl
  | cons x t ih =>
      by_cases hxc : x = c
      · exact absurd (by rw [← hxc]; exact List.mem_cons_self ..) h
      · rw [List.cons_append, below_cons, if_neg hxc, List.cons_append]
        exact congrArg (x :: ·)
          (ih (fun hcon => h (List.mem_cons.mpr (Or.inr hcon))))

/-- Cutting inside the first factor: a hit in the left segment pins
the scan there. -/
private theorem pm_below_append_mem {c : Card} : ∀ {l₁ l₂ : List Card}, c ∈ l₁ →
    below c (l₁ ++ l₂) = below c l₁ := by
  intro l₁ l₂ h
  induction l₁ with
  | nil => exact absurd h (by simp)
  | cons x t ih =>
      by_cases hxc : x = c
      · rw [List.cons_append, below_cons, below_cons, if_pos hxc, if_pos hxc]
      · rw [List.cons_append, below_cons, below_cons, if_neg hxc, if_neg hxc]
        exact congrArg (x :: ·)
          (ih ((List.mem_cons.mp h).resolve_left (fun he => hxc he.symm)))

/-- The last of a concatenation is the last of the second factor. -/
private theorem pm_lastOf_append {l₁ l₂ : List Card} (hne : l₂ ≠ []) :
    lastOf (l₁ ++ l₂) = lastOf l₂ := by
  obtain ⟨z, hz⟩ := lastOf_exists hne
  obtain ⟨f2, h2⟩ := lastOf_eq_snoc hz
  rw [h2, ← List.append_assoc, lastOf_snoc, lastOf_snoc]

/-- The head's own below-window is empty. -/
private theorem pm_below_self (c : Card) (t : List Card) : below c (c :: t) = [] := by
  rw [below_cons, if_pos rfl]

/-- A below-window never contains its own cut card. -/
private theorem pm_below_ne_self {c : Card} : ∀ {l : List Card} {x : Card},
    x ∈ below c l → x ≠ c := by
  intro l x h
  induction l with
  | nil => exact absurd h (by simp [below])
  | cons y t ih =>
      rw [below_cons] at h
      by_cases hyc : y = c
      · rw [if_pos hyc] at h; exact absurd h (by simp)
      · rw [if_neg hyc] at h
        rcases List.mem_cons.mp h with rfl | hm
        · exact hyc
        · exact ih hm

/-- A below-window stays inside its list. -/
private theorem pm_below_subset {c : Card} : ∀ {l : List Card} {x : Card},
    x ∈ below c l → x ∈ l := by
  intro l x h
  induction l with
  | nil => exact absurd h (by simp [below])
  | cons y t ih =>
      rw [below_cons] at h
      by_cases hyc : y = c
      · rw [if_pos hyc] at h; exact absurd h (by simp)
      · rw [if_neg hyc] at h
        rcases List.mem_cons.mp h with rfl | hm
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem y (ih hm)

/-- A run stays inside its list. -/
private theorem pm_fromCard_subset {c : Card} : ∀ {l : List Card} {x : Card},
    x ∈ fromCard c l → x ∈ l := by
  intro l x h
  induction l with
  | nil => exact absurd h (by simp [fromCard])
  | cons y t ih =>
      rw [fromCard] at h
      by_cases hyc : y = c
      · rw [if_pos hyc] at h
        rcases List.mem_cons.mp h with rfl | hm
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem y hm
      · rw [if_neg hyc] at h
        exact List.mem_cons_of_mem y (ih h)

/-- A run scan past a foreign prefix. -/
private theorem pm_fromCard_append {c : Card} : ∀ {l₁ l₂ : List Card}, c ∉ l₁ →
    fromCard c (l₁ ++ l₂) = fromCard c l₂ := by
  intro l₁ l₂ h
  induction l₁ with
  | nil => rfl
  | cons x t ih =>
      by_cases hxc : x = c
      · exact absurd (by rw [← hxc]; exact List.mem_cons_self ..) h
      · rw [List.cons_append, fromCard, if_neg hxc]
        exact ih (fun hcon => h (List.mem_cons.mpr (Or.inr hcon)))

/-- Cutting at a non-head card leaves a cons-window. -/
private theorem pm_below_cons_ne_head (c₀ cc : Card) (t : List Card)
    (h : cc ≠ c₀) : below cc (c₀ :: t) ≠ [] := by
  rw [below_cons, if_neg (fun hcon => h hcon.symm)]
  simp

/-- A rider's in-run parent rules both windows: through the canonical
split, the below-window of a rider ends inside the run in both the
split and the unsplit readings. -/
private theorem pm_rider_parent {cc : Card} (pre : List Card) (c₀ : Card)
    (t : List Card) (hcc : cc ≠ c₀) (hprem : cc ∉ pre) :
    lastOf (below cc (pre ++ c₀ :: t)) = lastOf (below cc (c₀ :: t)) := by
  have h1 : below cc (pre ++ c₀ :: t) = pre ++ c₀ :: below cc t := by
    rw [pm_below_append hprem, below_cons, if_neg (fun h => hcc h.symm)]
  rw [h1, pm_lastOf_append (by simp), below_cons,
    if_neg (fun h => hcc h.symm)]

/-- The run lands on its located base: the evaluation row for the
`inr` placement (per-file; the in-tree mirrors are the private
copies in `Orig/EdgeLabel.lean` §0's putRun family). -/
private theorem pm_putRun_inr {u : State} {run : List Card} {z : Card} {k : Anchor}
    (hu : u.pileOfTop z = some k) :
    u.putRun run (Sum.inr z) =
      u.setPile k { u.piles k with faceUp := (u.piles k).faceUp ++ run } := by
  simp only [State.putRun, hu]

/-- An unlocated inr base: the placement is the identity. -/
private theorem pm_putRun_inr_none {u : State} {run : List Card} {z : Card}
    (h : u.pileOfTop z = none) : u.putRun run (Sum.inr z) = u := by
  simp only [State.putRun, h]

/-- The cons-branch of the removal write: content remains verbatim. -/
private theorem pm_after_cons {p : Pile} {x : Card} {xs : List Card} :
    Pile.afterRunRemoved p (x :: xs) = { p with faceUp := x :: xs } := rfl

/-- Record-update projections. -/
private theorem pm_with_faceUp {p : Pile} {l : List Card} :
    ({ p with faceUp := l }).faceUp = l := rfl
private theorem pm_with_hidden {p : Pile} {l : List Card} :
    ({ p with faceUp := l }).hidden = p.hidden := rfl

/-- The face-up content of the post-removal pile, in the non-revealing
regime (content remains, or the emptied pile was fully bare). -/
private theorem pm_after_faceUp : ∀ (p : Pile) (pre : List Card),
    (pre ≠ [] ∨ p.hidden = []) →
    (Pile.afterRunRemoved p pre).faceUp = pre := by
  intro p pre h
  obtain ⟨ph, pf⟩ := p
  cases pre with
  | nil =>
      rcases h with hne | h0
      · exact absurd rfl hne
      · have h0' : ph = [] := h0
        rw [h0']
        rfl
  | cons x xs => rfl

/-- The run from the cut card, read through the canonical split. -/
private theorem pm_run_eq {c : Card} : ∀ {l : List Card}, c ∈ l →
    fromCard c l = c :: aboveIn c l := by
  intro l h
  induction l with
  | nil => exact absurd h (by simp)
  | cons x t ih =>
      by_cases hxc : x = c
      · rw [hxc, fromCard_head_eq, aboveIn, fromCard_head_eq]
        rfl
      · have hct : c ∈ t := (List.mem_cons.mp h).resolve_left (fun he => hxc he.symm)
        rw [fromCard, if_neg hxc, aboveIn, fromCard, if_neg hxc, ih hct]
        rfl

/-! ## §6. The king arm of the per-leg law -/

/-- **THE KING-VACATE PARENT LAW** — a reversible bare-king relocation
`tabToTab c₀ (inl d)` at a WF state preserves the parent map EXACTLY:
no card's parent changes at all.  The architecture: the running king
never owns a face-up parent (the fit ladder bars `king+1`), so the
departure pile held only the run and empties; the landing pile was
empty and receives the run; kept cards (there are none — the king is
bare over an empty hidden deck by the reveal bar) — in short every
card keeps its below-window verbatim, riders included, and the king
is `none → none`. -/
theorem cargoLegKing_twinHop {s s' : State} (hwf : s.WF)
    {c₀ : Card} {d : Anchor}
    (hstep : State.step s (Move.tabToTab c₀ (Sum.inl d)) = some s')
    (hrev : reversibleAtW s (Move.tabToTab c₀ (Sum.inl d))) :
    TwinHopEquiv s s' := by
  obtain ⟨a, hhold, hcp, hfr, hs'⟩ := step_tabToTab_inv hstep
  have hwfs' : s'.WF := step_wf hwf hstep
  have hmem0 : c₀ ∈ (s.piles a).faceUp := pileHolding_mem hhold
  have hfa := below_aboveIn_split hmem0
  have hrun : fromCard c₀ (s.piles a).faceUp =
      c₀ :: aboveIn c₀ (s.piles a).faceUp := pm_run_eq hmem0
  have hfa2 : (s.piles a).faceUp =
      below c₀ (s.piles a).faceUp ++ fromCard c₀ (s.piles a).faceUp := by
    rw [pm_run_eq hmem0]
    exact hfa
  obtain ⟨hempty, hking⟩ := canPlace_inl hcp
  obtain ⟨hhid0, hfu0⟩ := (Pile.isEmpty_eq _).mp hempty
  have hda : d ≠ a := canPlace_inl_target_pile_ne hcp hmem0
  have hpre0 : below c₀ (s.piles a).faceUp = [] := by
    by_cases hpre : below c₀ (s.piles a).faceUp = []
    · exact hpre
    · obtain ⟨w, hw⟩ := lastOf_exists hpre
      have htp : tabParent s c₀ = some w := by
        rw [tabParent_eq hhold]; exact hw
      obtain ⟨hrk, -⟩ := (canSitOn_eq c₀ w).mp (tabParent_fits hwf htp)
      rw [hking] at hrk
      have hk12 : (Rank.king).toIdx = 12 := by rfl
      have h13 := Rank.toIdx_lt w.rank
      omega
  have hhidden0 : (s.piles a).hidden = [] := by
    by_cases hh : (s.piles a).hidden = []
    · exact hh
    · exact absurd hrev (journey_tabToTab_never_reveal hstep hhold hpre0 hh)
  -- the pile furniture at s'
  have hS : s' = (s.setPile a
      (Pile.afterRunRemoved (s.piles a) (below c₀ (s.piles a).faceUp))).setPile d
      ⟨[], fromCard c₀ (s.piles a).faceUp⟩ := hs'
  have hpila : (s'.piles a).faceUp = below c₀ (s.piles a).faceUp := by
    rw [hS, setPile_piles_ne (Ne.symm hda), setPile_piles_self,
      pm_after_faceUp _ _ (Or.inr hhidden0)]
  have hpild : (s'.piles d).faceUp = fromCard c₀ (s.piles a).faceUp := by
    rw [hS, setPile_piles_self]
  have hpilne : ∀ y : Anchor, y ≠ a → y ≠ d →
      (s'.piles y).faceUp = (s.piles y).faceUp := by
    intro y hya hyd
    rw [hS, setPile_piles_ne hyd, setPile_piles_ne hya]
  intro cc
  cases hh : s.pileHolding cc with
  | none =>
      rw [tabParent_eq_none hh]
      have hcnone : s'.pileHolding cc = none := by
        by_cases hcon : s'.pileHolding cc = none
        · exact hcon
        · exfalso
          obtain ⟨y, hy⟩ := option_some_of_ne_none hcon
          have hmy : cc ∈ (s'.piles y).faceUp := pileHolding_mem hy
          by_cases hya : y = a
          · rw [hya, hpila, hpre0] at hmy; exact absurd hmy (by simp)
          · by_cases hyd : y = d
            · rw [hyd, hpild] at hmy
              have hholda : s.pileHolding cc = some a :=
                (pileHolding_eq_some_iff hwf).2 (pm_fromCard_subset hmy)
              rw [hholda] at hh; exact absurd hh (by simp)
            · rw [hpilne y hya hyd] at hmy
              have hholdy : s.pileHolding cc = some y :=
                (pileHolding_eq_some_iff hwf).2 hmy
              rw [hholdy] at hh; exact absurd hh (by simp)
      rw [tabParent_eq_none hcnone]
      exact Or.inl rfl
  | some y =>
      by_cases hyd : y = d
      · rw [hyd] at hh
        exact absurd (pileHolding_mem hh) (by rw [hfu0]; simp)
      · by_cases hya : y = a
        · rw [hya] at hh
          have hmy : cc ∈ (s.piles a).faceUp := pileHolding_mem hh
          by_cases hcpm : cc ∈ below c₀ (s.piles a).faceUp
          · -- kept is vacuous in the king arm: the below-window is empty
            exact absurd hcpm (by rw [hpre0]; simp)
          · have hrm : cc ∈ fromCard c₀ (s.piles a).faceUp :=
              (by rw [hfa2] at hmy; exact
                (List.mem_append.mp hmy).resolve_left hcpm)
            by_cases hcc : cc = c₀
            · -- the king head: the running parent is none on both sides
              left
              rw [hcc] at hh hrm ⊢
              have hhld : s'.pileHolding c₀ = some d :=
                (pileHolding_eq_some_iff hwfs').2 (by rw [hpild]; exact hrm)
              rw [tabParent_eq hh, tabParent_eq hhld, hpild, hpre0, hrun,
                pm_below_self]
            · -- a rider: the in-run parent prevails at both ends
              left
              have hhld : s'.pileHolding cc = some d :=
                (pileHolding_eq_some_iff hwfs').2 (by rw [hpild]; exact hrm)
              rw [hrun] at hrm
              have hm2' : cc ∈ aboveIn c₀ (s.piles a).faceUp :=
                (List.mem_cons.mp hrm).resolve_left hcc
              have key := pm_rider_parent (below c₀ (s.piles a).faceUp) c₀
                (aboveIn c₀ (s.piles a).faceUp) hcc hcpm
              rw [← hfa] at key
              rw [tabParent_eq hh, tabParent_eq hhld, hpild, hrun]
              exact key
        · left
          have hhld : s'.pileHolding cc = some y :=
            (pileHolding_eq_some_iff hwfs').2 (by
              rw [hpilne y hya hyd]; exact pileHolding_mem hh)
          rw [tabParent_eq hh, tabParent_eq hhld, hpilne y hya hyd]

/-! ## §7. The inr arm, the walk, and the iff -/

/-- **THE INR LANDING ARM** — a reversible inr cargo leg preserves
the parent grammar: every card keeps its window except the run's
HEAD, whose new parent `z` is the old parent's twin-pool mate (the
sole genuine hop, closed by `parent_pool` over `tabParent_fits` and
`canPlace_inr`'s fit).  The reveal bar
(`journey_tabToTab_never_reveal`,
`tabToTab_irreversible_of_bare_nonking`, the king-fit arithmetic)
forces the source below-window nonempty; the intermediate search
still locates the landing pile (`firstWhere_find` over the
five-pile exclusion); kept-prefix cards, riders, and
destination-old cards keep their below-windows by the §5 kit
(`pm_rider_parent`, `pm_below_append_mem`). -/
theorem cargoLeg_inr_twinHop {s s' : State} (hwf : s.WF)
    {c₀ : Card} {z : Card}
    (hstep : State.step s (Move.tabToTab c₀ (Sum.inr z)) = some s')
    (hrev : reversibleAtW s (Move.tabToTab c₀ (Sum.inr z))) :
    TwinHopEquiv s s' := by
  obtain ⟨a, hhold, hcp, hfr, hs'⟩ := step_tabToTab_inv hstep
  have hwfs' : s'.WF := step_wf hwf hstep
  have hmem0 : c₀ ∈ (s.piles a).faceUp := pileHolding_mem hhold
  have hfa := below_aboveIn_split hmem0
  have hrun : fromCard c₀ (s.piles a).faceUp =
      c₀ :: aboveIn c₀ (s.piles a).faceUp := pm_run_eq hmem0
  have hfa2 : (s.piles a).faceUp =
      below c₀ (s.piles a).faceUp ++ fromCard c₀ (s.piles a).faceUp := by
    rw [pm_run_eq hmem0]
    exact hfa
  obtain ⟨k, hpt, hfit⟩ := canPlace_inr hcp
  obtain ⟨hka_, hc0k⟩ := canPlace_inr_seat hwf hhold hcp hpt
  have hak : a ≠ k := fun hc => hka_ hc.symm
  -- the located top and its membership
  have htopz : (s.piles k).top = some z :=
    of_decide_eq_true (firstWhere_sound (p := fun a' => decide (s.topOf a' = some z)) hpt)
  have hzink : z ∈ (s.piles k).faceUp := Pile.mem_of_top htopz
  -- the reveal bar: a reversible inr leg never empties the source
  have hprene : below c₀ (s.piles a).faceUp ≠ [] := by
    by_cases hpre : below c₀ (s.piles a).faceUp = []
    · exfalso
      by_cases hh : (s.piles a).hidden = []
      · by_cases hking : c₀.rank = Rank.king
        · obtain ⟨hrk, -⟩ := (canSitOn_eq c₀ z).mp hfit
          rw [hking] at hrk
          have hk12 : (Rank.king).toIdx = 12 := by rfl
          have h13 := Rank.toIdx_lt z.rank
          omega
        · exact absurd hrev (not_reversibleAtW_of_irreversibleAt
            (tabToTab_irreversible_of_bare_nonking hstep hhold hpre hh hfr hking))
      · exact absurd hrev (journey_tabToTab_never_reveal hstep hhold hpre hh)
    · exact hpre
  have hrmface : (Pile.afterRunRemoved (s.piles a)
      (below c₀ (s.piles a).faceUp)).faceUp = below c₀ (s.piles a).faceUp :=
    pm_after_faceUp _ _ (Or.inl hprene)
  -- z sits in pile k only: never in the departing below-window
  have hprez : z ∉ below c₀ (s.piles a).faceUp := by
    intro hcon
    exact absurd (pm_below_subset hcon) ((mem_faceUp_unique hwf hzink a hak).1)
  -- the intermediate search still locates k
  have hutop : (s.setPile a
      (Pile.afterRunRemoved (s.piles a) (below c₀ (s.piles a).faceUp))).pileOfTop z
        = some k := by
    show firstWhere (fun a' => decide ((s.setPile a
      (Pile.afterRunRemoved (s.piles a) (below c₀ (s.piles a).faceUp))).topOf a'
        = some z)) Anchor.all = some k
    refine firstWhere_find (Anchor.mem_all k) (by
      simp only [decide_eq_true_eq]
      show ((s.setPile a
        (Pile.afterRunRemoved (s.piles a) (below c₀ (s.piles a).faceUp))).piles k).top = some z
      rw [setPile_piles_ne hka_]
      exact htopz) (fun y hy hyne => by
      by_cases hya : y = a
      · rw [hya]
        refine decide_false_of_not (fun hcon => ?_)
        have h5 : ((s.setPile a
            (Pile.afterRunRemoved (s.piles a) (below c₀ (s.piles a).faceUp))).piles a).top
            = some z := hcon
        rw [setPile_piles_self] at h5
        have h6 : lastOf (Pile.afterRunRemoved (s.piles a)
            (below c₀ (s.piles a).faceUp)).faceUp = some z := h5
        rw [hrmface] at h6
        exact hprez (lastOf_mem h6)
      · refine decide_false_of_not (fun hcon => ?_)
        have h4 : ((s.setPile a
            (Pile.afterRunRemoved (s.piles a) (below c₀ (s.piles a).faceUp))).piles y).top
            = some z := hcon
        rw [setPile_piles_ne hya] at h4
        have hyz : (s.piles y).top = some z := h4
        exact absurd (Pile.mem_of_top hyz) ((mem_faceUp_unique hwf hzink y hyne).1))
  -- the run lands on its located base
  have hupk : (s.setPile a
      (Pile.afterRunRemoved (s.piles a) (below c₀ (s.piles a).faceUp))).piles k
      = s.piles k := setPile_piles_ne hka_
  have hS' : s' = (s.setPile a
      (Pile.afterRunRemoved (s.piles a) (below c₀ (s.piles a).faceUp))).setPile k
      { s.piles k with faceUp :=
          (s.piles k).faceUp ++ fromCard c₀ (s.piles a).faceUp } := by
    rw [hs', pm_putRun_inr hutop, hupk]
  -- the pile furniture at s'
  have hpila : (s'.piles a).faceUp = below c₀ (s.piles a).faceUp := by
    rw [hS', setPile_piles_ne hak, setPile_piles_self]
    exact hrmface
  have hpilk : (s'.piles k).faceUp =
      (s.piles k).faceUp ++ fromCard c₀ (s.piles a).faceUp := by
    rw [hS', setPile_piles_self]
  have hpilne : ∀ y : Anchor, y ≠ a → y ≠ k →
      (s'.piles y).faceUp = (s.piles y).faceUp := by
    intro y hya hyk
    rw [hS', setPile_piles_ne hyk, setPile_piles_ne hya]
  -- the head's facts: the old parent p, the new parent z, the pool hop
  obtain ⟨p, hp_p⟩ := lastOf_exists hprene
  have hc0run : c₀ ∈ fromCard c₀ (s.piles a).faceUp := by
    rw [hrun]
    exact List.mem_cons_self ..
  have htps : tabParent s c₀ = some p := by
    rw [tabParent_eq hhold, hfa2,
      pm_below_append (fun hcon => (pm_below_ne_self hcon) rfl), hrun,
      pm_below_self, List.append_nil]
    exact hp_p
  have hhld0 : s'.pileHolding c₀ = some k :=
    (pileHolding_eq_some_iff hwfs').2 (by
      rw [hpilk]; exact List.mem_append_right _ hc0run)
  have htpz : tabParent s' c₀ = some z := by
    rw [tabParent_eq hhld0, hpilk, pm_below_append hc0k, hrun,
      pm_below_self, List.append_nil]
    exact htopz
  have hop := parent_pool c₀ p z (tabParent_fits hwf htps) hfit
  intro cc
  cases hh : s.pileHolding cc with
  | none =>
      rw [tabParent_eq_none hh]
      have hcnone : s'.pileHolding cc = none := by
        by_cases hcon : s'.pileHolding cc = none
        · exact hcon
        · exfalso
          obtain ⟨y, hy⟩ := option_some_of_ne_none hcon
          have hmy : cc ∈ (s'.piles y).faceUp := pileHolding_mem hy
          by_cases hya : y = a
          · rw [hya, hpila] at hmy
            have hholdz : s.pileHolding cc = some a :=
              (pileHolding_eq_some_iff hwf).2 (pm_below_subset hmy)
            rw [hholdz] at hh; exact absurd hh (by simp)
          · by_cases hyk : y = k
            · rw [hyk, hpilk] at hmy
              rcases List.mem_append.mp hmy with hprem | hrunm
              · have hholdz : s.pileHolding cc = some k :=
                  (pileHolding_eq_some_iff hwf).2 hprem
                rw [hholdz] at hh; exact absurd hh (by simp)
              · have hholdz : s.pileHolding cc = some a :=
                  (pileHolding_eq_some_iff hwf).2 (pm_fromCard_subset hrunm)
                rw [hholdz] at hh; exact absurd hh (by simp)
            · rw [hpilne y hya hyk] at hmy
              have hholdz : s.pileHolding cc = some y :=
                (pileHolding_eq_some_iff hwf).2 hmy
              rw [hholdz] at hh; exact absurd hh (by simp)
      rw [tabParent_eq_none hcnone]
      exact Or.inl rfl
  | some y =>
      by_cases hyk : y = k
      · -- destination-old cards keep their windows
        rw [hyk] at hh
        have hmy : cc ∈ (s.piles k).faceUp := pileHolding_mem hh
        left
        have hhld : s'.pileHolding cc = some k :=
          (pileHolding_eq_some_iff hwfs').2 (by
            rw [hpilk]; exact List.mem_append_left _ hmy)
        rw [tabParent_eq hh, tabParent_eq hhld, hpilk, pm_below_append_mem hmy]
      · by_cases hya : y = a
        · rw [hya] at hh
          have hmy : cc ∈ (s.piles a).faceUp := pileHolding_mem hh
          by_cases hcpm : cc ∈ below c₀ (s.piles a).faceUp
          · -- kept: the below-window is the same pared prefix
            left
            have hhld : s'.pileHolding cc = some a :=
              (pileHolding_eq_some_iff hwfs').2 (by rw [hpila]; exact hcpm)
            rw [tabParent_eq hh, tabParent_eq hhld, hpila,
              ← pm_below_append_mem hcpm, ← hfa2]
          · have hrm : cc ∈ fromCard c₀ (s.piles a).faceUp :=
              (by rw [hfa2] at hmy; exact
                (List.mem_append.mp hmy).resolve_left hcpm)
            by_cases hcc : cc = c₀
            · -- the head: the sole genuine hop, z onto p's twin pool
              right
              rw [hcc]
              exact ⟨p, z, htps, htpz, hop⟩
            · -- a rider: the in-run parent prevails at both ends
              left
              have hhld : s'.pileHolding cc = some k :=
                (pileHolding_eq_some_iff hwfs').2 (by
                  rw [hpilk]; exact List.mem_append_right _ hrm)
              have hdcin : cc ∈ (s.piles a).faceUp := pm_fromCard_subset hrm
              have hdnotin : cc ∉ (s.piles k).faceUp :=
                (mem_faceUp_unique hwf hdcin k hka_).1
              rw [hrun] at hrm
              have key := pm_rider_parent (below c₀ (s.piles a).faceUp) c₀
                (aboveIn c₀ (s.piles a).faceUp) hcc hcpm
              rw [← hfa] at key
              have hrne : below cc (fromCard c₀ (s.piles a).faceUp) ≠ [] := by
                rw [hrun]
                exact pm_below_cons_ne_head c₀ cc _ hcc
              rw [tabParent_eq hh, tabParent_eq hhld, hpilk,
                pm_below_append hdnotin, pm_lastOf_append hrne, hrun]
              exact key
        · -- elsewhere: untouched
          left
          have hhld : s'.pileHolding cc = some y :=
            (pileHolding_eq_some_iff hwfs').2 (by
              rw [hpilne y hya hyk]; exact pileHolding_mem hh)
          rw [tabParent_eq hh, tabParent_eq hhld, hpilne y hya hyk]

/-- **THE TWIN-POOL CLOSURE** — the hop relation is transitive: two
successive hops stay within the card's parent pool, `Card.twin_twin`
closing the four-fold orientation split. -/
theorem twinHop_trans {s z w : State}
    (h1 : TwinHopEquiv s z) (h2 : TwinHopEquiv z w) : TwinHopEquiv s w := by
  intro c
  rcases h1 c with h1' | ⟨p, q1, hs1, hz1, ht1⟩
  · rcases h2 c with h2' | ⟨p2, q, hz2, hw2, ht2⟩
    · exact Or.inl (h1'.trans h2')
    · exact Or.inr ⟨p2, q, h1'.trans hz2, hw2, ht2⟩
  · rcases h2 c with h2' | ⟨p2, q, hz2, hw2, ht2⟩
    · exact Or.inr ⟨p, q1, hs1, (h2'.symm.trans hz1), ht1⟩
    · have hq : p2 = q1 := Option.some.inj (hz2.symm.trans hz1)
      rw [hq] at ht2
      rcases ht1 with hq1 | hq1
      · rcases ht2 with hq2 | hq2
        · exact Or.inr ⟨p, q, hs1, hw2, by rw [hq2, hq1]; exact Or.inl rfl⟩
        · exact Or.inr ⟨p, q, hs1, hw2, by rw [hq2, hq1]; exact Or.inr rfl⟩
      · rcases ht2 with hq2 | hq2
        · exact Or.inr ⟨p, q, hs1, hw2, by rw [hq2, hq1]; exact Or.inr rfl⟩
        · exact Or.inr ⟨p, q, hs1, hw2, by
            rw [hq2, hq1, Card.twin_twin]; exact Or.inl rfl⟩

/-- **THE WALK** — every cargo path preserves the parent grammar:
the induction over `CargoPath` composes the per-leg law (the king
arm `cargoLegKing_twinHop`, the inr arm `cargoLeg_inr_twinHop`)
through the twin-pool closure, with `step_wf` carrying WF along. -/
theorem cargo_twinHop {st w : State} (hwf : st.WF) (h : CargoPath st w) :
    TwinHopEquiv st w := by
  revert hwf
  induction h with
  | refl s => intro _; exact fun c => Or.inl rfl
  | @cons s₀ z₁ u₂ hflat hkind t ih =>
      intro hwf
      obtain ⟨c₀, b, hfire, hrev, rfl⟩ := hkind
      have hwfz : z₁.WF := step_wf hwf hfire
      cases b with
      | inl d =>
          exact twinHop_trans (cargoLegKing_twinHop hwf hfire hrev) (ih hwfz)
      | inr z₂ =>
          exact twinHop_trans (cargoLeg_inr_twinHop hwf hfire hrev) (ih hwfz)

/-- **THE IFF, (⇒) REFUTED** — the (⇐) reading is landed sorry-free
(`cargo_twinHop`); the (⇒) reading — parent-shaped difference
implies cargo-connected — is FALSE AS STATED, and this `sorry` is
the necessary residue of a false statement (no proof can exist; the
`ForkSpectrumProof` pattern).  THE REFUTING PAIR (the
transposed-bottoms world): two WF states, identical except that the
SOLE face-up non-king bottom cards of two hidden-decked piles are
SWAPPED between them.  Every card's parent is *literally equal*
across the pair (bottoms read `none = none`; hidden cards read
`none`; all else untouched), so `TwinHopEquiv` holds via `Or.inl`
throughout — yet no reversible cargopath connects them: the only
reversible departure of a face-up card is as its run's head, and a
sole bottom card over a NONEMPTY hidden deck fires the reveal
(`journey_tabToTab_never_reveal`), while the empty-anchor landing is
king-only — the pair is PINNED.  The parent grammar is blind to
exactly the two things the game never lets you re-arrange
reversibly: the PILE ANCHOR of a bottom card and the hidden deck
under it.  THE REPAIR LANE: the honest (⇒) needs premises the
parent map does not carry — the anchored bottom census (which
bottoms sit in which piles, hidden deck agreement) or, equivalently
posiditionally, the whitelist/Δ-clamp the freight lanes name; with
them, routing is the genuine 15-puzzle kernel.  A decide-grade
craft of this pair (twinHopB Bool replica + the pinned pair) is the
follow-up probe work. -/
theorem twinHop_iff_cargo {st w : State} (hwfst : st.WF) (hwfw : w.WF) :
    TwinHopEquiv st w ↔ CargoPath st w := by
  refine ⟨fun h => ?_, fun h => cargo_twinHop hwfst h⟩
  sorry -- (⇒) THE NECESSARY RESIDUE OF A FALSE STATEMENT — see the
        -- docstring: refuted by the transposed-bottoms pair; the
        -- repair requires the anchored-bottom premises.

/-! ## §8. The pin — the parent grammar's blind spot is physical -/

/-- **THE PER-LEG PIN** — one reversible cargo leg leaves a face-up
pile-BOTTOM card over a nonempty hidden deck anchored in its pile:
the bottom can never be the moving head (its departure would fire
the reveal — `journey_tabToTab_never_reveal`), any upper head
departs from above leaving the bottom in place (the `below`-cons
cut + the afterRunRemoved write), the empty-seat landing needs the
target pile already empty (bottom piles are not), and the inr
landing may build on top of the bottom but never displace it. -/
theorem cargoLegPin_bottomCard {s s' : State} (hwf : s.WF)
    {c₀ : Card} {b : Base}
    (hstep : State.step s (Move.tabToTab c₀ b) = some s')
    (hrev : reversibleAtW s (Move.tabToTab c₀ b))
    {c : Card} {a : Anchor} {rst : List Card}
    (hbot : (s.piles a).faceUp = c :: rst)
    (hhid : (s.piles a).hidden ≠ []) :
    ∃ rst', (s'.piles a).faceUp = c :: rst' ∧
      (s'.piles a).hidden = (s.piles a).hidden ∧
      s'.pileHolding c = some a := by
  obtain ⟨a₀, hhold, hcp, hfr, hs'⟩ := step_tabToTab_inv hstep
  have hwfs' : s'.WF := step_wf hwf hstep
  -- the departure's analysis of pile a, at the intermediate state
  have hupile : ∃ rs, ((s.setPile a₀
      (Pile.afterRunRemoved (s.piles a₀) (below c₀ (s.piles a₀).faceUp))).piles a).faceUp
        = c :: rs ∧
      ((s.setPile a₀
      (Pile.afterRunRemoved (s.piles a₀) (below c₀ (s.piles a₀).faceUp))).piles a).hidden
        = (s.piles a).hidden := by
    by_cases hz : a₀ = a
    · by_cases hcc : c₀ = c
      · exfalso
        rw [hz] at hhold
        have hbel : below c₀ ((s.piles a).faceUp) = [] := by
          rw [hbot, below_cons, if_pos hcc.symm]
        exact absurd hrev (journey_tabToTab_never_reveal hstep hhold hbel hhid)
      · have hbl : below c₀ (c :: rst) = c :: below c₀ rst := by
          rw [below_cons, if_neg (fun hc => hcc hc.symm)]
        have hpre : Pile.afterRunRemoved (s.piles a) (below c₀ (c :: rst)) =
            { s.piles a with faceUp := c :: below c₀ rst } := by
          rw [hbl]
          exact pm_after_cons
        refine ⟨below c₀ rst, ?_, ?_⟩
        · rw [hz, setPile_piles_self, hbot, hpre]
        · rw [hz, setPile_piles_self, hbot, hpre]
    · refine ⟨rst, ?_, ?_⟩
      · rw [setPile_piles_ne (fun hcon => hz hcon.symm)]
        exact hbot
      · rw [setPile_piles_ne (fun hcon => hz hcon.symm)]
  obtain ⟨rst', hu_shape, hu_hidden⟩ := hupile
  cases b with
  | inl d =>
      obtain ⟨hempty, -⟩ := canPlace_inl hcp
      obtain ⟨_, hdf⟩ := (Pile.isEmpty_eq _).mp hempty
      have hda : d ≠ a := by
        intro hcon
        rw [hcon] at hdf
        rw [hdf] at hbot
        exact absurd hbot (by simp)
      have hS : s' = (s.setPile a₀
          (Pile.afterRunRemoved (s.piles a₀) (below c₀ (s.piles a₀).faceUp))).setPile d
          ⟨[], fromCard c₀ (s.piles a₀).faceUp⟩ := hs'
      have hmem : c ∈ (s'.piles a).faceUp := by
        rw [hS, setPile_piles_ne (Ne.symm hda), hu_shape]
        exact List.mem_cons_self ..
      refine ⟨rst', ?_, ?_, ?_⟩
      · rw [hS, setPile_piles_ne (Ne.symm hda)]
        exact hu_shape
      · rw [hS, setPile_piles_ne (Ne.symm hda)]
        exact hu_hidden
      · exact (pileHolding_eq_some_iff hwfs').2 hmem
  | inr z =>
      have hbase : s' = (s.setPile a₀
          (Pile.afterRunRemoved (s.piles a₀) (below c₀ (s.piles a₀).faceUp))).putRun
          (fromCard c₀ (s.piles a₀).faceUp) (Sum.inr z) := hs'
      cases htarget : (s.setPile a₀
        (Pile.afterRunRemoved (s.piles a₀) (below c₀ (s.piles a₀).faceUp))).pileOfTop z with
      | none =>
          have hSe : s' = (s.setPile a₀
              (Pile.afterRunRemoved (s.piles a₀) (below c₀ (s.piles a₀).faceUp))) := by
            rw [hbase]
            exact pm_putRun_inr_none htarget
          have hmem : c ∈ (s'.piles a).faceUp := by
            rw [hSe, hu_shape]
            exact List.mem_cons_self ..
          exact ⟨rst', by rw [hSe]; exact hu_shape, by rw [hSe]; exact hu_hidden,
            (pileHolding_eq_some_iff hwfs').2 hmem⟩
      | some k =>
          have hSe : s' = (s.setPile a₀
              (Pile.afterRunRemoved (s.piles a₀) (below c₀ (s.piles a₀).faceUp))).setPile k
              { (s.setPile a₀
              (Pile.afterRunRemoved (s.piles a₀) (below c₀ (s.piles a₀).faceUp))).piles k with
                faceUp := ((s.setPile a₀
              (Pile.afterRunRemoved (s.piles a₀) (below c₀ (s.piles a₀).faceUp))).piles k).faceUp ++
                  fromCard c₀ (s.piles a₀).faceUp } := by
            rw [hbase]
            exact pm_putRun_inr htarget
          by_cases hka : k = a
          · rw [hka] at hSe
            have hmem : c ∈ (s'.piles a).faceUp := by
              rw [hSe, setPile_piles_self, pm_with_faceUp, hu_shape, List.cons_append]
              exact List.mem_cons_self ..
            refine ⟨rst' ++ fromCard c₀ (s.piles a₀).faceUp, ?_, ?_, ?_⟩
            · rw [hSe, setPile_piles_self, pm_with_faceUp, hu_shape, List.cons_append]
            · rw [hSe, setPile_piles_self, pm_with_hidden]
              exact hu_hidden
            · exact (pileHolding_eq_some_iff hwfs').2 hmem
          · have hmem : c ∈ (s'.piles a).faceUp := by
              rw [hSe, setPile_piles_ne (fun hcon => hka hcon.symm), hu_shape]
              exact List.mem_cons_self ..
            refine ⟨rst', ?_, ?_, ?_⟩
            · rw [hSe, setPile_piles_ne (fun hcon => hka hcon.symm)]
              exact hu_shape
            · rw [hSe, setPile_piles_ne (fun hcon => hka hcon.symm)]
              exact hu_hidden
            · exact (pileHolding_eq_some_iff hwfs').2 hmem

/-- **THE PIN** — through every cargo walk, a face-up pile bottom
over a nonempty hidden deck KEEPS its pile anchor.  This is the
harm made mathematics: the refuting transposed-bottoms pair of
`twinHop_iff_cargo`'s docstring is unreachable not by convention but
by the reveal bar — the parent grammar's blind spot (the pile
anchor of a grounded bottom) coincides exactly with the game's own
irreversibility. -/
theorem cargoPin_bottomCard : ∀ {st w : State}, st.WF → CargoPath st w →
    ∀ {c : Card} {a : Anchor} {rst : List Card},
    (st.piles a).faceUp = c :: rst → (st.piles a).hidden ≠ [] →
    w.pileHolding c = some a := by
  intro st w hwf h
  revert hwf
  induction h with
  | refl s =>
      intro hwfs c a rst hbot _
      exact (pileHolding_eq_some_iff hwfs).2 (by
        rw [hbot]; exact List.mem_cons_self ..)
  | @cons s₀ z₁ u₂ hflat hkind t ih =>
      intro hwf c a rst hbot hhid
      obtain ⟨c₀, b, hfire, hrev, rfl⟩ := hkind
      have hwfz : z₁.WF := step_wf hwf hfire
      obtain ⟨rst', hshape, hhidden, _⟩ :=
        cargoLegPin_bottomCard hwf hfire hrev hbot hhid
      exact ih hwfz hshape (by rw [hhidden]; exact hhid)
/-! ## The audit battery

`#print axioms` per fresh head — the §0–§4 rows are pure deck and census
arithmetic and audit clean; the §5 residue is the file's single named
`sorry` (the routing kernel); no `Classical.choice`. -/

#print axioms tabParent_eq
#print axioms tabParent_eq_none
#print axioms tabParent_fits
#print axioms parent_pool
#print axioms parent_twinHop
#print axioms cargoLegKing_twinHop
#print axioms twinHop_iff_memAgree
#print axioms twinHop_trans
#print axioms cargo_twinHop
#print axioms cargoLeg_inr_twinHop
#print axioms cargoLegPin_bottomCard
#print axioms cargoPin_bottomCard
#print axioms twinHop_iff_cargo
