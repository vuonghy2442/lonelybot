import Orig.MergeWalls
import Orig.TwinExchangeQuotient
import Orig.Integrity
import Orig.Reach

/-!
# Orig — the both-occupied local twin exchange

The row `Orig/TwinExchange.lean` declared open: at a well-formed state
with BOTH twin hosts located face-up in distinct piles and BOTH host
above-regions occupied (a cargo run rising from each seat), the local
twin exchange preserves the verdict —

* `twin_exchange_both_iff` — **the general (both-occupied) exchange
  iff**: `WinFrom st ↔ WinFrom (st.exchangeTwin t)` at the translated
  `twinLicensed` bundle (WF, both hosts located in distinct piles,
  both `aboveIn` slots headed by a fitted cargo, and the braid-family
  clauses — neither twin seat above either cargo).

The proof is the old engine route (`Klondike/TwinQuotient.lean:3109`,
`State.solvable_exchangeTwinCargo_go_gen` — read as a route map only,
every line re-proved physically, zero engine vocabulary):

* **§0–1** kit — the six step-shape readers (private copies,
  dedup-marked against `Orig/TwinExchange.lean`, `Orig/MergeWalls.lean`
  and `Orig/Reach.lean`), the splice cutters on the `[t, z] ++ Sa`
  shapes, and the occurrence bookkeeping.
* **§2** `BothOcc` — the license as a re-seatable bundle (the two
  columns' face-up shapes, the fits, the braid clauses in the landed
  `aboveIn` vocabulary).
* **§3** the σ-representation — the search-congruence family at the
  exchanged state (tops swap, `canPlace` answers identically), so
  every guard reads the same at `st` and `st.exchangeTwin t`.
* **§4** the kill family — the seat lock (no `tabToTab` rooted at a
  cargo head can fire while both seats host), the rooted-exact-cargo
  rank kills, the own-pile landing kill, and the two merge corners
  CONSUMED as the landed walls (`Orig/MergeWalls.lean`) via the
  `go_gen` handler parameters — never re-proved.
* **§5** the transport rows — every move of the winning play commutes
  with the exchange: `(st.exchangeTwin t).step m` lands at
  `(s₁.exchangeTwin t)` with the license re-seated (the hosts
  re-anchor through `State.exchangeTwin_hosts_stable` and the
  integrity search pins), or — exactly the `tabToFound` of a cargo
  head — it is the *freedom breaker*: both hosts stop being occupied,
  the same move transports, and the landed bare row
  (`twin_exchange_bare_iff`) closes the tail.
* **§6** the g-simulation — `exchange_go_gen`, the play induction
  parameterized by a riding invariant `P` and the two merge-corner
  kill bridges, exactly the old assembly's shape; the instance rides
  `P := fun _ => True` and turns the bridges into the two walls.
* **§7** the theorem — forward through the simulation, backward
  through the involution (the license descends through the exchange).
* **§8** the quotient-widening corollary — the general license
  (bare-or-both-occupied), its descent, and the `WinFromQ₃` verdict
  row that extends `ExchOrbit.mk_exchangeTwin`'s content to the
  general license.

Discipline: zero `sorry`, zero `native_decide`, zero
`Classical.choice` (per-lemma audits run externally); axiom targets
`[propext]` / `[propext, Quot.sound]`.  All case splits ride decidable
data (`DecidableEq Card` / `Bool` matches), never classical.
-/

/-! ## §0. Step-shape readers (private, dedup-marked) -/

/-- The draw branch of `State.step`, read raw.  (Dedup-marked against
`Orig/Reach.lean`'s private `step_draw_inv` copy.) -/
private theorem step_draw_eq (st : State) :
    st.step Move.draw = st.stepDraw := rfl

/-- The wasteToFound branch, read raw.  (Dedup-marked as above.) -/
private theorem step_wasteToFound_eq (st : State) (c : Card) :
    st.step (Move.wasteToFound c) =
      (if st.wasteIs c && st.nextUp c then
        match st.waste with
        | _ :: ws => some { st.setFound c.suit (st.found c.suit ++ [c]) with waste := ws }
        | [] => none
      else none) := rfl

/-- The wasteToTab branch, read raw. -/
private theorem step_wasteToTab_eq (st : State) (c : Card) (b : Base) :
    st.step (Move.wasteToTab c b) =
      (if st.wasteIs c && st.canPlace c b then
        match st.waste with
        | _ :: ws => some { st.putCard c b with waste := ws }
        | [] => none
      else none) := rfl

/-- The tabToFound branch, read raw. -/
private theorem step_tabToFound_eq (st : State) (c : Card) :
    st.step (Move.tabToFound c) =
      (if st.nextUp c then
        match st.pileOfTop c with
        | none => none
        | some a =>
            some { st.setFound c.suit (st.found c.suit ++ [c]) with
                     piles := fun a' =>
                       if a' = a then Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
                       else st.piles a' }
      else none) := rfl

/-- The foundToTab branch, read raw. -/
private theorem step_foundToTab_eq (st : State) (c : Card) (b : Base) :
    st.step (Move.foundToTab c b) =
      (match st.foundTop c.suit with
       | some c' =>
           if decide (c' = c) && st.canPlace c b then
             some ((st.setFound c.suit (chop (st.found c.suit))).putCard c b)
           else none
       | none => none) := rfl

/-- The tabToTab branch, read raw.  (Dedup-marked against
`Orig/TwinExchange.lean`'s and `Orig/MergeWalls.lean`'s private
copies.) -/
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

/-- The two branches of `Pile.afterRunRemoved`: the empty prefix flips
the hidden card, the nonempty prefix becomes the whole face-up run. -/
private theorem afterRunRemoved_eq (p : Pile) (pre : List Card) :
    Pile.afterRunRemoved p pre =
      (match pre with
       | [] => Pile.revealTop { p with faceUp := [] }
       | _ => { p with faceUp := pre }) := by
  cases pre with
  | nil => rfl
  | cons w ws => rfl

/-- Prefix-plus-run splice determinacy: the write depends on the pile
only through its hidden card. -/
private theorem afterRunRemoved_congr (ph : List Card) : ∀ (pf : List Card)
    (qh : List Card) (qf : List Card) (pre : List Card), ph = qh →
    Pile.afterRunRemoved ⟨ph, pf⟩ pre = Pile.afterRunRemoved ⟨qh, qf⟩ pre := by
  cases ph with
  | nil =>
      intro pf qh qf pre hh
      cases qh with
      | nil => cases pre <;> rfl
      | cons u us => exact absurd hh (by simp)
  | cons h t =>
      intro pf qh qf pre hh
      cases qh with
      | nil => exact absurd hh (by simp)
      | cons u us =>
          cases pre <;> rw [hh] <;> rfl

private theorem afterRunRemoved_congr_pile {p q : Pile} {pre : List Card}
    (hh : p.hidden = q.hidden) :
    Pile.afterRunRemoved p pre = Pile.afterRunRemoved q pre :=
  afterRunRemoved_congr p.hidden p.faceUp q.hidden q.faceUp pre hh

private theorem putRun_eq_inl (st : State) (run : List Card) (a : Anchor) :
    st.putRun run (Sum.inl a) = st.setPile a ⟨[], run⟩ := rfl

private theorem putCard_eq_inl (st : State) (c : Card) (a : Anchor) :
    st.putCard c (Sum.inl a) = st.setPile a ⟨[], [c]⟩ := rfl

private theorem putRun_eq_inr {st : State} {run : List Card} {z : Card} {k : Anchor}
    (h : st.pileOfTop z = some k) :
    st.putRun run (Sum.inr z) =
      st.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ run } := by
  rw [show st.putRun run (Sum.inr z) =
    st.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ run } from by
    simp only [State.putRun, h]]

private theorem putCard_eq_inr {st : State} {c z : Card} {k : Anchor}
    (h : st.pileOfTop z = some k) :
    st.putCard c (Sum.inr z) =
      st.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ [c] } := by
  rw [show st.putCard c (Sum.inr z) =
    st.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ [c] } from by
    simp only [State.putCard, h]]

/-! ## §1. The list kit (private) -/

/-- `fromCard` cuts inside the head part when the cut card lives
there, keeping everything after the cut card — including the appended
tail — on the run. -/
private theorem fromCard_append_mem {x : Card} (B : List Card) :
    ∀ (R : List Card), x ∈ B → fromCard x (B ++ R) = fromCard x B ++ R := by
  induction B with
  | nil => intro R hmem; cases hmem
  | cons w ts ih =>
      intro R hmem
      by_cases hw : w = x
      · subst hw
        rw [List.cons_append, fromCard_cons_self, fromCard_cons_self, List.cons_append]
      · have hxts : x ∈ ts := (List.mem_cons.mp hmem).resolve_left (fun hc => hw hc.symm)
        rw [List.cons_append, fromCard_cons_ne (ts ++ R) hw,
          fromCard_cons_ne ts hw, ih R hxts]

/-- The generic splice cutter: strictly above the cut card in a splice
`B ++ t :: L` is exactly `L`. -/
private theorem aboveIn_cut_gen {t : Card} {B L : List Card} (hB : t ∉ B) :
    aboveIn t (B ++ t :: L) = L := by
  unfold aboveIn
  rw [fromCard_append_notmem hB, fromCard_cons_self]
  rfl

private theorem below_cut_gen {t : Card} {B L : List Card} (hB : t ∉ B) :
    below t (B ++ t :: L) = B := by
  rw [below_append_notmem hB, below_cons_self, List.append_nil]

/-- A nodup splice does not repeat the spliced card: it occurs
nowhere else in the prefix or the suffix. -/
private theorem nodup_splice_unique {x : Card} (B : List Card) :
    ∀ (M : List Card), (B ++ x :: M).Nodup → ((x ∉ B ∧ x ∉ M) ∧ ∀ y ∈ B, y ∉ M) := by
  induction B with
  | nil =>
      intro M hnd
      have hh := (List.nodup_cons).mp hnd
      constructor
      · constructor
        · intro hmem; cases hmem
        · exact hh.1
      · intro y hy; cases hy
  | cons w ts ih =>
      intro M hnd
      rw [List.cons_append] at hnd
      obtain ⟨hw, hnd'⟩ := (List.nodup_cons).mp hnd
      obtain ⟨⟨hB, hM⟩, hdisj⟩ := ih M hnd'
      constructor
      · constructor
        · intro hmem
          rcases (List.mem_cons.mp hmem) with rfl | hts
          · exact absurd (List.mem_append.mpr
              (Or.inr (List.mem_cons_self ..))) hw
          · exact hB hts
        · exact hM
      · intro y hy hyts
        rcases (List.mem_cons.mp hy) with hyw | hy'
        · subst hyw
          exact absurd (List.mem_append.mpr
            (Or.inr (List.mem_cons.mpr (Or.inr hyts)))) hw
        · exact hdisj y hy' hyts

/-- The last element of an append onto a nonempty right part is the
right part's last. -/
private theorem lastOf_append_right (B : List Card) : ∀ (R : List Card),
    R ≠ [] → lastOf (B ++ R) = lastOf R := by
  induction B with
  | nil => intro R _; rfl
  | cons w ws ih =>
      intro R hR
      have hne : ws ++ R ≠ [] := by
        intro hc
        cases ws with
        | nil => exact hR hc
        | cons u us => cases hc
      cases hs : ws ++ R with
      | nil => rw [hs] at hne; exact absurd rfl hne
      | cons u us =>
          show lastOf (w :: (ws ++ R)) = lastOf R
          rw [hs, show lastOf (w :: u :: us) = lastOf (u :: us) from rfl, ← hs]
          exact ih R hR

private theorem lastOf_append_cons {B : List Card} {x : Card} {L : List Card} :
    lastOf (B ++ x :: L) = lastOf (x :: L) :=
  lastOf_append_right B (x :: L) (by intro hc; cases hc)

/-- A card in the below-prefix of a cut card sits strictly below the
cut, so the cut card sits in the card's `aboveIn`. -/
private theorem mem_aboveIn_of_below {t x : Card} {l : List Card}
    (htl : t ∈ l) (h : x ∈ below t l) : t ∈ aboveIn x l := by
  have hxl : x ∈ l := below_subset_mem h
  have hsplit := below_aboveIn_split htl
  have hne : x ≠ t := fun hc => below_not_mem x l (hc ▸ h)
  have hfx := fromCard_append_mem (below t l) (t :: aboveIn t l) h
  have hmem : t ∈ x :: aboveIn x l := by
    have hh : t ∈ fromCard x (below t l) ++ t :: aboveIn t l :=
      List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
    rw [← hfx] at hh
    rw [← hsplit] at hh
    rw [fromCard_eq_of_mem hxl] at hh
    exact hh
  rcases (List.mem_cons.mp hmem) with heq | hin
  · exact absurd heq (Ne.symm hne)
  · exact hin

/-- An occupied top carries nothing above it: if a pile tops at `t`,
the region strictly above `t` is empty. -/
private theorem aboveIn_eq_nil_of_top {p : Pile} {t : Card}
    (hnd : p.faceUp.Nodup) (htop : p.top = some t) :
    aboveIn t p.faceUp = [] := by
  obtain ⟨front, hf⟩ := (Pile.top_eq_lastOf_iff).mp htop
  have hnd' : (front ++ t :: []).Nodup := by
    have := hnd
    rw [hf] at this
    exact this
  have hfront : t ∉ front := (nodup_splice_unique front _ hnd').1.1
  rw [hf, aboveIn_cut_gen hfront]

/-! ### The splice shapes

The license's face-up shapes are `B ++ [t, z] ++ Sa` splices (parsed
left: `(B ++ [t, z]) ++ Sa`).  These four navigate the parse. -/

private theorem splice_cons {t z : Card} : ∀ (B : List Card) (Sa : List Card),
    B ++ [t, z] ++ Sa = B ++ t :: (z :: Sa) := by
  intro B
  induction B with
  | nil => intro Sa; rfl
  | cons w ws ih =>
      intro Sa
      have hL : ((w :: ws) ++ [t, z]) ++ Sa = w :: ((ws ++ [t, z]) ++ Sa) := rfl
      have hR : (w :: ws) ++ (t :: z :: Sa) = w :: (ws ++ (t :: z :: Sa)) := rfl
      rw [hL, hR, ih Sa]

private theorem splice_head {t z : Card} : ∀ (B : List Card) (Sa : List Card),
    B ++ [t, z] ++ Sa = (B ++ [t]) ++ z :: Sa := by
  intro B
  induction B with
  | nil => intro Sa; rfl
  | cons w ws ih =>
      intro Sa
      have hL : ((w :: ws) ++ [t, z]) ++ Sa = w :: ((ws ++ [t, z]) ++ Sa) := rfl
      have hR : (w :: ws) ++ [t] ++ z :: Sa = w :: ((ws ++ [t]) ++ z :: Sa) := rfl
      rw [hL, hR, ih Sa]

private theorem aboveIn_splice_head {t z : Card} {B Sa : List Card} (hB : t ∉ B) :
    aboveIn t (B ++ [t, z] ++ Sa) = z :: Sa := by
  rw [splice_cons B Sa, aboveIn_cut_gen hB]

private theorem below_splice {t z : Card} {B Sa : List Card} (hB : t ∉ B) :
    below t (B ++ [t, z] ++ Sa) = B := by
  rw [splice_cons B Sa, below_cut_gen hB]

/-- Strictly above the cargo in the splice: `Sa`, given the cargo
does not occur earlier. -/
private theorem aboveIn_splice_cargo {t z : Card} {B Sa : List Card}
    (hzB : z ∉ B ++ [t]) :
    aboveIn z (B ++ [t, z] ++ Sa) = Sa := by
  rw [splice_head B Sa, aboveIn_cut_gen hzB]

/-- The members of a splice's suffix, read through the cargo slot. -/
private theorem mem_of_splice_tail {t z : Card} {B Sa : List Card} {c : Card}
    (hmem : c ∈ Sa) : c ∈ B ++ [t, z] ++ Sa := by
  rw [splice_head B Sa]
  exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hmem))

private theorem mem_splice_host {t z : Card} {B Sa : List Card} :
    t ∈ B ++ [t, z] ++ Sa ∧ z ∈ B ++ [t, z] ++ Sa := by
  constructor
  · rw [splice_head B Sa]
    exact List.mem_append.mpr
      (Or.inl (List.mem_append.mpr (Or.inr (List.mem_cons_self ..))))
  · rw [splice_cons B Sa]
    exact List.mem_append.mpr (Or.inr
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

/-! ## §2. The both-occupied license

`BothOcc` is the translated `twinLicensed` bundle (the old engine
bundle's `hvis hvis' h₀ h₀' hfit hfit' hnb hnb'` in the landed
vocabulary): the two hosts located in distinct piles, each with a
fitted cargo run rising from the seat, and the braid clauses —
neither twin seat above either cargo.  It is the riding license of
the g-simulation: it is re-seated at every step that preserves the
both-occupied shape, and its failure (the freedom events) is the
bare row's territory. -/

/-- The both-occupied exchange license.  The face-up shapes are the
splices `Bα ++ [t, z] ++ Sa` (one pile) and `B' ++ [t.twin, z'] ++ Sa'`
(the other); the fits and the braid clauses are card facts. -/
def BothOcc (st : State) (t : Card) : Prop :=
  ∃ α β : Anchor, ∃ z z' : Card, ∃ Bα B' Sa Sa' : List Card,
    st.pileHolding t = some α ∧
    st.pileHolding t.twin = some β ∧
    α ≠ β ∧
    (st.piles α).faceUp = Bα ++ [t, z] ++ Sa ∧
    (st.piles β).faceUp = B' ++ [t.twin, z'] ++ Sa' ∧
    canSitOn z t = true ∧
    canSitOn z' t.twin = true ∧
    t ∉ aboveIn z ((st.piles α).faceUp) ∧
    t.twin ∉ aboveIn z ((st.piles α).faceUp) ∧
    t ∉ aboveIn z' ((st.piles β).faceUp) ∧
    t.twin ∉ aboveIn z' ((st.piles β).faceUp)

/-- The license from the theorem's premise vocabulary: located hosts,
the `aboveIn` slots headed by a cargo, the fits, the braids. -/
theorem bothOcc_of {st : State} {t z z' : Card} {α β : Anchor} {Sa Sa' : List Card}
    (h₁ : st.pileHolding t = some α) (h₂ : st.pileHolding t.twin = some β) (hne : α ≠ β)
    (h₀ : aboveIn t ((st.piles α).faceUp) = z :: Sa)
    (h₀' : aboveIn t.twin ((st.piles β).faceUp) = z' :: Sa')
    (hfit : canSitOn z t = true) (hfit' : canSitOn z' t.twin = true)
    (hnb : t ∉ aboveIn z ((st.piles α).faceUp) ∧
      t.twin ∉ aboveIn z ((st.piles α).faceUp))
    (hnb' : t ∉ aboveIn z' ((st.piles β).faceUp) ∧
      t.twin ∉ aboveIn z' ((st.piles β).faceUp)) :
    BothOcc st t := by
  refine ⟨α, β, z, z',
    below t ((st.piles α).faceUp), below t.twin ((st.piles β).faceUp),
    Sa, Sa', h₁, h₂, hne, ?_, ?_, hfit, hfit', hnb.1, hnb.2, hnb'.1, hnb'.2⟩
  · have hsplit := below_aboveIn_split (pileHolding_mem h₁)
    rw [h₀] at hsplit
    exact hsplit.trans (splice_cons _ Sa).symm
  · have hsplit := below_aboveIn_split (pileHolding_mem h₂)
    rw [h₀'] at hsplit
    exact hsplit.trans (splice_cons _ Sa').symm

/-- The license pairs symmetrically: asking at the twin twin reads the
swapped bundle. -/
theorem bothOcc_mirror {st : State} {t : Card} (h : BothOcc st t) :
    BothOcc st t.twin := by
  obtain ⟨α, β, z, z', Bα, B', Sa, Sa', h₁, h₂, hne, hsα, hsβ, hfit, hfit',
    hb1, hb2, hb1', hb2'⟩ := h
  refine ⟨β, α, z', z, B', Bα, Sa', Sa, h₂, ?_, Ne.symm hne, hsβ, ?_, hfit',
    ?_, hb2', ?_, hb2, ?_⟩
  · rw [Card.twin_twin]
    exact h₁
  · rw [Card.twin_twin]
    exact hsα
  · rw [show canSitOn z (t.twin).twin = canSitOn z t from by rw [Card.twin_twin]]
    exact hfit
  · rw [Card.twin_twin]
    exact hb1'
  · rw [Card.twin_twin]
    exact hb1

/-- The WF bookkeeping of a host splice: the whole splice is nodup,
and none of the four region cards leaks into the wrong zone. -/
theorem wf_splice_book {st : State} {t z : Card} {α : Anchor} {B Sa : List Card}
    (hwf : st.WF) (hshape : (st.piles α).faceUp = B ++ [t, z] ++ Sa) :
    (B ++ [t, z] ++ Sa).Nodup ∧ t ∉ B ∧ t ∉ Sa ∧ z ∉ B ∧ z ∉ Sa := by
  have hr := hwf.runOK_of α
  rw [hshape] at hr
  have hnd := runOK_nodup hr
  have hz := nodup_splice_unique (B ++ [t]) Sa (by
    rw [← splice_head B Sa]
    exact hnd)
  have ht := nodup_splice_unique B (z :: Sa) (by
    rw [← splice_cons B Sa]
    exact hnd)
  exact ⟨hnd, ht.1.1,
    fun hc => ht.1.2 (List.mem_cons.mpr (Or.inr hc)),
    fun hc => hz.1.1 (List.mem_append.mpr (Or.inl hc)),
    hz.1.2⟩

/-- The license's region memberships, the common derived form. -/
theorem bothOcc_mem {st : State} {t z z' : Card} {α β : Anchor}
    {Bα B' Sa Sa' : List Card}
    (h₁ : st.pileHolding t = some α) (h₂ : st.pileHolding t.twin = some β)
    (hsα : (st.piles α).faceUp = Bα ++ [t, z] ++ Sa)
    (hsβ : (st.piles β).faceUp = B' ++ [t.twin, z'] ++ Sa') :
    t ∈ (st.piles α).faceUp ∧ z ∈ (st.piles α).faceUp ∧
      t.twin ∈ (st.piles β).faceUp ∧ z' ∈ (st.piles β).faceUp := by
  refine ⟨pileHolding_mem h₁, ?_, pileHolding_mem h₂, ?_⟩
  · rw [hsα]
    exact (mem_splice_host (t := t) (z := z) (B := Bα) (Sa := Sa)).2
  · rw [hsβ]
    exact (mem_splice_host (t := t.twin) (z := z') (B := B') (Sa := Sa')).2

/-! ## §3. The σ-representation — the exchanges search congruences

At a licensed state `st`, the exchanged state `st.exchangeTwin t`
writes the two host piles in the mirrored splice form (the hosts stay,
the cargos ride) and leaves every other pile alone.  The search
consequences: emptiness is preserved, tops swap with the piles, so
`pileOfTop` answers with the swapped anchor and `canPlace` reads
identically at the two states. -/

/-- A host splice is never empty. -/
private theorem splice_nonempty {c d : Card} : ∀ (B Sa : List Card),
    B ++ [c, d] ++ Sa ≠ [] := by
  intro B
  cases B with
  | nil =>
      intro Sa hc
      cases Sa with
      | nil => cases hc
      | cons u us => cases hc
  | cons w ws =>
      intro Sa hc
      cases hc

private theorem isEmpty_splice_false {h : List Card} {c d : Card}
    {B Sa : List Card} :
    Pile.isEmpty ⟨h, B ++ [c, d] ++ Sa⟩ = false := by
  cases h with
  | nil =>
      cases B with
      | nil => rfl
      | cons w ws => rfl
  | cons u us => rfl

/-- The written host records in splice form: the host keeps its pile,
its hidden deck, and its below-prefix; the other thread's cargo rides
on top. -/
theorem exch_pile_self_record {st : State} {t z z' : Card} {α β : Anchor}
    {Bα B' Sa Sa' : List Card}
    (hwf : st.WF)
    (h₁ : st.pileHolding t = some α) (h₂ : st.pileHolding t.twin = some β)
    (hne : α ≠ β)
    (hsα : (st.piles α).faceUp = Bα ++ [t, z] ++ Sa)
    (hsβ : (st.piles β).faceUp = B' ++ [t.twin, z'] ++ Sa') :
    (st.exchangeTwin t).piles α =
      ⟨(st.piles α).hidden, Bα ++ [t, z'] ++ Sa'⟩ := by
  obtain ⟨-, httB, -, -⟩ := wf_splice_book hwf hsβ
  have habove' : aboveIn t.twin ((st.piles β).faceUp) = z' :: Sa' := by
    rw [hsβ]
    exact aboveIn_splice_head (t := t.twin) (z := z') httB
  have hbelow : below t ((st.piles α).faceUp) = Bα := by
    rw [hsα]
    exact below_splice (wf_splice_book hwf hsα).2.1
  rw [State.exchangeTwin_pile_self h₁ h₂ hne, hbelow, habove', splice_cons Bα Sa']

theorem exch_pile_other_record {st : State} {t z z' : Card} {α β : Anchor}
    {Bα B' Sa Sa' : List Card}
    (hwf : st.WF)
    (h₁ : st.pileHolding t = some α) (h₂ : st.pileHolding t.twin = some β)
    (hne : α ≠ β)
    (hsα : (st.piles α).faceUp = Bα ++ [t, z] ++ Sa)
    (hsβ : (st.piles β).faceUp = B' ++ [t.twin, z'] ++ Sa') :
    (st.exchangeTwin t).piles β =
      ⟨(st.piles β).hidden, B' ++ [t.twin, z] ++ Sa⟩ := by
  obtain ⟨hnd, htB, -, -, -⟩ := wf_splice_book hwf hsα
  have habove : aboveIn t ((st.piles α).faceUp) = z :: Sa := by
    rw [hsα]
    exact aboveIn_splice_head (t := t) (z := z) htB
  have hbelow : below t.twin ((st.piles β).faceUp) = B' := by
    rw [hsβ]
    exact below_splice (wf_splice_book hwf hsβ).2.1
  rw [State.exchangeTwin_pile_other h₁ h₂ hne, hbelow, habove, splice_cons B' Sa]

/-- Both host searches re-locate the same anchors (the landed
`State.exchangeTwin_hosts_stable`, with the counts from WF). -/
theorem exch_hosts {st : State} {t : Card} {α β : Anchor}
    (hwf : st.WF)
    (h₁ : st.pileHolding t = some α) (h₂ : st.pileHolding t.twin = some β)
    (hne : α ≠ β) :
    (st.exchangeTwin t).pileHolding t = some α ∧
      (st.exchangeTwin t).pileHolding t.twin = some β :=
  State.exchangeTwin_hosts_stable h₁ h₂ hne
    (hwf.cardCount_eq (Card.mem_universe t))
    (hwf.cardCount_eq (Card.mem_universe t.twin))

/-- Emptiness is preserved at every pile. -/
theorem exch_isEmpty_congr {st : State} {t z z' : Card} {α β : Anchor}
    {Bα B' Sa Sa' : List Card}
    (hwf : st.WF)
    (h₁ : st.pileHolding t = some α) (h₂ : st.pileHolding t.twin = some β)
    (hne : α ≠ β)
    (hsα : (st.piles α).faceUp = Bα ++ [t, z] ++ Sa)
    (hsβ : (st.piles β).faceUp = B' ++ [t.twin, z'] ++ Sa')
    (k : Anchor) :
    ((st.exchangeTwin t).piles k).isEmpty = (st.piles k).isEmpty := by
  by_cases hkα : k = α
  · rw [hkα]
    have hσ : (st.exchangeTwin t).piles α = ⟨(st.piles α).hidden, Bα ++ [t, z'] ++ Sa'⟩ :=
      exch_pile_self_record hwf h₁ h₂ hne hsα hsβ
    have hst : (st.piles α).isEmpty = false := by
      cases hd : ((st.piles α).isEmpty) with
      | false => rfl
      | true =>
          obtain ⟨-, hfe⟩ := (Pile.isEmpty_eq _).mp hd
          rw [hsα] at hfe
          exact absurd hfe (splice_nonempty Bα Sa)
    rw [hσ]
    rw [isEmpty_splice_false (c := t) (d := z') (B := Bα) (Sa := Sa')]
    exact hst.symm
  · by_cases hkβ : k = β
    · rw [hkβ]
      have hσ : (st.exchangeTwin t).piles β = ⟨(st.piles β).hidden, B' ++ [t.twin, z] ++ Sa⟩ :=
        exch_pile_other_record hwf h₁ h₂ hne hsα hsβ
      have hst : (st.piles β).isEmpty = false := by
        cases hd : ((st.piles β).isEmpty) with
        | false => rfl
        | true =>
            obtain ⟨-, hfe⟩ := (Pile.isEmpty_eq _).mp hd
            rw [hsβ] at hfe
            exact absurd hfe (splice_nonempty B' Sa')
      rw [hσ]
      rw [isEmpty_splice_false (c := t.twin) (d := z) (B := B') (Sa := Sa)]
      exact hst.symm
    · rw [State.exchangeTwin_pile_ne h₁ h₂ hne hkα hkβ]

/-- The swapped-anchor helper: an anchor swaps with its host twin or
stays put. -/
private def swapAnch (α β : Anchor) (k : Anchor) : Anchor :=
  if k = α then β else if k = β then α else k

/-- The last of a splice is the last of its cargo suffix. -/
private theorem lastOf_splice_tail {c d : Card} {B S : List Card} :
    lastOf (B ++ [c, d] ++ S) = lastOf (d :: S) := by
  rw [splice_head B S, lastOf_append_cons]

/-- A spliced pile tops at its cargo suffix's last. -/
private theorem top_splice_eq {c d : Card} {B S : List Card} {p : Pile}
    (hp : p.faceUp = B ++ [c, d] ++ S) :
    p.top = lastOf (d :: S) := by
  show lastOf p.faceUp = lastOf (d :: S)
  rw [hp, lastOf_splice_tail]

private theorem top_splice_lit (h : List Card) (c d : Card) (B S : List Card) :
    (⟨h, B ++ [c, d] ++ S⟩ : Pile).top = lastOf (d :: S) := by
  show lastOf (B ++ [c, d] ++ S) = lastOf (d :: S)
  rw [lastOf_splice_tail]

private theorem swapAnch_left (α β : Anchor) : swapAnch α β α = β := by
  cases α <;> cases β <;> rfl

private theorem swapAnch_right (α β : Anchor) : swapAnch α β β = α := by
  cases α <;> cases β <;> rfl

private theorem swapAnch_ne {α β k : Anchor} (h₁ : k ≠ α) (h₂ : k ≠ β) :
    swapAnch α β k = k := by
  cases k <;> cases α <;> cases β <;> simp_all [swapAnch]

/-- The two ite collapses, self-made (the core `if_pos`/`if_neg`
shims are deprecated). -/
private theorem ite_true_eq {c : Prop} [inst : Decidable c] (hc : c)
    {γ : Sort u} (t e : γ) : (if c then t else e) = t := by
  cases inst with
  | isTrue _ => rfl
  | isFalse hnc => exact absurd hc hnc

private theorem ite_false_eq {c : Prop} [inst : Decidable c] (hnc : ¬c)
    {γ : Sort u} (t e : γ) : (if c then t else e) = e := by
  cases inst with
  | isTrue hc => exact absurd hc hnc
  | isFalse _ => rfl

/-- The σ top table: pile tops swap between the two host piles and
stay put elsewhere. -/
theorem exch_topOf_swap {st : State} {t z z' : Card} {α β : Anchor}
    {Bα B' Sa Sa' : List Card}
    (hwf : st.WF)
    (h₁ : st.pileHolding t = some α) (h₂ : st.pileHolding t.twin = some β)
    (hne : α ≠ β)
    (hsα : (st.piles α).faceUp = Bα ++ [t, z] ++ Sa)
    (hsβ : (st.piles β).faceUp = B' ++ [t.twin, z'] ++ Sa')
    (k : Anchor) :
    (st.exchangeTwin t).topOf k =
      (if k = α then st.topOf β else if k = β then st.topOf α else st.topOf k) := by
  by_cases hkα : k = α
  · rw [ite_true_eq hkα, hkα]
    show lastOf ((st.exchangeTwin t).piles α).faceUp = st.topOf β
    rw [exch_pile_self_record hwf h₁ h₂ hne hsα hsβ,
      show ((⟨(st.piles α).hidden, Bα ++ [t, z'] ++ Sa'⟩ : Pile)).faceUp
        = Bα ++ [t, z'] ++ Sa' from rfl,
      lastOf_splice_tail]
    show lastOf (z' :: Sa') = lastOf ((st.piles β).faceUp)
    rw [hsβ, lastOf_splice_tail]
  · by_cases hkβ : k = β
    · rw [ite_false_eq hkα, ite_true_eq hkβ, hkβ]
      show lastOf ((st.exchangeTwin t).piles β).faceUp = st.topOf α
      rw [exch_pile_other_record hwf h₁ h₂ hne hsα hsβ,
        show ((⟨(st.piles β).hidden, B' ++ [t.twin, z] ++ Sa⟩ : Pile)).faceUp
          = B' ++ [t.twin, z] ++ Sa from rfl,
        lastOf_splice_tail]
      show lastOf (z :: Sa) = lastOf ((st.piles α).faceUp)
      rw [hsα, lastOf_splice_tail]
    · have hkeq : (st.exchangeTwin t).piles k = st.piles k :=
        State.exchangeTwin_pile_ne h₁ h₂ hne hkα hkβ
      rw [ite_false_eq hkα, ite_false_eq hkβ]
      show ((st.exchangeTwin t).piles k).top = (st.piles k).top
      rw [hkeq]

/-- pileOfTop answers with the swapped anchors. -/
theorem exch_pileOfTop_swap {st : State} {t z z' : Card} {α β : Anchor}
    {Bα B' Sa Sa' : List Card}
    (hwf : st.WF)
    (h₁ : st.pileHolding t = some α) (h₂ : st.pileHolding t.twin = some β)
    (hne : α ≠ β)
    (hsα : (st.piles α).faceUp = Bα ++ [t, z] ++ Sa)
    (hsβ : (st.piles β).faceUp = B' ++ [t.twin, z'] ++ Sa')
    (d : Card) :
    (st.exchangeTwin t).pileOfTop d = (st.pileOfTop d).map (swapAnch α β) := by
  have hσwf : (st.exchangeTwin t).WF := State.wf_exchangeTwin hwf h₁ h₂ hne
  cases hh : st.pileOfTop d with
  | none =>
      show (st.exchangeTwin t).pileOfTop d = none
      cases hh2 : (st.exchangeTwin t).pileOfTop d with
      | none => rfl
      | some j =>
          exfalso
          have hjtop : ((st.exchangeTwin t).piles j).top = some d :=
            (pileOfTop_eq_some_iff hσwf).mp hh2
          by_cases hjα : j = α
          · rw [hjα] at hjtop
            rw [exch_pile_self_record hwf h₁ h₂ hne hsα hsβ, top_splice_lit] at hjtop
            have hβ : (st.piles β).top = some d := by
              rw [top_splice_eq hsβ]
              exact hjtop
            have hcon : st.pileOfTop d = some β :=
              (pileOfTop_eq_some_iff hwf).mpr hβ
            rw [hh] at hcon
            exact absurd hcon (by simp)
          · by_cases hjβ : j = β
            · rw [hjβ] at hjtop
              rw [exch_pile_other_record hwf h₁ h₂ hne hsα hsβ, top_splice_lit] at hjtop
              have hα : (st.piles α).top = some d := by
                rw [top_splice_eq hsα]
                exact hjtop
              have hcon : st.pileOfTop d = some α :=
                (pileOfTop_eq_some_iff hwf).mpr hα
              rw [hh] at hcon
              exact absurd hcon (by simp)
            · rw [State.exchangeTwin_pile_ne h₁ h₂ hne hjα hjβ] at hjtop
              have hcon : st.pileOfTop d = some j :=
                (pileOfTop_eq_some_iff hwf).mpr hjtop
              rw [hh] at hcon
              exact absurd hcon (by simp)
  | some κ =>
      have hκtop : (st.piles κ).top = some d :=
        (pileOfTop_eq_some_iff hwf).mp hh
      show (st.exchangeTwin t).pileOfTop d = some (swapAnch α β κ)
      by_cases hκα : κ = α
      · rw [hκα, swapAnch_left]
        rw [hκα] at hκtop
        have hz : lastOf (z :: Sa) = some d := by
          rw [← top_splice_eq hsα]
          exact hκtop
        have hσtop : ((st.exchangeTwin t).piles β).top = some d := by
          rw [exch_pile_other_record hwf h₁ h₂ hne hsα hsβ, top_splice_lit]
          exact hz
        exact (pileOfTop_eq_some_iff hσwf).mpr hσtop
      · by_cases hκβ : κ = β
        · rw [hκβ, swapAnch_right]
          rw [hκβ] at hκtop
          have hz : lastOf (z' :: Sa') = some d := by
            rw [← top_splice_eq hsβ]
            exact hκtop
          have hσtop : ((st.exchangeTwin t).piles α).top = some d := by
            rw [exch_pile_self_record hwf h₁ h₂ hne hsα hsβ, top_splice_lit]
            exact hz
          exact (pileOfTop_eq_some_iff hσwf).mpr hσtop
        · have hswap : swapAnch α β κ = κ := swapAnch_ne hκα hκβ
          rw [hswap]
          have hσtop : ((st.exchangeTwin t).piles κ).top = some d := by
            rw [State.exchangeTwin_pile_ne h₁ h₂ hne hκα hκβ]
            exact hκtop
          exact (pileOfTop_eq_some_iff hσwf).mpr hσtop

/-- canPlace reads identically at the two states. -/
theorem exch_canPlace_congr {st : State} {t z z' : Card} {α β : Anchor}
    {Bα B' Sa Sa' : List Card}
    (hwf : st.WF)
    (h₁ : st.pileHolding t = some α) (h₂ : st.pileHolding t.twin = some β)
    (hne : α ≠ β)
    (hsα : (st.piles α).faceUp = Bα ++ [t, z] ++ Sa)
    (hsβ : (st.piles β).faceUp = B' ++ [t.twin, z'] ++ Sa')
    (c : Card) (b : Base) :
    (st.exchangeTwin t).canPlace c b = st.canPlace c b := by
  have hempty : ∀ k : Anchor,
      ((st.exchangeTwin t).piles k).isEmpty = (st.piles k).isEmpty :=
    exch_isEmpty_congr hwf h₁ h₂ hne hsα hsβ
  have hpop : ∀ d : Card,
      (st.exchangeTwin t).pileOfTop d = (st.pileOfTop d).map (swapAnch α β) :=
    exch_pileOfTop_swap hwf h₁ h₂ hne hsα hsβ
  cases b with
  | inl a =>
      rw [canPlace_inl_unfold, canPlace_inl_unfold, hempty a]
  | inr d =>
      rw [canPlace_inr_eq, canPlace_inr_eq, hpop d]
      cases hh : st.pileOfTop d with
      | none => rfl
      | some κ =>
          show (match Option.map (swapAnch α β) (some κ) with
                | some _ => canSitOn c d
                | none => false) =
               (match some κ with
                | some _ => canSitOn c d
                | none => false)
          rfl

/-! ## §4. The kill family

The seat lock and its arithmetic: while both seats host, no
`tabToTab` rooted at a cargo head can fire (its only rank-and-color
candidate bases are the two occupied seats, neither a live top), the
hosts are not pile tops, and the within-thread fits rule out the
cross-landings by rank. -/


/-- A card never sits on itself.  (Dedup-marked against
`Orig/TwinExchange.lean`'s private companions.) -/
private theorem canSitOn_self_false (x : Card) : canSitOn x x = false := by
  cases hb : canSitOn x x with
  | false => rfl
  | true =>
      exfalso
      obtain ⟨hr, -⟩ := (canSitOn_eq x x).mp hb
      omega

private theorem rank_ne_king_of_lt {r : Rank} (h : r.toIdx < 12) : r ≠ Rank.king := by
  cases r <;> simp_all [Rank.toIdx]

private theorem color_eq_of_ne_ne {x u v : Card}
    (h1 : x.suit.color ≠ u.suit.color) (h2 : x.suit.color ≠ v.suit.color) :
    u.suit.color = v.suit.color := by
  rcases x with ⟨xs, xr⟩
  rcases u with ⟨us, ur⟩
  rcases v with ⟨vs, vr⟩
  have h1' : ¬ (xs.color = us.color) := h1
  have h2' : ¬ (xs.color = vs.color) := h2
  show us.color = vs.color
  cases xs <;> cases us <;> cases vs <;> first | rfl | simp_all [Suit.color] | rfl

private theorem suit_color_eq {s s' : Suit} (h : s.color = s'.color) :
    s = s' ∨ s = s'.twin := by
  cases s <;> cases s' <;> simp_all [Suit.color, Suit.twin]

/-- Two cards of the same rank and color are the suit-twin pair. -/
private theorem same_rank_same_color {d u : Card}
    (hr : d.rank = u.rank) (hc : d.suit.color = u.suit.color) :
    d = u ∨ d = u.twin := by
  obtain ⟨ds, dr⟩ := d
  obtain ⟨us, ur⟩ := u
  have hc' : ds.color = us.color := hc
  have hr' : dr = ur := hr
  have hs : ds = us ∨ ds = us.twin := suit_color_eq hc'
  rcases hs with rfl | hs
  · exact Or.inl (by rw [hr'])
  · refine Or.inr ?_
    simp only [Card.twin, hs, hr']

/-- The two cargo fits put both cargos one rank under their seats;
twin seats share the rank. -/
theorem twin_fit_ranks {t z z' : Card}
    (hfit : canSitOn z t = true) (hfit' : canSitOn z' t.twin = true) :
    z.rank.toIdx + 1 = t.rank.toIdx ∧
      z'.rank.toIdx + 1 = t.rank.toIdx ∧
      z.rank.toIdx = z'.rank.toIdx := by
  obtain ⟨h1, -⟩ := (canSitOn_eq z t).mp hfit
  obtain ⟨h2, -⟩ := (canSitOn_eq z' t.twin).mp hfit'
  rw [show t.twin.rank.toIdx = t.rank.toIdx from
    congrArg Rank.toIdx (Card.twin_rank t)] at h2
  refine ⟨h1, h2, ?_⟩
  omega

/-- A rank-impossible sit. -/
private theorem canSitOn_false_of {x y : Card}
    (h : ¬ (x.rank.toIdx + 1 = y.rank.toIdx)) :
    canSitOn x y = false := by
  cases hb : canSitOn x y with
  | false => rfl
  | true => exact absurd ((canSitOn_eq x y).mp hb).1 h

/-- The within-thread fit kills: a seat never fits its own cargo or
the other thread's cargo (the fits would cycle the rank); the two
cargos never interfit.  (A cargo DOES fit the other seat — `canSitOn`
is twin-blind in its target — which is exactly why only the two
occupied seats are the cargo's landing candidates.) -/
theorem thread_fit_kills {t z z' : Card}
    (hfit : canSitOn z t = true) (hfit' : canSitOn z' t.twin = true) :
    canSitOn t z = false ∧ canSitOn t z' = false ∧
      canSitOn t.twin z = false ∧ canSitOn t.twin z' = false ∧
      canSitOn z z' = false ∧ canSitOn z' z = false := by
  obtain ⟨h1, h2, h3⟩ := twin_fit_ranks hfit hfit'
  have htt : t.twin.rank.toIdx = t.rank.toIdx :=
    congrArg Rank.toIdx (Card.twin_rank t)
  refine ⟨canSitOn_false_of (by omega), canSitOn_false_of (by omega),
    canSitOn_false_of (by omega), canSitOn_false_of (by omega),
    canSitOn_false_of (by omega), canSitOn_false_of (by omega)⟩

/-- While both seats are occupied, neither host is a pile top. -/
theorem hosts_not_top {st : State} {t z z' : Card} {α β : Anchor}
    {Bα B' Sa Sa' : List Card}
    (hwf : st.WF)
    (h₁ : st.pileHolding t = some α) (h₂ : st.pileHolding t.twin = some β)
    (hsα : (st.piles α).faceUp = Bα ++ [t, z] ++ Sa)
    (hsβ : (st.piles β).faceUp = B' ++ [t.twin, z'] ++ Sa')
    (hfit : canSitOn z t = true) (hfit' : canSitOn z' t.twin = true) :
    st.pileOfTop t = none ∧ st.pileOfTop t.twin = none := by
  constructor
  · cases hh : st.pileOfTop t with
    | none => rfl
    | some k =>
        exfalso
        have hktop : (st.piles k).top = some t := (pileOfTop_eq_some_iff hwf).mp hh
        have htkm : t ∈ (st.piles k).faceUp := Pile.mem_of_top hktop
        have hkα : k = α := by
          by_cases hka : k = α
          · exact hka
          · exact absurd htkm (mem_faceUp_unique hwf (pileHolding_mem h₁) k hka).1
        rw [hkα] at hktop
        rw [top_splice_eq hsα] at hktop
        rcases (List.mem_cons.mp (lastOf_mem hktop)) with heq | hsa
        · exact ne_of_canSitOn hfit heq.symm
        · exact absurd hsa (wf_splice_book hwf hsα).2.2.1
  · cases hh : st.pileOfTop t.twin with
    | none => rfl
    | some k =>
        exfalso
        have hktop : (st.piles k).top = some t.twin := (pileOfTop_eq_some_iff hwf).mp hh
        have htkm : t.twin ∈ (st.piles k).faceUp := Pile.mem_of_top hktop
        have hkβ : k = β := by
          by_cases hkb : k = β
          · exact hkb
          · exact absurd htkm (mem_faceUp_unique hwf (pileHolding_mem h₂) k hkb).1
        rw [hkβ] at hktop
        rw [top_splice_eq hsβ] at hktop
        rcases (List.mem_cons.mp (lastOf_mem hktop)) with heq | hsa
        · exact ne_of_canSitOn hfit' heq.symm
        · exact absurd hsa (wf_splice_book hwf hsβ).2.2.1

/-- The seat lock for one cargo head: a card that fits its occupied
seat cannot be placed anywhere — the anchor arm dies at the king, the
card arm's only rank-and-color candidates are the two occupied seats,
and neither is a live top. -/
private theorem seat_lock_one {st : State} {z t : Card}
    (hfit : canSitOn z t = true)
    (hnp : st.pileOfTop t = none ∧ st.pileOfTop t.twin = none)
    (b : Base) : st.canPlace z b = false := by
  cases b with
  | inl a =>
      obtain ⟨h1, -⟩ := (canSitOn_eq z t).mp hfit
      have hlt : z.rank.toIdx < 12 := by
        have := Rank.toIdx_lt t.rank
        omega
      have hking : z.rank ≠ Rank.king := rank_ne_king_of_lt hlt
      cases hb : st.canPlace z (Sum.inl a) with
      | false => rfl
      | true =>
          exfalso
          rw [canPlace_inl_unfold] at hb
          cases hdd : decide (z.rank = Rank.king) with
          | false => rw [hdd] at hb; simp at hb
          | true => exact hking (of_decide_eq_true hdd)
  | inr d =>
      show (match st.pileOfTop d with
            | some _ => canSitOn z d
            | none => false) = false
      cases hd : st.pileOfTop d with
      | none => rfl
      | some k =>
          show canSitOn z d = false
          cases hb : canSitOn z d with
          | false => rfl
          | true =>
              exfalso
              obtain ⟨hr1, hc1⟩ := (canSitOn_eq z t).mp hfit
              obtain ⟨hr2, hc2⟩ := (canSitOn_eq z d).mp hb
              have hc : d.suit.color = t.suit.color := color_eq_of_ne_ne hc2 hc1
              have hdt : d = t ∨ d = t.twin :=
                same_rank_same_color (Rank.toIdx_inj (by omega)) hc
              rcases hdt with rfl | rfl
              · rw [hnp.1] at hd
                exact absurd hd (by simp)
              · rw [hnp.2] at hd
                exact absurd hd (by simp)

/-- THE SEAT LOCK: at the both-occupied license, no `tabToTab` rooted
at a cargo head can fire — `canPlace` of the head is false on every
base. -/
theorem seat_lock {st : State} {t z z' : Card} {α β : Anchor}
    {Bα B' Sa Sa' : List Card} (b : Base)
    (hwf : st.WF)
    (h₁ : st.pileHolding t = some α) (h₂ : st.pileHolding t.twin = some β)
    (hsα : (st.piles α).faceUp = Bα ++ [t, z] ++ Sa)
    (hsβ : (st.piles β).faceUp = B' ++ [t.twin, z'] ++ Sa')
    (hfit : canSitOn z t = true) (hfit' : canSitOn z' t.twin = true) :
    st.canPlace z b = false ∧ st.canPlace z' b = false := by
  obtain ⟨hnp1, hnp2⟩ := hosts_not_top hwf h₁ h₂ hsα hsβ hfit hfit'
  refine ⟨seat_lock_one hfit ⟨hnp1, hnp2⟩ b, seat_lock_one hfit' ?_ b⟩
  rw [Card.twin_twin]
  exact ⟨hnp2, hnp1⟩

/-! ## §5. The transport rows

Every move of the winning play commutes with the exchange: the same
move fires at `st.exchangeTwin t` and lands at `s₁.exchangeTwin t`,
with the license re-seated — or it is the freedom breaker (the
`tabToFound` of a cargo head), where the same move transports and the
landed bare row closes the tail.

§5.0 is the congruence ministry: the searches read the piles only, so
they agree on pile-equivalent states, and the exchange itself does
too. -/

/-- The holding search reads only the piles. -/
private theorem pileHolding_congr {st s' : State} {c : Card}
    (hp : s'.piles = st.piles) :
    s'.pileHolding c = st.pileHolding c := by
  show (firstWhere (fun a => decide (c ∈ (s'.piles a).faceUp)) Anchor.all) = _
  rw [hp]
  rfl

/-- The top search reads only the piles. -/
private theorem pileHolding_all_congr {st s' : State}
    (hp : s'.piles = st.piles) :
    ∀ c : Card, s'.pileHolding c = st.pileHolding c :=
  fun _ => pileHolding_congr hp

/-- The exchange writes piles and reads piles: pile-equivalent states
exchange to pile-equivalent states. -/
private theorem exch_piles_congr {st s' : State} {t : Card}
    (hp : s'.piles = st.piles) :
    (s'.exchangeTwin t).piles = (st.exchangeTwin t).piles := by
  have hh1 : s'.pileHolding t = st.pileHolding t := pileHolding_congr hp
  have hh2 : s'.pileHolding t.twin = st.pileHolding t.twin := pileHolding_congr hp
  cases h1 : st.pileHolding t with
  | none =>
      rw [State.exchangeTwin_eq_self_of_missing (Or.inl (hh1.trans h1)),
          State.exchangeTwin_eq_self_of_missing (Or.inl h1), hp]
  | some a =>
      cases h2 : st.pileHolding t.twin with
      | none =>
          rw [State.exchangeTwin_eq_self_of_missing (Or.inr (hh2.trans h2)),
              State.exchangeTwin_eq_self_of_missing (Or.inr h2), hp]
      | some a' =>
          by_cases hE : a = a'
          · rw [State.exchangeTwin_eq_self_of_same (hh1.trans h1) (by rw [hh2, hE]; exact h2),
              State.exchangeTwin_eq_self_of_same h1 (by rw [hE]; exact h2)]
            exact hp
          · rw [State.exchangeTwin_eq_of_located (hh1.trans h1)
              (hh2.trans h2) hE,
              State.exchangeTwin_eq_of_located h1 h2 hE]
            funext k
            show (if k = a then ⟨(s'.piles a).hidden,
                    below t ((s'.piles a).faceUp) ++
                      t :: aboveIn t.twin ((s'.piles a').faceUp)⟩
                  else if k = a' then ⟨((s'.piles a').hidden),
                    below t.twin ((s'.piles a').faceUp) ++
                      t.twin :: aboveIn t ((s'.piles a).faceUp)⟩
                  else s'.piles k) =
              (if k = a then ⟨(st.piles a).hidden,
                    below t ((st.piles a).faceUp) ++
                      t :: aboveIn t.twin ((st.piles a').faceUp)⟩
              else if k = a' then ⟨(st.piles a').hidden,
                    below t.twin ((st.piles a').faceUp) ++
                      t.twin :: aboveIn t ((st.piles a).faceUp)⟩
              else st.piles k)
            by_cases hka : k = a
            · rw [ite_true_eq hka, ite_true_eq hka, hp]
            · by_cases hka' : k = a'
              · rw [ite_false_eq hka, ite_true_eq hka', ite_false_eq hka, ite_true_eq hka', hp]
              · rw [ite_false_eq hka, ite_false_eq hka', ite_false_eq hka, ite_false_eq hka', hp]

/-- The five-field table of a pile-equivalent state's exchange. -/
private theorem exch_fields_congr {st s' : State} {t : Card}
    (hp : s'.piles = st.piles) (hfound : s'.found = st.found)
    (hstock : s'.stock = st.stock) (hwaste : s'.waste = st.waste)
    (hdraw : s'.drawStep = st.drawStep) :
    (s'.exchangeTwin t).piles = (st.exchangeTwin t).piles ∧
      (s'.exchangeTwin t).found = (st.exchangeTwin t).found ∧
      (s'.exchangeTwin t).stock = (st.exchangeTwin t).stock ∧
      (s'.exchangeTwin t).waste = (st.exchangeTwin t).waste ∧
      (s'.exchangeTwin t).drawStep = (st.exchangeTwin t).drawStep :=
  ⟨exch_piles_congr hp,
    by rw [State.exchangeTwin_found, State.exchangeTwin_found, hfound],
    by rw [State.exchangeTwin_stock, State.exchangeTwin_stock, hstock],
    by rw [State.exchangeTwin_waste, State.exchangeTwin_waste, hwaste],
    by rw [State.exchangeTwin_drawStep, State.exchangeTwin_drawStep, hdraw]⟩

/-- The braid clauses hold at any licensed shape with WF: the braid
family is WF-automatic. -/
theorem braid_splice {st : State} {t z z' : Card} {α β : Anchor}
    {Bα B' Sa Sa' : List Card}
    (hwf : st.WF)
    (h₁ : st.pileHolding t = some α) (h₂ : st.pileHolding t.twin = some β)
    (hne : α ≠ β)
    (hsα : (st.piles α).faceUp = Bα ++ [t, z] ++ Sa)
    (hsβ : (st.piles β).faceUp = B' ++ [t.twin, z'] ++ Sa')
    (hfit : canSitOn z t = true) (hfit' : canSitOn z' t.twin = true) :
    t ∉ aboveIn z ((st.piles α).faceUp) ∧
      t.twin ∉ aboveIn z ((st.piles α).faceUp) ∧
      t ∉ aboveIn z' ((st.piles β).faceUp) ∧
      t.twin ∉ aboveIn z' ((st.piles β).faceUp) := by
  obtain ⟨hnd, htB, htS, hzB, hzS⟩ := wf_splice_book hwf hsα
  obtain ⟨-, htB', htS', hzB', hzS'⟩ := wf_splice_book hwf hsβ
  have hab : aboveIn z ((st.piles α).faceUp) = Sa := by
    rw [hsα]
    refine aboveIn_splice_cargo ?_
    intro hc
    rcases (List.mem_append.mp hc) with h | h
    · exact hzB h
    · rcases (List.mem_cons.mp h) with heq | hnil
      · exact ne_of_canSitOn hfit heq
      · exact absurd hnil (by simp)
  have hab' : aboveIn z' ((st.piles β).faceUp) = Sa' := by
    rw [hsβ]
    refine aboveIn_splice_cargo ?_
    intro hc
    rcases (List.mem_append.mp hc) with h | h
    · exact hzB' h
    · rcases (List.mem_cons.mp h) with heq | hnil
      · exact ne_of_canSitOn hfit' heq
      · exact absurd hnil (by simp)
  refine ⟨fun hc => htS (hab ▸ hc), ?_, ?_, fun hc => htS' (hab' ▸ hc)⟩
  · intro hc
    have hmem : t.twin ∈ Bα ++ [t, z] ++ Sa :=
      mem_of_splice_tail (t := t) (z := z) (hab ▸ hc)
    have hm : t.twin ∈ (st.piles α).faceUp := by
      rw [hsα]
      exact hmem
    exact (mem_faceUp_unique hwf (pileHolding_mem h₂) α hne).1 hm
  · intro hc
    have hmem : t ∈ B' ++ [t.twin, z'] ++ Sa' :=
      mem_of_splice_tail (t := t.twin) (z := z') (hab' ▸ hc)
    have hm : t ∈ (st.piles β).faceUp := by
      rw [hsβ]
      exact hmem
    exact (mem_faceUp_unique hwf (pileHolding_mem h₁) β (Ne.symm hne)).1 hm

/-! ### §5.1 The draw stages -/

/-- The recycle only rewrites stock and waste. -/
private theorem recycle_facts (st : State) :
    (State.recycle st).piles = st.piles ∧ (State.recycle st).found = st.found ∧
      (State.recycle st).drawStep = st.drawStep ∧
      ((st.stock ≠ [] ∧ State.recycle st = st) ∨
        (st.stock = [] ∧ st.waste = [] ∧ State.recycle st = st) ∨
        (st.stock = [] ∧
          State.recycle st = { st with stock := st.waste.reverse, waste := [] })) := by
  cases hss : st.stock with
  | nil =>
      cases hws : st.waste with
      | nil =>
          have hr : State.recycle st = st := by simp [State.recycle, hss, hws]
          rw [hr]
          exact ⟨rfl, rfl, rfl, Or.inr (Or.inl ⟨by simp, by simp, rfl⟩)⟩
      | cons w ws =>
          have hr : State.recycle st =
              { st with stock := (w :: ws).reverse, waste := [] } := by
            simp [State.recycle, hss, hws]
          rw [hr]
          exact ⟨rfl, rfl, rfl, Or.inr (Or.inr ⟨by simp, rfl⟩)⟩
  | cons s ss =>
      have hr : State.recycle st = st := by simp [State.recycle, hss]
      rw [hr]
      exact ⟨rfl, rfl, rfl, Or.inl ⟨by simp, rfl⟩⟩

/-- The deal only rewrites stock and waste. -/
private theorem dealStock_facts (st : State) :
    (st.stock = [] ∧ State.dealStock st = none) ∨
      (st.stock ≠ [] ∧ ∃ ds : State, State.dealStock st = some ds ∧
        ds.piles = st.piles ∧ ds.found = st.found ∧ ds.drawStep = st.drawStep) := by
  cases hss : st.stock with
  | nil => exact Or.inl ⟨by simp, by simp [State.dealStock, hss]⟩
  | cons s ss =>
      have hne : (s :: ss) ≠ [] := fun hc => by cases hc
      have hR : State.dealStock st = some { st with stock := (State.dealUpTo st.drawStep (s :: ss)).snd, waste := (State.dealUpTo st.drawStep (s :: ss)).fst.reverse ++ st.waste } := by
        simp [State.dealStock, hss]
      exact Or.inr ⟨hne, ⟨_, hR, rfl, rfl, rfl⟩⟩

/-- What the draw may change: piles, found, and the draw step never
move. -/
private theorem draw_facts {st s₁ : State} (hstep : st.stepDraw = some s₁) :
    s₁.piles = st.piles ∧ s₁.found = st.found ∧ s₁.drawStep = st.drawStep := by
  rw [show st.stepDraw = State.dealStock (State.recycle st) from rfl] at hstep
  obtain ⟨rp, rf, rd, hrec⟩ := recycle_facts st
  rcases hrec with ⟨-, hre⟩ | ⟨hcs, -, hre⟩ | ⟨_, _⟩
  · rw [hre] at hstep
    rcases dealStock_facts st with ⟨hc, -⟩ | ⟨-, ds, hds, hp, hf, hd⟩
    · have hnn : State.dealStock st = none := by simp [State.dealStock, hc]
      rw [hnn] at hstep
      exact absurd hstep (by simp)
    · have heq : s₁ = ds := Option.some.inj (hstep.symm.trans hds)
      rw [heq]
      exact ⟨hp, hf, hd⟩
  · rw [hre] at hstep
    rcases dealStock_facts st with ⟨hc, -⟩ | ⟨hne', -⟩
    · have hnn : State.dealStock st = none := by simp [State.dealStock, hc]
      rw [hnn] at hstep
      exact absurd hstep (by simp)
    · exact absurd hcs hne'
  · rcases dealStock_facts (State.recycle st) with ⟨hc, -⟩ | ⟨-, ds, hds, hp, hf, hd⟩
    · have hnn : State.dealStock (State.recycle st) = none := by simp [State.dealStock, hc]
      rw [hnn] at hstep
      exact absurd hstep (by simp)
    · have heq : s₁ = ds := Option.some.inj (hstep.symm.trans hds)
      rw [heq]
      exact ⟨hp.trans rp, hf.trans rf, hd.trans rd⟩

/-- The draw is field-determined: two states that agree on stock,
waste and draw step draw to outcomes that keep their own piles,
found and draw step and share the dealt stock and waste. -/
private theorem stepDraw_rel {u v u₁ : State}
    (hstock : v.stock = u.stock) (hwaste : v.waste = u.waste)
    (hdraw : v.drawStep = u.drawStep)
    (hu : u.stepDraw = some u₁) :
    ∃ v₁ : State, v.stepDraw = some v₁ ∧
      v₁.piles = v.piles ∧ u₁.piles = u.piles ∧ v₁.found = v.found ∧
      u₁.found = u.found ∧ v₁.drawStep = v.drawStep ∧ u₁.drawStep = u.drawStep ∧
      v₁.stock = u₁.stock ∧ v₁.waste = u₁.waste := by
  cases hus : u.stock with
  | nil =>
      cases huw : u.waste with
      | nil =>
          exfalso
          have hdead : u.stepDraw = none := by
            simp [State.stepDraw, State.dealStock, State.recycle, hus, huw]
          rw [hdead] at hu
          exact absurd hu (by simp)
      | cons w ws =>
          have hvs : v.stock = [] := hstock.trans hus
          have hvw : v.waste = w :: ws := hwaste.trans huw
          have hru : State.recycle u = { u with stock := (w :: ws).reverse, waste := [] } := by
            simp [State.recycle, hus, huw]
          have hrv : State.recycle v = { v with stock := (w :: ws).reverse, waste := [] } := by
            simp [State.recycle, hvs, hvw]
          rw [show u.stepDraw = State.dealStock (State.recycle u) from rfl, hru] at hu
          cases hrr : (w :: ws).reverse with
          | nil =>
              have hd : State.dealStock { u with stock := (w :: ws).reverse, waste := [] } = none := by
                rw [hrr]
                rfl
              rw [hd] at hu
              exact absurd hu (by simp)
          | cons r rs =>
              rw [hrr] at hu hru hrv
              have hfU : State.dealStock { u with stock := (r :: rs), waste := [] } =
                  some { u with stock := (State.dealUpTo u.drawStep (r :: rs)).snd, waste := (State.dealUpTo u.drawStep (r :: rs)).fst.reverse ++ [] } := by
                simp [State.dealStock]
              have hu' : State.dealStock { u with stock := (r :: rs), waste := [] } = some u₁ := hu
              have hui : u₁ = { u with stock := (State.dealUpTo u.drawStep (r :: rs)).snd, waste := (State.dealUpTo u.drawStep (r :: rs)).fst.reverse ++ [] } :=
                Option.some.inj (hu'.symm.trans hfU)
              rw [hui]
              refine ⟨{ v with stock := (State.dealUpTo v.drawStep (r :: rs)).snd, waste := (State.dealUpTo v.drawStep (r :: rs)).fst.reverse ++ [] }, ?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
              · rw [show v.stepDraw = State.dealStock (State.recycle v) from rfl, hrv]
                simp [State.dealStock]
              · rw [hdraw]
              · rw [hdraw]
  | cons s ss =>
      have hvs : v.stock = s :: ss := hstock.trans hus
      have hru : State.recycle u = u := by simp [State.recycle, hus]
      have hrv : State.recycle v = v := by simp [State.recycle, hvs]
      rw [show u.stepDraw = State.dealStock (State.recycle u) from rfl, hru] at hu
      have hfU : State.dealStock u = some { u with stock := (State.dealUpTo u.drawStep (s :: ss)).snd, waste := (State.dealUpTo u.drawStep (s :: ss)).fst.reverse ++ u.waste } := by
        simp [State.dealStock, hus]
      have hui : u₁ = { u with stock := (State.dealUpTo u.drawStep (s :: ss)).snd, waste := (State.dealUpTo u.drawStep (s :: ss)).fst.reverse ++ u.waste } :=
        Option.some.inj (hu.symm.trans hfU)
      rw [hui]
      refine ⟨{ v with stock := (State.dealUpTo v.drawStep (s :: ss)).snd, waste := (State.dealUpTo v.drawStep (s :: ss)).fst.reverse ++ v.waste }, ?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
      · rw [show v.stepDraw = State.dealStock (State.recycle v) from rfl, hrv]
        simp [State.dealStock, hvs]
      · rw [hdraw]
      · rw [hdraw, hwaste]

/-- THE DRAW TRANSPORT: the draw commutes with the exchange and the
license re-seats untouched (the draw never writes a pile). -/
theorem exch_step_draw {st s₁ : State} {t z z' : Card} {α β : Anchor}
    {Bα B' Sa Sa' : List Card}
    (hwf : st.WF)
    (h₁ : st.pileHolding t = some α) (h₂ : st.pileHolding t.twin = some β) (hne : α ≠ β)
    (hsα : (st.piles α).faceUp = Bα ++ [t, z] ++ Sa)
    (hsβ : (st.piles β).faceUp = B' ++ [t.twin, z'] ++ Sa')
    (hfit : canSitOn z t = true) (hfit' : canSitOn z' t.twin = true)
    (hstep : st.step Move.draw = some s₁) :
    ((st.exchangeTwin t).step Move.draw) = some (s₁.exchangeTwin t) ∧ BothOcc s₁ t := by
  have hs : st.stepDraw = some s₁ := by
    rw [show st.stepDraw = st.step Move.draw from rfl]
    exact hstep
  obtain ⟨hpil, hfnd, hdrw⟩ := draw_facts hs
  have hwf₁ : s₁.WF := step_wf hwf hstep
  have h₁s : s₁.pileHolding t = some α := by
    rw [pileHolding_congr hpil]
    exact h₁
  have h₂s : s₁.pileHolding t.twin = some β := by
    rw [pileHolding_congr hpil]
    exact h₂
  have hsαs : (s₁.piles α).faceUp = Bα ++ [t, z] ++ Sa := by rw [hpil]; exact hsα
  have hsβs : (s₁.piles β).faceUp = B' ++ [t.twin, z'] ++ Sa' := by rw [hpil]; exact hsβ
  have hb := braid_splice hwf₁ h₁s h₂s hne hsαs hsβs hfit hfit'
  refine ⟨?_, ⟨α, β, z, z', Bα, B', Sa, Sa', h₁s, h₂s, hne, hsαs, hsβs,
    hfit, hfit', hb.1, hb.2.1, hb.2.2.1, hb.2.2.2⟩⟩
  show (st.exchangeTwin t).stepDraw = some (s₁.exchangeTwin t)
  obtain ⟨T, hT, hTp, hsp, hTf, hsf, hTd, hsd, hTsk, hTsw⟩ :=
    stepDraw_rel (u := st) (v := st.exchangeTwin t) (u₁ := s₁)
      State.exchangeTwin_stock State.exchangeTwin_waste
      State.exchangeTwin_drawStep hs
  have hTe : T = s₁.exchangeTwin t := by
    apply State.ext
    · exact hTf.trans (State.exchangeTwin_found.trans (hfnd.symm.trans State.exchangeTwin_found.symm))
    · rw [hTp, exch_piles_congr hpil]
    · exact hTsk.trans State.exchangeTwin_stock.symm
    · exact hTsw.trans State.exchangeTwin_waste.symm
    · exact hTd.trans (State.exchangeTwin_drawStep.trans (hdrw.symm.trans State.exchangeTwin_drawStep.symm))
  rw [hT, hTe]

/-- The license carries over a pile-preserving step: the searches,
shapes and fits hold verbatim and WF re-derives the braid family. -/
theorem bothOcc_pilesCarry {st s₁ : State} {m : Move} {t z z' : Card} {α β : Anchor}
    {Bα B' Sa Sa' : List Card}
    (hwf : st.WF) (hstep : State.step st m = some s₁)
    (hpil : s₁.piles = st.piles)
    (h₁ : st.pileHolding t = some α) (h₂ : st.pileHolding t.twin = some β) (hne : α ≠ β)
    (hsα : (st.piles α).faceUp = Bα ++ [t, z] ++ Sa)
    (hsβ : (st.piles β).faceUp = B' ++ [t.twin, z'] ++ Sa')
    (hfit : canSitOn z t = true) (hfit' : canSitOn z' t.twin = true) :
    BothOcc s₁ t := by
  have hwf₁ : s₁.WF := step_wf hwf hstep
  have h₁s : s₁.pileHolding t = some α := by
    rw [pileHolding_congr hpil]
    exact h₁
  have h₂s : s₁.pileHolding t.twin = some β := by
    rw [pileHolding_congr hpil]
    exact h₂
  have hsαs : (s₁.piles α).faceUp = Bα ++ [t, z] ++ Sa := by rw [hpil]; exact hsα
  have hsβs : (s₁.piles β).faceUp = B' ++ [t.twin, z'] ++ Sa' := by rw [hpil]; exact hsβ
  have hb := braid_splice hwf₁ h₁s h₂s hne hsαs hsβs hfit hfit'
  exact ⟨α, β, z, z', Bα, B', Sa, Sa', h₁s, h₂s, hne, hsαs, hsβs,
    hfit, hfit', hb.1, hb.2.1, hb.2.2.1, hb.2.2.2⟩

/-- The wasteToFound firing shape. -/
private theorem setFound_found_self {st : State} {s : Suit} {l : List Card} :
    (st.setFound s l).found s = l := by
  show (if s = s then l else st.found s) = l
  cases hdd : decide (s = s) with
  | true => rw [ite_true_eq (of_decide_eq_true hdd)]
  | false => exact absurd rfl (of_decide_eq_false hdd)

private theorem setFound_found_ne {st : State} {s s' : Suit} {l : List Card}
    (hne : s' ≠ s) : (st.setFound s l).found s' = st.found s' := by
  show (if s' = s then l else st.found s') = st.found s'
  cases hdd : decide (s' = s) with
  | true => exact absurd (of_decide_eq_true hdd) hne
  | false => rw [ite_false_eq (of_decide_eq_false hdd)]

private theorem step_wasteToFound_shape {st s₁ : State} {c : Card}
    (hstep : st.step (Move.wasteToFound c) = some s₁) :
    (st.wasteIs c && st.nextUp c) = true ∧ ∃ ws : List Card,
      st.waste = c :: ws ∧
      s₁ = { st.setFound c.suit (st.found c.suit ++ [c]) with waste := ws } := by
  cases hg : (st.wasteIs c && st.nextUp c) with
  | false =>
      rw [show st.step (Move.wasteToFound c) = none from by
        rw [step_wasteToFound_eq, hg]
        rfl] at hstep
      exact absurd hstep (by simp)
  | true =>
      rw [show st.step (Move.wasteToFound c) =
          (match st.waste with
           | _ :: ws => some { st.setFound c.suit (st.found c.suit ++ [c]) with waste := ws }
           | [] => none) from by
        rw [step_wasteToFound_eq, hg]
        rfl] at hstep
      cases hwl : st.waste with
      | nil => rw [hwl] at hstep; exact absurd hstep (by simp)
      | cons w ws =>
          have hwc : w = c := by
            cases hb : st.wasteIs c with
            | true =>
                have hh : (match st.waste with
                    | [] => false
                    | c' :: _ => decide (c' = c)) = true := hb
                rw [hwl] at hh
                exact of_decide_eq_true hh
            | false =>
                rw [hb] at hg
                exact absurd hg (by simp)
          rw [hwl, hwc] at hstep
          injection hstep with hstep'
          exact ⟨rfl, ws, by rw [hwc], hstep'.symm⟩

/-- THE WASTETOF FOUND TRANSPORT: waste-to-foundation commutes with
the exchange (both write only foundations and waste); the license
carries verbatim. -/
theorem exch_step_wasteToFound {st s₁ : State} {t z z' : Card} {α β : Anchor}
    {Bα B' Sa Sa' : List Card} {c : Card}
    (hwf : st.WF)
    (h₁ : st.pileHolding t = some α) (h₂ : st.pileHolding t.twin = some β) (hne : α ≠ β)
    (hsα : (st.piles α).faceUp = Bα ++ [t, z] ++ Sa)
    (hsβ : (st.piles β).faceUp = B' ++ [t.twin, z'] ++ Sa')
    (hfit : canSitOn z t = true) (hfit' : canSitOn z' t.twin = true)
    (hstep : st.step (Move.wasteToFound c) = some s₁) :
    ((st.exchangeTwin t).step (Move.wasteToFound c)) = some (s₁.exchangeTwin t) ∧
      BothOcc s₁ t := by
  obtain ⟨hg, ws, hwl, hs₁⟩ := step_wasteToFound_shape hstep
  have hpil : s₁.piles = st.piles := by rw [hs₁]; rfl
  refine ⟨?_, bothOcc_pilesCarry hwf hstep hpil h₁ h₂ hne hsα hsβ hfit hfit'⟩
  show State.step (st.exchangeTwin t) (Move.wasteToFound c) =
    some (s₁.exchangeTwin t)
  have hw : (st.exchangeTwin t).wasteIs c = st.wasteIs c := by
    show (match (st.exchangeTwin t).waste with
      | [] => false
      | c' :: _ => decide (c' = c)) = _
    rw [State.exchangeTwin_waste]
    rfl
  have hn : (st.exchangeTwin t).nextUp c = st.nextUp c := by
    show decide (c.rank.toIdx =
      ((st.exchangeTwin t).found c.suit).length) = _
    rw [State.exchangeTwin_found]
    rfl
  have hgs : (st.wasteIs c && st.nextUp c) =
      ((st.exchangeTwin t).wasteIs c && (st.exchangeTwin t).nextUp c) := by
    rw [hw, hn]
  cases hg2 : ((st.exchangeTwin t).wasteIs c && (st.exchangeTwin t).nextUp c) with
  | false =>
      rw [← hgs] at hg2
      rw [hg2] at hg
      exact absurd hg (by simp)
  | true =>
      rw [show State.step (st.exchangeTwin t) (Move.wasteToFound c) =
          (match (st.exchangeTwin t).waste with
           | _ :: ws => some { (st.exchangeTwin t).setFound c.suit
               ((st.exchangeTwin t).found c.suit ++ [c]) with waste := ws }
           | [] => none) from by
        rw [step_wasteToFound_eq, hg2]
        rfl]
      rw [show ((st.exchangeTwin t).waste) = c :: ws from State.exchangeTwin_waste.trans hwl]
      rw [show (match (c :: ws : List Card) with
          | _ :: ws' => some ({ (st.exchangeTwin t).setFound c.suit
              ((st.exchangeTwin t).found c.suit ++ [c]) with waste := ws' } : State)
          | [] => none) =
          some ({ (st.exchangeTwin t).setFound c.suit
              ((st.exchangeTwin t).found c.suit ++ [c]) with waste := ws } : State) from rfl]
      rw [Option.some.injEq]
      apply State.ext
      · funext s'
        by_cases hs' : s' = c.suit
        · rw [hs']
          rw [setFound_found_self]
          rw [congrFun State.exchangeTwin_found c.suit]
          rw [show (s₁.exchangeTwin t).found c.suit = s₁.found c.suit from
            congrFun State.exchangeTwin_found c.suit]
          rw [hs₁]
          exact setFound_found_self.symm
        · rw [setFound_found_ne hs']
          rw [congrFun State.exchangeTwin_found s']
          rw [show (s₁.exchangeTwin t).found s' = s₁.found s' from
            congrFun State.exchangeTwin_found s']
          rw [hs₁]
          exact (setFound_found_ne hs').symm
      · simp only [State.setFound]
        exact (exch_piles_congr hpil).symm
      · simp only [State.setFound]
        rw [show (s₁.exchangeTwin t).stock = s₁.stock from State.exchangeTwin_stock]
        rw [hs₁]
        rw [State.exchangeTwin_stock]
        rfl
      · rw [State.exchangeTwin_waste, hs₁]
      · simp only [State.setFound]
        rw [show (s₁.exchangeTwin t).drawStep = s₁.drawStep from State.exchangeTwin_drawStep]
        rw [hs₁]
        rw [State.exchangeTwin_drawStep]
        rfl

/-! ### §5.2 The search congruences at one written pile -/

/-- firstWhere is determined pointwise by its predicate. -/
private theorem firstWhere_congr' {p q : Anchor → Bool} :
    ∀ (l : List Anchor), (∀ a : Anchor, p a = q a) →
      firstWhere p l = firstWhere q l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a ls ih =>
      intro hp
      show (match p a with
            | true => some a
            | false => firstWhere p ls) =
          (match q a with
            | true => some a
            | false => firstWhere q ls)
      rw [hp a]
      cases hpq : q a with
      | true => rfl
      | false => exact ih hp

/-- A pile write at `κ` leaves every other pile alone. -/
private theorem setPile_skips {st : State} {κ : Anchor} {p : Pile}
    {j : Anchor} (hj : j ≠ κ) :
    (st.setPile κ p).piles j = st.piles j := by
  show (if j = κ then p else st.piles j) = st.piles j
  rw [ite_false_eq hj]

/-- Membership on the right of a single append. -/
private theorem mem_append_single_iff {c x : Card} {l : List Card} (hx : x ≠ c) :
    x ∈ l ++ [c] ↔ x ∈ l := by
  constructor
  · intro h
    rcases (List.mem_append.mp h) with h | h
    · exact h
    · rcases (List.mem_cons.mp h) with heq | hnil
      · exact absurd heq hx
      · exact absurd hnil (by simp)
  · intro h
    exact List.mem_append.mpr (Or.inl h)

/-- The holding search is untouched by appending one fresh card to a
single pile, for any searched card distinct from the appended one. -/
theorem pileHolding_append_congr {st s' : State} {κ : Anchor} {c x : Card}
    (hκ : (s'.piles κ).faceUp = (st.piles κ).faceUp ++ [c])
    (hskip : ∀ j : Anchor, j ≠ κ → s'.piles j = st.piles j)
    (hne : x ≠ c) :
    s'.pileHolding x = st.pileHolding x := by
  have hfull : ∀ a : Anchor, (s'.piles a).faceUp = (st.piles a).faceUp ∨
      (a = κ ∧ (s'.piles a).faceUp = (st.piles a).faceUp ++ [c]) := by
    intro a
    by_cases haj : a = κ
    · exact Or.inr ⟨haj, haj ▸ hκ⟩
    · exact Or.inl (by rw [← hskip a haj])
  show firstWhere (fun a => decide (x ∈ (s'.piles a).faceUp)) Anchor.all = _
  refine firstWhere_congr' Anchor.all ?_
  intro a
  cases hfull a with
  | inl h => rw [h]
  | inr h =>
      rw [h.2]
      cases hd : decide (x ∈ (st.piles a).faceUp) with
      | true =>
          have hmem : x ∈ (st.piles a).faceUp := of_decide_eq_true hd
          rw [show decide (x ∈ (st.piles a).faceUp ++ [c]) = true from
            decide_eq_true (List.mem_append.mpr (Or.inl hmem))]
      | false =>
          have h : ¬(x ∈ (st.piles a).faceUp) := of_decide_eq_false hd
          rw [show decide (x ∈ (st.piles a).faceUp ++ [c]) = false from
            decide_eq_false (fun hc => h ((mem_append_single_iff hne).mp hc))]

/-- The wasteToTab firing shape. -/
private theorem step_wasteToTab_shape {st s₁ : State} {c : Card} {b : Base}
    (hstep : st.step (Move.wasteToTab c b) = some s₁) :
    (st.wasteIs c && st.canPlace c b) = true ∧ ∃ ws : List Card,
      st.waste = c :: ws ∧ s₁ = { st.putCard c b with waste := ws } := by
  cases hg : (st.wasteIs c && st.canPlace c b) with
  | false =>
      rw [show st.step (Move.wasteToTab c b) = none from by
        rw [step_wasteToTab_eq, hg]; rfl] at hstep
      exact absurd hstep (by simp)
  | true =>
      rw [show st.step (Move.wasteToTab c b) =
          (match st.waste with
           | _ :: ws => some { st.putCard c b with waste := ws }
           | [] => none) from by
        rw [step_wasteToTab_eq, hg]; rfl] at hstep
      cases hwl : st.waste with
      | nil => rw [hwl] at hstep; exact absurd hstep (by simp)
      | cons w ws =>
          have hwc : w = c := by
            cases hb : st.wasteIs c with
            | true =>
                have hh : (match st.waste with
                    | [] => false
                    | c' :: _ => decide (c' = c)) = true := hb
                rw [hwl] at hh
                exact of_decide_eq_true hh
            | false =>
                rw [hb] at hg
                exact absurd hg (by simp)
          rw [hwl, hwc] at hstep
          injection hstep with hstep'
          exact ⟨rfl, ws, by rw [hwc], hstep'.symm⟩

/-- The landing case of a putCard firing: which anchor gets written. -/
private theorem putCard_cases {st : State} {c : Card} {b : Base}
    (hcp : st.canPlace c b = true) :
    (∃ κ : Anchor, b = Sum.inl κ ∧ (st.piles κ).isEmpty = true) ∨
    (∃ (d : Card) (κ : Anchor), b = Sum.inr d ∧ st.pileOfTop d = some κ) := by
  cases b with
  | inl κ =>
      rw [canPlace_inl_unfold] at hcp
      refine Or.inl ⟨κ, rfl, ?_⟩
      cases hsi : ((st.piles κ).isEmpty) with
      | true => rfl
      | false =>
          rw [hsi] at hcp
          exact absurd hcp (by simp)
  | inr d =>
      cases hd : st.pileOfTop d with
      | none =>
          rw [canPlace_inr_eq, hd] at hcp
          exact absurd hcp (by simp)
      | some κ => exact Or.inr ⟨d, κ, rfl, hd⟩

/-! ### §5.3 The append carries -/

/-- A face-up card is never on the waste. -/
theorem card_not_in_waste {st : State} {x : Card} {a : Anchor}
    (hwf : st.WF) (hmem : x ∈ (st.piles a).faceUp) : x ∉ st.waste := by
  obtain ⟨-, -, hn, -⟩ := mem_pile_unique hwf (Or.inr hmem)
  exact hn

/-- setPile at its own anchor. -/
private theorem setPile_self {st : State} {κ : Anchor} {p : Pile} :
    (st.setPile κ p).piles κ = p := by
  show (if κ = κ then p else st.piles κ) = p
  rw [ite_true_eq rfl]

/-- The putCard landing, uniformly: one pile's face-up run gains the
placed card. -/
theorem putCard_pile_write {st : State} {c : Card} {b : Base}
    (hcp : st.canPlace c b = true) :
    ∃ κ : Anchor, ((st.putCard c b).piles κ).faceUp = (st.piles κ).faceUp ++ [c] ∧
      ∀ j : Anchor, j ≠ κ → (st.putCard c b).piles j = st.piles j := by
  rcases putCard_cases hcp with ⟨κ, rfl, hempty⟩ | ⟨d, κ, rfl, hd⟩
  · refine ⟨κ, ?_, ?_⟩
    · have hpf : (st.piles κ).faceUp = [] := (Pile.isEmpty_eq _).mp hempty |>.2
      show ((st.putCard c (Sum.inl κ)).piles κ).faceUp = (st.piles κ).faceUp ++ [c]
      rw [putCard_eq_inl, setPile_self, hpf]
      rfl
    · intro j hj
      show (st.putCard c (Sum.inl κ)).piles j = st.piles j
      rw [putCard_eq_inl]
      exact setPile_skips hj
  · refine ⟨κ, ?_, ?_⟩
    · show ((st.putCard c (Sum.inr d)).piles κ).faceUp = (st.piles κ).faceUp ++ [c]
      rw [putCard_eq_inr hd, setPile_self]
    · intro j hj
      show (st.putCard c (Sum.inr d)).piles j = st.piles j
      rw [putCard_eq_inr hd]
      exact setPile_skips hj

/-- The spine append juggle. -/
private theorem splice_snoc {t z : Card} {B Sa : List Card} (c : Card) :
    (B ++ [t, z] ++ Sa) ++ [c] = B ++ [t, z] ++ (Sa ++ [c]) := by
  simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- Appending at the very top leaves the below-prefix walk unchanged. -/
private theorem below_append_post {t : Card} : ∀ {l : List Card} (c : Card),
    t ∈ l → below t (l ++ [c]) = below t l := by
  intro l
  induction l with
  | nil => intro _ h; cases h
  | cons w ls ih =>
      intro c h
      by_cases hw : w = t
      · rw [hw, List.cons_append, below_cons_self, below_cons_self]
      · have hwt : w ≠ t := hw
        have htls : t ∈ ls :=
          (List.mem_cons.mp h).resolve_left (fun hc => hwt hc.symm)
        rw [List.cons_append, below_cons_ne (ls ++ [c]) hwt, below_cons_ne ls hwt,
          ih c htls]

/-- Appending at the very top extends the aboveIn walk in place. -/
private theorem aboveIn_append_post {t : Card} : ∀ {l : List Card} (c : Card),
    t ∈ l → aboveIn t (l ++ [c]) = aboveIn t l ++ [c] := by
  intro l
  induction l with
  | nil => intro _ h; cases h
  | cons w ls ih =>
      intro c h
      by_cases hw : w = t
      · rw [hw, List.cons_append, aboveIn_cons_self, aboveIn_cons_self]
      · have hwt : w ≠ t := hw
        have htls : t ∈ ls :=
          (List.mem_cons.mp h).resolve_left (fun hc => hwt hc.symm)
        rw [List.cons_append, aboveIn_cons_ne (ls ++ [c]) hwt,
          aboveIn_cons_ne ls hwt, ih c htls]

/-- License carry when the step appended one fresh card to a pile away
from both hosts: the searches, shapes and fits carry verbatim. -/
theorem bothOcc_freshWrite {st s₁ : State} {m : Move} {t z z' c : Card}
    {α β κ : Anchor} {Bα B' Sa Sa' : List Card}
    (hwf : st.WF) (hstep : State.step st m = some s₁)
    (hκ : (s₁.piles κ).faceUp = (st.piles κ).faceUp ++ [c])
    (hskip : ∀ j : Anchor, j ≠ κ → s₁.piles j = st.piles j)
    (hneκ : κ ≠ α) (hneκ' : κ ≠ β) (hct : c ≠ t) (hct' : c ≠ t.twin)
    (h₁ : st.pileHolding t = some α) (h₂ : st.pileHolding t.twin = some β) (hne : α ≠ β)
    (hsα : (st.piles α).faceUp = Bα ++ [t, z] ++ Sa)
    (hsβ : (st.piles β).faceUp = B' ++ [t.twin, z'] ++ Sa')
    (hfit : canSitOn z t = true) (hfit' : canSitOn z' t.twin = true) :
    BothOcc s₁ t := by
  have hwf₁ : s₁.WF := step_wf hwf hstep
  have h₁s : s₁.pileHolding t = some α := by
    rw [pileHolding_append_congr hκ hskip (Ne.symm hct)]
    exact h₁
  have h₂s : s₁.pileHolding t.twin = some β := by
    rw [pileHolding_append_congr hκ hskip (Ne.symm hct')]
    exact h₂
  have hsαs : (s₁.piles α).faceUp = Bα ++ [t, z] ++ Sa := by
    rw [show (s₁.piles α).faceUp = (st.piles α).faceUp from by
        rw [hskip α (Ne.symm hneκ)]]
    exact hsα
  have hsβs : (s₁.piles β).faceUp = B' ++ [t.twin, z'] ++ Sa' := by
    rw [show (s₁.piles β).faceUp = (st.piles β).faceUp from by
        rw [hskip β (Ne.symm hneκ')]]
    exact hsβ
  have hb := braid_splice hwf₁ h₁s h₂s hne hsαs hsβs hfit hfit'
  exact ⟨α, β, z, z', Bα, B', Sa, Sa', h₁s, h₂s, hne, hsαs, hsβs, hfit, hfit',
    hb.1, hb.2.1, hb.2.2.1, hb.2.2.2⟩

/-- License carry when the step appended one fresh card on top of the
host pile α: the cargo head stays `z`, the suffix swallows the append. -/
theorem bothOcc_swollenSelf {st s₁ : State} {m : Move} {t z z' c : Card}
    {α β : Anchor} {Bα B' Sa Sa' : List Card}
    (hwf : st.WF) (hstep : State.step st m = some s₁)
    (hαw : (s₁.piles α).faceUp = (st.piles α).faceUp ++ [c])
    (hskip : ∀ j : Anchor, j ≠ α → s₁.piles j = st.piles j)
    (hct : c ≠ t) (hct' : c ≠ t.twin)
    (h₁ : st.pileHolding t = some α) (h₂ : st.pileHolding t.twin = some β) (hne : α ≠ β)
    (hsα : (st.piles α).faceUp = Bα ++ [t, z] ++ Sa)
    (hsβ : (st.piles β).faceUp = B' ++ [t.twin, z'] ++ Sa')
    (hfit : canSitOn z t = true) (hfit' : canSitOn z' t.twin = true) :
    BothOcc s₁ t := by
  have hwf₁ : s₁.WF := step_wf hwf hstep
  have h₁s : s₁.pileHolding t = some α := by
    rw [pileHolding_append_congr hαw hskip (Ne.symm hct)]
    exact h₁
  have h₂s : s₁.pileHolding t.twin = some β := by
    rw [pileHolding_append_congr hαw hskip (Ne.symm hct')]
    exact h₂
  have hsαs : (s₁.piles α).faceUp = Bα ++ [t, z] ++ (Sa ++ [c]) := by
    rw [hαw, hsα, splice_snoc c]
  have hsβs : (s₁.piles β).faceUp = B' ++ [t.twin, z'] ++ Sa' := by
    rw [show (s₁.piles β).faceUp = (st.piles β).faceUp from by
        rw [hskip β (Ne.symm hne)]]
    exact hsβ
  have hb := braid_splice hwf₁ h₁s h₂s hne hsαs hsβs hfit hfit'
  exact ⟨α, β, z, z', Bα, B', Sa ++ [c], Sa', h₁s, h₂s, hne, hsαs, hsβs, hfit, hfit',
    hb.1, hb.2.1, hb.2.2.1, hb.2.2.2⟩

/-- License carry when the step appended one fresh card on top of the
twin host pile β: the primed suffix swallows the append. -/
theorem bothOcc_swollenOther {st s₁ : State} {m : Move} {t z z' c : Card}
    {α β : Anchor} {Bα B' Sa Sa' : List Card}
    (hwf : st.WF) (hstep : State.step st m = some s₁)
    (hβw : (s₁.piles β).faceUp = (st.piles β).faceUp ++ [c])
    (hskip : ∀ j : Anchor, j ≠ β → s₁.piles j = st.piles j)
    (hct : c ≠ t) (hct' : c ≠ t.twin)
    (h₁ : st.pileHolding t = some α) (h₂ : st.pileHolding t.twin = some β) (hne : α ≠ β)
    (hsα : (st.piles α).faceUp = Bα ++ [t, z] ++ Sa)
    (hsβ : (st.piles β).faceUp = B' ++ [t.twin, z'] ++ Sa')
    (hfit : canSitOn z t = true) (hfit' : canSitOn z' t.twin = true) :
    BothOcc s₁ t := by
  have hwf₁ : s₁.WF := step_wf hwf hstep
  have h₁s : s₁.pileHolding t = some α := by
    rw [pileHolding_append_congr hβw hskip (Ne.symm hct)]
    exact h₁
  have h₂s : s₁.pileHolding t.twin = some β := by
    rw [pileHolding_append_congr hβw hskip (Ne.symm hct')]
    exact h₂
  have hsβs : (s₁.piles β).faceUp = B' ++ [t.twin, z'] ++ (Sa' ++ [c]) := by
    rw [hβw, hsβ, splice_snoc c]
  have hsαs : (s₁.piles α).faceUp = Bα ++ [t, z] ++ Sa := by
    rw [show (s₁.piles α).faceUp = (st.piles α).faceUp from by
        rw [hskip α hne]]
    exact hsα
  have hb := braid_splice hwf₁ h₁s h₂s hne hsαs hsβs hfit hfit'
  exact ⟨α, β, z, z', Bα, B', Sa, Sa' ++ [c], h₁s, h₂s, hne, hsαs, hsβs, hfit, hfit',
    hb.1, hb.2.1, hb.2.2.1, hb.2.2.2⟩

/-- The two guard conjuncts of a wasteToTab firing. -/
private theorem wasteToTab_guard_split {st : State} {c : Card} {b : Base}
    (hg : (st.wasteIs c && st.canPlace c b) = true) :
    st.canPlace c b = true := by
  cases hcp : st.canPlace c b with
  | true => rfl
  | false =>
      rw [hcp] at hg
      exact absurd hg (by simp)

/-- THE WASTETOTAB TRANSPORT: waste-to-tableau commutes with the
exchange — the anchor search reads identically (exch_hosts), the
canPlace guard reads identically (exch_canPlace_congr), so the σ-side
fires and writes its putCard at the ANCHOR-SWAPPED mirror of the
st-side landing: a host-pile landing crosses to the twin host pile,
a fresh landing stays fresh.  Both resulting splices match by the
snoc juggle. -/
theorem exch_step_wasteToTab {st s₁ : State} {t z z' : Card} {α β : Anchor}
    {Bα B' Sa Sa' : List Card} {c : Card} {b : Base}
    (hwf : st.WF)
    (h₁ : st.pileHolding t = some α) (h₂ : st.pileHolding t.twin = some β) (hne : α ≠ β)
    (hsα : (st.piles α).faceUp = Bα ++ [t, z] ++ Sa)
    (hsβ : (st.piles β).faceUp = B' ++ [t.twin, z'] ++ Sa')
    (hfit : canSitOn z t = true) (hfit' : canSitOn z' t.twin = true)
    (hstep : st.step (Move.wasteToTab c b) = some s₁) :
    ((st.exchangeTwin t).step (Move.wasteToTab c b)) = some (s₁.exchangeTwin t) ∧
      BothOcc s₁ t := by
  obtain ⟨hg, ws, hwl, hs₁⟩ := step_wasteToTab_shape hstep
  have htcp : st.canPlace c b = true := wasteToTab_guard_split hg
  have hwf₁ : s₁.WF := step_wf hwf hstep
  have hnt : t ≠ c := by
    intro hcon
    apply card_not_in_waste hwf (pileHolding_mem h₁)
    rw [hcon, hwl]
    exact List.mem_cons_self ..
  have hntw : t.twin ≠ c := by
    intro hcon
    apply card_not_in_waste hwf (pileHolding_mem h₂)
    rw [hcon, hwl]
    exact List.mem_cons_self ..
  have hαne : (st.piles α).faceUp ≠ [] := fun hcon =>
    (splice_nonempty Bα Sa) (hsα.symm.trans hcon)
  have hβne : (st.piles β).faceUp ≠ [] := fun hcon =>
    (splice_nonempty B' Sa') (hsβ.symm.trans hcon)
  have hcpσ : (st.exchangeTwin t).canPlace c b = st.canPlace c b :=
    exch_canPlace_congr hwf h₁ h₂ hne hsα hsβ c b
  have hw2 : (st.exchangeTwin t).wasteIs c = st.wasteIs c := by
    show (match (st.exchangeTwin t).waste with
      | [] => false
      | c' :: _ => decide (c' = c)) = _
    rw [State.exchangeTwin_waste]
    rfl
  have hgs : (st.wasteIs c && st.canPlace c b) =
      ((st.exchangeTwin t).wasteIs c && (st.exchangeTwin t).canPlace c b) := by
    rw [hw2, hcpσ]
  by_cases hg2 : ((st.exchangeTwin t).wasteIs c && (st.exchangeTwin t).canPlace c b) = true
  · rw [show State.step (st.exchangeTwin t) (Move.wasteToTab c b) =
      (match (st.exchangeTwin t).waste with
       | _ :: ws' => some { (st.exchangeTwin t).putCard c b with waste := ws' }
       | [] => none) from by
      rw [step_wasteToTab_eq, hg2]; rfl]
    rw [show ((st.exchangeTwin t)).waste = c :: ws from State.exchangeTwin_waste.trans hwl]
    rw [show (match (c :: ws : List Card) with
        | _ :: ws' => some ({ (st.exchangeTwin t).putCard c b with waste := ws' } : State)
        | [] => none) =
        some ({ (st.exchangeTwin t).putCard c b with waste := ws } : State) from rfl]
    rw [Option.some.injEq]
    -- the landing dispatch:
    rcases putCard_cases htcp with ⟨κ, rfl, hempty⟩ | ⟨d, κ, rfl, hd⟩
    · -- (A) the empty-anchor write: the written pile was empty, so it
      -- cannot be a host pile; the license carries verbatim.
      have hκA : κ ≠ α := by
        intro hcon
        rw [hcon] at hempty
        exact hαne ((Pile.isEmpty_eq _).mp hempty).2
      have hκB : κ ≠ β := by
        intro hcon
        rw [hcon] at hempty
        exact hβne ((Pile.isEmpty_eq _).mp hempty).2
      have hsκ : (s₁.piles κ).faceUp = (st.piles κ).faceUp ++ [c] := by
        have hpf : (st.piles κ).faceUp = [] := (Pile.isEmpty_eq _).mp hempty |>.2
        rw [hs₁]
        show ((st.putCard c (Sum.inl κ)).piles κ).faceUp = (st.piles κ).faceUp ++ [c]
        rw [putCard_eq_inl, setPile_self, hpf]
        rfl
      have hskips : ∀ j : Anchor, j ≠ κ → s₁.piles j = st.piles j := by
        intro j hj
        rw [hs₁]
        show (st.putCard c (Sum.inl κ)).piles j = st.piles j
        rw [putCard_eq_inl]
        exact setPile_skips hj
      have h₁s : s₁.pileHolding t = some α := by
        rw [pileHolding_append_congr hsκ hskips hnt]
        exact h₁
      have h₂s : s₁.pileHolding t.twin = some β := by
        rw [pileHolding_append_congr hsκ hskips hntw]
        exact h₂
      have hsαs : (s₁.piles α).faceUp = Bα ++ [t, z] ++ Sa := by
        rw [show (s₁.piles α).faceUp = (st.piles α).faceUp from by
            rw [hskips α (Ne.symm hκA)]]
        exact hsα
      have hsβs : (s₁.piles β).faceUp = B' ++ [t.twin, z'] ++ Sa' := by
        rw [show (s₁.piles β).faceUp = (st.piles β).faceUp from by
            rw [hskips β (Ne.symm hκB)]]
        exact hsβ
      refine ⟨?_,
        bothOcc_freshWrite hwf hstep hsκ hskips hκA hκB (Ne.symm hnt) (Ne.symm hntw)
          h₁ h₂ hne hsα hsβ hfit hfit'⟩
      -- the σ side lands on the same empty anchor
      have hσempty : ((st.exchangeTwin t).piles κ).isEmpty = true := by
        rw [exch_isEmpty_congr hwf h₁ h₂ hne hsα hsβ κ]
        exact hempty
      rw [show (st.exchangeTwin t).putCard c (Sum.inl κ) =
          (st.exchangeTwin t).setPile κ ⟨[], [c]⟩ from rfl]
      apply State.ext
      · show (st.exchangeTwin t).found = (s₁.exchangeTwin t).found
        rw [State.exchangeTwin_found, State.exchangeTwin_found]
        show st.found = s₁.found
        rw [hs₁]
        rfl
      · funext j
        show (if j = κ then (⟨[], [c]⟩ : Pile) else (st.exchangeTwin t).piles j) =
          (s₁.exchangeTwin t).piles j
        by_cases hjκ : j = κ
        · rw [hjκ, ite_true_eq rfl,
            State.exchangeTwin_pile_ne h₁s h₂s hne hκA hκB,
            show (s₁.piles κ) = (⟨[], [c]⟩ : Pile) from by
              rw [hs₁]
              show (st.putCard c (Sum.inl κ)).piles κ = _
              rw [putCard_eq_inl]
              exact setPile_self]
        · by_cases hjα : j = α
          · rw [hjα, ite_false_eq (Ne.symm hκA),
              exch_pile_self_record hwf h₁ h₂ hne hsα hsβ,
              exch_pile_self_record hwf₁ h₁s h₂s hne hsαs hsβs,
              show (s₁.piles α).hidden = (st.piles α).hidden from by
                rw [hskips α (Ne.symm hκA)]]
          · by_cases hjβ : j = β
            · rw [hjβ, ite_false_eq (Ne.symm hκB),
                exch_pile_other_record hwf h₁ h₂ hne hsα hsβ,
                exch_pile_other_record hwf₁ h₁s h₂s hne hsαs hsβs,
                show (s₁.piles β).hidden = (st.piles β).hidden from by
                  rw [hskips β (Ne.symm hκB)]]
            · rw [ite_false_eq hjκ,
                show (s₁.exchangeTwin t).piles j = s₁.piles j from
                  State.exchangeTwin_pile_ne h₁s h₂s hne hjα hjβ,
                hskips j hjκ,
                show (st.exchangeTwin t).piles j = st.piles j from
                  State.exchangeTwin_pile_ne h₁ h₂ hne hjα hjβ]
      · show (st.exchangeTwin t).stock = (s₁.exchangeTwin t).stock
        rw [State.exchangeTwin_stock, State.exchangeTwin_stock]
        show st.stock = s₁.stock
        rw [hs₁]
        rfl
      · show ws = (s₁.exchangeTwin t).waste
        rw [State.exchangeTwin_waste]
        show ws = s₁.waste
        rw [hs₁]
      · show (st.exchangeTwin t).drawStep = (s₁.exchangeTwin t).drawStep
        rw [State.exchangeTwin_drawStep, State.exchangeTwin_drawStep]
        show st.drawStep = s₁.drawStep
        rw [hs₁]
        rfl
    · -- (B) the top-directed landing: the write appends at the κ-pile top
      have hsκ : (s₁.piles κ).faceUp = (st.piles κ).faceUp ++ [c] := by
        rw [hs₁]
        show ((st.putCard c (Sum.inr d)).piles κ).faceUp = (st.piles κ).faceUp ++ [c]
        rw [putCard_eq_inr hd, setPile_self]
      have hskips : ∀ j : Anchor, j ≠ κ → s₁.piles j = st.piles j := by
        intro j hj
        rw [hs₁]
        show (st.putCard c (Sum.inr d)).piles j = st.piles j
        rw [putCard_eq_inr hd]
        exact setPile_skips hj
      have h₁s : s₁.pileHolding t = some α := by
        rw [pileHolding_append_congr hsκ hskips hnt]
        exact h₁
      have h₂s : s₁.pileHolding t.twin = some β := by
        rw [pileHolding_append_congr hsκ hskips hntw]
        exact h₂
      have hs₁f : s₁.found = st.found := by
        rw [hs₁, putCard_eq_inr hd]
        rfl
      have hs₁sk : s₁.stock = st.stock := by
        rw [hs₁, putCard_eq_inr hd]
        rfl
      have hs₁w : s₁.waste = ws := by
        rw [hs₁, putCard_eq_inr hd]
      have hs₁d : s₁.drawStep = st.drawStep := by
        rw [hs₁, putCard_eq_inr hd]
        rfl
      -- the σ-side landing anchor:
      have hdσ : (st.exchangeTwin t).pileOfTop d = some (swapAnch α β κ) := by
        rw [exch_pileOfTop_swap hwf h₁ h₂ hne hsα hsβ d, hd]
        rfl
      by_cases hjα : κ = α
      · -- (B1) the append lands on the host pile α: the mirror lands
        -- it on the twin host pile β, and the exchanged suffixes
        -- swallow the append.
        rw [hjα] at hsκ hskips hd hdσ
        rw [swapAnch_left α β] at hdσ
        have hsαs : (s₁.piles α).faceUp = Bα ++ [t, z] ++ (Sa ++ [c]) := by
          rw [hsκ, hsα, splice_snoc c]
        have hsβs : (s₁.piles β).faceUp = B' ++ [t.twin, z'] ++ Sa' := by
          rw [show (s₁.piles β).faceUp = (st.piles β).faceUp from by
              rw [hskips β (Ne.symm hne)]]
          exact hsβ
        have hsαrec : (s₁.piles α) = { st.piles α with faceUp := (st.piles α).faceUp ++ [c] } := by
          rw [hs₁]
          show ((st.putCard c (Sum.inr d)).piles α) = _
          rw [putCard_eq_inr hd, setPile_self]
        rw [putCard_eq_inr hdσ]
        refine ⟨?_,
          bothOcc_swollenSelf hwf hstep hsκ hskips (Ne.symm hnt) (Ne.symm hntw)
            h₁ h₂ hne hsα hsβ hfit hfit'⟩
        apply State.ext
        · show (st.exchangeTwin t).found = (s₁.exchangeTwin t).found
          rw [State.exchangeTwin_found, State.exchangeTwin_found, hs₁f]
        · funext j
          show (if j = β then
                { (st.exchangeTwin t).piles β with
                  faceUp := ((st.exchangeTwin t).piles β).faceUp ++ [c] }
              else (st.exchangeTwin t).piles j) =
            (s₁.exchangeTwin t).piles j
          by_cases hjβ : j = β
          · rw [hjβ, ite_true_eq rfl,
              exch_pile_other_record hwf h₁ h₂ hne hsα hsβ]
            show ((⟨(st.piles β).hidden, (B' ++ [t.twin, z] ++ Sa) ++ [c]⟩ : Pile) =
              (s₁.exchangeTwin t).piles β)
            rw [exch_pile_other_record hwf₁ h₁s h₂s hne hsαs hsβs,
                splice_snoc c,
                show (s₁.piles β).hidden = (st.piles β).hidden from by
                  rw [hskips β (Ne.symm hne)]]
          · by_cases hjα' : j = α
            · rw [hjα', ite_false_eq hne,
                exch_pile_self_record hwf h₁ h₂ hne hsα hsβ,
                exch_pile_self_record hwf₁ h₁s h₂s hne hsαs hsβs,
                show (s₁.piles α).hidden = (st.piles α).hidden from by
                  rw [hsαrec]]
            · rw [ite_false_eq hjβ,
                show (s₁.exchangeTwin t).piles j = s₁.piles j from
                  State.exchangeTwin_pile_ne h₁s h₂s hne hjα' hjβ,
                hskips j hjα',
                show (st.exchangeTwin t).piles j = st.piles j from
                  State.exchangeTwin_pile_ne h₁ h₂ hne hjα' hjβ]
        · show (st.exchangeTwin t).stock = (s₁.exchangeTwin t).stock
          rw [State.exchangeTwin_stock, State.exchangeTwin_stock, hs₁sk]
        · show ws = (s₁.exchangeTwin t).waste
          rw [State.exchangeTwin_waste, hs₁w]
        · show (st.exchangeTwin t).drawStep = (s₁.exchangeTwin t).drawStep
          rw [State.exchangeTwin_drawStep, State.exchangeTwin_drawStep, hs₁d]
      · by_cases hjβκ : κ = β
        · -- (B2) the mirror-land: the append lands on the twin host
          -- pile β; the σ-side lands it on the host pile α.
          rw [hjβκ] at hsκ hskips hd hdσ
          rw [swapAnch_right α β] at hdσ
          have hsβs : (s₁.piles β).faceUp = B' ++ [t.twin, z'] ++ (Sa' ++ [c]) := by
            rw [hsκ, hsβ, splice_snoc c]
          have hsαs : (s₁.piles α).faceUp = Bα ++ [t, z] ++ Sa := by
            rw [show (s₁.piles α).faceUp = (st.piles α).faceUp from by
                rw [hskips α hne]]
            exact hsα
          have hsβrec : (s₁.piles β) = { st.piles β with faceUp := (st.piles β).faceUp ++ [c] } := by
            rw [hs₁]
            show ((st.putCard c (Sum.inr d)).piles β) = _
            rw [putCard_eq_inr hd, setPile_self]
          rw [putCard_eq_inr hdσ]
          refine ⟨?_,
            bothOcc_swollenOther hwf hstep hsκ hskips (Ne.symm hnt) (Ne.symm hntw)
              h₁ h₂ hne hsα hsβ hfit hfit'⟩
          apply State.ext
          · show (st.exchangeTwin t).found = (s₁.exchangeTwin t).found
            rw [State.exchangeTwin_found, State.exchangeTwin_found, hs₁f]
          · funext j
            show (if j = α then
                  { (st.exchangeTwin t).piles α with
                    faceUp := ((st.exchangeTwin t).piles α).faceUp ++ [c] }
                else (st.exchangeTwin t).piles j) =
              (s₁.exchangeTwin t).piles j
            by_cases hjα' : j = α
            · rw [hjα', ite_true_eq rfl,
                exch_pile_self_record hwf h₁ h₂ hne hsα hsβ]
              show ((⟨(st.piles α).hidden, (Bα ++ [t, z'] ++ Sa') ++ [c]⟩ : Pile) =
                (s₁.exchangeTwin t).piles α)
              rw [exch_pile_self_record hwf₁ h₁s h₂s hne hsαs hsβs,
                  splice_snoc c,
                  show (s₁.piles α).hidden = (st.piles α).hidden from by
                    rw [hskips α hne]]
            · by_cases hjβ' : j = β
              · rw [hjβ', ite_false_eq (Ne.symm hne),
                  exch_pile_other_record hwf h₁ h₂ hne hsα hsβ,
                  exch_pile_other_record hwf₁ h₁s h₂s hne hsαs hsβs,
                  show (s₁.piles β).hidden = (st.piles β).hidden from by
                    rw [hsβrec]]
              · rw [ite_false_eq hjα',
                  show (s₁.exchangeTwin t).piles j = s₁.piles j from
                    State.exchangeTwin_pile_ne h₁s h₂s hne hjα' hjβ',
                  hskips j hjβ',
                  show (st.exchangeTwin t).piles j = st.piles j from
                    State.exchangeTwin_pile_ne h₁ h₂ hne hjα' hjβ']
          · show (st.exchangeTwin t).stock = (s₁.exchangeTwin t).stock
            rw [State.exchangeTwin_stock, State.exchangeTwin_stock, hs₁sk]
          · show ws = (s₁.exchangeTwin t).waste
            rw [State.exchangeTwin_waste, hs₁w]
          · show (st.exchangeTwin t).drawStep = (s₁.exchangeTwin t).drawStep
            rw [State.exchangeTwin_drawStep, State.exchangeTwin_drawStep, hs₁d]
        · -- (B0) a pile away from both hosts: the license carries
          -- verbatim; the σ-side lands on the same anchor.
          have hκA : κ ≠ α := hjα
          have hκB : κ ≠ β := hjβκ
          rw [swapAnch_ne hκA hκB] at hdσ
          have hsαs : (s₁.piles α).faceUp = Bα ++ [t, z] ++ Sa := by
            rw [show (s₁.piles α).faceUp = (st.piles α).faceUp from by
                rw [hskips α (Ne.symm hκA)]]
            exact hsα
          have hsβs : (s₁.piles β).faceUp = B' ++ [t.twin, z'] ++ Sa' := by
            rw [show (s₁.piles β).faceUp = (st.piles β).faceUp from by
                rw [hskips β (Ne.symm hκB)]]
            exact hsβ
          rw [putCard_eq_inr hdσ]
          refine ⟨?_,
            bothOcc_freshWrite hwf hstep hsκ hskips hκA hκB (Ne.symm hnt) (Ne.symm hntw)
              h₁ h₂ hne hsα hsβ hfit hfit'⟩
          apply State.ext
          · show (st.exchangeTwin t).found = (s₁.exchangeTwin t).found
            rw [State.exchangeTwin_found, State.exchangeTwin_found, hs₁f]
          · funext j
            show (if j = κ then
                  { (st.exchangeTwin t).piles κ with
                    faceUp := ((st.exchangeTwin t).piles κ).faceUp ++ [c] }
                else (st.exchangeTwin t).piles j) =
              (s₁.exchangeTwin t).piles j
            by_cases hjκ : j = κ
            · rw [hjκ, ite_true_eq rfl,
                show ((st.exchangeTwin t).piles κ) = (st.piles κ) from
                  State.exchangeTwin_pile_ne h₁ h₂ hne hκA hκB,
                show ((s₁.exchangeTwin t).piles κ) =
                    ({ st.piles κ with faceUp := (st.piles κ).faceUp ++ [c] } : Pile) from by
                  rw [show ((s₁.exchangeTwin t).piles κ) = (s₁.piles κ) from
                      State.exchangeTwin_pile_ne h₁s h₂s hne hκA hκB, hs₁]
                  show ((st.putCard c (Sum.inr d)).piles κ) = _
                  rw [putCard_eq_inr hd, setPile_self]]
            · by_cases hjα' : j = α
              · rw [hjα', ite_false_eq (Ne.symm hκA),
                  exch_pile_self_record hwf h₁ h₂ hne hsα hsβ,
                  exch_pile_self_record hwf₁ h₁s h₂s hne hsαs hsβs,
                  show (s₁.piles α).hidden = (st.piles α).hidden from by
                    rw [hskips α (Ne.symm hκA)]]
              · by_cases hjβ' : j = β
                · rw [hjβ', ite_false_eq (Ne.symm hκB),
                    exch_pile_other_record hwf h₁ h₂ hne hsα hsβ,
                    exch_pile_other_record hwf₁ h₁s h₂s hne hsαs hsβs,
                    show (s₁.piles β).hidden = (st.piles β).hidden from by
                      rw [hskips β (Ne.symm hκB)]]
                · rw [ite_false_eq hjκ,
                    show (s₁.exchangeTwin t).piles j = s₁.piles j from
                      State.exchangeTwin_pile_ne h₁s h₂s hne hjα' hjβ',
                    hskips j hjκ,
                    show (st.exchangeTwin t).piles j = st.piles j from
                      State.exchangeTwin_pile_ne h₁ h₂ hne hjα' hjβ']
          · show (st.exchangeTwin t).stock = (s₁.exchangeTwin t).stock
            rw [State.exchangeTwin_stock, State.exchangeTwin_stock, hs₁sk]
          · show ws = (s₁.exchangeTwin t).waste
            rw [State.exchangeTwin_waste, hs₁w]
          · show (st.exchangeTwin t).drawStep = (s₁.exchangeTwin t).drawStep
            rw [State.exchangeTwin_drawStep, State.exchangeTwin_drawStep, hs₁d]
  · exfalso
    apply hg2
    rw [← hgs]
    exact hg
