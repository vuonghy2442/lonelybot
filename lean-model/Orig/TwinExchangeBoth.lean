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

/-- The nonempty-pre branch: the written pile keeps the hidden deck
and takes the prefix as its whole face-up run.  (Dedup-marked against
`Orig/TwinExchange.lean`'s private `afterRunRemoved_ne`.) -/
private theorem afterRunRemoved_ne {p : Pile} {pre : List Card} (h : pre ≠ []) :
    Pile.afterRunRemoved p pre = { p with faceUp := pre } := by
  cases pre with
  | nil => exact absurd rfl h
  | cons w ws => rfl

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

private theorem canPlace_inl_eq (st : State) (c : Card) (a : Anchor) :
    st.canPlace c (Sum.inl a) =
      ((st.piles a).isEmpty && decide (c.rank = Rank.king)) := rfl

private theorem canPlace_inr_eq (st : State) (c z : Card) :
    st.canPlace c (Sum.inr z) =
      (match st.pileOfTop z with
       | some _ => canSitOn c z
       | none => false) := rfl

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

private theorem mem_splice_host {t z : Card} {B Sa : List Card} (_hB : t ∉ B) :
    t ∈ B ++ [t, z] ++ Sa ∧ z ∈ B ++ [t, z] ++ Sa := by
  constructor
  · rw [splice_head B Sa]
    exact List.mem_append.mpr
      (Or.inl (List.mem_append.mpr (Or.inr (List.mem_cons_self ..))))
  · rw [splice_cons B Sa]
    exact List.mem_append.mpr (Or.inr
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
