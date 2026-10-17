import Orig2.Vocab
import Orig2.CargoKit
import Orig2.Classification

/-!
# Orig2.FloaterLadder — THE FLOATER LADDER (chartered card)

PROMOTION NOTE (2026-10-17): dry-ran as `Temp/float_check.lean`
(chartered at owner request — "prove these to check if they are
correct before we put in the claim"), re-verified against the live
tree at promotion time (zero error, zero sorry, battery green),
installed at owner approval ("sure help me commit then" — same
hour; the installation trued the king-branch statement and paid
its corollary into the chart book's re-gate).  All content below
is byte-identical to the dry-run.

Three THEOREM rows, once claims-layer candidates, now certified:

* Row 1  `floater_iff`          - the Floater iff the honest seat chart
  (PROVED AFTER FIX: the king branch requires `hidden = []` — the
  coordinator's suspected gap, refuted-as-drafted by the probe and
  repaired in-statement);
* Row 2  `floater_hop_targets`  - the hop-target inventory of a floater
  (PROVED AS DRAFTED; the feared mixed king-with-company arm is
  unreachable — kings never sit on cards at WF);
* Row 3  `floater_seat_change`  - the class fiber: a reversible bare-cargo
  exchange moves a card's seat only across the twin pair, or vacates a
  king (PROVED AS DRAFTED; the forward path alone suffices — the
  return path and `hwfB` are redundant though kept as drafted).

COROLLARY PAID AT INSTALLATION: `chart_tabToTab_ungated_false` below
(the kernel witness refuting the ungated form of the chart row) was
consumed by the claims book — `chart_tabToTab` RE-GATED at
`Orig2/Claims.lean` the same hour (commit `bc369bd`); the sibling
chart rows carry analogous gates at their own discharge.

IMPORT SURFACE (the seam rule): `Orig2.Vocab` + `Orig2.Classification` +
`Orig2.CargoKit` (hence `Orig2.Kit` and the certified core seam
`Orig.Basic`/`Orig.State`/`Orig.Play`).  Nothing above the seam is
imported.

KIT NOTE (2026-10-17 consolidation, owner call "full extraction"):
the per-file private kit this card carried — the `cnt`/`cntFlat`
occurrence bookkeeping and the `tabToTab` WF preservation, the
list/run rows, the search rows, the seat readers, the twin algebra,
the one-point-edit row `tfc_seat_point_edit`, the per-leg
seat-relation chain kit (the whole `tfc_*`/`tfa_*` family) — moved
VERBATIM, per-row frozen-home cites kept, to the shared home
`Orig2/CargoKit.lean`, byte-identical with the copy this card
dry-ran (`Temp/float_check.lean`).  Three never-referenced rows
(`tfc_cnt_singleton`, `tfc_cntFlat_map_congr`, the fresh
`fli_cnt_append_left`) were pruned at the 2026-10-17 cleanup pass
rather than moved.  The `chart_tabToTab_ungated_false` witness row
stays at the tail; the battery claim stands.

GATE DISCIPLINE: every private row states its own gate; the three
public rows are the ONLY public artifact.  Zero sorry; the battery at
the tail expects `[propext]`/`[propext, Quot.sound]` on all three heads.
-/

/-! ## §F. THE THREE ROWS UNDER TEST (the only public artifact) -/

/-- **Row 1 — `floater_iff`.**  VERDICT SHAPE (the draft needed the
`hidden = []` conjunct in the king branch): the Floater is the honest
seat chart — on-card company, or a bare-king bottom seat — together
with the existence of a placement. -/
theorem floater_iff (st : State) (hwf : st.WF) (c : Card) :
    Floater st c ↔
      ((∃ z, seatOf st c = some (.inr z)) ∨
       (c.rank = Rank.king ∧ ∃ a, seatOf st c = some (.inl a) ∧
          (st.piles a).hidden = [])) ∧
      ∃ b, st.canPlace c b = true := by
  constructor
  · intro hF
    obtain ⟨b₀, hrev⟩ := hF
    have hcell := (tabToTabR_iff_reversibleAtW hwf c b₀).mpr hrev
    obtain ⟨a, hhold, hcp, hbcell⟩ := tfc_tabToTabR_inv hcell
    refine ⟨?_, b₀, hcp⟩
    rcases hbcell with hbne | ⟨hb0, hhid, hkng⟩
    · obtain ⟨z, hlz⟩ := lastOf_exists hbne
      exact Or.inl ⟨z, tfc_seatOf_inr_intro hhold hlz⟩
    · exact Or.inr ⟨hkng, a, tfc_seatOf_inl_intro hhold hb0, hhid⟩
  · intro hh
    obtain ⟨hseat, hplace⟩ := hh
    obtain ⟨b₀, hcp⟩ := hplace
    rcases hseat with hz | hk
    · obtain ⟨z, hse⟩ := hz
      obtain ⟨a1, hh1, hbNE, -⟩ := tfc_seatOf_of_inr hse
      refine ⟨b₀, (tabToTabR_iff_reversibleAtW hwf c b₀).mp ?_⟩
      show tabToTabR st c b₀ = true
      simp only [tabToTabR, hh1, hcp]
      cases hb : below c ((st.piles a1).faceUp) with
      | cons y ys => rfl
      | nil => exact absurd hb hbNE
    · obtain ⟨hkng, a, hse, hhid⟩ := hk
      obtain ⟨hh2, hbE⟩ := tfc_seatOf_of_inl hse
      refine ⟨b₀, (tabToTabR_iff_reversibleAtW hwf c b₀).mp ?_⟩
      show tabToTabR st c b₀ = true
      simp only [tabToTabR, hh2, hcp, hbE, hhid]
      rw [hkng]
      rfl

/-- **Row 2 — `floater_hop_targets`** (proved as drafted; see the file
header and the report: the `.inl a'` landing's strength rides the
reversibility-entailed `canPlace`, which forces the fully-empty target
— the drafted `faceUp = []` clause follows). -/
theorem floater_hop_targets {st : State} (hwf : st.WF) {c : Card}
    (hF : Floater st c) :
    ∃ b, reversibleAtW st (Move.tabToTab c b) ∧
      ((∃ z, seatOf st c = some (.inr z) ∧ b = .inr z.twin) ∨
       (c.rank = Rank.king ∧ ∃ a a', seatOf st c = some (.inl a) ∧
          b = .inl a' ∧ (st.piles a').faceUp = [])) := by
  obtain ⟨b₀, hrev⟩ := hF
  have hcell := (tabToTabR_iff_reversibleAtW hwf c b₀).mpr hrev
  obtain ⟨a, hhold, hcp, hbcell⟩ := tfc_tabToTabR_inv hcell
  rcases hbcell with hbne | ⟨hb0, hhid, hkng⟩
  · -- company beneath: the card sits on z; kings never sit on cards
    obtain ⟨z, hlz⟩ := lastOf_exists hbne
    have hse : seatOf st c = some (Sum.inr z) := tfc_seatOf_inr_intro hhold hlz
    obtain ⟨hsit, htopNone⟩ := tfc_seat_parent hwf hhold hlz
    obtain ⟨hidx, -⟩ := (canSitOn_eq c z).mp hsit
    have hzlt := Rank.toIdx_lt z.rank
    have hcnk : c.rank ≠ Rank.king := by
      intro hk
      have h12 : c.rank.toIdx = 12 := by rw [hk]; rfl
      omega
    cases b₀ with
    | inl a' =>
        obtain ⟨-, hking⟩ := canPlace_inl hcp
        exact absurd hking hcnk
    | inr w =>
        obtain ⟨k, hlocw, hfitw⟩ := canPlace_inr hcp
        rcases tfc_fitting_parent hfitw hsit with heq | heq
        · rw [heq] at hlocw
          rw [htopNone] at hlocw
          exact absurd hlocw (by simp)
        · exact ⟨Sum.inr w, hrev, Or.inl ⟨z, hse, by rw [heq]⟩⟩
  · -- the bare-king vacate
    have hse : seatOf st c = some (Sum.inl a) := tfc_seatOf_inl_intro hhold hb0
    cases b₀ with
    | inr w =>
        obtain ⟨k, -, hfitw⟩ := canPlace_inr hcp
        obtain ⟨hidx, -⟩ := (canSitOn_eq c w).mp hfitw
        have hlt := Rank.toIdx_lt w.rank
        have h12 : c.rank.toIdx = 12 := by rw [hkng]; rfl
        exfalso
        omega
    | inl a' =>
        obtain ⟨hE, -⟩ := canPlace_inl hcp
        exact ⟨Sum.inl a', hrev, Or.inr ⟨hkng, a, a', hse, rfl,
          ((Pile.isEmpty_eq _).mp hE).2⟩⟩

/-- **Row 3 — `floater_seat_change`** (proved as drafted).  The class
fiber: a reversible bare-cargo exchange moves a card's seat only
across the twin pair, or vacates a king. -/
theorem floater_seat_change (A B : State) (hwfA : A.WF) (hwfB : B.WF)
    (hbc : BareCargoEquiv A B) (c : Card)
    (hdiff : seatOf A c ≠ seatOf B c) :
    (∃ z, seatOf A c = some (.inr z) ∧
       seatOf B c = some (.inr z.twin)) ∨
    (c.rank = Rank.king ∧ ∃ a a', seatOf A c = some (.inl a) ∧
       seatOf B c = some (.inl a')) := by
  obtain ⟨hAB, -⟩ := hbc
  obtain ⟨-, hrel⟩ := tfc_chain_inv hAB hwfA
  rcases hrel c with heq | htwin | hking
  · exact absurd heq.symm hdiff
  · exact Or.inl htwin
  · exact Or.inr hking

/-! ## The battery -/

#print axioms floater_iff
#print axioms floater_hop_targets
#print axioms floater_seat_change


/-! ## §G (SURPRISE FINDING, bonus): the priced stub WITHOUT gates is
refuted by witness.  `Orig2/Claims.lean`'s `chart_tabToTab` is priced
ungated (step fires -> one point edit on seats).  At a WILD state
with the mover duplicated on two piles, the fired slide leaves the
duplicate holding the search: the mover's successor seat is read off
the OTHER copy (`inl p3`), not the base (`inl p6`).  Kernel-computed
witness. -/

/-- A wild world: the king of spades duplicated on two piles. -/
private def wild : State :=
  { piles := fun a => match a with
      | Anchor.p0 => { hidden := [], faceUp := [⟨Suit.spade, Rank.king⟩] }
      | Anchor.p3 => { hidden := [], faceUp := [⟨Suit.spade, Rank.king⟩] }
      | _ => { hidden := [], faceUp := [] }
    , found := fun _ => []
    , stock := []
    , waste := []
    , drawStep := 1 }

/-- The concrete successor of the wild slide. -/
private def wild' : State :=
  (wild.setPile Anchor.p0
    (Pile.afterRunRemoved (wild.piles Anchor.p0)
      (below ⟨Suit.spade, Rank.king⟩ (wild.piles Anchor.p0).faceUp))).putRun
    (fromCard ⟨Suit.spade, Rank.king⟩ (wild.piles Anchor.p0).faceUp)
    (Sum.inl Anchor.p6)

/-- REFUTATION (wild duplicate): the slide `tabToTab K♠ (inl p6)`
fires from p0 onto the empty p6, but the successor holding search
finds the duplicate on p3 first, so the mover's successor seat is
`inl p3` - the ungated one-point-edit row fails. -/
private theorem chart_tabToTab_ungated_false :
    ¬ ∀ {st s' : State} {c : Card} {b : Base},
      st.step (Move.tabToTab c b) = some s' →
      (∀ x, seatOf s' x = if x = c then some b else seatOf st x) := by
  intro h
  have hstep : wild.step
      (Move.tabToTab ⟨Suit.spade, Rank.king⟩ (Sum.inl Anchor.p6)) = some wild' := by
    rfl
  have hclaimed := @h wild wild' ⟨Suit.spade, Rank.king⟩ (Sum.inl Anchor.p6) hstep
    ⟨Suit.spade, Rank.king⟩
  rw [ite_eq_left rfl] at hclaimed
  have hs3 : wild'.pileHolding ⟨Suit.spade, Rank.king⟩ = some Anchor.p3 := by decide
  have hb : below ⟨Suit.spade, Rank.king⟩ (wild'.piles Anchor.p3).faceUp = [] := by rfl
  rw [tfc_seatOf_inl_intro hs3 hb] at hclaimed
  exact absurd hclaimed (by simp)

#print axioms chart_tabToTab_ungated_false
