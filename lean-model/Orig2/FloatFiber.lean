import Orig2.Vocab
import Orig2.Classification
import Orig2.CargoKit
import Orig2.FloaterLadder

/-!
# Orig2.FloatFiber — THE FLOATER QUARTET (the agent dry-run
promoted to a chartered card at owner approval, 2026-10-17)

PROMOTION PROVENANCE: dry-ran as `Temp/float_agent_check.lean`
(the shared-board four-row program), re-verified against the live
tree at promotion time (all four heads `[propext, Quot.sound]`,
zero sorry, zero `Classical.choice`), installed at owner approval
("sure can you help me do that incorporate the new theorem for me"
— same hour).

THE FOUR ROWS (the address-and-structural tier of the floater program —
the seat-edit, lift, and classification companions of the
`Orig2.FloaterLadder` card's three public rows):

* `floater_seat_change_spec` (their "Row 3") — the one-point chart
  edit realized by a reversible slide, and the class-STEP fiber:
  twin-family reseating or a bare king vacate — the SeatEdit-grade
  restatement of `FloaterLadder.floater_seat_change` (renamed at
  installation; no name collision with the ladder's row);
* `floater_cargo_lift` — a live, fiber-valid cell with a
  placement license fires as an actual reversible cargo leg
  realizing the SeatEdit spec;
* `floater_seat_to_equiv'` — with the round-trip chart readout as
  a PRICED HYPOTHESIS (never sorry'd: the chart pivot row rides
  where it belongs — priced in the claims book — and this row
  consumes it as a hypothesis, per the house never-force rule):
  a valid one-point SeatEdit at a live, fiber-valid cell derives
  the bare-cargo class;
* `floater_classification` — the structural classification: the
  behavioral Floater iff `FloaterSpec` (the target-existence
  shape: the company cell with its twin-fiber target, or the
  bare-king vacate cell).

KIT DISCIPLINE (2026-10-17 consolidation, owner call "full
extraction"): the `tfc_*`/`tfa_*` kit this card re-proved privately
per the per-file dedup discipline (the cut-record and the row briefs
live in the §H header below, kept from the dry-run verbatim) moved
VERBATIM, per-row frozen-home cites kept, to the shared home
`Orig2/CargoKit.lean` — byte-identical with the certified copy this
card dry-ran as.  Three never-referenced rows (`tfc_cnt_singleton`,
`tfc_cntFlat_map_congr`, the fresh `fli_cnt_append_left`) were pruned
at the 2026-10-17 cleanup pass rather than moved.  The §H1 placement
constructors (`tfa_canPlace_inl`/`tfa_canPlace_inr`/`tfa_fit_twin`)
stay here as this card's own restatements.  The four rows ride the
oracle bridge (`tabToTabR_iff_reversibleAtW`), constructive
placement rows, and the conservation/hiding rows — no
hand-assembled plays, no `reversible_mirrorW`, no choice.

IMPORT SURFACE: `Orig2.Vocab` + `Orig2.Classification` +
`Orig2.CargoKit` + `Orig2.FloaterLadder` (the ladder import is
presentational; nothing else enters above the certified seam).

GATE DISCIPLINE: every private row states its own gate; the three
public rows are the ONLY public artifact.  Zero sorry; the battery at
the tail expects `[propext]`/`[propext, Quot.sound]` on all three heads.
-/

/-! ## §H. THE AGENT DRY-RUN ADDENDUM (this copy only)

Snapshot protocol: everything above is a fresh verbatim snapshot of
the owner's `Temp/float_check.lean` kit regions (§A-§E6, frozen
docstrings kept).  Cut record: the owner's §F public rows
(`floater_iff`, `floater_hop_targets`, `floater_seat_change`, with
their battery) and §G (the wild-duplicate refutation around
`wild`/`wild'`) are NOT re-landed here — they are the owner's live
drafting, and this file's own `floater_seat_change` statement differs
from theirs (no name room); every `tfc_*` kit row they ride is kept
above and suffices without them.

The four rows under test here:

* Row 3  `floater_seat_change`  - the one-point chart edit realized by a
  reversible slide, and the class-STEP fiber: twin-family reseating or
  a bare king vacate;
* Row R1 `floater_cargo_lift`   - the reverse layer 1: a live, fiber-valid
  cell with a placement license fires as an actual reversible cargo
  leg realizing the spec;
* Row 2' `floater_seat_to_equiv'` - the reverse layer 2 modulo the priced
  keystone: with the round-trip chart readout as a HYPOTHESIS, a valid
  one-point seat spec derives the bare-cargo class;
* Row 1' `floater_classification` - the structural classification: the
  Floater iff the target-existence shape.

Method note, honestly recorded: every reversibility promise below is
carried by the oracle bridge `tabToTabR_iff_reversibleAtW` (public,
`Orig2/Classification.lean:2627`) — no hand-assembled witness plays,
and `Orig2.Kit.reversible_mirrorW` is not needed for them.  The priced
round-trip hypothesis of `floater_seat_to_equiv'` is hoisted TWICE:
once to identify the spec-mate with the real successor, and once to
pin the mirror's own successor to the origin — so the canonical mirror
never needs pile-level state surgery.  The reversible cells never
reveal, which is what the hidden-deck conservation row rides. -/

/-- **SeatEdit st w c β** — the one-point chart spec: w's chart is
st's with exactly the mover's value replaced by β; fixed readouts
agree. -/
def SeatEdit (st w : State) (c : Card) (β : Base) : Prop :=
  (∀ x, seatOf w x = if x = c then some β else seatOf st x) ∧
    boardFixed st w ∧ foundsFixed st w ∧
    drawPool st = drawPool w ∧ cutOf st = cutOf w

/-! ### §H1. The placement constructors
(fresh; the converses Kit's `canPlace_inl`/`canPlace_inr` do not
carry, plus the reversible-cell hidden conservation) -/

/-- The empty-seat placement, constructed (the converse of Kit's
`canPlace_inl`; the registry placement arm, `Orig/State.lean:348`). -/
private theorem tfa_canPlace_inl {st : State} {c : Card} {a : Anchor}
    (hemp : (st.piles a).isEmpty = true) (hkng : c.rank = Rank.king) :
    st.canPlace c (Sum.inl a) = true := by
  simp only [State.canPlace, Bool.and_eq_true]
  exact ⟨hemp, decide_eq_true hkng⟩

/-- The located card-on-card placement, constructed (the converse of
Kit's `canPlace_inr`; the located arm, `Orig/State.lean:349`). -/
private theorem tfa_canPlace_inr {st : State} {c z : Card} {k : Anchor}
    (hloc : st.pileOfTop z = some k) (hfit : canSitOn c z = true) :
    st.canPlace c (Sum.inr z) = true := by
  simp only [State.canPlace, hloc]
  exact hfit

/-- The twin relabeling keeps the fit (twin-blindness; rides
`canSitOn_twin_right` at `Orig/Basic.lean:119` through `Card.twin`'s
`Suit.twin` shape, `Orig2/Vocab.lean:425`). -/
private theorem tfa_fit_twin {c z : Card} (hfit : canSitOn c z = true) :
    canSitOn c z.twin = true := by
  have hz : z.twin = { z with suit := z.suit.twin } := rfl
  rw [hz, canSitOn_twin_right]
  exact hfit

/-! ### §H2. The four rows under test (the only public artifact of
the addendum) -/

/-- **floater_seat_change** — Row 3, the class-STEP fiber: a
reversible slide realizes the one-point chart edit at the mover (the
point-edit row plus the conservation row above), and the changed pair
is twin-family — the mover reseated at its parent's twin (two fitting
parents are equal-or-twin at `tfc_fitting_parent`, and the parent
itself tops no pile at `tfc_seat_parent`, so the strict parent is
excluded) — or the mover is a bare king vacating to an empty seat. -/
theorem floater_seat_change_spec {st s' : State} {c : Card} {b : Base}
    (hwf : st.WF) (hstep : State.step st (Move.tabToTab c b) = some s')
    (hrev : reversibleAtW st (Move.tabToTab c b)) :
    SeatEdit st s' c b ∧
    ((∃ z z', seatOf st c = some (Sum.inr z) ∧ b = Sum.inr z' ∧
        (z' = z ∨ z' = z.twin)) ∨
     (∃ a a', seatOf st c = some (Sum.inl a) ∧ b = Sum.inl a' ∧
        c.rank = Rank.king ∧ (st.piles a).hidden = [])) := by
  have hed := tfc_seat_point_edit hwf hstep hrev
  obtain ⟨hbf, hff, hdp, hco⟩ := tfa_slide_conserves hwf hstep hrev
  refine ⟨⟨hed, hbf, hff, hdp, hco⟩, ?_⟩
  obtain ⟨a, hhold, hcp, hbcell⟩ :=
    tfc_tabToTabR_inv ((tabToTabR_iff_reversibleAtW hwf c b).mpr hrev)
  rcases tfc_seat_cases hhold with ⟨z, hse⟩ | hse
  · obtain ⟨a1, hh1, hbNE, hlz⟩ := tfc_seatOf_of_inr hse
    obtain ⟨hsit, htopNone⟩ := tfc_seat_parent hwf hh1 hlz
    have hcnk : c.rank ≠ Rank.king := by
      obtain ⟨hidx, -⟩ := (canSitOn_eq c z).mp hsit
      have hzlt := Rank.toIdx_lt z.rank
      intro hk
      have h12 : c.rank.toIdx = 12 := by rw [hk]; rfl
      omega
    cases b with
    | inl a' =>
        obtain ⟨-, hking⟩ := canPlace_inl hcp
        exact (hcnk hking).elim
    | inr w =>
        obtain ⟨k, hlocw, hfitw⟩ := canPlace_inr hcp
        rcases tfc_fitting_parent hfitw hsit with heq | heq
        · exfalso
          rw [heq] at hlocw
          rw [htopNone] at hlocw
          nomatch hlocw
        · exact Or.inl ⟨z, w, hse, by rw [heq], by rw [heq]; exact Or.inr rfl⟩
  · obtain ⟨-, hbE⟩ := tfc_seatOf_of_inl hse
    have hkng : c.rank = Rank.king := by
      rcases hbcell with hbne | ⟨hb0, hhid, hk⟩
      · exact (hbne hbE).elim
      · exact hk
    cases b with
    | inr w =>
        exfalso
        obtain ⟨k, -, hfitw⟩ := canPlace_inr hcp
        obtain ⟨hidx, -⟩ := (canSitOn_eq c w).mp hfitw
        have hlt := Rank.toIdx_lt w.rank
        have h12 : c.rank.toIdx = 12 := by rw [hkng]; rfl
        omega
    | inl a' =>
        rcases hbcell with hbne | ⟨hb0, hhid, -⟩
        · exact (hbne hbE).elim
        · exact Or.inr ⟨a, a', hse, rfl, hkng, hhid⟩

/-- **floater_cargo_lift** — the reverse layer 1: a live, fiber-valid
cell plus a placement license FIRES as an actual reversible cargo leg
whose successor realizes the chart spec (the oracle bridge carries
the reversibility; the point-edit row and the conservation row carry
the SeatEdit). -/
theorem floater_cargo_lift {st : State} {c : Card} {β : Base} (hwf : st.WF)
    (hmove : st.canPlace c β = true)
    (hcell : (∃ z, seatOf st c = some (Sum.inr z)) ∨
      ∃ a, seatOf st c = some (Sum.inl a) ∧ c.rank = Rank.king ∧
        (st.piles a).hidden = []) :
    ∃ w, st.step (Move.tabToTab c β) = some w ∧
      reversibleAtW st (Move.tabToTab c β) ∧ SeatEdit st w c β := by
  have hR : tabToTabR st c β = true := by
    rcases hcell with ⟨z, hse⟩ | ⟨a, hse, hkng, hhid⟩
    · obtain ⟨a1, hh1, hbNE, -⟩ := tfc_seatOf_of_inr hse
      show tabToTabR st c β = true
      simp only [tabToTabR, hh1, hmove]
      cases hb : below c ((st.piles a1).faceUp) with
      | cons y ys => rfl
      | nil => exact (hbNE hb).elim
    · obtain ⟨hh2, hbE⟩ := tfc_seatOf_of_inl hse
      show tabToTabR st c β = true
      simp only [tabToTabR, hh2, hmove, hbE, hhid]
      rw [hkng]
      rfl
  have hrev : reversibleAtW st (Move.tabToTab c β) :=
    (tabToTabR_iff_reversibleAtW hwf c β).mp hR
  obtain ⟨w, play, hstep, hrun⟩ := hrev
  obtain ⟨hbf, hff, hdp, hco⟩ :=
    tfa_slide_conserves hwf hstep ⟨w, play, hstep, hrun⟩
  exact ⟨w, hstep, ⟨w, play, hstep, hrun⟩,
    ⟨tfc_seat_point_edit hwf hstep ⟨w, play, hstep, hrun⟩, hbf, hff, hdp, hco⟩⟩

/-! ### §H3. Row 1' — the classification -/

/-- **FloaterSpec st c** — the structural read of the floater: the
company cell (c seated on a parent whose twin tops some pile — the
twin-fiber target exists) or the bare-king cell on an empty-hidden
pile with a second empty pile to vacate to. -/
def FloaterSpec (st : State) (c : Card) : Prop :=
  (∃ z a, seatOf st c = some (Sum.inr z) ∧ st.pileHolding c = some a ∧
      ((∃ k, st.pileOfTop z.twin = some k) ∨
        (c.rank = Rank.king ∧ ∃ a', (st.piles a').isEmpty = true))) ∨
  (∃ a, seatOf st c = some (Sum.inl a) ∧ c.rank = Rank.king ∧
      (st.piles a).hidden = [] ∧ ∃ a', (st.piles a').isEmpty = true)

/-- **floater_classification** — Row 1': the behavioral Floater (some
reversible slide exists) iff the target-existence shape.  Forward:
the oracle cell unpacked by `tfc_tabToTabR_inv` places the mover, and
the fitting-parent arithmetic names the target (the twin pile or the
empty seat).  Backward: the named target licenses the placement
(constructed), the cell licenses the oracle, and the bridge
re-exports the witness. -/
theorem floater_classification (st : State) (hwf : st.WF) (c : Card) :
    Floater st c ↔ FloaterSpec st c := by
  constructor
  · intro hF
    obtain ⟨b₀, hrev⟩ := hF
    obtain ⟨a, hhold, hcp, hbcell⟩ :=
      tfc_tabToTabR_inv ((tabToTabR_iff_reversibleAtW hwf c b₀).mpr hrev)
    rcases hbcell with hbne | ⟨hb0, hhid, hkng⟩
    · obtain ⟨z, hlz⟩ := lastOf_exists hbne
      have hse : seatOf st c = some (Sum.inr z) := tfc_seatOf_inr_intro hhold hlz
      obtain ⟨hsit, htopNone⟩ := tfc_seat_parent hwf hhold hlz
      have hcnk : c.rank ≠ Rank.king := by
        obtain ⟨hidx, -⟩ := (canSitOn_eq c z).mp hsit
        have hzlt := Rank.toIdx_lt z.rank
        intro hk
        have h12 : c.rank.toIdx = 12 := by rw [hk]; rfl
        omega
      cases b₀ with
      | inl a' =>
          obtain ⟨-, hking⟩ := canPlace_inl hcp
          exact (hcnk hking).elim
      | inr w₀ =>
          obtain ⟨k, hlocw, hfitw⟩ := canPlace_inr hcp
          rcases tfc_fitting_parent hfitw hsit with heq | heq
          · exfalso
            rw [heq] at hlocw
            rw [htopNone] at hlocw
            nomatch hlocw
          · refine Or.inl ⟨z, a, hse, hhold, Or.inl ⟨k, ?_⟩⟩
            rw [← heq]
            exact hlocw
    · have hse : seatOf st c = some (Sum.inl a) := tfc_seatOf_inl_intro hhold hb0
      cases b₀ with
      | inr w₀ =>
          exfalso
          obtain ⟨k, -, hfitw⟩ := canPlace_inr hcp
          obtain ⟨hidx, -⟩ := (canSitOn_eq c w₀).mp hfitw
          have hlt := Rank.toIdx_lt w₀.rank
          have h12 : c.rank.toIdx = 12 := by rw [hkng]; rfl
          omega
      | inl a' =>
          obtain ⟨hE, -⟩ := canPlace_inl hcp
          exact Or.inr ⟨a, hse, hkng, hhid, a', hE⟩
  · intro hspec
    rcases hspec with ⟨z, a, hse, hhold, harm⟩ | ⟨a, hse, hkng, hhid, a', hempty⟩
    · rcases harm with ⟨k, hlocT⟩ | ⟨hkng2, -⟩
      · obtain ⟨a1, hh1, hbNE, hlz⟩ := tfc_seatOf_of_inr hse
        obtain ⟨hsit, -⟩ := tfc_seat_parent hwf hh1 hlz
        have hfitT : canSitOn c z.twin = true := tfa_fit_twin hsit
        have hcp : st.canPlace c (Sum.inr z.twin) = true :=
          tfa_canPlace_inr hlocT hfitT
        refine ⟨Sum.inr z.twin, (tabToTabR_iff_reversibleAtW hwf c _).mp ?_⟩
        show tabToTabR st c (Sum.inr z.twin) = true
        simp only [tabToTabR, hh1, hcp]
        cases hb : below c ((st.piles a1).faceUp) with
        | cons y ys => rfl
        | nil => exact (hbNE hb).elim
      · exfalso
        obtain ⟨a1, hh1, hbNE, hlz⟩ := tfc_seatOf_of_inr hse
        obtain ⟨hsit, -⟩ := tfc_seat_parent hwf hh1 hlz
        obtain ⟨hidx, -⟩ := (canSitOn_eq c z).mp hsit
        have hzlt := Rank.toIdx_lt z.rank
        have h12 : c.rank.toIdx = 12 := by rw [hkng2]; rfl
        omega
    · obtain ⟨hh2, hbE⟩ := tfc_seatOf_of_inl hse
      have hcp : st.canPlace c (Sum.inl a') = true :=
        tfa_canPlace_inl hempty hkng
      refine ⟨Sum.inl a', (tabToTabR_iff_reversibleAtW hwf c _).mp ?_⟩
      show tabToTabR st c (Sum.inl a') = true
      simp only [tabToTabR, hh2, hcp, hbE, hhid]
      rw [hkng]
      rfl

/-! ### §H4. Row 2' — the reverse layer 2, modulo the priced keystone -/

/-- **floater_seat_to_equiv'** — the reverse layer 2 modulo the priced
round trip (the registry prices it as `chart_round_trip`; here it is
a HYPOTHESIS, not a sorry): a valid one-point seat spec at a live,
fiber-valid cell derives the bare-cargo class.  Strategy: the lift
(the reverse layer 1) produces the real successor; the two chart-mates
coincide by the hypothesis; the canonical mirror at the successor
(the old seat as the base) certifies by the ORACLE at the successor,
and the chartAgree-ladder plus the hypothesis pin ITS successor to the
origin — the two legs then assemble the class by hand. -/
theorem floater_seat_to_equiv' {st w : State} {c : Card} {β : Base}
    (hwf : st.WF)
    (hroundtrip : ∀ A B, chartAgree A B → A = B)
    (hspec : SeatEdit st w c β)
    (hmove : st.canPlace c β = true)
    (hcell : (∃ z, seatOf st c = some (Sum.inr z)) ∨
      ∃ a, seatOf st c = some (Sum.inl a) ∧ c.rank = Rank.king ∧
        (st.piles a).hidden = []) :
    BareCargoEquiv st w := by
  obtain ⟨s1, hstepL, hrevL, ⟨hedL, hbfL, hffL, hdpL, hcoL⟩⟩ :=
    floater_cargo_lift hwf hmove hcell
  obtain ⟨hseatW, hbfW, hffW, hdpW, hcoW⟩ := hspec
  have hchart : chartAgree w s1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x
      rw [hseatW x, hedL x]
    · obtain ⟨h1, h2⟩ := hbfW
      obtain ⟨h3, h4⟩ := hbfL
      exact ⟨fun j => (h1 j).symm.trans (h3 j), h2.symm.trans h4⟩
    · intro s0
      exact (hffW s0).symm.trans (hffL s0)
    · exact hdpW.symm.trans hdpL
    · exact hcoW.symm.trans hcoL
  have hws : w = s1 := hroundtrip w s1 hchart
  rw [← hws] at hstepL hedL hbfL hffL hdpL hcoL
  have WWF : w.WF := tfc_tabToTab_wf hwf hstepL
  obtain ⟨a0, hhold0, hcp0, hfr, hs1shape⟩ := step_tabToTab_inv hstepL
  obtain ⟨tr, hcrr⟩ := tfc_fromCard_cons_head _ (pileHolding_mem hhold0)
  rw [hcrr] at hs1shape
  have hcctx : c ∈ (st.piles a0).faceUp := pileHolding_mem hhold0
  rcases hcell with ⟨z, hse⟩ | ⟨aC, hseC, hkngC, hhidC⟩
  · obtain ⟨a1, hh1, hbNE, hlz⟩ := tfc_seatOf_of_inr hse
    have ha1 : a1 = a0 := Option.some.inj (hh1.symm.trans hhold0)
    rw [ha1] at hh1 hbNE hlz
    obtain ⟨hsit, htopNone⟩ := tfc_seat_parent hwf hh1 hlz
    have hcnk : c.rank ≠ Rank.king := by
      obtain ⟨hidx, -⟩ := (canSitOn_eq c z).mp hsit
      have hzlt := Rank.toIdx_lt z.rank
      intro hk
      have h12 : c.rank.toIdx = 12 := by rw [hk]; rfl
      omega
    cases β with
    | inl a' =>
        exfalso
        obtain ⟨-, hking⟩ := canPlace_inl hcp0
        exact (hcnk hking).elim
    | inr w₀ =>
        obtain ⟨k, hlocw, hfitw⟩ := canPlace_inr hcp0
        have hka : k ≠ a0 := tfc_mover_pile_not_target hwf hhold0 hlocw hfitw
        have hak0 : a0 ≠ k := fun hh => hka hh.symm
        have hccw : st.cardCount w₀ = 1 := hwf.2.2.1 w₀ (Card.mem_universe w₀)
        have hktopk : lastOf ((st.piles k).faceUp) = some w₀ :=
          (tfc_pileOfTop_top hlocw).2
        have hMk : (st.setPile a0 (Pile.afterRunRemoved (st.piles a0)
            (below c ((st.piles a0).faceUp)))).piles k = st.piles k :=
          setPile_piles_ne hka
        have hlocM : (st.setPile a0 (Pile.afterRunRemoved (st.piles a0)
            (below c ((st.piles a0).faceUp)))).pileOfTop w₀ = some k := by
          have hmidk : (st.setPile a0 (Pile.afterRunRemoved (st.piles a0)
              (below c ((st.piles a0).faceUp)))).topOf k = some w₀ := by
            show lastOf ((st.setPile a0 (Pile.afterRunRemoved (st.piles a0)
              (below c ((st.piles a0).faceUp)))).piles k).faceUp = some w₀
            rw [hMk]
            exact hktopk
          refine firstWhere_find (Anchor.mem_all k) (decide_eq_true hmidk) ?_
          intro j _ hjk
          by_cases hja : j = a0
          · rw [hja]
            refine decide_false_of_not ?_
            intro hcon
            have hset : (st.setPile a0 (Pile.afterRunRemoved (st.piles a0)
                (below c ((st.piles a0).faceUp)))).piles a0
                = Pile.afterRunRemoved (st.piles a0)
                    (below c ((st.piles a0).faceUp)) :=
              setPile_piles_self
            have hcon0 : lastOf (Pile.afterRunRemoved (st.piles a0)
                (below c ((st.piles a0).faceUp))).faceUp = some w₀ := by
              have hp : ((st.setPile a0 (Pile.afterRunRemoved (st.piles a0)
                  (below c ((st.piles a0).faceUp)))).piles a0).top = some w₀ := hcon
              rw [hset] at hp
              exact hp
            have hznew : w₀ ∈ (Pile.afterRunRemoved (st.piles a0)
                (below c ((st.piles a0).faceUp))).faceUp := lastOf_mem hcon0
            have hzone : w₀ ∈ (Pile.afterRunRemoved (st.piles a0)
                (below c ((st.piles a0).faceUp))).hidden
                ++ (Pile.afterRunRemoved (st.piles a0)
                  (below c ((st.piles a0).faceUp))).faceUp :=
              List.mem_append.mpr (Or.inr hznew)
            have hzold : w₀ ∈ (st.piles a0).hidden ++ (st.piles a0).faceUp :=
              tfc_mem_afterRunRemoved_below_zone hzone
            have hzk : w₀ ∈ (st.piles k).hidden ++ (st.piles k).faceUp :=
              List.mem_append.mpr (Or.inr (lastOf_mem hktopk))
            exact tfc_two_pile_zone_absurd hak0 hccw hzold hzk
          · refine decide_false_of_not ?_
            intro hcon
            have hcon2 : st.topOf j = some w₀ := by
              have hp : ((st.setPile a0 (Pile.afterRunRemoved (st.piles a0)
                  (below c ((st.piles a0).faceUp)))).piles j).top = some w₀ := hcon
              rw [setPile_piles_ne hja] at hp
              exact hp
            exact hjk (tfc_top_search_unique hccw hcon2 hktopk)
        rw [putRun_inr_eq hlocM] at hs1shape
        have hface : (st.piles a0).faceUp
            = below c ((st.piles a0).faceUp) ++ (c :: tr) := by
          have h0 := tfc_below_fromCard c ((st.piles a0).faceUp)
          rw [hcrr] at h0
          exact h0.symm
        have hAface : (w.piles a0).faceUp
            = below c ((st.piles a0).faceUp) := by
          rw [hs1shape, setPile_piles_ne hak0, setPile_piles_self,
            afterRunRemoved_ne hbNE]
        have hKface : (w.piles k).faceUp = (st.piles k).faceUp ++ (c :: tr) := by
          rw [hs1shape, setPile_piles_self, hMk]
        have hOther : ∀ j, j ≠ a0 → j ≠ k →
            (w.piles j).faceUp = (st.piles j).faceUp := by
          intro j hja0 hjk
          rw [hs1shape, setPile_piles_ne hjk, setPile_piles_ne hja0]
        have hwseat : seatOf w c = some (Sum.inr w₀) := by
          have hbc := hedL c
          rwa [ite_eq_left rfl] at hbc
        have hwHold : w.pileHolding c = some k := by
          cases hq : w.pileHolding c with
          | none =>
              exfalso
              have hnone := tfc_seatOf_none hq
              rw [hwseat] at hnone
              nomatch hnone
          | some q =>
              have hmemk : c ∈ (w.piles k).faceUp := by
                rw [hKface]
                exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
              rw [tfc_holding_pin' WWF hq hmemk]
        have hlocWz : w.pileOfTop z = some a0 := by
          show firstWhere (fun a => decide (w.topOf a = some z)) Anchor.all
            = some a0
          have hmidk : w.topOf a0 = some z := by
            show lastOf ((w.piles a0).faceUp) = some z
            rw [hAface]
            exact hlz
          refine firstWhere_find (Anchor.mem_all a0) (decide_eq_true hmidk) ?_
          intro j _ hja0
          by_cases hjk : j = k
          · rw [hjk]
            refine decide_false_of_not ?_
            intro hcon
            have hcon0 : lastOf ((st.piles k).faceUp ++ (c :: tr)) = some z := by
              have hp : lastOf ((w.piles k).faceUp) = some z := hcon
              rw [hKface] at hp
              exact hp
            have hzne : (c :: tr : List Card) ≠ [] := by simp
            rw [tfc_lastOf_append_ne _ hzne] at hcon0
            have hlast : z ∈ (c :: tr) := lastOf_mem hcon0
            exact tfc_two_mem_faceUp_absurd hwf hface (lastOf_mem hlz) hlast
          · refine decide_false_of_not ?_
            intro hjj
            have hp0 : lastOf ((w.piles j).faceUp) = some z := hjj
            rw [hOther j hja0 hjk] at hp0
            have h1 := tfc_firstWhere_mem_true
              (p := fun a => decide (st.topOf a = some z)) Anchor.all j
              (Anchor.mem_all j)
              (decide_eq_true (show st.topOf j = some z from hp0))
            rw [show st.pileOfTop z
                  = firstWhere (fun a => decide (st.topOf a = some z)) Anchor.all
                from rfl] at htopNone
            rw [htopNone] at h1
            exact h1 rfl
        have hcpWz : w.canPlace c (Sum.inr z) = true :=
          tfa_canPlace_inr hlocWz hsit
        have hcnk' : c ∉ (st.piles k).faceUp := tfc_faceUp_uniq_other hwf hcctx hka
        have hbelowEq : below c ((w.piles k).faceUp)
            = (st.piles k).faceUp := by
          have h1 : below c ((w.piles k).faceUp)
              = below c ((st.piles k).faceUp ++ (c :: tr)) := by
            rw [← hKface]
          rw [h1, (tfc_below_fromCard_excl c (st.piles k).faceUp (c :: tr) hcnk').1,
            below_cons, ite_eq_left rfl, List.append_nil]
        have hbelowWne : below c ((w.piles k).faceUp) ≠ [] := by
          rw [hbelowEq]
          exact (tfc_pileOfTop_top hlocw).1
        have hRw : tabToTabR w c (Sum.inr z) = true := by
          show tabToTabR w c (Sum.inr z) = true
          simp only [tabToTabR, hwHold, hcpWz]
          cases hb : below c ((w.piles k).faceUp) with
          | cons y ys => rfl
          | nil => exact (hbelowWne hb).elim
        have hrevW := (tabToTabR_iff_reversibleAtW WWF c (Sum.inr z)).mp hRw
        obtain ⟨u, playU, hstepU, hrunU⟩ := hrevW
        have hedU := tfc_seat_point_edit WWF hstepU ⟨u, playU, hstepU, hrunU⟩
        obtain ⟨hbfWU, hffWU, hdpWU, hcoWU⟩ :=
          tfa_slide_conserves WWF hstepU ⟨u, playU, hstepU, hrunU⟩
        have hchartU : chartAgree u st := by
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · intro x
            by_cases hxc : x = c
            · rw [hxc]
              have hxU := hedU c
              rw [hxU, ite_eq_left rfl]
              exact hse.symm
            · have hxU := hedU x
              have hxW := hedL x
              rw [hxU, ite_eq_right hxc, hxW, ite_eq_right hxc]
          · obtain ⟨h1, h2⟩ := hbfL
            obtain ⟨h3, h4⟩ := hbfWU
            exact ⟨fun j => (h3 j).symm.trans (h1 j).symm, h4.symm.trans h2.symm⟩
          · intro s0
            exact (hffWU s0).symm.trans (hffL s0).symm
          · exact hdpWU.symm.trans hdpL.symm
          · exact hcoWU.symm.trans hcoL.symm
        have hu : u = st := hroundtrip u st hchartU
        rw [hu] at hstepU hrunU
        exact ⟨Steps.cons ⟨c, Sum.inr w₀, hstepL, hrevL⟩ (Steps.refl w),
          Steps.cons ⟨c, Sum.inr z, hstepU, ⟨st, playU, hstepU, hrunU⟩⟩ (Steps.refl st)⟩
  · obtain ⟨hh2C, hbE⟩ := tfc_seatOf_of_inl hseC
    have haC : aC = a0 := Option.some.inj (hh2C.symm.trans hhold0)
    rw [haC] at hseC hbE hhidC
    cases β with
    | inr w₀ =>
        exfalso
        obtain ⟨k, -, hfitw⟩ := canPlace_inr hcp0
        obtain ⟨hidx, -⟩ := (canSitOn_eq c w₀).mp hfitw
        have hlt := Rank.toIdx_lt w₀.rank
        have h12 : c.rank.toIdx = 12 := by rw [hkngC]; rfl
        omega
    | inl a' =>
        have hA0a' : a0 ≠ a' := by
          intro heq
          rw [heq] at hhold0
          have hmem : c ∈ (st.piles a').faceUp := pileHolding_mem hhold0
          have hemp : (st.piles a').isEmpty = true := (canPlace_inl hcp0).1
          rw [Pile.isEmpty_eq_false_of_mem hmem] at hemp
          exact Bool.noConfusion hemp
        rw [putRun_eq_inl] at hs1shape
        have hAempty : (w.piles a0) = ⟨[], ([] : List Card)⟩ := by
          rw [hs1shape, setPile_piles_ne hA0a', setPile_piles_self, hbE,
            Pile.afterRunRemoved_bare hhidC]
        have hWface : (w.piles a').faceUp = c :: tr := by
          rw [hs1shape, setPile_piles_self]
        have hwseat : seatOf w c = some (Sum.inl a') := by
          have hbc := hedL c
          rwa [ite_eq_left rfl] at hbc
        have hwHold : w.pileHolding c = some a' := by
          cases hq : w.pileHolding c with
          | none =>
              exfalso
              have hnone := tfc_seatOf_none hq
              rw [hwseat] at hnone
              nomatch hnone
          | some q =>
              have hmemk : c ∈ (w.piles a').faceUp := by
                rw [hWface]
                exact List.mem_cons_self
              rw [tfc_holding_pin' WWF hq hmemk]
        have hipsA0 : (w.piles a0).isEmpty = true := by
          rw [hAempty]
          rfl
        have hcpW : w.canPlace c (Sum.inl a0) = true :=
          tfa_canPlace_inl hipsA0 hkngC
        have hbelowW : below c ((w.piles a').faceUp) = [] := by
          rw [hWface, below_cons, ite_eq_left rfl]
        have hhiddenW : (w.piles a').hidden = [] := by
          rw [hs1shape, setPile_piles_self]
        have hRw : tabToTabR w c (Sum.inl a0) = true := by
          show tabToTabR w c (Sum.inl a0) = true
          simp only [tabToTabR, hwHold, hcpW, hbelowW, hhiddenW]
          rw [hkngC]
          rfl
        have hrevW := (tabToTabR_iff_reversibleAtW WWF c (Sum.inl a0)).mp hRw
        obtain ⟨u, playU, hstepU, hrunU⟩ := hrevW
        have hedU := tfc_seat_point_edit WWF hstepU ⟨u, playU, hstepU, hrunU⟩
        obtain ⟨hbfWU, hffWU, hdpWU, hcoWU⟩ :=
          tfa_slide_conserves WWF hstepU ⟨u, playU, hstepU, hrunU⟩
        have hchartU : chartAgree u st := by
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · intro x
            by_cases hxc : x = c
            · rw [hxc]
              have hxU := hedU c
              rw [hxU, ite_eq_left rfl]
              exact hseC.symm
            · have hxU := hedU x
              have hxW := hedL x
              rw [hxU, ite_eq_right hxc, hxW, ite_eq_right hxc]
          · obtain ⟨h1, h2⟩ := hbfL
            obtain ⟨h3, h4⟩ := hbfWU
            exact ⟨fun j => (h3 j).symm.trans (h1 j).symm, h4.symm.trans h2.symm⟩
          · intro s0
            exact (hffWU s0).symm.trans (hffL s0).symm
          · exact hdpWU.symm.trans hdpL.symm
          · exact hcoWU.symm.trans hcoL.symm
        have hu : u = st := hroundtrip u st hchartU
        rw [hu] at hstepU hrunU
        exact ⟨Steps.cons ⟨c, Sum.inl a', hstepL, hrevL⟩ (Steps.refl w),
          Steps.cons ⟨c, Sum.inl a0, hstepU, ⟨st, playU, hstepU, hrunU⟩⟩ (Steps.refl st)⟩
/-! ### §H5. THE IFF RESTATINGS — the class characterization.  Two
grades: the per-slide oracle re-read at the seat algebra, and the
book's top row: the bare-cargo class IS the iterated one-point
floater-edit closure of the chart. -/

/-- **FloaterCell st c** — the live, fiber-valid cell: the mover sits
on a card (company), or bottoms an empty-hidden pile as a bare king.
The common cell premise of the reverse rows, named for the iffs. -/
def FloaterCell (st : State) (c : Card) : Prop :=
  (∃ z, seatOf st c = some (Sum.inr z)) ∨
    ∃ a, seatOf st c = some (Sum.inl a) ∧ c.rank = Rank.king ∧
      (st.piles a).hidden = []

/-- **slide_reversible_iff_cell** — the per-slide oracle at the seat
algebra: at a WF origin, a slide's witness reversibility is exactly
the placement license together with a live cell (the R-shape's
below/hidden cases re-read as seat shapes). -/
theorem slide_reversible_iff_cell {st : State} {c : Card} {b : Base}
    (hwf : st.WF) :
    reversibleAtW st (Move.tabToTab c b) ↔
      st.canPlace c b = true ∧ FloaterCell st c := by
  constructor
  · intro hrev
    obtain ⟨a, hhold, hcp, hbcell⟩ :=
      tfc_tabToTabR_inv ((tabToTabR_iff_reversibleAtW hwf c b).mpr hrev)
    rcases hbcell with hbne | ⟨hb0, hhid, hkng⟩
    · obtain ⟨z, hlz⟩ := lastOf_exists hbne
      exact ⟨hcp, Or.inl ⟨z, tfc_seatOf_inr_intro hhold hlz⟩⟩
    · exact ⟨hcp, Or.inr ⟨a, tfc_seatOf_inl_intro hhold hb0, hkng, hhid⟩⟩
  · intro hpair
    obtain ⟨-, -, hrev, -⟩ := floater_cargo_lift hwf hpair.1 hpair.2
    exact hrev

/-- **floaterSpec_iff_cargoEdit** — the PER-CARD flat iff: c's target
spec is exactly the existence of a licensed one-point class edit at c
— a bare-cargo class-mate w whose chart is st's with exactly c's
seat edited, mover-licensed, at a live cell.  Forward: the spec's
named target licenses the placement (constructed), the lift realizes
the edit, and the priced round trip carries the class; backward: the
lift alone re-exports the floater, and the classification re-exports
the spec.  (This is the flat "FloaterSpec + condition" grade — the
class-grade iff needs the iterated closure below, since composed
hops separate charts at more than one card.) -/
theorem floaterSpec_iff_cargoEdit {st : State} (hwf : st.WF)
    (hroundtrip : ∀ A B, chartAgree A B → A = B) (c : Card) :
    FloaterSpec st c ↔
      ∃ (w : State) (b : Base), BareCargoEquiv st w ∧ SeatEdit st w c b ∧
        st.canPlace c b = true ∧ FloaterCell st c := by
  constructor
  · intro hspec
    rcases hspec with ⟨z, a, hse, hhold, harm⟩ | ⟨a, hse, hkng, hhid, a', hempty⟩
    · rcases harm with ⟨k, hlocT⟩ | ⟨hkng2, -⟩
      · obtain ⟨a1, hh1, hbNE, hlz⟩ := tfc_seatOf_of_inr hse
        obtain ⟨hsit, -⟩ := tfc_seat_parent hwf hh1 hlz
        have hmove : st.canPlace c (Sum.inr z.twin) = true :=
          tfa_canPlace_inr hlocT (tfa_fit_twin hsit)
        have hcell : FloaterCell st c := Or.inl ⟨z, hse⟩
        obtain ⟨w, hstepL, hrevL, hsed⟩ := floater_cargo_lift hwf hmove hcell
        exact ⟨w, Sum.inr z.twin,
          floater_seat_to_equiv' hwf hroundtrip hsed hmove hcell, hsed, hmove, hcell⟩
      · exfalso
        obtain ⟨a1, hh1, hbNE, hlz⟩ := tfc_seatOf_of_inr hse
        obtain ⟨hsit, -⟩ := tfc_seat_parent hwf hh1 hlz
        obtain ⟨hidx, -⟩ := (canSitOn_eq c z).mp hsit
        have hzlt := Rank.toIdx_lt z.rank
        have h12 : c.rank.toIdx = 12 := by rw [hkng2]; rfl
        omega
    · have hcell : FloaterCell st c := Or.inr ⟨a, hse, hkng, hhid⟩
      have hmove : st.canPlace c (Sum.inl a') = true :=
        tfa_canPlace_inl hempty hkng
      obtain ⟨w, hstepL, hrevL, hsed⟩ := floater_cargo_lift hwf hmove hcell
      exact ⟨w, Sum.inl a',
        floater_seat_to_equiv' hwf hroundtrip hsed hmove hcell, hsed, hmove, hcell⟩
  · intro hmate
    obtain ⟨w, b, -, -, hmove, hcell⟩ := hmate
    obtain ⟨-, -, hrev, -⟩ := floater_cargo_lift hwf hmove hcell
    exact (floater_classification st hwf c).mp ⟨b, hrev⟩

/-- **floater_iff_cargoEdit** — the registry-grade companion: the
BEHAVIORAL Floater (the registry's `Floater`, `Orig2/Vocab.lean §10`)
is exactly the existence of a licensed one-point class edit at the
mover — the classification row composed with the spec row above. -/
theorem floater_iff_cargoEdit {st : State} (hwf : st.WF)
    (hroundtrip : ∀ A B, chartAgree A B → A = B) (c : Card) :
    Floater st c ↔
      ∃ (w : State) (b : Base), BareCargoEquiv st w ∧ SeatEdit st w c b ∧
        st.canPlace c b = true ∧ FloaterCell st c :=
  (floater_classification st hwf c).trans (floaterSpec_iff_cargoEdit hwf hroundtrip c)

/-- **ChartEdits st w** — THE ONE-POINT FLOATER-EDIT CLOSURE: w is
reached from st by zero or more licensed singleton chart edits, each
at a live cell, each edited mate a WF state. -/
inductive ChartEdits : State → State → Prop
  | nil (st : State) : ChartEdits st st
  | cons {st u w : State} {c : Card} {β : Base}
      (hwfu : u.WF) (hedit : SeatEdit st u c β)
      (hmove : st.canPlace c β = true) (hcell : FloaterCell st c)
      (hrest : ChartEdits u w) : ChartEdits st w

/-- Chains of the generic pair closure concatenate (the Steps
companion of `Walk_append`, `Orig2/Vocab.lean:259`; fresh, same
induction). -/
private theorem steps_append {Q : State → State → Prop} : ∀ {a b : State},
    Steps Q a b → ∀ {c : State}, Steps Q b c → Steps Q a c := by
  intro a b h
  induction h with
  | refl s => intro c h₂; exact h₂
  | @cons s0 s1 s2 hl _ ih =>
      intro c h₂
      exact .cons hl (ih h₂)

/-- The bare-cargo class is transitive (chain concatenation, both
directions). -/
private theorem bareCargo_trans {a b c : State}
    (h₁ : BareCargoEquiv a b) (h₂ : BareCargoEquiv b c) :
    BareCargoEquiv a c := by
  obtain ⟨p1, p2⟩ := h₁
  obtain ⟨q1, q2⟩ := h₂
  exact ⟨steps_append p1 q1, steps_append q2 p2⟩

/-- The forward half: every reversible cargo leg IS one one-point
chart edit (the point-edit row, the conservation row, and the cell
unpacking), so a cargo path unrolls into the edit closure.  This half
consumes ONE direction of the class and needs no round trip. -/
private theorem chartEdits_of_cargoPath : ∀ {s w : State},
    Steps CargoLeg s w → s.WF → ChartEdits s w := by
  intro s w h
  induction h with
  | refl s' =>
      intro _
      exact .nil s'
  | @cons s0 s1 s2 hleg hrest ih =>
      intro hwf0
      obtain ⟨c₀, b₀, hstep, hrev⟩ := hleg
      obtain ⟨a, hhold, hcp, hbcell⟩ :=
        tfc_tabToTabR_inv ((tabToTabR_iff_reversibleAtW hwf0 c₀ b₀).mpr hrev)
      have hed' := tfc_seat_point_edit hwf0 hstep hrev
      obtain ⟨hbfE, hffE, hdpE, hcoE⟩ := tfa_slide_conserves hwf0 hstep hrev
      have hcell : FloaterCell s0 c₀ := by
        rcases hbcell with hbne | ⟨hb0, hhid, hkng⟩
        · obtain ⟨z, hlz⟩ := lastOf_exists hbne
          exact Or.inl ⟨z, tfc_seatOf_inr_intro hhold hlz⟩
        · exact Or.inr ⟨a, tfc_seatOf_inl_intro hhold hb0, hkng, hhid⟩
      have hwfs1 := tfc_tabToTab_wf hwf0 hstep
      exact .cons hwfs1 ⟨hed', hbfE, hffE, hdpE, hcoE⟩ hcp hcell (ih hwfs1)

/-- The backward half: each closure step is a real class-mate (the
lift fires, the priced round trip pins the spec-mate to the real
successor), and the class is transitive. -/
private theorem bareCargo_of_chartEdits (hroundtrip : ∀ A B, chartAgree A B → A = B) :
    ∀ {s w : State}, ChartEdits s w → s.WF → BareCargoEquiv s w := by
  intro s w h
  induction h with
  | nil s' =>
      intro _
      exact ⟨Steps.refl s', Steps.refl s'⟩
  | @cons s0 s1 s2 c₀ b₀ hwfs1 hedit hmove hcell hrest ih =>
      intro hwf0
      exact bareCargo_trans
        (floater_seat_to_equiv' hwf0 hroundtrip hedit hmove hcell) (ih hwfs1)

/-- **bareCargo_iff_chartEdits** — the class iff: two positions are
bare-cargo equivalent EXACTLY when one is reached from the other by
iterating licensed one-point floater edits of the chart (each step at
a live cell, mover-licensed, mates staying WF).  The forward half
consumes only the one-way cargo path (and needs no round trip); the
backward half hoists the priced chart round trip once and rides the
reverse-layer rows per edit. -/
theorem bareCargo_iff_chartEdits {st w : State} (hwf : st.WF)
    (hroundtrip : ∀ A B, chartAgree A B → A = B) :
    BareCargoEquiv st w ↔ ChartEdits st w := by
  constructor
  · exact fun hpair => chartEdits_of_cargoPath hpair.1 hwf
  · exact fun h => bareCargo_of_chartEdits hroundtrip h hwf

/-! ## The battery (the fiber card's heads) -/

#print axioms floater_seat_change_spec
#print axioms floater_cargo_lift
#print axioms floater_seat_to_equiv'
#print axioms floater_classification
#print axioms slide_reversible_iff_cell
#print axioms floaterSpec_iff_cargoEdit
#print axioms floater_iff_cargoEdit
#print axioms bareCargo_iff_chartEdits
