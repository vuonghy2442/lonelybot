import Orig2.Vocab
import Orig2.Classification
import Orig2.StepWF
import Orig2.FloatOrbit
import Orig2.PairClassSeed

/-!
# Orig2.CargoRaise — THE CARGO BRIDGE (the flat characterization's
migration wave, stage 2)

THE MISSION: `CanRaiseS` as CARGO-REACHABILITY OF A VANILLA RAISE —
the {slide · raise} closure is exactly the cargo path span:

  `CanRaiseS st c ↔ ∃ z, CargoPath st z ∧ CanRaise z c`

The via-leg IS `CargoLeg` by definition — the identical ∃-shape at
`Vocab`'s `CanRaiseS.via` and `CargoLeg` — so both directions are
structural inductions.  This is the bridge the flat
characterization's migration rides: with the cargo-orbit
characterization (`bareCargo_iff_vk` / `bareCargo_iff_split`,
`Orig2/FloatOrbit.lean`) the necessity direction of the frozen
`canRaiseS_iff` (`Orig/ForkStateS.lean:539`) becomes a SEAT-DIFF
READING rather than a path induction — the mutual lock, the
position engine, and the sufficiency construction all live inside
the certified orbit iff:

* the only cards that can come to sit on `c` within the class came
  from `c.twin` (the twin-carried clause);
* the cover of `c` can only leave to `c.twin` (the same clause);
* `nextUp` is `foundsFixed` (a clause of the iff, no induction);
* the mate-slide IS the iff's own sufficiency construction.

RESTATE (2026-10-27, the flat restate at the registry): `CanRaiseS`
is now DEFINED as the cargo span (`Orig2/Vocab.lean` — `∃ z,
CargoPath st z ∧ CanRaise z c`, the retired inductive's constructor
names preserved as flagged intro rows at the def).  The bridge below
is therefore DEFINITIONAL — the two structural inductions collapsed
to one-liners and `canRaiseS_cargoPath_iff` is `Iff.rfl`-grade; the
mission's shape and every downstream stage ride unchanged.

WAVE: this card's landing is the bridge (§1).  Staged next:
`cargoPath` symmetry (the leg inversion — the undo's
reversibility is `reversible_mirrorW`, only the undo-fires
construction remains), the seat-diff corollaries of
`bareCargo_iff_split`, the FloaterSpec ↔ twin-top correspondence,
then the flat iff and the decidability packaging (the `RankSat`
checker — Q9 of the campaign's question family).

STAGE 5 (landed here, §4): THE FLAT CHARACTERIZATION — the frozen
`canRaiseS_iff` (`Orig/ForkStateS.lean:539`) at the Orig2 seam,
re-derived by the migration's collapse: the necessity is a
SEAT-DIFF READING over the certified orbit iff (the seat condition
from the twin-carried/FloaterSpec clauses; the run-or-twin from
`bareCargo_cover_license` with `tfc_seat_parent` as the movement
witness — a cover seated on `c` at the far end makes `c` a parent,
and parents top no pile); the sufficiency is the single-hop
construction (the cover's run slides onto the twin's top, the
oracle `tabToTabR_iff_reversibleAtW` replacing the frozen
under-cell grind).  The frozen tier's engines
(`canRaiseS_positionSeat`, `canRaiseS_runOrTwin`,
`canRaiseS_free`) are NOT imported — the orbit characterization
carries their content at the class grade.

STAGE 6 (landed here, §5): THE DECIDABILITY PACKAGING — the probe
`canRaiseSB` (the Orig census pattern lifted to the cascade
grade: no anchor scan, the holding-pile pin plus the computed
below/fromCard split), certified against `CanRaiseS` at `WF`
(`canRaiseSB_iff`); the frontier `RankSat k` with its universe
scan `rankSatB` and the certified iff (`rankSatB_iff`) — Q9 of
the campaign's question family, and the door to the Q-family
probes (vacuity first).

House compliance: additive leaf (`Orig2.Vocab` +
`Orig2.Classification` for the public mirror row, `Orig2.StepWF`
for the well-formedness propagation, `Orig2.FloatOrbit` for the
cargo-orbit characterization, `Orig2.PairClassSeed` for the
SeedKit fit row the mate-slide rides); zero `sorry`, zero
`Classical.choice`; the battery at the tail.
-/

/-! ## §1. The bridge -/

/-- **THE CARGO BRIDGE, REACHABILITY HALF** — a cargo path to a
state where the vanilla raise fires is already a maneuver-raise.
DEFINITIONAL since the flat restate (the S-license IS the span):
the path and the far-end raise are the certificate outright, no
leg-peeling induction needed. -/
theorem canRaiseS_of_cargoPath {st z : State} {c : Card}
    (hp : CargoPath st z) : CanRaise z c → CanRaiseS st c :=
  fun hcr => ⟨z, hp, hcr⟩

/-- **THE CARGO BRIDGE, WITNESS HALF** — a maneuver-raise deposits a
cargo path to a vanilla-raise state.  DEFINITIONAL since the flat
restate: the certificate already is the path-plus-raise pair. -/
theorem cargoPath_of_canRaiseS {st : State} {c : Card}
    (h : CanRaiseS st c) : ∃ z, CargoPath st z ∧ CanRaise z c := h

/-- **THE CARGO BRIDGE** — the swap-aware license IS the cargo
span of the vanilla license: `CanRaiseS st c` exactly when some
cargo path reaches a state where `c` raises now.  The flat
characterization's migration base: every downstream question about
the S-license becomes a question about the cargo class.
DEFINITIONAL since the flat restate (`Iff.rfl`). -/
theorem canRaiseS_cargoPath_iff {st : State} {c : Card} :
    CanRaiseS st c ↔ ∃ z, CargoPath st z ∧ CanRaise z c :=
  Iff.rfl

/-! ## §2. The leg inversion (the wave's stage 3) -/

/-- **STEPS TRANSITIVITY** — path concatenation: a path to `z` then
a path from `z` lands at `u`.  The generic closure the reversal
composes through. -/
theorem steps_trans {Q : State → State → Prop} {w z u : State}
    (h₁ : Steps Q w z) : Steps Q z u → Steps Q w u := by
  induction h₁ with
  | refl _ => exact fun h₂ => h₂
  | cons h _ ih => exact fun h₂ => Steps.cons h (ih h₂)

/-- **THE LEG INVERSION** — at `WF`, every cargo leg has a mirror
leg: the reversible slide's moved run relocates back whole.  The
mirror's EXISTENCE is the classification's public `tabToTab_mirror`
(stage 3's one public extraction — the undo rows' conclusions were
strengthened to expose the firing); the mirror's own reversibility
is `reversible_mirrorW` over the two firings. -/
theorem cargoLeg_symm {a b : State} (hwf : a.WF) (h : CargoLeg a b) : CargoLeg b a := by
  obtain ⟨c, b', hfire, hrev⟩ := h
  obtain ⟨b₂, hfire2⟩ := tabToTab_mirror hwf hfire hrev
  exact ⟨c, b₂, hfire2, reversible_mirrorW hfire2 hfire⟩

/-- **THE CARGO PATH IS SYMMETRIC** — at `WF`, one-way cargo
reachability is two-way: reverse the legs one mirror at a time,
propagating well-formedness through each firing. -/
theorem cargoPath_symm {a b : State} (hwf : a.WF) (h : CargoPath a b) : CargoPath b a := by
  revert hwf
  induction h with
  | refl _ => exact fun _ => Steps.refl _
  | @cons w z u hleg t ih =>
      intro hwf
      obtain ⟨c, b', hfire, hrev⟩ := hleg
      exact steps_trans (ih (step_wf hwf hfire))
        (Steps.cons (cargoLeg_symm hwf ⟨c, b', hfire, hrev⟩) (Steps.refl w))

/-- **ONE-WAY IS TWO-WAY** — at `WF`, cargo reachability IS the
bare cargo equivalence: the bridge's existential reads directly on
the orbit characterization's currency. -/
theorem cargoPath_bareCargo {a b : State} (hwf : a.WF) (h : CargoPath a b) :
    BareCargoEquiv a b := ⟨h, cargoPath_symm hwf h⟩

/-- **THE BRIDGE, BARE-CARGO FORM** — the swap-aware license reads
on the orbit characterization's currency: some bare-cargo mate of
`st` raises `c` now.  Stage 4 (the seat-diff readings of
`bareCargo_iff_split`) picks up exactly here. -/
theorem canRaiseS_bareCargo_iff {st : State} (hwf : st.WF) {c : Card} :
    CanRaiseS st c ↔ ∃ z, BareCargoEquiv st z ∧ CanRaise z c := by
  rw [canRaiseS_cargoPath_iff]
  constructor
  · rintro ⟨z, hp, hcr⟩
    exact ⟨z, ⟨hp, cargoPath_symm hwf hp⟩, hcr⟩
  · rintro ⟨z, ⟨hp, -⟩, hcr⟩
    exact ⟨z, hp, hcr⟩

/-! ## §3. The seat-diff readings (the wave's stage 4) -/

/-- A card seated `.inr` on a card parent is not a king.  Lineage:
`Archive/TwinFoundationRow.lean:180`, restated private at
`Orig2/FiberTransfer.lean:531`; re-landed here (the wave's card,
over the public CargoKit seat rows) rather than widening the
import surface to the fiber-transfer card. -/
private theorem seatOf_inr_rank_ne_king {s : State} {c r : Card}
    (hwf : s.WF) (hseat : seatOf s c = some (Sum.inr r)) :
    c.rank ≠ Rank.king := by
  obtain ⟨a, hhold, -, hlast⟩ := tfc_seatOf_of_inr hseat
  have hfit : canSitOn c r = true := (tfc_seat_parent hwf hhold hlast).1
  intro hking
  have hlt := ((canSitOn_eq c r).mp hfit).1
  have hidx : c.rank.toIdx = 12 := by rw [hking]; rfl
  have hlt' := Rank.toIdx_lt r.rank
  omega

/-- **THE COVER LEAVES ONLY TO THE TWIN** — within a bare-cargo
pair, a card seated on `c` at `st` that moves at all lands on
`c.twin`: the twin-carried clause of the split iff, read at the
`.inr` seat.  The mate-slide's rigidity, stated at the class
grade. -/
theorem bareCargo_cover_to {st w : State} (hwfst : st.WF) (hw : w.WF)
    (h : BareCargoEquiv st w) {y c : Card}
    (hy : seatOf st y = some (Sum.inr c))
    (hchg : seatOf st y ≠ seatOf w y) :
    seatOf w y = some (Sum.inr c.twin) := by
  obtain ⟨⟨-, hnon⟩, -⟩ := (bareCargo_iff_split hwfst hw).mp h
  have hk : y.rank ≠ Rank.king := seatOf_inr_rank_ne_king hwfst hy
  obtain ⟨z', hz1, hz2⟩ := hnon y hk hchg
  rw [hy] at hz1
  injection hz1 with hz1'
  injection hz1' with hz1''
  rw [← hz1''] at hz2
  exact hz2

/-- **THE ONLY ARRIVAL IS FROM THE TWIN** — within a bare-cargo
pair, a card seated on `c` at `w` that moved at all came from
`c.twin`: the twin-carried clause, reverse direction. -/
theorem bareCargo_cover_from {st w : State} (hwfst : st.WF) (hw : w.WF)
    (h : BareCargoEquiv st w) {y c : Card}
    (hy : seatOf w y = some (Sum.inr c))
    (hchg : seatOf st y ≠ seatOf w y) :
    seatOf st y = some (Sum.inr c.twin) := by
  obtain ⟨⟨hking, hnon⟩, -⟩ := (bareCargo_iff_split hwfst hw).mp h
  by_cases hk : y.rank = Rank.king
  · obtain ⟨a', hcon, -⟩ := hking y hk hchg
    rw [hcon] at hy
    exact absurd hy (by simp)
  · obtain ⟨z', hz1, hz2⟩ := hnon y hk hchg
    rw [hz2] at hy
    injection hy with hy'
    injection hy' with hy''
    have hz : z' = c.twin := by
      rw [← tfc_card_twin_twin z', hy'']
    rw [hz] at hz1
    exact hz1

/-- **THE MOVED COVER'S ORIGIN LICENSE IS THE TWIN-TOP
CONDITION** — a card seated on `c` that moves within the class
carries `FloaterSpec` at the origin, and for a non-king `.inr`
seat that license IS the company cell: the parent's twin tops
some pile.  This is the mutual lock's core, stated at the class
grade — the flat characterization's run-or-twin clause rides it. -/
theorem bareCargo_cover_license {st w : State} (hwfst : st.WF) (hw : w.WF)
    (h : BareCargoEquiv st w) {y c : Card}
    (hy : seatOf st y = some (Sum.inr c))
    (hchg : seatOf st y ≠ seatOf w y) :
    st.pileOfTop c.twin ≠ none := by
  obtain ⟨⟨hking, hnon⟩, hlic, hro⟩ := (bareCargo_iff_split hwfst hw).mp h
  have hk : y.rank ≠ Rank.king := seatOf_inr_rank_ne_king hwfst hy
  have hfsp : FloaterSpec st y := hlic y hchg
  unfold FloaterSpec at hfsp
  rcases hfsp with
    ⟨z, a₁, hz, hhold₁, hinner⟩ | ⟨a₂, hclash, hkk, hh, he⟩
  · rw [hy] at hz
    injection hz with hz'
    injection hz' with hz''
    rw [← hz''] at hinner
    rcases hinner with ⟨k, hk2⟩ | ⟨hk2, hke⟩
    · intro hcon
      rw [hcon] at hk2
      exact absurd hk2 (by simp)
    · exact absurd hk2 hk
  · rw [hclash] at hy
    exact absurd hy (by simp)

/-- **THE FOUNDATIONS ARE THE LICENSE'S PHASE** — within a
bare-cargo pair the vanilla `nextUp` read is preserved (the
`foundsFixed` readout; the {slide · raise} closure never leaves
its fiber). -/
theorem bareCargo_nextUp {st w : State} (hwfst : st.WF) (hw : w.WF)
    (h : BareCargoEquiv st w) {c : Card} :
    st.nextUp c = w.nextUp c := by
  obtain ⟨-, -, hro⟩ := (bareCargo_iff_split hwfst hw).mp h
  have hf : st.found = w.found := funext (fun s => hro.2.1 s)
  exact congrArg (fun (f : Suit → List Card) =>
    decide (c.rank.toIdx = (f c.suit).length)) hf

/-! ## §4. The flat characterization (the wave's stage 5) -/

/-- The custom `lastOf` never answers `none` on a nonempty list
(the seat map's `none` arm reads through `tfc_getLast?_lastOf`).
Lineage: the core `getLast?`-side dichotomy restated at the
custom function — fresh, kept local to this card. -/
private theorem lastOf_eq_none : ∀ (l : List Card), lastOf l = none → l = [] := by
  intro l
  cases l with
  | nil => intro _; rfl
  | cons w t =>
      cases t with
      | nil =>
          intro h
          rw [show lastOf [w] = some w from rfl] at h
          exact absurd h (Option.some_ne_none w)
      | cons w2 t2 =>
          intro h
          rw [show lastOf (w :: w2 :: t2) = lastOf (w2 :: t2) from rfl] at h
          exact absurd (lastOf_eq_none (w2 :: t2) h) (List.cons_ne_nil w2 t2)

/-- A card strictly inside a nodup append is not in the front part.
Lineage: `Orig/ForkStateS.lean:141` (private there, the frozen
flat characterization's own kit — the closed-seam policy restates
it here rather than importing the frozen card). -/
private theorem nodup_mid_notmem (d : Card) :
    ∀ (l rest : List Card), (l ++ d :: rest).Nodup → d ∉ l := by
  intro l
  induction l with
  | nil => intro rest _ hm; exact absurd hm (by simp)
  | cons x xs ih =>
      intro rest hnd hm
      rcases List.mem_cons.mp hm with rfl | hin
      · exact absurd (List.mem_append.mpr (Or.inr (List.mem_cons_self ..)))
          ((List.nodup_cons.mp hnd).1)
      · exact ih rest ((List.nodup_cons.mp hnd).2) hin

/-- **THE PATH PRESERVES WELL-FORMEDNESS** — every leg is a firing
step, and firing steps preserve `WF` (`step_wf`); the induction the
flat characterization's necessity rides (the far-end state of a
bare-cargo pair is `WF`, so the orbit iff's premises discharge). -/
theorem cargoPath_wf {a b : State} (hwf : a.WF) (h : CargoPath a b) : b.WF := by
  revert hwf
  induction h with
  | refl w => exact fun h => h
  | @cons w z u hleg t ih =>
      intro hwf
      obtain ⟨c, b', hfire, -⟩ := hleg
      exact ih (step_wf hwf hfire)

/-- **THE FLAT CHARACTERIZATION'S NECESSITY** — the maneuver-raise
forces the flat shape: `c` next-up, seated on the board at some
pile `a` with face-up `bs ++ c :: run`, the seat condition
(company below or the bare-king cell), and the cover's
run-or-twin.  THE MIGRATION'S COLLAPSE: the frozen tier's two
engines (`canRaiseS_positionSeat` / `canRaiseS_runOrTwin`,
`Orig/PositionSeat.lean` / `Orig/RunOrTwin.lean`) are NOT
re-proved — both readings fall out of the certified orbit iff
`bareCargo_iff_split`: the position from the seat transfer (a
moved card's reversed clauses make its seat nonempty at `st`),
the seat condition from the twin-carried license (FloaterSpec's
bare-king cell when the seat moved; the exposed cell at the far
end when it did not), and the run-or-twin from
`bareCargo_cover_license` — the cover that must move (a card
seated on `c` at `z` makes `c` a parent, and `tfc_seat_parent`
says parents top no pile, against the raise's own top pin)
licenses the twin-top. -/
theorem canRaiseS_flat_necessity {st : State} {c : Card} (hwf : st.WF)
    (h : CanRaiseS st c) :
    st.nextUp c = true ∧
    ∃ a bs run, (st.piles a).faceUp = bs ++ c :: run ∧
      (bs ≠ [] ∨ ((st.piles a).hidden = [] ∧ c.rank = Rank.king)) ∧
      (run = [] ∨ st.pileOfTop c.twin ≠ none) := by
  -- the class-mate with the vanilla raise, and its well-formedness:
  obtain ⟨z, hbce, hcr⟩ := (canRaiseS_bareCargo_iff hwf).mp h
  have hwz : z.WF := cargoPath_wf hwf hbce.1
  obtain ⟨hnextZ, a_z, hpodZ, hseatZ⟩ := hcr
  -- c tops pile a_z at z, hence held there:
  have htopZ : lastOf ((z.piles a_z).faceUp) = some c := (pileOfTop_top hpodZ).2
  have hmemZ : c ∈ (z.piles a_z).faceUp := lastOf_mem htopZ
  have hholdZ : z.pileHolding c = some a_z := (pileHolding_eq_some_iff hwz).2 hmemZ
  -- the forward and reversed split readings:
  obtain ⟨⟨hkingF, hnonF⟩, hlicF, hroF⟩ := (bareCargo_iff_split hwf hwz).mp hbce
  obtain ⟨⟨hkingR, hnonR⟩, hlicR, hroR⟩ :=
    (bareCargo_iff_split hwz hwf).mp ⟨hbce.2, hbce.1⟩
  -- nextUp transfers (foundsFixed):
  have hnext : st.nextUp c = true := by
    rw [bareCargo_nextUp hwf hwz hbce]
    exact hnextZ
  -- the far-end seat exists:
  have hzne : seatOf z c ≠ none := by
    intro hcon
    simp only [tfc_seatOf_eq, hholdZ] at hcon
    cases hlastZ0 : List.getLast? (below c (z.piles a_z).faceUp) <;>
      simp only [hlastZ0] at hcon <;> exact absurd hcon (Option.some_ne_none _)
  cases hh : st.pileHolding c with
  | none =>
      -- dead: a moved card's reversed clauses seat it nonempty at st
      have hseNone : seatOf st c = none := tfc_seatOf_none hh
      have hdiffR : seatOf z c ≠ seatOf st c := fun heq => hzne (heq.trans hseNone)
      by_cases hk : c.rank = Rank.king
      · obtain ⟨a', hse', hvkR⟩ := hkingR c hk hdiffR
        rw [hseNone] at hse'
        exact absurd hse' (fun hcon => Option.some_ne_none _ hcon.symm)
      · obtain ⟨z', hzz, hse'⟩ := hnonR c hk hdiffR
        rw [hseNone] at hse'
        exact absurd hse' (fun hcon => Option.some_ne_none _ hcon.symm)
  | some a =>
      -- the position shape at st's holding pile:
      have hmem : c ∈ (st.piles a).faceUp := pileHolding_mem hh
      obtain ⟨run, hcrr⟩ := tfc_fromCard_cons_head _ hmem
      have hshape : (st.piles a).faceUp
          = below c ((st.piles a).faceUp) ++ c :: run := by
        have h0 := tfc_below_fromCard c ((st.piles a).faceUp)
        rw [hcrr] at h0
        exact h0.symm
      refine ⟨hnext, a, below c ((st.piles a).faceUp), run, hshape, ?_, ?_⟩
      · -- the seat condition:
        cases hlast : List.getLast? (below c ((st.piles a).faceUp)) with
        | some r =>
            have hlast' : lastOf (below c ((st.piles a).faceUp)) = some r := by
              rw [← tfc_getLast?_lastOf]
              exact hlast
            refine Or.inl ?_
            intro hcon
            rw [hcon] at hlast'
            rw [show lastOf ([] : List Card) = none from rfl] at hlast'
            exact absurd hlast'.symm (Option.some_ne_none r)
        | none =>
            -- the bare-king cell: the inl seat
            have hseatInl : seatOf st c = some (Sum.inl a) := by
              rw [tfc_seatOf_pair hh, hlast]
            refine Or.inr ?_
            -- the moved-seat license (FloaterSpec's bare-king cell):
            have hfspRoute (hdiff : seatOf st c ≠ seatOf z c) :
                (st.piles a).hidden = [] ∧ c.rank = Rank.king := by
              have hfsp := hlicF c hdiff
              rcases hfsp with
                ⟨zz, aa, hse', hhold', hinner⟩ | ⟨aa, hse', hkk', hhid', hemp'⟩
              · rw [hseatInl] at hse'
                injection hse' with hse2
                cases hse2
              · have h1 : some (Sum.inl aa) = some (Sum.inl a) :=
                  hse'.symm.trans hseatInl
                injection h1 with h2
                injection h2 with haa
                rw [haa] at hhid'
                exact ⟨hhid', hkk'⟩
            cases hlastZ : List.getLast? (below c (z.piles a_z).faceUp) with
            | some r =>
                have hzseat : seatOf z c = some (Sum.inr r) := by
                  rw [tfc_seatOf_pair hholdZ, hlastZ]
                have hdiff : seatOf st c ≠ seatOf z c := by
                  intro heq
                  rw [hseatInl, hzseat] at heq
                  injection heq with heq2
                  cases heq2
                exact hfspRoute hdiff
            | none =>
                have hzseat : seatOf z c = some (Sum.inl a_z) := by
                  rw [tfc_seatOf_pair hholdZ, hlastZ]
                by_cases haz : a_z = a
                · -- seat unchanged: c exposed bare at the far end
                  have hbelowZnil : below c (z.piles a_z).faceUp = [] := by
                    have h1 : lastOf (below c (z.piles a_z).faceUp) = none := by
                      rw [← tfc_getLast?_lastOf]
                      exact hlastZ
                    exact lastOf_eq_none _ h1
                  obtain ⟨restZ, hcrrZ⟩ := tfc_fromCard_cons_head _ hmemZ
                  have hshapeZ : (z.piles a_z).faceUp = c :: restZ := by
                    have h0 := tfc_below_fromCard c ((z.piles a_z).faceUp)
                    rw [hcrrZ, hbelowZnil, List.nil_append] at h0
                    exact h0.symm
                  have htopZ2 : lastOf ((z.piles a_z).faceUp) = some c := htopZ
                  rw [hshapeZ] at htopZ2
                  -- c tops its own pile, so nothing sits above it:
                  have hrestZnil : restZ = [] := by
                    cases restZ with
                    | nil => rfl
                    | cons w ws =>
                        rw [show lastOf (c :: w :: ws) = lastOf (w :: ws) from rfl] at htopZ2
                        have hcm : c ∈ w :: ws := lastOf_mem htopZ2
                        have hndZ : ((z.piles a_z).faceUp).Nodup :=
                          runOK_nodup (hwz.2.1 a_z)
                        rw [hshapeZ] at hndZ
                        exact absurd hcm (List.nodup_cons.1 hndZ).1
                  rw [hrestZnil] at hshapeZ
                  rcases hseatZ with hchopZ | ⟨hhidZ, hkkZ⟩
                  · rw [hshapeZ] at hchopZ
                    exact absurd hchopZ (fun hcon => hcon rfl)
                  · rw [haz] at hhidZ
                    exact ⟨(hroF.1.1 a).trans hhidZ, hkkZ⟩
                · -- seat moved between inl anchors: FloaterSpec
                  have hdiff : seatOf st c ≠ seatOf z c := by
                    intro heq
                    have h1 : some (Sum.inl a) = some (Sum.inl a_z) :=
                      (hseatInl.symm.trans heq).trans hzseat
                    injection h1 with h2
                    injection h2 with haa
                    exact haz haa.symm
                  exact hfspRoute hdiff
      · -- the run-or-twin: the cover's movement licenses the twin-top
        cases run with
        | nil => exact Or.inl rfl
        | cons d rest' =>
            refine Or.inr ?_
            have hid : (below c ((st.piles a).faceUp) ++ [c]) ++ d :: rest'
                = below c ((st.piles a).faceUp) ++ c :: d :: rest' := by
              rw [List.append_assoc, List.cons_append, List.nil_append]
            have hdnotin : d ∉ below c ((st.piles a).faceUp) ++ [c] :=
              nodup_mid_notmem d (below c ((st.piles a).faceUp) ++ [c]) rest'
                (by rw [hid, ← hshape]; exact runOK_nodup (hwf.2.1 a))
            have hexcl := tfc_below_fromCard_excl d
              (below c ((st.piles a).faceUp) ++ [c]) (d :: rest') hdnotin
            have hbelD : below d ((st.piles a).faceUp)
                = below c ((st.piles a).faceUp) ++ [c] := by
              have h1 := hexcl.1
              rw [below_cons_self, List.append_nil] at h1
              rw [congrArg (below d) hshape, ← hid]
              exact h1
            have hdmem : d ∈ (st.piles a).faceUp := by
              rw [hshape]
              exact List.mem_append.mpr
                (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons_self ..))))
            have hholdD : st.pileHolding d = some a :=
              (pileHolding_eq_some_iff hwf).2 hdmem
            -- the cover's seat at st: directly on c
            have hseatD : seatOf st d = some (Sum.inr c) := by
              rw [tfc_seatOf_pair hholdD, hbelD, tfc_getLast?_lastOf, lastOf_snoc]
            -- the cover must have moved (else c is a parent at z):
            have hdmoved : seatOf st d ≠ seatOf z d := by
              intro heq
              rw [hseatD] at heq
              obtain ⟨a_d, hholdDZ, hbelDZne, hlastDZ⟩ := tfc_seatOf_of_inr heq.symm
              have hnoneC := (tfc_seat_parent hwz hholdDZ hlastDZ).2
              rw [hnoneC] at hpodZ
              cases hpodZ
            exact bareCargo_cover_license hwf hwz hbce hseatD hdmoved

/-- **THE FLAT CHARACTERIZATION'S SUFFICIENCY** — the flat shape
raises: with an empty cover the vanilla `now`-leg fires directly;
with a covered run and the twin topped, the single hop
`tabToTab d (inr c.twin)` exposes `c` — the cover's run relocates
onto the twin's top (the twin-blind fit of `canSitOn`), the leg
is reversible (the oracle `tabToTabR_iff_reversibleAtW` replaces
the frozen under-cell grind), and `c` raises at the successor
(the slide never wrote the foundations, never touched `c`'s
under-seat, and the cover is gone).  THE MIGRATION'S COLLAPSE: the
frozen tier's mate-slide construction (`canRaiseS_free`,
`Orig/ForkStateS.lean:202`) is re-derived as this one hop. -/
theorem canRaiseS_flat_sufficiency {st : State} {c : Card} (hwf : st.WF)
    (hflat : st.nextUp c = true ∧
      ∃ a bs run, (st.piles a).faceUp = bs ++ c :: run ∧
        (bs ≠ [] ∨ ((st.piles a).hidden = [] ∧ c.rank = Rank.king)) ∧
        (run = [] ∨ st.pileOfTop c.twin ≠ none)) :
    CanRaiseS st c := by
  obtain ⟨hnext, a, bs, run, hshape, hseatFlat, hdisj⟩ := hflat
  cases run with
  | nil =>
      -- the vanilla now-leg: c tops pile a over its seat
      have htop : (st.piles a).top = some c := by
        show lastOf ((st.piles a).faceUp) = some c
        rw [hshape]
        exact lastOf_snoc
      have hpod : st.pileOfTop c = some a := (pileOfTop_eq_some_iff hwf).2 htop
      have hseat' : chop (st.piles a).faceUp ≠ [] ∨
          ((st.piles a).hidden = [] ∧ c.rank = Rank.king) := by
        rcases hseatFlat with hbs | hbk
        · exact Or.inl (by rw [hshape, chop_snoc]; exact hbs)
        · exact Or.inr hbk
      exact CanRaiseS.now c ⟨hnext, a, hpod, hseat'⟩
  | cons d rest' =>
      -- the twin must be topped (the run is nonempty):
      rcases hdisj with hre | htwinTopne
      · exact absurd hre (by simp)
      cases htwinTop : st.pileOfTop c.twin with
      | none => exact absurd htwinTop htwinTopne
      | some b =>
          -- the fit: the cover sits directly on c, and the fit is twin-blind
          have hok : runOK (bs ++ c :: d :: rest') = true := by
            rw [← hshape]; exact hwf.2.1 a
          have hfit : canSitOn d c = true :=
            SeedKit.runOK_adjacent_fit c d bs rest' hok
          have hfittwin : canSitOn d c.twin = true := by
            rw [show c.twin = { c with suit := c.suit.twin } from rfl,
              canSitOn_twin_right]
            exact hfit
          have hcpD : st.canPlace d (Sum.inr c.twin) = true := by
            rw [canPlace_inr_located htwinTop]
            exact hfittwin
          -- the cover's split at st:
          have hid : (bs ++ [c]) ++ d :: rest' = bs ++ c :: d :: rest' := by
            rw [List.append_assoc bs [c], List.cons_append, List.nil_append]
          have hdnotin : d ∉ bs ++ [c] :=
            nodup_mid_notmem d (bs ++ [c]) rest'
              (by rw [hid, ← hshape]; exact runOK_nodup (hwf.2.1 a))
          have hexcl := tfc_below_fromCard_excl d (bs ++ [c]) (d :: rest') hdnotin
          have hbelD : below d ((st.piles a).faceUp) = bs ++ [c] := by
            have h1 := hexcl.1
            rw [below_cons_self, List.append_nil] at h1
            rw [hshape, ← hid]
            exact h1
          have hfromD : fromCard d ((st.piles a).faceUp) = d :: rest' := by
            have h2 := hexcl.2
            rw [fromCard_head_eq] at h2
            rw [hshape, ← hid]
            exact h2
          have hholdD : st.pileHolding d = some a :=
            (pileHolding_eq_some_iff hwf).2 (by
              rw [hshape]
              exact List.mem_append.mpr
                (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons_self ..)))))
          -- FIRE the slide; the successor is the literal:
          have hsteplit : st.step (Move.tabToTab d (Sum.inr c.twin)) = some
              ((st.setPile a (Pile.afterRunRemoved (st.piles a) (bs ++ [c]))).putRun
                (d :: rest') (Sum.inr c.twin)) := by
            show (match st.pileHolding d with
              | none => none
              | some a₂ =>
                  if st.canPlace d (Sum.inr c.twin) then
                    match fromCard d ((st.piles a₂).faceUp) with
                    | [] => none
                    | run => some ((st.setPile a₂
                        (Pile.afterRunRemoved (st.piles a₂)
                          (below d ((st.piles a₂).faceUp)))).putRun run (Sum.inr c.twin))
                    else none) = _
            rw [hholdD]
            simp only [canPlace_inr_located htwinTop, hfittwin]
            rw [hfromD, hbelD]
            rfl
          obtain ⟨s', hs'eq, hstep⟩ : ∃ s', s' =
              (st.setPile a (Pile.afterRunRemoved (st.piles a) (bs ++ [c]))).putRun
                (d :: rest') (Sum.inr c.twin) ∧
              st.step (Move.tabToTab d (Sum.inr c.twin)) = some s' :=
            ⟨_, rfl, hsteplit⟩
          -- the twin tops a DIFFERENT pile (the rank arithmetic):
          have hbna : b ≠ a := by
            intro hcon
            rw [hcon] at htwinTop
            have hmemT : c.twin ∈ (st.piles a).faceUp :=
              Pile.mem_of_top (pileOfTop_top htwinTop).2
            rw [hshape] at hmemT
            have htr : c.twin.rank = c.rank := rfl
            rcases List.mem_append.mp hmemT with hbs' | hrun'
            · have h1 := runOK_desc hok hbs' (List.mem_cons_self ..)
              rw [htr] at h1
              omega
            · rcases List.mem_cons.mp hrun' with heq | hrest'
              · exact card_twin_ne c heq
              · have hokL : runOK ((bs ++ [c]) ++ d :: rest') = true := by
                  rw [hid]; exact hok
                have h2 := runOK_desc hokL
                  (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))) hrest'
                rw [htr] at h2
                omega
          -- the mid-state facts:
          have hpre : bs ++ [c] ≠ [] := by cases bs <;> simp
          have hmidFu : (Pile.afterRunRemoved (st.piles a) (bs ++ [c])).faceUp
              = bs ++ [c] := afterRunRemoved_faceUp_ne hpre
          have hmidHi : (Pile.afterRunRemoved (st.piles a) (bs ++ [c])).hidden
              = (st.piles a).hidden := by
            rcases afterRunRemoved_hidden (st.piles a) (bs ++ [c]) with
              ⟨hne, hhid⟩ | ⟨hnil, hph1, hph2⟩ | ⟨hnil, hph1, hph2⟩
            · exact hhid
            · exact absurd hnil hpre
            · exact absurd hnil hpre
          have htwinmemb : c.twin ∈ (st.piles b).faceUp :=
            Pile.mem_of_top (pileOfTop_top htwinTop).2
          have hnoTtwin : ∀ y : Anchor, y ≠ b → (st.piles y).top ≠ some c.twin := by
            intro y hyb htop
            exact (mem_faceUp_unique hwf htwinmemb y hyb).1 (Pile.mem_of_top htop)
          have hmidA : (st.setPile a (Pile.afterRunRemoved (st.piles a) (bs ++ [c]))).piles a
              = Pile.afterRunRemoved (st.piles a) (bs ++ [c]) := setPile_piles_self
          have hmidTopA : (Pile.afterRunRemoved (st.piles a) (bs ++ [c])).top = some c := by
            show lastOf ((Pile.afterRunRemoved (st.piles a) (bs ++ [c])).faceUp) = some c
            rw [hmidFu]
            exact lastOf_snoc
          -- the twin still tops b at the mid-state (the profile of tops):
          have hmidpin : (st.setPile a (Pile.afterRunRemoved (st.piles a) (bs ++ [c]))).pileOfTop c.twin
              = some b := by
            show (firstWhere (fun a₂ => decide
                ((st.setPile a (Pile.afterRunRemoved (st.piles a) (bs ++ [c]))).topOf a₂
                  = some c.twin)) Anchor.all) = some b
            refine firstWhere_find (Anchor.mem_all b) ?_ ?_
            · show decide (((st.setPile a
                  (Pile.afterRunRemoved (st.piles a) (bs ++ [c]))).topOf b) = some c.twin) = true
              rw [setPile_topOf_ne hbna]
              exact decide_eq_true (pileOfTop_top htwinTop).2
            · intro y _hyp hyne
              show decide (((st.setPile a
                  (Pile.afterRunRemoved (st.piles a) (bs ++ [c]))).topOf y) = some c.twin) = false
              by_cases hya : y = a
              · rw [hya]
                have htopA : (st.setPile a
                    (Pile.afterRunRemoved (st.piles a) (bs ++ [c]))).topOf a = some c := by
                  rw [show (st.setPile a
                      (Pile.afterRunRemoved (st.piles a) (bs ++ [c]))).topOf a
                      = ((st.setPile a
                        (Pile.afterRunRemoved (st.piles a) (bs ++ [c]))).piles a).top from rfl,
                    hmidA]
                  exact hmidTopA
                rw [htopA]
                exact decide_false_of_not (fun hcon =>
                  card_twin_ne c (Option.some.inj hcon).symm)
              · rw [setPile_topOf_ne hya]
                exact decide_false_of_not (fun hcon =>
                  hnoTtwin y hyne hcon)
          -- the successor's pile a: exposed c over the seat
          have hwfs' : s'.WF := step_wf hwf hstep
          have hs'A : s'.piles a = Pile.afterRunRemoved (st.piles a) (bs ++ [c]) := by
            rw [hs'eq, putRun_piles_inr_ne _ _ _ _ hmidpin (Ne.symm hbna), hmidA]
          have hstop : (s'.piles a).top = some c := by rw [hs'A]; exact hmidTopA
          have hpodS' : s'.pileOfTop c = some a := (pileOfTop_eq_some_iff hwfs').2 hstop
          have hchopS' : chop (s'.piles a).faceUp = bs := by
            rw [hs'A, hmidFu, chop_snoc]
          have hseatS' : chop (s'.piles a).faceUp ≠ [] ∨
              ((s'.piles a).hidden = [] ∧ c.rank = Rank.king) := by
            rcases hseatFlat with hbs | hbk
            · exact Or.inl (by rw [hchopS']; exact hbs)
            · refine Or.inr ⟨?_, hbk.2⟩
              rw [hs'A, hmidHi]
              exact hbk.1
          -- the slide never wrote the foundations:
          have hfndS' : s'.found = st.found := by
            rw [hs'eq, putRun_found, setPile_found]
          have hnextS' : s'.nextUp c = st.nextUp c :=
            congrArg (fun (f : Suit → List Card) =>
              decide (c.rank.toIdx = (f c.suit).length)) hfndS'
          -- the oracle: the slide is reversible at WF
          have hor : tabToTabR st d (Sum.inr c.twin) = true := by
            cases hbelow : below d ((st.piles a).faceUp) with
            | nil =>
                rw [hbelD] at hbelow
                exact absurd hbelow (by cases bs <;> simp)
            | cons w t =>
                simp only [tabToTabR, hholdD, hcpD, hbelow]
          have hrev : reversibleAtW st (Move.tabToTab d (Sum.inr c.twin)) :=
            (tabToTabR_iff_reversibleAtW hwf d (Sum.inr c.twin)).mp hor
          exact CanRaiseS.via c ⟨d, Sum.inr c.twin, hstep, hrev⟩
            (CanRaiseS.now c ⟨hnextS'.trans hnext, a, hpodS', hseatS'⟩)

/-- **THE FLAT CHARACTERIZATION** — the frozen biconditional,
migrated: `CanRaiseS` is exactly the flat shape — `c` next-up,
seated at pile `a` with face-up `bs ++ c :: run`, the seat
condition, and the cover's run-or-twin.  PORTED from
`Orig/ForkStateS.lean:539` (`canRaiseS_iff`) — the statement
verbatim, the proof REPLACED by the migration's collapse: the
necessity a seat-diff reading over the certified orbit iff, the
sufficiency the single-hop construction.  The twin-top clause's
reading: `c` either stands exposed (its run empty) or its
`c.twin` tops some pile (the mate-slide's landing site).  Stage 5
of the flat characterization's migration — the decidability
packaging (the `RankSat` checker) plugs in here. -/
theorem canRaiseS_iff {st : State} {c : Card} (hwf : st.WF) :
    CanRaiseS st c ↔
      st.nextUp c = true ∧
      ∃ a bs run, (st.piles a).faceUp = bs ++ c :: run ∧
        (bs ≠ [] ∨ ((st.piles a).hidden = [] ∧ c.rank = Rank.king)) ∧
        (run = [] ∨ st.pileOfTop c.twin ≠ none) := by
  constructor
  · exact canRaiseS_flat_necessity hwf
  · exact canRaiseS_flat_sufficiency hwf

/-! ## §5. The decidability packaging (the wave's stage 6) -/

/-- **canRaiseSB st c** — THE S-LICENSE PROBE (the Orig census
pattern, `canRaiseB` lifted to the cascade grade): the flat
characterization as a single Bool.  No anchor scan — the flat
witness pins to the holding pile by occurrence uniqueness, and
`bs`/`run` are the computed below/fromCard split, not a search.
The match arms are the flat clauses verbatim: the seat condition
(company below, or the bare-king cell) and the cover's run-or-twin
(the run empty, or the twin topping some pile).  Certified against
`CanRaiseS` at `WF` below. -/
def canRaiseSB (st : State) (c : Card) : Bool :=
  st.nextUp c &&
  match st.pileHolding c with
  | none => false
  | some a =>
      match fromCard c ((st.piles a).faceUp) with
      | [] => false
      | _ :: run =>
          (decide (below c ((st.piles a).faceUp) ≠ []) ||
            (decide ((st.piles a).hidden = []) && decide (c.rank = Rank.king))) &&
          (decide (run = []) || (st.pileOfTop c.twin).isSome)

/-- **THE PROBE AGREES WITH THE LICENSE** — at `WF`, the S-license
is its flat Bool: the migration's decidability dividend.  The
reading rides the flat iff both ways: the probe's computed
witness IS the flat witness (the holding pile, the below/fromCard
split — the shape definitional through `tfc_below_fromCard`), and
the flat witness's pile IS the holding pile (occurrence
uniqueness), its `bs` the computed below (the run discipline's
duplicate-freedom), its `run` the fromCard tail. -/
theorem canRaiseSB_iff {st : State} {c : Card} (hwf : st.WF) :
    canRaiseSB st c = true ↔ CanRaiseS st c := by
  rw [canRaiseS_iff hwf]
  constructor
  · -- the probe reads the flat shape at the holding pile
    intro h
    rw [canRaiseSB, Bool.and_eq_true] at h
    obtain ⟨hnext, hrest⟩ := h
    cases hhold : st.pileHolding c with
    | none => simp only [hhold] at hrest; exact absurd hrest (by simp)
    | some a =>
        simp only [hhold] at hrest
        have hcmem : c ∈ (st.piles a).faceUp := pileHolding_mem hhold
        obtain ⟨run₀, hcrr⟩ := tfc_fromCard_cons_head _ hcmem
        cases hF : fromCard c ((st.piles a).faceUp) with
        | nil =>
            rw [hF] at hcrr
            exact absurd hcrr (by simp)
        | cons c' run =>
            rw [hF] at hcrr
            injection hcrr with hchd hrun
            simp only [hF] at hrest
            rw [Bool.and_eq_true] at hrest
            obtain ⟨hseat, hrot⟩ := hrest
            rw [Bool.or_eq_true] at hseat
            refine ⟨hnext, a, below c ((st.piles a).faceUp), run, ?_, ?_, ?_⟩
            · have h0 := tfc_below_fromCard c ((st.piles a).faceUp)
              rw [hF, hchd] at h0
              exact h0.symm
            · rcases hseat with hbs | hhk
              · exact Or.inl (decide_eq_true_iff.mp hbs)
              · rw [Bool.and_eq_true] at hhk
                obtain ⟨hd1, hd2⟩ := hhk
                exact Or.inr ⟨decide_eq_true_iff.mp hd1, decide_eq_true_iff.mp hd2⟩
            · rw [Bool.or_eq_true] at hrot
              rcases hrot with hr | his
              · exact Or.inl (decide_eq_true_iff.mp hr)
              · refine Or.inr ?_
                intro hcon
                rw [hcon] at his
                exact absurd his (by simp)
  · -- the flat shape sets the probe
    rintro ⟨hnext, a, bs, run, hshape, hseat, hdisj⟩
    have hcmem : c ∈ (st.piles a).faceUp := by
      rw [hshape]
      exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
    have hhold : st.pileHolding c = some a := (pileHolding_eq_some_iff hwf).2 hcmem
    have hnd : (bs ++ c :: run).Nodup := by
      have h := runOK_nodup (hwf.2.1 a)
      rw [hshape] at h
      exact h
    have hcNbs : c ∉ bs := nodup_mid_notmem c bs run hnd
    have hbelow : below c ((st.piles a).faceUp) = bs := by
      have hexcl := tfc_below_fromCard_excl c bs (c :: run) hcNbs
      have h1 := hexcl.1
      rw [below_cons_self, List.append_nil] at h1
      rw [hshape]
      exact h1
    have hfc : fromCard c ((st.piles a).faceUp) = c :: run := by
      have hexcl := tfc_below_fromCard_excl c bs (c :: run) hcNbs
      have h2 := hexcl.2
      rw [fromCard_head_eq] at h2
      rw [hshape]
      exact h2
    simp only [canRaiseSB, hnext, hhold, hfc, Bool.true_and]
    rw [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · rcases hseat with hbs | ⟨hh1, hh2⟩
      · rw [hbelow, Bool.or_eq_true]
        exact Or.inl (decide_eq_true hbs)
      · rw [hbelow, Bool.or_eq_true, Bool.and_eq_true]
        exact Or.inr ⟨decide_eq_true hh1, decide_eq_true hh2⟩
    · rcases hdisj with hre | htwin
      · rw [hre, Bool.or_eq_true]
        exact Or.inl (decide_eq_true rfl)
      · cases hp : st.pileOfTop c.twin with
        | none => exact absurd hp htwin
        | some k => rw [Bool.or_eq_true]; exact Or.inr rfl

/-- **freeCardS st c** — THE TABLEAU-READINESS PROBE (the campaign's
new predicate, owner line 2026-10-27): the S-license's flat shape
with the foundation gate REMOVED — `canRaiseSB` minus its `nextUp`
head.  A pure piles-function (no clause reads `st.found`): the card
is seated with company (or a bare king), and either stands exposed
or its twin tops a pile — "free but not yet due".  The split below
factors the license into foundation-gate ∧ tableau-readiness; the
orbit-invariance campaign (`Orig2/FreeOrbit.lean`) proves the
readiness is an (orbit, rung-tuple) invariant. -/
def freeCardS (st : State) (c : Card) : Bool :=
  match st.pileHolding c with
  | none => false
  | some a =>
      match fromCard c ((st.piles a).faceUp) with
      | [] => false
      | _ :: run =>
          (decide (below c ((st.piles a).faceUp) ≠ []) ||
            (decide ((st.piles a).hidden = []) && decide (c.rank = Rank.king))) &&
          (decide (run = []) || (st.pileOfTop c.twin).isSome)

/-- The definitional bridge: the S-probe is the foundation gate
conjoined with the readiness probe, verbatim. -/
theorem canRaiseSB_eq (st : State) (c : Card) :
    canRaiseSB st c = (st.nextUp c && freeCardS st c) := rfl

/-- **THE LICENSE SPLITS** — the S-license is the foundation gate
conjoined with the tableau-readiness probe.  The flat iff's first
clause is the tuple shadow (the rung); the remaining clauses are
the probe verbatim.  The orbit-invariance campaign rides this
decomposition: `nextUp` is (orbit, tuple)-fixed by `foundsFixed`,
and the campaign proves `freeCardS` is too. -/
theorem canRaiseS_split {st : State} {c : Card} (hwf : st.WF) :
    CanRaiseS st c ↔ st.nextUp c = true ∧ freeCardS st c = true := by
  rw [← canRaiseSB_iff hwf, canRaiseSB_eq, Bool.and_eq_true]

/-- **RankSat k st** — the level-k saturation frontier: no card of
rank-index at most `k` is S-raisable at `st`.  The question
family's anchor predicate (the campaign's Q-family — vacuity,
κ-spectrum, the residue — reads at this grade).  Fresh def at the
migration card; the campaign's consumption card re-exports as
needed. -/
def RankSat (k : Nat) (st : State) : Prop :=
  ∀ c, c.rank.toIdx ≤ k → ¬ CanRaiseS st c

/-- **rankSatB** — the frontier probe: the universe scan over the
S-license checker.  Completeness rides `Card.mem_universe` (every
card is scanned); soundness rides `canRaiseSB_iff`. -/
def rankSatB (k : Nat) (st : State) : Bool :=
  Card.universe.all (fun c => !(decide (c.rank.toIdx ≤ k) && canRaiseSB st c))

/-- **THE FRONTIER IS DECIDABLE** — Q9 of the campaign's question
family: the saturation frontier is its Bool, at every `WF` state.
The whole Q-family now reads on decidable questions — vacuity,
the κ-spectrum, the residue's witnesses. -/
theorem rankSatB_iff {st : State} (hwf : st.WF) (k : Nat) :
    rankSatB k st = true ↔ RankSat k st := by
  constructor
  · intro h c hc hS
    have hSB : canRaiseSB st c = true := (canRaiseSB_iff hwf).mpr hS
    have h1 := (List.all_eq_true.mp h) c (Card.mem_universe c)
    have h2 : (decide (c.rank.toIdx ≤ k) && canRaiseSB st c) = true := by
      rw [Bool.and_eq_true]
      exact ⟨decide_eq_true hc, hSB⟩
    rw [h2, Bool.not_true] at h1
    exact absurd h1 (by simp)
  · intro h
    refine List.all_eq_true.mpr ?_
    intro c hmem
    by_cases hle : c.rank.toIdx ≤ k
    · have hnS : ¬ CanRaiseS st c := h c hle
      have hSB : canRaiseSB st c = false := by
        cases hSB' : canRaiseSB st c with
        | false => rfl
        | true => exact absurd ((canRaiseSB_iff hwf).mp hSB') hnS
      rw [decide_eq_true hle, hSB, Bool.and_false, Bool.not_false]
    · rw [decide_false_of_not hle, Bool.false_and, Bool.not_false]

/-! ## §6. The battery -/

#print axioms canRaiseS_of_cargoPath
#print axioms cargoPath_of_canRaiseS
#print axioms canRaiseS_cargoPath_iff
#print axioms steps_trans
#print axioms cargoLeg_symm
#print axioms cargoPath_symm
#print axioms cargoPath_bareCargo
#print axioms canRaiseS_bareCargo_iff
#print axioms bareCargo_cover_to
#print axioms bareCargo_cover_from
#print axioms bareCargo_cover_license
#print axioms bareCargo_nextUp
#print axioms cargoPath_wf
#print axioms canRaiseS_flat_necessity
#print axioms canRaiseS_flat_sufficiency
#print axioms canRaiseS_iff
#print axioms canRaiseSB_iff
#print axioms rankSatB_iff
#print axioms canRaiseSB_eq
#print axioms canRaiseS_split
