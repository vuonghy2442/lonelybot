import Orig2.Substrate.CargoRaise
import Orig2.Substrate.Position

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Orig2.ForkCriticalPair — the local fork critical pair

THE LOCAL DICHOTOMY AT A LIVE TWIN PAIR.  At a `WF` state `F` whose
`CanRaiseS` spectrum is exactly `{x, x.twin}`, put `y = x.twin`.

* §1 the configuration (`TwinLivePair`, the arm span `ArmRaise`).
* §2 THE RUNG OBSTRUCTION: cargo and flat letters preserve the rung
  ledger; a raise climbs the raised suit's rung by one.  The two
  ONE-RAISE arms can never be `FlatPath`/`BareCargoEquiv` joined — their
  rung vectors differ.  The literal one-raise join target is therefore
  arithmetically false; the correct grade is the TWO-RAISE critical
  pair.
* §3 THE JOIN: when both twins are vanilla-raisable, the two-raise
  square commutes exactly (no cargo correction), and the one-raise arms
  meet after the second raise.
* §4 THE COVER LOCK: when one twin is covered, the fork orientation pin
  is exactly "the twin is covered" (`forkWitness_iff_covered`), and
  after the other twin is raised no CARGO descendant tops the covered
  twin (`no_raise_after_twin_raise`).
* §5 the assembled critical-pair ledger.

THE REMAINING GLOBAL RESIDUE (not in this card): a long WITNESS play —
not just a cargo path — could in principle raise the cover itself after
advancing its suit.  The local lock quantifies cargo descendants only.
That full-play cascade is the named residue `ForkCoverCascade`; see the
campaign memo and `Temp/ForkCP_report.md`.

House compliance: additive leaf (`Orig2.CargoRaise` for the flat
characterization and seat-diff rows, `Orig2.Position` for the rung
ledger); zero `sorry`, zero `Classical.choice`; battery at the tail.
-/

/-! ## §1. The configuration -/

/-- **TwinLivePair st x** — the S-live set is exactly the twin pair
`{x, x.twin}`.  This is the first conjunct of `ForkWitness`, named so
the cover equivalence can speak about the live set without the
orientation pin. -/
def TwinLivePair (st : State) (x : Card) : Prop :=
  ∀ c, CanRaiseS st c ↔ c = x ∨ c = x.twin

/-- `ForkWitness` is the live-pair condition plus the orientation pin. -/
theorem forkWitness_iff (st : State) (x : Card) :
    ForkWitness st x ↔ TwinLivePair st x ∧ ¬ CanRaise st x.twin := by
  unfold ForkWitness TwinLivePair
  constructor
  · rintro ⟨h, h2⟩
    exact ⟨fun c => (h c).symm, h2⟩
  · rintro ⟨h, h2⟩
    exact ⟨fun c => (h c).symm, h2⟩

/-- **ArmRaise F c A** — `c` is raised at some cargo accommodation of
`F`: the one-raise arm's first leg, read as a span rather than a single
move.  The `cargoPath` leg is the `CanRaiseS` accommodation. -/
def ArmRaise (F : State) (c : Card) (A : State) : Prop :=
  ∃ z, CargoPath F z ∧ State.step z (Move.tabToFound c) = some A

/-! ## §2. The rung obstruction -/

/-- A cargo leg is a flat step (its letter is a reversible `tabToTab`). -/
theorem cargoLeg_flatStep {a b : State} (h : CargoLeg a b) : FlatStep a b := by
  obtain ⟨c, bs, hstep, hrev⟩ := h
  exact FlatStep.cargo c bs hstep hrev

/-- A cargo path is a flat path. -/
theorem cargoPath_flatPath {a b : State} (h : CargoPath a b) : FlatPath a b := by
  induction h with
  | refl w => exact Steps.refl w
  | cons hleg _ ih => exact Steps.cons (cargoLeg_flatStep hleg) ih

theorem rungAt_flatStep {a b : State} (h : FlatStep a b) (σ : Suit) :
    rungAt a σ = rungAt b σ := by
  cases h with
  | cargo c bs hstep hrev => exact (rungAt_tabToTab hstep σ).symm
  | draw hstep hrev => exact (rungAt_draw hstep σ).symm

/-- A flat path fixes every rung. -/
theorem rungAt_flatPath {a b : State} (h : FlatPath a b) (σ : Suit) :
    rungAt a σ = rungAt b σ := by
  induction h with
  | refl w => rfl
  | cons hstep _ ih => exact (rungAt_flatStep hstep σ).trans ih

/-- A cargo path fixes every rung. -/
theorem rungAt_cargoPath {a b : State} (h : CargoPath a b) (σ : Suit) :
    rungAt a σ = rungAt b σ :=
  rungAt_flatPath (cargoPath_flatPath h) σ

/-- The one-raise arm's ledger: the raised suit gains exactly one rung,
every other suit is fixed. -/
theorem armRaise_rung {F A : State} {c : Card} (hA : ArmRaise F c A) (σ : Suit) :
    rungAt A σ = if σ = c.suit then rungAt F σ + 1 else rungAt F σ := by
  obtain ⟨z, hpath, hstep⟩ := hA
  rw [rungAt_tabToFound hstep σ, rungAt_cargoPath hpath σ]

/-- **THE ONE-RAISE ARMS ARE NEVER FLAT-JOINED.** -/
theorem arms_never_flatJoin {F A B : State} {c d : Card}
    (hA : ArmRaise F c A) (hB : ArmRaise F d B) (hsu : c.suit ≠ d.suit) :
    ¬ FlatPath A B := by
  intro hfab
  have h1 : rungAt A c.suit = rungAt B c.suit := rungAt_flatPath hfab c.suit
  have h2 : rungAt A c.suit = rungAt F c.suit + 1 := by
    have h := armRaise_rung hA c.suit
    rw [ite_eq_left rfl] at h
    exact h
  have h3 : rungAt B c.suit = rungAt F c.suit := by
    have h := armRaise_rung hB c.suit
    rw [ite_eq_right hsu] at h
    exact h
  omega

def raiseSt (u : State) (c : Card) (a : Anchor) : State :=
  (u.setFound c.suit (u.found c.suit ++ [c])).setPile a
    (Pile.afterRunRemoved (u.piles a) (chop (u.piles a).faceUp))

theorem raiseSt_found_apply (u : State) (c : Card) (a : Anchor) (s : Suit) :
    (raiseSt u c a).found s =
      if s = c.suit then u.found c.suit ++ [c] else u.found s := rfl

theorem raiseSt_piles_apply (u : State) (c : Card) (a : Anchor) (a' : Anchor) :
    (raiseSt u c a).piles a' =
      if a' = a then Pile.afterRunRemoved (u.piles a) (chop (u.piles a).faceUp)
      else u.piles a' := rfl

theorem raiseSt_stock (u : State) (c : Card) (a : Anchor) :
    (raiseSt u c a).stock = u.stock := rfl

theorem raiseSt_waste (u : State) (c : Card) (a : Anchor) :
    (raiseSt u c a).waste = u.waste := rfl

theorem raiseSt_drawStep (u : State) (c : Card) (a : Anchor) :
    (raiseSt u c a).drawStep = u.drawStep := rfl

/-- Rung arithmetic at the raise landing. -/
theorem rungAt_raiseSt {u : State} {c : Card} {a : Anchor} (σ : Suit) :
    rungAt (raiseSt u c a) σ =
      if σ = c.suit then rungAt u σ + 1 else rungAt u σ := by
  unfold rungAt
  by_cases hσ : σ = c.suit
  · subst hσ
    rw [raiseSt_found_apply, ite_eq_left rfl, ite_eq_left rfl]
    simp [List.length_append]
  · rw [raiseSt_found_apply, ite_eq_right hσ, ite_eq_right hσ]

/-- A raise of `c` leaves `d`'s `nextUp` alone when the suits differ. -/
theorem raiseSt_nextUp_ne {u : State} {c d : Card} {a : Anchor}
    (hsu : c.suit ≠ d.suit) :
    (raiseSt u c a).nextUp d = u.nextUp d := by
  unfold State.nextUp State.foundHeight
  rw [raiseSt_found_apply, ite_eq_right (Ne.symm hsu)]

/-- `raiseSt` is exactly a `setPile` of the set-found state. -/
theorem raiseSt_setPile (u : State) (c : Card) (a : Anchor) :
    raiseSt u c a = (u.setFound c.suit (u.found c.suit ++ [c])).setPile a
      (Pile.afterRunRemoved (u.piles a) (chop (u.piles a).faceUp)) := rfl

/-- Membership bookkeeping for the run removal. -/
theorem mem_afterRunRemoved_faceUp_zone {p : Pile} {pre : List Card} {z : Card}
    (h : z ∈ (Pile.afterRunRemoved p pre).faceUp) : z ∈ pre ∨ z ∈ p.hidden := by
  cases pre with
  | nil =>
      cases hp : p.hidden with
      | nil =>
          simp only [Pile.afterRunRemoved, hp, Pile.revealTop, List.not_mem_nil] at h
      | cons g gs =>
          simp only [Pile.afterRunRemoved, hp, Pile.revealTop, List.mem_singleton,
            List.nil_append] at h
          exact Or.inr (by rw [h]; exact List.mem_cons_self ..)
  | cons x xs =>
      exact Or.inl (by simpa [Pile.afterRunRemoved] using h)

/-- The pile-top search at another pile is untouched by a raise. -/
theorem raiseSt_pileOfTop_ne {u : State} (hwf : u.WF) {c d : Card} {a b : Anchor}
    (hdb : u.pileOfTop d = some b) (hab : a ≠ b) :
    (raiseSt u c a).pileOfTop d = some b := by
  have hdmem : d ∈ (u.piles b).faceUp :=
    lastOf_mem (pileOfTop_top hdb).2
  have huniq := mem_faceUp_unique hwf hdmem a hab
  have hdFuA : d ∉ (u.piles a).faceUp := huniq.1
  have hdHidA : d ∉ (u.piles a).hidden := huniq.2.1
  have hQmem : d ∉ (Pile.afterRunRemoved (u.piles a) (chop (u.piles a).faceUp)).faceUp := by
    intro hmem
    rcases mem_afterRunRemoved_faceUp_zone hmem with hpre | hhid
    · exact hdFuA (chop_mem hpre)
    · exact hdHidA hhid
  rw [raiseSt_setPile]
  rw [State.setPile_pileOfTop_of_not_mem hQmem (by rw [setFound_piles]; exact hdFuA)]
  rw [State.setFound_pileOfTop]
  exact hdb

/-- Raising `c` at `u` does not disturb a raise of `d` (different suit,
different source pile): the second raise fires at the landing state. -/
theorem step_raiseSt_raise {u : State} (hwf : u.WF) {c d : Card} {a b : Anchor}
    (hsu : c.suit ≠ d.suit) (hab : a ≠ b)
    (hnd : u.nextUp d = true) (hpd : u.pileOfTop d = some b) :
    State.step (raiseSt u c a) (Move.tabToFound d) =
      some (raiseSt (raiseSt u c a) d b) := by
  rw [step_tabToFound_splice (by rw [raiseSt_nextUp_ne hsu]; exact hnd)
    (raiseSt_pileOfTop_ne hwf hpd hab)]
  rfl

/-- The functional commutation behind the square. -/
theorem raiseSt_commute {u : State} {c d : Card} {a b : Anchor}
    (hab : a ≠ b) (hsu : c.suit ≠ d.suit) :
    raiseSt (raiseSt u c a) d b = raiseSt (raiseSt u d b) c a := by
  apply State.ext
  · funext s
    simp only [raiseSt_found_apply]
    by_cases hsc : s = c.suit <;> by_cases hsd : s = d.suit <;> simp_all
  · funext a'
    simp only [raiseSt_piles_apply]
    by_cases ha : a' = a <;> by_cases hb : a' = b <;> simp_all
  · rw [raiseSt_stock, raiseSt_stock, raiseSt_stock, raiseSt_stock]
  · rw [raiseSt_waste, raiseSt_waste, raiseSt_waste, raiseSt_waste]
  · rw [raiseSt_drawStep, raiseSt_drawStep, raiseSt_drawStep, raiseSt_drawStep]

/-- **THE TWIN-RAISE SQUARE (EXACT).**  Two vanilla raises of different
suits fire in both orders and land on the SAME state.  This is case (a)
of the dichotomy at the critical-pair (two-raise) grade. -/
theorem twin_raise_square {u v u' : State} {c d : Card}
    (hwf : u.WF) (hsu : c.suit ≠ d.suit)
    (h1 : State.step u (Move.tabToFound c) = some v)
    (h2 : State.step u (Move.tabToFound d) = some u') :
    ∃ w, State.step v (Move.tabToFound d) = some w ∧
         State.step u' (Move.tabToFound c) = some w := by
  obtain ⟨hnu, a, hpa, hv⟩ := step_tabToFound_inv h1
  obtain ⟨hnd, b, hpb, hu'⟩ := step_tabToFound_inv h2
  have hcd : c ≠ d := by intro h; exact hsu (by rw [h])
  have hab : a ≠ b := by
    intro hab
    rw [hab] at hpa
    have hc := (pileOfTop_top hpa).2
    have hd := (pileOfTop_top hpb).2
    have : c = d := Option.some.inj (hc.symm.trans hd)
    exact hcd this
  have hv' : v = raiseSt u c a := by
    rw [hv]; rfl
  have hu'' : u' = raiseSt u d b := by
    rw [hu']; rfl
  refine ⟨raiseSt (raiseSt u c a) d b, ?_, ?_⟩
  · rw [hv']
    exact step_raiseSt_raise hwf hsu hab hnd hpb
  · rw [hu'', step_raiseSt_raise hwf (Ne.symm hsu) (Ne.symm hab) hnu hpa]
    exact congrArg some (raiseSt_commute hab hsu).symm

/-- A vanilla license fires. -/
theorem step_tabToFound_of_canRaise {st : State} {c : Card} (h : CanRaise st c) :
    ∃ v, State.step st (Move.tabToFound c) = some v := by
  obtain ⟨hnext, a, hpa, -⟩ := h
  exact ⟨raiseSt st c a, step_tabToFound_splice hnext hpa⟩

/-- **THE NON-FORK CASE, IN LIVE-PAIR FORM.**  At a WF state whose live
set is the twin pair, if both twins are vanilla-raisable the two raises
commute and join exactly. -/
theorem both_vanilla_twin_join {F : State} {x y : Card}
    (hwf : F.WF) (hxy : y = x.twin) (hx : CanRaise F x) (hy : CanRaise F y) :
    ∃ v u' w, State.step F (Move.tabToFound x) = some v ∧
      State.step F (Move.tabToFound y) = some u' ∧
      State.step v (Move.tabToFound y) = some w ∧
      State.step u' (Move.tabToFound x) = some w := by
  obtain ⟨v, hv⟩ := step_tabToFound_of_canRaise hx
  obtain ⟨u', hu'⟩ := step_tabToFound_of_canRaise hy
  have hsu : x.suit ≠ y.suit := by
    rw [hxy]
    intro h
    exact Suit.twin_ne x.suit (by simpa [Card.twin] using h.symm)
  obtain ⟨w, h1, h2⟩ := twin_raise_square hwf hsu hv hu'
  exact ⟨v, u', w, hv, hu', h1, h2⟩

/-! ## §4. The fork side: the cover lock

A founded card tops no pile; a card seated on `y` keeps its seat across
`x`'s raise (different piles, equal ranks cannot share a run); and
`bareCargo_cover_license` says a cover that moves along a cargo path
forces the parent's twin to top a pile at the origin.  Hence after `x`
is raised no cargo descendant can top `y`. -/

/-- A founded card is no pile top. -/
theorem pileOfTop_eq_none_of_found {st : State} (hwf : st.WF) {c : Card}
    (h : c ∈ st.found c.suit) : st.pileOfTop c = none := by
  by_cases hp : st.pileOfTop c = none
  · exact hp
  · obtain ⟨a, ha⟩ := option_some_of_ne_none hp
    have hmem : c ∈ (st.piles a).faceUp := Pile.mem_of_top (pileOfTop_top ha).2
    exact absurd hmem (((mem_found_unique hwf h).1 a).2)

/-- **THE COVER LOCK.**  If `y` is covered at `F` (its immediate cover
`d` is seated on it) and `x` is raised at `F`, then no cargo descendant
of the landing state tops `y`.  With `y = x.twin` this is the fork-side
non-joinability: the only state that can free `y` would have to expose it
by placing `d` on `y.twin = x`, and `x` is now founded. -/
theorem no_raise_after_twin_raise {F A : State} {x y d : Card}
    (hwf : F.WF) (hxy : y = x.twin)
    (hx : State.step F (Move.tabToFound x) = some A)
    (hdseat : seatOf F d = some (Sum.inr y)) :
    ∀ Z, CargoPath A Z → ¬ CanRaise Z y := by
  intro Z hZ hcan
  obtain ⟨hnx, a, hpa, hA⟩ := step_tabToFound_inv hx
  have hwfA : A.WF := step_wf hwf hx
  have hwfZ : Z.WF := cargoPath_wf hwfA hZ
  -- x is founded at A, hence tops no pile there
  obtain ⟨hF1, -, -⟩ := tabToFound_found_trio hA
  have hxA : x ∈ A.found x.suit := by rw [hF1]; simp
  have htopxA : A.pileOfTop x = none := pileOfTop_eq_none_of_found hwfA hxA
  -- CanRaise Z y makes y a pile top at Z
  obtain ⟨-, b, hpb, -⟩ := hcan
  -- the cover's seat, read at F
  obtain ⟨ad, hholdF, -, hlastF⟩ := tfc_seatOf_of_inr hdseat
  have hdmem : d ∈ (F.piles ad).faceUp := pileHolding_mem hholdF
  have hymem : y ∈ (F.piles ad).faceUp := mem_below _ (lastOf_mem hlastF)
  -- the cover lives in a different pile than x's source
  have hada : ad ≠ a := by
    intro had
    have hxmem : x ∈ (F.piles a).faceUp :=
      lastOf_mem (pileOfTop_top hpa).2
    have hymema : y ∈ (F.piles a).faceUp := by rw [← had]; exact hymem
    have hrank : x.rank = y.rank := by rw [hxy]; rfl
    have hxyc : x = y := runOK_rank_distinct (hwf.2.1 a) hxmem hymema hrank
    exact (card_twin_ne x) (by rw [← hxy]; exact hxyc.symm)
  have hpilesAd : A.piles ad = F.piles ad := by
    rw [hA]
    simp only [ite_eq_right hada]
  have hdmemA : d ∈ (A.piles ad).faceUp := by rw [hpilesAd]; exact hdmem
  have hholdA : A.pileHolding d = some ad :=
    (pileHolding_eq_some_iff hwfA).2 hdmemA
  -- the cover's seat is unchanged by the raise
  have hseatA : seatOf A d = some (Sum.inr y) := by
    rw [tfc_seatOf_pair hholdA]
    rw [hpilesAd]
    rw [tfc_getLast?_lastOf, hlastF]
  -- at Z the cover cannot still sit on y (y tops a pile)
  have hnotseat : seatOf Z d ≠ some (Sum.inr y) := by
    intro hcont
    obtain ⟨aZ, hholdZ, -, hlastZ⟩ := tfc_seatOf_of_inr hcont
    have hnone := (tfc_seat_parent hwfZ hholdZ hlastZ).2
    rw [hpb] at hnone
    exact absurd hnone (by simp)
  have hchg : seatOf A d ≠ seatOf Z d := by
    rw [hseatA]
    exact fun h => hnotseat h.symm
  have hbce : BareCargoEquiv A Z := cargoPath_bareCargo hwfA hZ
  have hlic := bareCargo_cover_license hwfA hwfZ hbce hseatA hchg
  have hyx : y.twin = x := by rw [hxy, tfc_card_twin_twin]
  rw [hyx] at hlic
  exact hlic htopxA

/-! ## §5. The assembled dichotomy -/

theorem below_append_notmem {t : Card} : ∀ {xs : List Card}, t ∉ xs → ∀ ys,
    below t (xs ++ ys) = xs ++ below t ys := by
  intro xs
  induction xs with
  | nil => intro _ ys; rfl
  | cons x xs ih =>
      intro h ys
      have hx : ¬(x = t) := by
        intro hxt
        exact h (by rw [hxt]; exact List.mem_cons_self ..)
      rw [List.cons_append, below_cons, ite_eq_right hx]
      rw [ih (fun hmem => h (List.mem_cons_of_mem _ hmem)) ys]
      rw [List.cons_append]

/-- **THE FLAT DICHOTOMY PER CARD.**  An S-live card is either
vanilla-raisable already, or it is covered.  (The flat characterization
`canRaiseS_flat_necessity`: if the run above the card is empty the flat
seat shape IS the vanilla shape; otherwise the first card above it is
seated on it.) -/
theorem canRaise_or_covered {st : State} {c : Card} (hwf : st.WF)
    (hs : CanRaiseS st c) : CanRaise st c ∨ CoveredAt st c := by
  obtain ⟨hnext, a, bs, run, hshape, hseat, hrun⟩ :=
    canRaiseS_flat_necessity hwf hs
  cases run with
  | nil =>
      refine Or.inl ⟨hnext, a, ?_, ?_⟩
      · rw [pileOfTop_eq_some_iff hwf]
        show lastOf (st.piles a).faceUp = some c
        rw [hshape]
        exact lastOf_snoc
      · show chop (st.piles a).faceUp ≠ [] ∨ _
        rw [hshape, chop_snoc]
        exact hseat
  | cons d rest =>
      have hnd : (bs ++ c :: d :: rest).Nodup := by
        rw [← hshape]
        exact runOK_nodup (hwf.2.1 a)
      have hdnotbs : d ∉ bs := by
        intro hmem
        exact ((List.nodup_append.1 hnd).2.2 d hmem) d (by simp) rfl
      have hnd2 : (c :: d :: rest).Nodup := (List.nodup_append.1 hnd).2.1
      have hcnd : c ≠ d := by
        intro hcd
        exact (List.nodup_cons.1 hnd2).1 (by rw [hcd]; exact List.mem_cons_self ..)
      have hh : st.pileHolding d = some a := by
        rw [pileHolding_eq_some_iff hwf, hshape]
        exact List.mem_append.mpr (Or.inr (by simp))
      have hbd : below d (bs ++ c :: d :: rest) = bs ++ [c] := by
        rw [below_append_notmem hdnotbs, below_cons, ite_eq_right hcnd, below_cons_self]
      refine Or.inr ⟨d, ?_⟩
      rw [tfc_seatOf_pair hh]
      show (match (below d (st.piles a).faceUp).getLast? with
        | none => some (Sum.inl a)
        | some z => some (Sum.inr z)) = some (Sum.inr c)
      rw [hshape, hbd, tfc_getLast?_lastOf, lastOf_snoc]

/-- **THE FLAT GLUE.**  A card that is S-raisable but not vanilla-raisable
is covered. -/
theorem covered_of_live_not_canRaise {st : State} {c : Card} (hwf : st.WF)
    (hs : CanRaiseS st c) (hn : ¬ CanRaise st c) : CoveredAt st c :=
  (canRaise_or_covered hwf hs).resolve_left hn

/-- The converse per-card read: an S-live, uncovered card is vanilla
raisable. -/
theorem canRaise_of_live_not_covered {st : State} {c : Card} (hwf : st.WF)
    (hs : CanRaiseS st c) (hc : ¬ CoveredAt st c) : CanRaise st c :=
  (canRaise_or_covered hwf hs).resolve_right hc

/-- A covered card is not vanilla-raisable (its parent tops no pile). -/
theorem not_canRaise_of_covered {st : State} (hwf : st.WF) {c : Card}
    (h : CoveredAt st c) : ¬ CanRaise st c := by
  obtain ⟨d, hd⟩ := h
  obtain ⟨a, hhold, -, hlast⟩ := tfc_seatOf_of_inr hd
  have hnone := (tfc_seat_parent hwf hhold hlast).2
  intro hcan
  obtain ⟨-, a', hpa', -⟩ := hcan
  rw [hnone] at hpa'
  exact absurd hpa' (by simp)

/-- **FORK ⟺ COVER (at a live pair).**  With `y = x.twin` and `y`
S-live, `ForkWitness F x` holds exactly when `y` is covered.  This is the
exact local reading of the orientation pin: the blocked twin is the
covered one. -/
theorem forkWitness_iff_covered {st : State} {x y : Card} (hwf : st.WF)
    (hxy : y = x.twin) (hlive : TwinLivePair st x) (hy : CanRaiseS st y) :
    ForkWitness st x ↔ CoveredAt st y := by
  constructor
  · rintro ⟨-, hn⟩
    rw [← hxy] at hn
    exact covered_of_live_not_canRaise hwf hy hn
  · rintro hcov
    rw [forkWitness_iff]
    refine ⟨hlive, ?_⟩
    rw [← hxy]
    exact not_canRaise_of_covered hwf hcov

/-- **NEITHER COVERED ⟹ THE SQUARE JOINS.**  At a live twin pair, if
neither twin is covered then both are vanilla-raisable (the glue's
contrapositive) and the two-raise square commutes exactly. -/
theorem join_of_not_covered {F : State} {x y : Card}
    (hwf : F.WF) (hxy : y = x.twin)
    (hxS : CanRaiseS F x) (hyS : CanRaiseS F y)
    (hxc : ¬ CoveredAt F x) (hyc : ¬ CoveredAt F y) :
    ∃ v u' w, State.step F (Move.tabToFound x) = some v ∧
      State.step F (Move.tabToFound y) = some u' ∧
      State.step v (Move.tabToFound y) = some w ∧
      State.step u' (Move.tabToFound x) = some w := by
  have hx : CanRaise F x := canRaise_of_live_not_covered hwf hxS hxc
  have hy : CanRaise F y := canRaise_of_live_not_covered hwf hyS hyc
  exact both_vanilla_twin_join hwf hxy hx hy

/-! ## §6. The critical-pair ledger (summary)

At a `WF` state `F` with `TwinLivePair F x`, put `y = x.twin`.

* If neither twin is covered, `join_of_not_covered` gives the exact
  two-raise square (both orders fire, same landing state).
* If `ForkWitness F x` (`y` covered), `fork_second_leg_dead` says the
  `y`-arm never fires after `raise x` along any cargo accommodation.
  Symmetrically, the only way to fire the `y`-arm first is the mate-slide
  of `y`'s cover onto `y.twin = x`, which covers `x`; applying the same
  theorem with the roles swapped kills the `x`-arm after `raise y`.
* The literal ONE-RAISE join is impossible in either case
  (`arms_never_flatJoin`): the arms differ in rung by construction.

The open side — a long WITNESS play that raises the cover itself after
advancing its suit — is the named global residue, not a gap in the rows
above. -/


/-! ## §6b. Saturation first-step rows -/

theorem seat_of_tabToFoundR {st : State} {c : Card}
    (h : tabToFoundR st c = true) :
    ∃ a, st.pileOfTop c = some a ∧
      (chop (st.piles a).faceUp ≠ [] ∨
        ((st.piles a).hidden = [] ∧ c.rank = Rank.king)) := by
  unfold tabToFoundR at h
  split at h
  · exact absurd h (by simp)
  · rename_i hn
    split at h
    · exact absurd h (by simp)
    · rename_i a ha
      refine ⟨a, ha, ?_⟩
      cases hc : chop (st.piles a).faceUp with
      | cons x xs => exact Or.inl (by simp)
      | nil =>
          rw [hc] at h
          cases hh : (st.piles a).hidden with
          | cons y ys => rw [hh] at h; exact absurd h (by simp)
          | nil => rw [hh] at h; exact Or.inr ⟨rfl, of_decide_eq_true h⟩

/-- **At `WF`, an undoable raise is a legal vanilla raise.**  `CanRaise` and
the raise shape `tabToFoundR` agree cell-for-cell on the seat (a nonempty chop
or a bare-king seat); the missing link is `reversibleAtW → tabToFoundR`, which
is exactly the `WF` bridge `tabToFoundR_iff_reversibleAtW`.  (The raw
`step .tabToFound` does NOT check the seat, so a fired raise letter alone is
not enough at wild states.) -/
theorem canRaise_of_reversible_raise {st : State} (hwf : st.WF) {c : Card}
    (h : reversibleAtW st (Move.tabToFound c)) : CanRaise st c := by
  have hR : tabToFoundR st c = true :=
    (tabToFoundR_iff_reversibleAtW hwf c).mpr h
  obtain ⟨a, ha, hseat⟩ := seat_of_tabToFoundR hR
  have hn : st.nextUp c = true := by
    unfold tabToFoundR at hR
    split at hR
    · exact absurd hR (by simp)
    · rename_i hn
      split at hR
      · exact absurd hR (by simp)
      · exact hn
  exact ⟨hn, a, ha, hseat⟩

theorem sameOrbit_reachable {u v : State} (h : sameOrbitSetoid.r u v) :
    ∃ ρ : List Move, ShufflePlayW u ρ v := by
  obtain ⟨ρ, _, ρ', hρ'⟩ := h
  exact ⟨ρ', hρ'⟩

/-- A class-mate of a `WF` state is `WF`. -/
theorem wf_of_sameOrbit {u v : State} (hcls : sameOrbitSetoid.r u v)
    (hu : u.WF) : v.WF := by
  obtain ⟨σ, hσ, τ, hτ⟩ := hcls
  exact run_wf hu (Walk_run _ hτ)

/-- Two raises of the same suit cannot both fire in both orders. -/
theorem raise_same_suit_contra {u s1 s2 s12 : State} (hwf : u.WF) {c1 c2 : Card}
    (h1 : State.step u (Move.tabToFound c1) = some s1)
    (h2 : State.step u (Move.tabToFound c2) = some s2)
    (hsu : c1.suit = c2.suit)
    (h12 : State.step s1 (Move.tabToFound c2) = some s12) : False := by
  obtain ⟨hnextU1, a, hpa, hs1⟩ := step_tabToFound_inv h1
  obtain ⟨hnextU2, -⟩ := step_tabToFound_inv h2
  obtain ⟨hnextS2, -⟩ := step_tabToFound_inv h12
  have hu1 : c1.rank.toIdx = (u.found c1.suit).length := by
    have h := of_decide_eq_true hnextU1
    simpa [State.nextUp, State.foundHeight] using h
  have hu2 : c2.rank.toIdx = (u.found c2.suit).length := by
    have h := of_decide_eq_true hnextU2
    simpa [State.nextUp, State.foundHeight] using h
  have hs2l : c2.rank.toIdx = (s1.found c2.suit).length := by
    have h := of_decide_eq_true hnextS2
    simpa [State.nextUp, State.foundHeight] using h
  have hs1f : s1.found c2.suit = u.found c1.suit ++ [c1] := by
    rw [hs1]
    show (u.setFound c1.suit (u.found c1.suit ++ [c1])).found c2.suit = _
    rw [← hsu, setFound_found_self]
  have hlen : (s1.found c2.suit).length = (u.found c1.suit).length + 1 := by
    rw [hs1f, List.length_append]
    simp
  have hc2c1 : c2 = c1 := by
    have hr : c2.rank = c1.rank := by
      apply Rank.toIdx_inj
      rw [hu2, ← hsu, ← hu1]
    cases c2
    cases c1
    simp_all
  rw [← hc2c1] at hu1
  rw [hsu] at hlen
  omega

/-! ## §4. Battery -/

/-! ## §7. The battery -/

#print axioms forkWitness_iff
#print axioms arms_never_flatJoin
#print axioms twin_raise_square
#print axioms raiseSt_commute
#print axioms both_vanilla_twin_join
#print axioms pileOfTop_eq_none_of_found
#print axioms no_raise_after_twin_raise
#print axioms covered_of_live_not_canRaise
#print axioms canRaise_or_covered
#print axioms canRaise_of_live_not_covered
#print axioms not_canRaise_of_covered
#print axioms forkWitness_iff_covered
#print axioms join_of_not_covered

#print axioms canRaise_of_reversible_raise
#print axioms raise_same_suit_contra
#print axioms sameOrbit_reachable
#print axioms wf_of_sameOrbit
