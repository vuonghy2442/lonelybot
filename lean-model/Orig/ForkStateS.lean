import Orig.ForkStateUniqGate
import Orig.RunOrTwin
import Orig.PositionSeat

/-!
# Orig.ForkStateS — THE S-GRADE DETECTION, FIRST CARD (the maneuver-stable forkState)

THE BRIEF: the three-clause `forkState` rows were refuted at both uniqueness
grades (§11-L5/L6/L7: the flat falsifier family — `forkState_unique`, then
`forkSpectrum_complete`, the third landing the same mechanism), and the repair
the falsifiers kept naming was the maneuver-stable grade: the detection must
fire only where NO slide can arm a raise.  The license for that grade is
already in-tree (`CanRaiseS`, the {slide · raise} closure at
`Orig.MacroInternal`), and this card lands the detection on it, in the user's
final corrected form:

    forkState st := ∃ x,
      (∀ c, (c = x ∨ c = x.twin) ↔ CanRaiseS st c) ∧
      ¬ CanRaise st x.twin

THE TWO CONJUNCTS: the S-IFF — maximality at the maneuver grade, both
directions: nothing outside the pair can be raised even after finitely many
reversible cargo slides (the ⇒ half that kills the craft's `cell`: 6♠ is
covered by 5♥ and its twin 6♣ tops the landing pile, so the slide
`tabToTab 5♥ (inr 6♣)` — the falsifier's own first leg — exhibits
`CanRaiseS cell 6♠`, §2 below, at theorem grade), and both pair members ARE
S-live (the ⇐ half that kills BOTH craft endpoints: the bare twin 5♦ can never
be S-licensed — no reversible slide can ever seat a bare-bottom non-king, the
restoration-impossibility route priced below); and the ORIENTATION PIN
`¬ CanRaise st x.twin` — at an S-graded fork state, an S-live twin without the
vanilla license is exactly a COVERED twin (its free slide needs `(x.twin).twin`
topping — the witness — so the pin forces the witness to top and raise), i.e.
the pin selects the forkPointC-V3 geometry from the inside: one vanilla-live
witness raising now, one twin blocked under cargo, everything else saturated
even one slide deep.  (The converse derivations — "the pin forces the witness
vanilla" — consume the covered-necessarity row the classification follow-up
owns; priced in the ledger note below.)  THE PINS TRAVEL FREE (the user's
minimality observation): the pair-live half instantiates `CanRaiseS` at both
members, §1's rung pin transports each suit, and `Card.twin_rank` lands the
twin's rank — the old clauses 1–2 are the THEOREM `forkState_pins` (§3),
not premises of the detection.

WHAT THIS FILE LANDS (additive leaf, importing `Orig.ForkStateUniq`
(bringing `Orig.MacroInternal` transitively),
NOT wired into the root, zero sorry):

* §1 THE RUNG PIN — `canRaiseS_rung`: an S-license at `c` already pins
  `c`'s suit rung at `c`'s rank (the `now` leg is the vanilla pin
  (`stackable_now_rungexact`), the `via` leg rides the per-slide rung
  preservation through a one-leg `CargoPath` and `cargoPath_rungs`).  The
  public replica of the in-tree private row, first half of the flat
  characterization: an S-raised card IS next-up on its rung.
* §2 THE FREE LEMMA — `canRaiseS_free`, the constructive half of the flat
  characterization and the engine of the new detection: a next-up card `c`
  covered directly by a card `d` fitting on it, with seat content below and
  `c.twin` topping some other pile, is `CanRaiseS`: the cover's run slides
  onto the twin's top (the fit onto `c.twin` is automatic — the tableau
  rules cannot tell twins apart), the leg is reversible (the banked
  under-cell `tabToTab_undo_under`: the undo slides the run back onto the
  exposed `c`), and the exposed `c` raises at the successor with its under
  seat untouched.  This is the falsifier's own journey leg made into a
  generator witness — at the craft's `cell` it IS
  `[tabToTab 5♥ (inr 6♣)]` followed by the licensed `6♠` raise.
* §3 THE DETECTION — `forkState` (the user's corrected def, minimal form),
  the parcel assembly row, **THE FREE-PIN THEOREM** `forkState_pins` (the
  rung pins travel free through the S-iff — the user's redundancy
  observation, made formal), and the two projection reads (pair-live both
  members; the twin vanilla-blocked).
* §4 THE MATE-ORBIT LIVE — `slid_mate_shape_pairS_live`: at the slid-mate
  shape (the in-tree `forkState_slide_mate` endpoint: the twin topping its
  seat-package pile, the witness covered directly by the fitting cargo),
  BOTH pair members are S-live — the twin by the vanilla now-leg, the
  witness by §2's free.  The mate orbit survives the detection upgrade,
  with the witness flipped — exactly the slide-mate's license flip.

THE LEDGER — all priced follow-ups LANDED (the extraction card wave):

- THE NEVER-LEG (the ⇐ half's enforcement) — PROVED in `Orig.PositionSeat`
  (`canRaiseS_positionSeat`, zero sorry: the pillar engine — an emptied
  pile rebuilds only to a king head; the ride disqualifiers; the seat
  read survives every via leg backwards).
- THE COVERED-NECESSITY (the twin's topping) — PROVED in
  `Orig.RunOrTwin` (`canRaiseS_runOrTwin`, zero sorry: the mutual lock,
  the deck census `{c, c.twin}`, the reveal-cell banking).
- THE FLAT CHARACTERIZATION'S FULL BICONDITIONAL — `canRaiseS_iff` and
  its readable form `canRaiseS_iff_or` below, both directions proved:
  the ⟸ both branches constructive; the ⟶ from the pin plus the two
  tails above.
- THE KING LEG: carried by the pillar's king-headed vacate arm and the
  `Orig/Vacate` chapter rows.
- THE MIGRATION: DONE — the canonical `def forkState` lives in
  `Orig.MacroInternal` (beside `CanRaiseS`); the retired vanilla def is
  `weakForkState`; the strong-to-weak bridge is `Orig.ForkWeaker`
  (`forkState_to_weak`, same witness).

House compliance: additive leaf; the in-tree interface mirrored, never
redefined (`CanRaiseS`, `CanRaise`, `reversibleAtW` consumed as-is); zero
sorry; every fresh head audited (`#print axioms` — expected `[propext]` or
`[propext, Quot.sound]`, zero `Classical.choice`).  The import extends the
mandated `Orig.MacroInternal` (transitively, through `Orig.ForkStateUniq`)
with `Orig.ForkStateUniq` itself — the pin's via leg consumes the public
`cargoPath_rungs`, and re-crafting a duplicate rung-transport family would
violate the dedup discipline (the §11-L5 precedent).
-/

/-! ## §0. The private kit (per-file copies, the house dedup discipline) -/

/-- A snoc-nodup membership bar (the copy of the in-tree private row). -/
private theorem nodup_snoc_notmem :
    ∀ (bs : List Card) (d : Card) (_hnd : (bs ++ [d]).Nodup), d ∉ bs
  | [], _, _ =>
      by
        intro hcon
        simp at hcon
  | b :: t, d, hnd =>
      by
        intro hcon
        rcases List.mem_cons.mp hcon with hdb | hcon'
        · have hbmem : b ∈ t ++ [d] :=
              List.mem_append.mpr (Or.inr (List.mem_singleton.mpr hdb.symm))
          exact absurd hbmem (List.nodup_cons.mp hnd).1
        · exact nodup_snoc_notmem t d (List.nodup_cons.mp hnd).2 hcon'

/-- A `tabToTab` never writes any foundation (the found-equality behind
the rung-preservation; `putRun_found`, `setPile_found` are public; the copy
of the in-tree private row). -/
private theorem slide_foundEq {st st' : State} {c : Card} {b : Base}
    (hstep : State.step st (Move.tabToTab c b) = some st') :
    ∀ σ, st'.found σ = st.found σ := by
  obtain ⟨a, _, _, _, hs⟩ := step_tabToTab_inv hstep
  intro σ
  rw [hs, putRun_found, setPile_found]

/-- A twin is never its own card (the copy of the in-tree private row). -/
private theorem card_twin_ne (c : Card) : c.twin ≠ c := by
  intro hcon
  exact Suit.twin_ne c.suit (congrArg Card.suit hcon)

/-- A mid-run nodup bar: an element of the snoc-after-position is not in the
prefix (the `nodup_snoc_notmem` shape generalized to a rest suffix). -/
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
        -- d = x: the head duplicates its own later slot
      · exact ih rest (List.nodup_cons.mp hnd).2 hin

/-- The `fromCard` mid-run split: cut at a card not in the prefix. -/
private theorem fromCard_append_mid (t : Card) :
    ∀ (l rest : List Card), t ∉ l → fromCard t (l ++ t :: rest) = t :: rest := by
  intro l
  induction l with
  | nil => intro rest _; exact fromCard_cons_self t rest
  | cons x xs ih =>
      intro rest hnu
      have hxt : x ≠ t := by
        intro hcon
        apply hnu
        rw [hcon]
        exact List.mem_cons_self ..
      rw [List.cons_append,
        show fromCard t (x :: (xs ++ t :: rest))
            = fromCard t (xs ++ t :: rest) from fromCard_cons_ne _ hxt]
      exact ih rest (fun hcon => hnu (List.mem_cons.mpr (Or.inr hcon)))

/-! ## §1. The rung pin — an S-raised card is next-up on its rung -/

/-- **THE RUNG PIN** (the public replica of the in-tree private row): the
S-license already pins the rung — the `now` leg is the vanilla license's own
pin, and the `via` leg's slide never writes foundations (a one-leg
`CargoPath`, `cargoPath_rungs`). -/
theorem canRaiseS_rung {st : State} {c : Card} (h : CanRaiseS st c) :
    rungAt st c.suit = c.rank.toIdx := by
  induction h with
  | now c hcan => exact stackable_now_rungexact _ c hcan
  | via c hl _h2 ih =>
      obtain ⟨d, b, hstep, hrev⟩ := hl
      have hcp : CargoPath _ _ :=
        CargoPath.cons (FlatStep.cargo d b hstep hrev)
          ⟨d, b, hstep, hrev, rfl⟩ (CargoPath.refl _)
      have hr := cargoPath_rungs hcp c.suit
      omega

/-! ## §2. The free lemma — the covered card's one-slide S-license -/

/-- **THE FREE LEMMA** — the constructive half of the flat characterization:
`c` next-up, covered directly by `d` (fitting on it by the run discipline),
over seat content `bs`, with `c.twin` topping some other pile — then `c` is
`CanRaiseS`.  The cover's run slides onto the twin's top (the fit onto
`c.twin` is the twin-blind arithmetic of `canSitOn`), the leg is reversible
(the under-cell: the undo slides the run back onto the exposed `c`), and the
exposed `c` raises at the successor: the slide never wrote the foundations
and never touched `c`'s under-seat.  At the §11-L6 craft this is the
falsifier's own first leg: `CanRaiseS cell 6♠` through
`[tabToTab 5♥ (inr 6♣)]`. -/
theorem canRaiseS_free {st : State} {c d : Card} {a b : Anchor} {bs rest : List Card}
    (hwf : st.WF)
    (hshape : (st.piles a).faceUp = bs ++ [c] ++ (d :: rest))
    (htwinTop : st.pileOfTop c.twin = some b)
    (hbna : b ≠ a)
    (hfit : canSitOn d c = true)
    (hnext : st.nextUp c = true)
    (hseat : bs ≠ [] ∨ ((st.piles a).hidden = [] ∧ c.rank = Rank.king)) :
    CanRaiseS st c := by
  -- the fit arithmetic: the cover sits one below, opposite color
  obtain ⟨hrank, hcolne⟩ := (canSitOn_eq d c).mp hfit
  have hdne : d ≠ c := by
    intro hcon
    rw [← hcon] at hrank
    omega
  -- the memberships and the covering split
  have hassol0 : (st.piles a).faceUp = (bs ++ [c]) ++ (d :: rest) := hshape
  have hdmemA : d ∈ (st.piles a).faceUp := by
    rw [hassol0]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
  have hcmem : c ∈ (st.piles a).faceUp := by
    rw [hshape]
    exact List.mem_append.mpr (Or.inl
      (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))))
  have hdhold : st.pileHolding d = some a := (pileHolding_eq_some_iff hwf).2 hdmemA
  -- the covering split through the run discipline's duplicate-freedom:
  -- d sits above c, and no card of the descent-correct pile can repeat
  have hnd : ((bs ++ [c]) ++ (d :: rest)).Nodup := by
    have h := runOK_nodup (hwf.runOK_of a)
    rw [hassol0] at h
    exact h
  have hdnotmem : d ∉ bs ++ [c] :=
    nodup_mid_notmem d (bs ++ [c]) rest hnd
  have hbel : below d ((st.piles a).faceUp) = bs ++ [c] := by
    rw [hassol0]
    exact below_append_stop hdnotmem
  have hfrom : fromCard d ((st.piles a).faceUp) = d :: rest := by
    rw [hassol0]
    exact fromCard_append_mid d (bs ++ [c]) rest hdnotmem
  have hpre : bs ++ [c] ≠ [] := by
    cases bs with
    | nil => simp
    | cons w ws => simp
  -- the twin-blind fit: the cover fits the twin's seat by the same arithmetic
  have hfittwin : canSitOn d c.twin = true :=
    (canSitOn_eq d c.twin).2
      ⟨by rw [Card.twin_rank]; exact hrank,
       by rw [show c.twin.suit.color = c.suit.color from
          Suit.color_twin c.suit]; exact hcolne⟩
  -- FIRE the slide; the successor is the literal
  have hsteplit : st.step (Move.tabToTab d (Sum.inr c.twin)) = some
      ((st.setPile a (Pile.afterRunRemoved (st.piles a) (bs ++ [c]))).putRun
        (d :: rest) (Sum.inr c.twin)) := by
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
    rw [hdhold]
    simp only [canPlace_inr_located htwinTop, hfittwin]
    rw [hfrom, hbel]
    rfl
  obtain ⟨s', hs'eq, hstep⟩ : ∃ s', s' =
      (st.setPile a (Pile.afterRunRemoved (st.piles a) (bs ++ [c]))).putRun
        (d :: rest) (Sum.inr c.twin) ∧
      st.step (Move.tabToTab d (Sum.inr c.twin)) = some s' :=
    ⟨_, rfl, hsteplit⟩
  -- the mid-state pile a: the exposed c over the hidden deck
  have hmida : (st.setPile a (Pile.afterRunRemoved (st.piles a) (bs ++ [c]))).piles a
      = ⟨(st.piles a).hidden, bs ++ [c]⟩ := by
    rw [setPile_piles_self, afterRunRemoved_ne hpre]
  -- the twin's top is found at the mid-state (the profile of tops: the twin
  -- tops b at st; pile a's mid top is the exposed c, not the twin)
  have htwinmemb : c.twin ∈ (st.piles b).faceUp :=
    Pile.mem_of_top (pileOfTop_top htwinTop).2
  have hnoTtwin : ∀ y : Anchor, y ≠ b → (st.piles y).top ≠ some c.twin := by
    intro y hyp htop
    exact (mem_faceUp_unique hwf htwinmemb y hyp).1 (Pile.mem_of_top htop)
  have hmidx : (st.setPile a
      (Pile.afterRunRemoved (st.piles a) (bs ++ [c]))).pileOfTop c.twin
      = some b := by
    show (firstWhere (fun a₂ =>
        decide ((st.setPile a
          (Pile.afterRunRemoved (st.piles a) (bs ++ [c]))).topOf a₂ = some c.twin))
      Anchor.all) = some b
    refine firstWhere_find (Anchor.mem_all b) ?_ ?_
    · show decide (((st.setPile a
          (Pile.afterRunRemoved (st.piles a) (bs ++ [c]))).topOf b) = some c.twin) = true
      rw [setPile_topOf_ne hbna]
      exact decide_eq_true (pileOfTop_top htwinTop).2
    · intro y _hyp hyne
      show decide (((st.setPile a
          (Pile.afterRunRemoved (st.piles a) (bs ++ [c]))).topOf y)
          = some c.twin) = false
      by_cases hya : y = a
      · have hmidtopa : ((st.setPile a
            (Pile.afterRunRemoved (st.piles a) (bs ++ [c]))).piles a).top
            ≠ some c.twin := by
          rw [hmida]
          show lastOf (bs ++ [c]) ≠ some c.twin
          intro hcon
          have hsnoc : lastOf (bs ++ [c]) = some c := lastOf_snoc
          exact card_twin_ne c (Option.some.inj (hcon.symm.trans hsnoc))
        exact decide_false_of_not (by rw [hya]; exact hmidtopa)
      · rw [setPile_topOf_ne hya]
        exact decide_false_of_not (fun hcon => hnoTtwin y hyne
          (show (st.piles y).top = some c.twin from hcon))
  -- the successor's pile profile
  have hmidb : (st.setPile a
      (Pile.afterRunRemoved (st.piles a) (bs ++ [c]))).piles b = st.piles b :=
    setPile_piles_ne hbna
  have hs'l : s' = (st.setPile a
      (Pile.afterRunRemoved (st.piles a) (bs ++ [c]))).setPile b
      { (st.piles b) with faceUp := (st.piles b).faceUp ++ (d :: rest) } := by
    rw [hs'eq, putRun_inr_eq hmidx, hmidb]
  have hs'b : s'.piles b = ⟨(st.piles b).hidden, (st.piles b).faceUp ++ (d :: rest)⟩ := by
    rw [hs'l, setPile_piles_self]
  have hs'a : s'.piles a = ⟨(st.piles a).hidden, bs ++ [c]⟩ := by
    rw [hs'l, setPile_piles_ne (Ne.symm hbna), hmida]
  have hs'others : ∀ y, y ≠ a → y ≠ b → s'.piles y = st.piles y := by
    intro y hyp hyq
    rw [hs'l, setPile_piles_ne hyq, setPile_piles_ne hyp]
  -- the founds and WF never leave the leg
  have hfounds : ∀ σ, s'.found σ = st.found σ := fun σ => slide_foundEq hstep σ
  have hwfs' : s'.WF := step_wf hwf hstep
  -- the leg is reversible: the under-cell, with the undo sliding the run
  -- back onto the exposed c at pile a
  have hzc : lastOf (below d ((st.piles a).faceUp)) = some c := by
    rw [hbel]
    exact lastOf_snoc
  have hdmemb : d ∈ (s'.piles b).faceUp := by
    rw [hs'b]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
  have hdhold' : s'.pileHolding d = some b := (pileHolding_eq_some_iff hwfs').2 hdmemb
  have hseat' : ((Sum.inr c.twin : Base) = Sum.inl b) ∨
      ∃ z' : Card, (Sum.inr c.twin : Base) = Sum.inr z' ∧
      (st.setPile a (Pile.afterRunRemoved (st.piles a)
        (below d ((st.piles a).faceUp))) : State).pileOfTop z' = some b := by
    refine Or.inr ⟨c.twin, rfl, ?_⟩
    rw [hbel]
    exact hmidx
  have hcN : d ∉ (st.piles b).faceUp :=
    fun hmemb => (mem_faceUp_unique hwf hdmemA b hbna).1 hmemb
  have hzOnly : ∀ y, y ≠ a → (s'.piles y).top ≠ some c := by
    intro y hya htop
    by_cases hyb : y = b
    · rw [hyb] at htop
      have hcmem' : c ∈ (s'.piles b).faceUp := Pile.mem_of_top htop
      have hcmemA' : c ∈ (s'.piles a).faceUp := by
        rw [hs'a]
        exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
      exact (mem_faceUp_unique hwfs' hcmemA' b hbna).1 hcmem'
    · have hyp : y ≠ b := hyb
      rw [hs'others y hya hyp] at htop
      exact (mem_faceUp_unique hwf hcmem y hya).1 (Pile.mem_of_top htop)
  have hzK : (st.piles b).top ≠ some c := fun htop =>
    (mem_faceUp_unique hwf hcmem b hbna).1 (Pile.mem_of_top htop)
  have hrev : reversibleAtW st (Move.tabToTab d (Sum.inr c.twin)) :=
    tabToTab_undo_under hstep hdhold hzc hfit hdhold' hseat' hs'others hcN
      hzOnly hzK
  -- the exposed card raises at the successor: nextUp rides the slide's
  -- found-nonwrite, the under-seat is untouched, the pin follows
  have hLn : (st.found c.suit).length = c.rank.toIdx :=
    (of_decide_eq_true hnext : c.rank.toIdx = (st.found c.suit).length).symm
  have hnextS : s'.nextUp c = true := by
    show decide (c.rank.toIdx = (s'.found c.suit).length) = true
    rw [hfounds c.suit]
    exact decide_eq_true hLn.symm
  have htopS : (s'.piles a).top = some c := by
    rw [hs'a]
    show lastOf (bs ++ [c]) = some c
    exact lastOf_snoc
  have hpodS : s'.pileOfTop c = some a := (pileOfTop_eq_some_iff hwfs').2 htopS
  have hseatS : chop (s'.piles a).faceUp ≠ [] ∨
      ((s'.piles a).hidden = [] ∧ c.rank = Rank.king) := by
    rw [hs'a]
    rcases hseat with hbs | hhk
    · exact Or.inl (by rw [chop_snoc]; exact hbs)
    · exact Or.inr hhk
  exact CanRaiseS.via c ⟨d, Sum.inr c.twin, hstep, hrev⟩
    (CanRaiseS.now c ⟨hnextS, a, hpodS, hseatS⟩)

/-! ## §3. The detection — the user's corrected `forkState` at the S grade

The canonical `def forkState` — the two-conjunct minimal form (the pair ↔
CanRaiseS iff, plus the orientation pin) — now lives in `Orig.MacroInternal`
(the migration); this card consumes it. -/

/-- **THE FREE-PIN THEOREM** (the user's redundancy observation, formal):
the S-iff's pair-live half already carries the old detection's two rung
pins — both members are `CanRaiseS`, the rung pin (§1) transports each
suit, and the twin's rank read is the witness's own. -/
theorem forkState_pins {st : State} (h : forkState st) :
    ∃ x : Card, rungAt st x.suit = x.rank.toIdx ∧
      rungAt st x.twin.suit = x.rank.toIdx := by
  obtain ⟨x, hiff, -⟩ :
    ∃ x : Card, (∀ c, (c = x ∨ c = x.twin) ↔ CanRaiseS st c) ∧
      ¬ CanRaise st x.twin := h
  refine ⟨x, canRaiseS_rung ((hiff x).mp (Or.inl rfl)), ?_⟩
  have hr := canRaiseS_rung ((hiff x.twin).mp (Or.inr rfl))
  rwa [Card.twin_rank] at hr

/-- The parcel assembly: the two conjuncts build a detection; named for the
migration consumers. -/
theorem forkState_of_parcel {st : State} {x : Card}
    (hiff : ∀ c, (c = x ∨ c = x.twin) ↔ CanRaiseS st c)
    (hnt : ¬ CanRaise st x.twin) : forkState st :=
  ⟨x, hiff, hnt⟩

/-- The pair-live read (the ⇐ half): at an S-graded detection BOTH pair
members are S-licensed.  This half is what the old craft endpoints violate
(the bare twin 5♦ is not S-live anywhere along its class), and the mate
orbit satisfies via §4. -/
theorem forkState_pairS {st : State} (h : forkState st) :
    ∃ x : Card, ∀ c, (c = x ∨ c = x.twin) → CanRaiseS st c := by
  obtain ⟨x, hiff, -⟩ :
    ∃ x : Card, (∀ c, (c = x ∨ c = x.twin) ↔ CanRaiseS st c) ∧
      ¬ CanRaise st x.twin := h
  exact ⟨x, fun c hc => (hiff c).mp hc⟩

/-- The twin-blocked read: the detection's orientation pin, exported for the
follow-up derivations (the covered-twin / vanilla-live-witness geometry). -/
theorem forkState_twinBlocked {st : State} (h : forkState st) :
    ∃ x : Card, ¬ CanRaise st x.twin := by
  obtain ⟨x, -, hnt⟩ :
    ∃ x : Card, (∀ c, (c = x ∨ c = x.twin) ↔ CanRaiseS st c) ∧
      ¬ CanRaise st x.twin := h
  exact ⟨x, hnt⟩

/-! ## §4. The mate-orbit live — both pair members S-licensed at the slid shape

At the slid-mate shape (the in-tree `forkState_slide_mate` endpoint shape:
the twin now TOPS its seat-package pile, and the witness is covered
directly by the fitting cargo, carried along under it), the detection's
pair-live half holds at BOTH members: the twin by the vanilla now-leg (the
slide exposed it over its seat package), the witness by §2's free (the
covering cargo's run slides onto the twin's top — its own fit mirrored at
`(x).twin` — and the exposed witness raises).  The mate orbit survives the
detection upgrade with the witness FLIPPED — exactly the slide-mate's
license flip, now at the maneuver grade. -/

/-- **THE MATE-ORBIT PAIR-LIVE** — at the slid-mate shape, both pair members
are `CanRaiseS`: the twin by `now` (topping over its seat package), the
witness by the free lemma (covered by the fitting cargo, its twin topping
the CargoPath leg's landing pile).  Consumed by the migration's re-witnessed
`forkState_slide_mate`. -/
theorem slid_mate_shape_pairS_live {w : State} {x d : Card} {p q : Anchor}
    {bs bs' : List Card}
    (hwf : w.WF)
    (hpq : q ≠ p)
    (hshapep : (w.piles p).faceUp = bs' ++ [x, d])
    (hshapeq : (w.piles q).faceUp = bs ++ [x.twin])
    (htwintop : w.pileOfTop x.twin = some q)
    (hfit : canSitOn d x = true)
    (hnextx : w.nextUp x = true)
    (hseatx : bs' ≠ [] ∨ ((w.piles p).hidden = [] ∧ x.rank = Rank.king))
    (hnextt : w.nextUp x.twin = true)
    (hseatt : bs ≠ [] ∨ ((w.piles q).hidden = [] ∧ x.twin.rank = Rank.king)) :
    CanRaiseS w x ∧ CanRaiseS w x.twin := by
  -- the witness half: THE FREE at (c := x, d := the cargo, a := p, b := q)
  have hfree : CanRaiseS w x :=
    canRaiseS_free (rest := []) hwf
      (show (w.piles p).faceUp = (bs' ++ [x]) ++ (d :: ([] : List Card)) from
        hshapep.trans ((List.append_assoc bs' [x] [d]).symm))
      htwintop hpq hfit hnextx hseatx
  -- the twin half: the vanilla now-leg at the slid shape
  have hseatt' : chop (w.piles q).faceUp ≠ [] ∨
      ((w.piles q).hidden = [] ∧ x.twin.rank = Rank.king) := by
    rw [hshapeq]
    rcases hseatt with hbs | hhk
    · exact Or.inl (by rw [chop_snoc]; exact hbs)
    · exact Or.inr hhk
  have htwinRaise : CanRaise w x.twin := ⟨hnextt, q, htwintop, hseatt'⟩
  exact ⟨hfree, CanRaiseS.now _ htwinRaise⟩

/-! ## §5. The flat characterization — the full biconditional

    CanRaiseS st c ↔
      st.nextUp c = true ∧
      ∃ a bs run, (st.piles a).faceUp = bs ++ c :: run ∧
        (bs ≠ [] ∨ ((st.piles a).hidden = [] ∧ c.rank = Rank.king)) ∧
        (run = [] ∨ st.pileOfTop c.twin ≠ none)

THE ⟸ (sufficiency) IS PROVED COMPLETE, both branches: the `run = []`
branch is the vanilla now-leg over the topping read (`lastOf_snoc`,
`chop_snoc`); the `run ≠ []` branch is §2's free at the general covering
run (the adjacent fit rides the run discipline).  THE → (necessity) carries
one proved leg — the rung pin, §1 — and TWO NAMED BLOCKED TARGETS, stated as
theorems below with their complete routes:

* **`canRaiseS_positionSeat`** — the position/seat necessity.  Route: the
  member-and-seat reads survive every via leg (arrivals stack above;
  departures not headed at `c` leave the below read intact); the only leg
  that could move `c` is its own run's departure from an emptied seat,
  and it is not `reversibleAtW` by two cells: over a nonempty hidden deck
  it reveals (the banked `journey_tabToTab_never_reveal`, hidden descent),
  and over an empty hidden deck THE PILLAR closes the undo — a play that
  rebuilds face-up content on a fully emptied pile can only head it with
  a KING (the first arrival must be an empty-seat vacate by `canPlace`
  inl; inr landings need a top; departures leave prefixes; `tabToFound`
  chops the tail), so a non-king's bare seat can never be restored.
  Then the `now` end's own license contradicts the bad seat.
* **`canRaiseS_runOrTwin`** — the run-or-twin necessity (the mutual
  confinement).  Route: if `c` ends the chain topping, some leg first
  exposed it; the exposing departure lands its cover run on a
  `c`-family card (rank r, `c`'s color: exactly `{c, c.twin}`), and `c`
  itself was covered, so THE TWIN topped already; backward, a twin that
  does not top can never gain it while `c` stays covered (the covering
  family is two cards, both frozen: the mutual lock), so the twin topped
  at `st` itself. -/

/- **THE POSITION-SEAT NECESSITY** — PROVED in `Orig.PositionSeat` (the
never-leg: the pillar — an emptied pile rebuilds only to a king head, so
a non-king's bare-seat departure has no undo; the seat read survives every
reversible leg backwards intact, to the chain's `now` end whose own
license demands it good).  The necessity target is imported; this file's
audit battery prints the imported head below. -/

/-- **THE RUN-OR-TWIN NECESSITY** — PROVED in `Orig.RunOrTwin` (the mutual
lock: the deck census `{c, c.twin}` kills every un-covering landing, rides
keep covers, the reveal cell bars off-board appearances; the chain-end
tops, so the start does too).  This re-export keeps the card's audit
battery single-sourced. -/
theorem runOrTwin_tail {st : State} {c : Card} (hwf : st.WF)
    (h : CanRaiseS st c) :
    ∀ a bs run, (st.piles a).faceUp = bs ++ c :: run →
      run = [] ∨ st.pileOfTop c.twin ≠ none :=
  canRaiseS_runOrTwin hwf h

/-- **THE FLAT CHARACTERIZATION** — the full biconditional, assembled: the
sufficiency both branches proved; the necessity from §1's pin plus the two
named targets above. -/
theorem canRaiseS_iff {st : State} {c : Card} (hwf : st.WF) :
    CanRaiseS st c ↔
      st.nextUp c = true ∧
      ∃ a bs run, (st.piles a).faceUp = bs ++ c :: run ∧
        (bs ≠ [] ∨ ((st.piles a).hidden = [] ∧ c.rank = Rank.king)) ∧
        (run = [] ∨ st.pileOfTop c.twin ≠ none) := by
  constructor
  · -- necessity: the pin plus the two named rows
      intro h
      have hr : rungAt st c.suit = c.rank.toIdx := canRaiseS_rung h
      have hnext : st.nextUp c = true := by
        show decide (c.rank.toIdx = (st.found c.suit).length) = true
        exact decide_eq_true hr.symm
      obtain ⟨a, bs, run, hshape, hseat⟩ := canRaiseS_positionSeat hwf h
      exact ⟨hnext, a, bs, run, hshape, hseat,
        canRaiseS_runOrTwin hwf h a bs run hshape⟩
  · -- sufficiency: both branches, proved
      rintro ⟨hnext, a, bs, run, hshape, hseat, hdisj⟩
      have htopcase : run = [] ∨ ∃ d rest', run = d :: rest' := by
        cases run with
        | nil => exact Or.inl rfl
        | cons d rest' => exact Or.inr ⟨d, rest', rfl⟩
      rcases htopcase with rfl | ⟨d, rest', rfl⟩
      · -- the vanilla now-leg: c tops at pile a over its seat
          have htop : (st.piles a).top = some c := by
            show lastOf (st.piles a).faceUp = some c
            rw [hshape]
            exact lastOf_snoc
          have hpod : st.pileOfTop c = some a := (pileOfTop_eq_some_iff hwf).2 htop
          have hseat' : chop (st.piles a).faceUp ≠ [] ∨
              ((st.piles a).hidden = [] ∧ c.rank = Rank.king) := by
            rw [hshape]
            rcases hseat with hbs | hhk
            · exact Or.inl (by rw [chop_snoc]; exact hbs)
            · exact Or.inr hhk
          exact CanRaiseS.now c ⟨hnext, a, hpod, hseat'⟩
      · -- the free at the covering run: c covered, the twin topped
          rcases hdisj with hre | htwin
          · exact absurd hre (by simp)
          cases hpin : st.pileOfTop c.twin with
          | none => exact absurd htwin (by rw [hpin]; simp)
          | some b =>
                  -- b ≠ a: the twin is nowhere in c's own pile (the
                  -- rank arithmetic and the twin's rank)
                  have hbna : b ≠ a := by
                    intro hcon
                    rw [hcon] at hpin
                    have htopB : (st.piles a).top = some c.twin :=
                      (pileOfTop_top hpin).2
                    have hlB : lastOf (st.piles a).faceUp = some c.twin := htopB
                    rw [hshape] at hlB
                    have hmem : c.twin ∈ bs ++ c :: (d :: rest') := lastOf_mem hlB
                    have hok : runOK (bs ++ c :: (d :: rest')) = true := by
                      rw [← hshape]; exact hwf.runOK_of a
                    rcases List.mem_append.mp hmem with hbs' | hrun'
                    · -- the twin below c: rank too high
                        have hLt : c.rank.toIdx < c.twin.rank.toIdx :=
                          runOK_desc (P := bs) (S := c :: (d :: rest')) hok hbs'
                            (List.mem_cons.mpr (Or.inl rfl))
                        rw [Card.twin_rank] at hLt
                        omega
                    · rcases List.mem_cons.mp hrun' with htwinEq | hrest'
                      · exact card_twin_ne c htwinEq
                      · -- the twin above c: rank too low
                          have hokL : runOK ((bs ++ [c]) ++ (d :: rest')) = true := by
                            rw [List.append_assoc bs [c] (d :: rest')]
                            exact hok
                          have hGt : c.twin.rank.toIdx < c.rank.toIdx :=
                            runOK_desc (P := bs ++ [c]) (S := (d :: rest')) hokL
                              (List.mem_append.mpr
                                (Or.inr (List.mem_singleton.mpr rfl))) hrest'
                          rw [Card.twin_rank] at hGt
                          omega
                  have hfit := SeedKit.runOK_adjacent_fit c d bs rest' (by
                    rw [← hshape]; exact hwf.runOK_of a)
                  exact canRaiseS_free hwf
                    (show (st.piles a).faceUp = (bs ++ [c]) ++ (d :: rest') from
                      hshape.trans ((List.append_assoc bs [c] (d :: rest')).symm))
                    hpin hbna hfit hnext hseat

/-! ## §6. The readable form — the vanilla license, or the one covered shape

    CanRaiseS st c ↔
      CanRaise st c ∨
        (st.nextUp c = true ∧ SeatOK st c ∧ coveredIn st c ∧
           st.pileOfTop c.twin ≠ none)

in words: **c is maneuver-raisable iff it raises now, or it is next-up with
a refillable seat, covered, and the twin tops somewhere.**  Everything is
vocabulary now: the `run = []` branch IS the vanilla `CanRaise` (nextUp,
tops, seat — spelled once instead of three times), the position split
dissolves into the banked `below`/`coveredIn` reads, and the only new word
is `SeatOK` below.  Proved from the landed `canRaiseS_iff`; the two named
necessity tails are untouched (same content, both forms). -/

/-- **THE SEAT READ** — the refillable-seat discipline at `c`'s pile: face-up
content below (the undo lands `c` back on it), or the bare king over an
empty hidden deck (the vacate channel). -/
def SeatOK (st : State) (c : Card) : Prop :=
  ∃ a, st.pileHolding c = some a ∧
    (below c (st.piles a).faceUp ≠ [] ∨
      ((st.piles a).hidden = [] ∧ c.rank = Rank.king))

/-- The list splits at the searched card: everything before it, then the
suffix from it. -/
private theorem below_fromCard_split (t : Card) :
    ∀ (l : List Card), l = below t l ++ fromCard t l
  | [] => rfl
  | x :: xs => by
      by_cases hxt : x = t
      · rw [hxt, below_cons_self, fromCard_cons_self]
        rfl
      · rw [below_cons_ne xs hxt, fromCard_cons_ne xs hxt, List.cons_append]
        exact congrArg (x :: ·) (below_fromCard_split t xs)

/-- The suffix from a present card is the card atop its above-read. -/
private theorem fromCard_mem_split (t : Card) :
    ∀ (l : List Card), t ∈ l → fromCard t l = t :: aboveIn t l
  | [], hmem => absurd hmem (by simp)
  | x :: xs, hmem => by
      by_cases hxt : x = t
      · rw [hxt]
        simp only [aboveIn, fromCard_cons_self]
        rfl
      · rw [fromCard_cons_ne xs hxt]
        have hin : t ∈ xs := by
          rcases List.mem_cons.mp hmem with rfl | hrest
          · exact absurd rfl hxt
          · exact hrest
        have hskip : aboveIn t (x :: xs) = aboveIn t xs := by
          simp only [aboveIn]
          rw [fromCard_cons_ne xs hxt]
        rw [fromCard_mem_split t xs hin, hskip]

/-- **THE FLAT CHARACTERIZATION, READABLE FORM** — the corollary of
`canRaiseS_iff` through the vocabulary: the vanilla license alone, or the
one covered shape with its two reads (the seat, the twin's top). -/
theorem canRaiseS_iff_or {st : State} {c : Card} (hwf : st.WF) :
    CanRaiseS st c ↔
      (CanRaise st c ∨
        (st.nextUp c = true ∧ SeatOK st c ∧ coveredIn st c ∧
           st.pileOfTop c.twin ≠ none)) := by
  constructor
  · -- necessity: through the landed iff, both branches re-spelled
      intro h
      obtain ⟨hnext, a, bs, run, hshape, hseat, hdisj⟩ := (canRaiseS_iff hwf).1 h
      have hcmem : c ∈ (st.piles a).faceUp := by
        rw [hshape]
        exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
      have hnd : (bs ++ c :: run).Nodup := by
        have h := runOK_nodup (hwf.runOK_of a)
        rw [hshape] at h
        exact h
      have hcNbs : c ∉ bs := nodup_mid_notmem c bs run hnd
      cases run with
      | nil =>
          refine Or.inl ⟨hnext, a, (pileOfTop_eq_some_iff hwf).2 ?_, ?_⟩
          · show lastOf (st.piles a).faceUp = some c
            rw [hshape]
            exact lastOf_snoc
          · rw [hshape]
            rcases hseat with hbs | hhk
            · exact Or.inl (by rw [chop_snoc]; exact hbs)
            · exact Or.inr hhk
      | cons d rest' =>
          have hbelow : below c (st.piles a).faceUp = bs := by
            rw [hshape]
            exact below_append_stop hcNbs
          have hhold : st.pileHolding c = some a :=
            (pileHolding_eq_some_iff hwf).2 hcmem
          have hfc1 : fromCard c (st.piles a).faceUp
              = c :: aboveIn c (st.piles a).faceUp :=
            fromCard_mem_split c (st.piles a).faceUp hcmem
          have hfc2 : fromCard c (st.piles a).faceUp = c :: d :: rest' := by
            rw [hshape]
            exact fromCard_append_mid c bs (d :: rest') hcNbs
          have hcc := hfc1.symm.trans hfc2
          injection hcc with _ habove
          refine Or.inr ⟨hnext, ⟨a, hhold, ?_⟩, ⟨a, hhold, ?_⟩, ?_⟩
          · rw [hbelow]
            exact hseat
          · rw [habove]
            simp
          · cases hdisj with
            | inl habs => exact absurd habs (by simp)
            | inr htwin => exact htwin
  · -- sufficiency: the vanilla case is the now-leg; the covered case feeds
    -- the landed iff with the position reassembled from the vocabulary
      intro hd
      rcases hd with hcan | hcover
      · exact CanRaiseS.now c hcan
      · obtain ⟨hnext, hseat, hcov, htwin⟩ := hcover
        obtain ⟨aS, hholdS, hseatS⟩ : ∃ a, st.pileHolding c = some a ∧
            (below c (st.piles a).faceUp ≠ [] ∨
              ((st.piles a).hidden = [] ∧ c.rank = Rank.king)) := hseat
        obtain ⟨aC, hholdC, haboveC⟩ : ∃ a, st.pileHolding c = some a ∧
            aboveIn c (st.piles a).faceUp ≠ [] := hcov
        have hsame : aC = aS := Option.some.inj (hholdC.symm.trans hholdS)
        rw [hsame] at haboveC
        have hcmemS : c ∈ (st.piles aS).faceUp := pileHolding_mem hholdS
        refine (canRaiseS_iff hwf).2
          ⟨hnext, aS, below c ((st.piles aS).faceUp),
            aboveIn c ((st.piles aS).faceUp), ?_, hseatS, Or.inr htwin⟩
        have h1 : (st.piles aS).faceUp
            = below c (st.piles aS).faceUp ++ fromCard c (st.piles aS).faceUp :=
          below_fromCard_split c (st.piles aS).faceUp
        have h2 : fromCard c (st.piles aS).faceUp
            = c :: aboveIn c (st.piles aS).faceUp :=
          fromCard_mem_split c (st.piles aS).faceUp hcmemS
        refine h1.trans ?_
        rw [h2]

/-! ## The audit battery -/

#print axioms canRaiseS_rung
#print axioms canRaiseS_free
#print axioms forkState_of_parcel
#print axioms forkState_pins
#print axioms forkState_pairS
#print axioms forkState_twinBlocked
#print axioms slid_mate_shape_pairS_live
#print axioms canRaiseS_iff
#print axioms canRaiseS_iff_or
#print axioms canRaiseS_positionSeat
#print axioms canRaiseS_runOrTwin

/- APPEND-MARKER -/
