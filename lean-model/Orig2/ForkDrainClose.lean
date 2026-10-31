import Orig2.Fork
import Orig2.ForkOneSlideLive
import Orig2.ForkDrainInduction

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# Orig2.ForkDrainClose — the drain is complete

`fork_exists_of_asymmetry`: the twin asymmetry plus the rank floor forces a
fork somewhere in the class, unconditionally.  The slide endpoint frame
(`slide_frame`), the rank-floor transport (`floor_slide`, `floor_raise`), the
invariant step, and the `52 - rungSum` strong recursion are all proved here;
the copied `OneSlide` and `Drain` kits now come from
`Orig2.ForkOneSlideLive` and `Orig2.ForkDrainInduction`.
-/


namespace DrainClose

/-! ## §A. Cargo invariance of `CanRaiseS` and the slide's rank floor -/

/-- `CanRaiseS` is invariant along a single reversible cargo leg (read
backwards): a path from the leg's endpoint prepends the leg. -/
theorem canRaiseS_of_cargoLeg {u v : State} {d : Card}
    (h : CargoLeg u v) (hS : CanRaiseS v d) : CanRaiseS u d := by
  obtain ⟨z, hpath, hcan⟩ := hS
  exact ⟨z, Steps.cons h hpath, hcan⟩

/-- **R2 (slide half).**  The rank floor survives the slide, because the
slide is a reversible cargo leg and `CanRaiseS` is cargo-invariant. -/
theorem floor_slide {u v : State} {x : Card}
    (h : CargoLeg u v)
    (hfloor : ∀ d, CanRaiseS u d → x.rank.toIdx ≤ d.rank.toIdx) :
    ∀ d, CanRaiseS v d → x.rank.toIdx ≤ d.rank.toIdx :=
  fun d hd => hfloor d (canRaiseS_of_cargoLeg h hd)

/-- A vanilla raisable card has a reversible raise (`tabToFoundR`). -/
theorem tabToFoundR_of_canRaise {st : State} {c : Card} (h : CanRaise st c) :
    tabToFoundR st c = true := by
  obtain ⟨hnext, a, hpa, hseat⟩ := h
  unfold tabToFoundR
  rw [hnext]
  simp only [hpa]
  rcases hseat with hchop | ⟨hhid, hking⟩
  · cases hch : chop (st.piles a).faceUp with
    | nil => exact absurd hch hchop
    | cons w ws => rfl
  · cases hch : chop (st.piles a).faceUp with
    | nil =>
        rw [hhid]
        exact decide_eq_true hking
    | cons w ws => rfl

/-- The vanilla raise is reversible at `WF`. -/
theorem reversibleAtW_tabToFound_of_canRaise {st : State} {c : Card}
    (hwf : st.WF) (h : CanRaise st c) :
    reversibleAtW st (Move.tabToFound c) :=
  (tabToFoundR_iff_reversibleAtW hwf c).mp (tabToFoundR_of_canRaise h)

/-- A slide leaves the rank sum alone (`rungAt` reads only `found`). -/
theorem rungSum_slide {u v : State} {c : Card} {b : Base}
    (hstep : State.step u (Move.tabToTab c b) = some v) :
    Drain.rungSum v = Drain.rungSum u := by
  unfold Drain.rungSum
  have h : (fun s => rungAt v s) = (fun s => rungAt u s) := by
    funext s
    exact rungAt_tabToTab hstep s
  rw [h]

/-- The raise climb, in the `Drain` namespace. -/
theorem rungSum_raise {u v : State} {c : Card}
    (hstep : State.step u (Move.tabToFound c) = some v) :
    Drain.rungSum v = Drain.rungSum u + 1 :=
  Drain.rungSum_tabToFound hstep

/-! ## §B. R1 — the slide endpoint frame -/

/-- The twin's top pile is never the covered card's pile: the twin would
have to occur in the legal run `bs ++ c :: u1 :: rest` at rank `c.rank`,
which the strict descent forbids. -/
theorem twin_pile_ne_source {st : State} {c : Card} (hwf : st.WF)
    {a k : Anchor} {bs rest : List Card} {u1 : Card}
    (hshape : (st.piles a).faceUp = bs ++ c :: u1 :: rest)
    (htwinTop : st.pileOfTop c.twin = some k) : k ≠ a := by
  intro hka
  rw [hka] at htwinTop
  have hmemT : c.twin ∈ (st.piles a).faceUp :=
    Pile.mem_of_top (pileOfTop_top htwinTop).2
  rw [hshape] at hmemT
  have hok : runOK (bs ++ c :: u1 :: rest) = true := by
    rw [← hshape]; exact hwf.2.1 a
  have htr : c.twin.rank = c.rank := rfl
  rcases List.mem_append.mp hmemT with hbs | hrun
  · have h1 := runOK_desc hok hbs (List.mem_cons_self ..)
    rw [htr] at h1
    omega
  · rcases List.mem_cons.mp hrun with heq | hrest
    · exact card_twin_ne c heq
    · have hokL : runOK ((bs ++ [c]) ++ u1 :: rest) = true := by
        rw [show (bs ++ [c]) ++ u1 :: rest = bs ++ c :: u1 :: rest from by
          rw [List.append_assoc bs [c], List.cons_append, List.nil_append]]
        exact hok
      have h2 := runOK_desc hokL
        (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))) hrest
      rw [htr] at h2
      omega

/-- **The re-resolution row** (copied from `Temp/Commute_Slide_Kit.lean:79`):
editing the source pile of a slide does not move the top search of any
other pile's top card. -/
theorem setPile_afterRunRemoved_pileOfTop {st : State} (hwf : st.WF)
    {z : Card} {k a : Anchor} (hk : st.pileOfTop z = some k) (hak : k ≠ a)
    (c : Card) :
    (st.setPile a ((st.piles a).afterRunRemoved (below c (st.piles a).faceUp))).pileOfTop z
      = some k := by
  obtain ⟨-, hzlast⟩ := pileOfTop_top hk
  have hzmem : z ∈ (st.piles k).faceUp := lastOf_mem hzlast
  have huniq := mem_faceUp_unique hwf hzmem a (Ne.symm hak)
  have hznot : ∀ j : Anchor, j ≠ k → (st.piles j).top ≠ some z := by
    intro j hj ht
    exact (mem_faceUp_unique hwf hzmem j hj).1 (Pile.mem_of_top ht)
  have hedit : ((st.piles a).afterRunRemoved (below c (st.piles a).faceUp)).top
      ≠ some z := by
    intro ht
    have hzone : z ∈ (st.piles a).hidden ++ (st.piles a).faceUp :=
      tfc_mem_afterRunRemoved_below_zone (x := z) (c := c)
        (List.mem_append.mpr (Or.inr (Pile.mem_of_top ht)))
    rcases List.mem_append.mp hzone with hh | hh
    · exact huniq.2.1 hh
    · exact huniq.1 hh
  show firstWhere (fun a' => decide ((st.setPile a
      ((st.piles a).afterRunRemoved (below c (st.piles a).faceUp))).topOf a' = some z))
    Anchor.all = some k
  refine firstWhere_find (Anchor.mem_all k) ?_ ?_
  · show decide ((st.setPile a
      ((st.piles a).afterRunRemoved (below c (st.piles a).faceUp))).topOf k = some z) = true
    have hp : (st.setPile a
        ((st.piles a).afterRunRemoved (below c (st.piles a).faceUp))).piles k = st.piles k :=
      setPile_piles_ne hak
    have htop : (st.setPile a
        ((st.piles a).afterRunRemoved (below c (st.piles a).faceUp))).topOf k
        = (st.piles k).top := by
      show ((st.setPile a
        ((st.piles a).afterRunRemoved (below c (st.piles a).faceUp))).piles k).top
        = (st.piles k).top
      rw [hp]
    rw [htop, show (st.piles k).top = some z from (pileOfTop_eq_some_iff hwf).mp hk]
    exact decide_eq_true rfl
  · intro x _ hxk
    show decide ((st.setPile a
      ((st.piles a).afterRunRemoved (below c (st.piles a).faceUp))).topOf x = some z) = false
    apply decide_false_of_not
    intro ht
    by_cases hxa : x = a
    · rw [hxa] at ht
      have ht' : ((st.setPile a
          ((st.piles a).afterRunRemoved (below c (st.piles a).faceUp))).piles a).top
          = some z := ht
      rw [setPile_piles_self] at ht'
      exact hedit ht'
    · have htop : (st.setPile a
          ((st.piles a).afterRunRemoved (below c (st.piles a).faceUp))).topOf x
          = (st.piles x).top := by
        show ((st.setPile a
          ((st.piles a).afterRunRemoved (below c (st.piles a).faceUp))).piles x).top
          = (st.piles x).top
        rw [setPile_piles_ne hxa]
      rw [htop] at ht
      exact hznot x hxk ht
/-- **R1 — the exact piles at the cover-slide endpoint.**  The source pile
becomes `bs ++ [c]` (new top `c`, hidden unchanged), the twin's pile `k`
receives the whole moved run `u1 :: rest`, all other piles are untouched,
and the foundations are unchanged. -/
theorem slide_frame {st z : State} {c u1 : Card} {rest bs : List Card} {a k : Anchor}
    (hwf : st.WF)
    (hshape : (st.piles a).faceUp = bs ++ c :: u1 :: rest)
    (htwinTop : st.pileOfTop c.twin = some k)
    (hstep : st.step (Move.tabToTab u1 (Sum.inr c.twin)) = some z) :
    z.piles a = { st.piles a with faceUp := bs ++ [c] } ∧
    z.piles k = { st.piles k with faceUp := (st.piles k).faceUp ++ (u1 :: rest) } ∧
    (∀ j : Anchor, j ≠ a → j ≠ k → z.piles j = st.piles j) ∧
    z.found = st.found := by
  have hka : k ≠ a := twin_pile_ne_source hwf hshape htwinTop
  obtain ⟨a', hhold', hcp, hfromne, hz⟩ := step_tabToTab_inv hstep
  -- the holding pile is `a`
  have hhold : st.pileHolding u1 = some a :=
    (pileHolding_eq_some_iff hwf).2 (by
      rw [hshape]
      exact List.mem_append.mpr
        (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons_self ..)))))
  have haa : a' = a := Option.some.inj (hhold'.symm.trans hhold)
  subst a'
  -- the run and prefix splits
  have hid : (bs ++ [c]) ++ u1 :: rest = bs ++ c :: u1 :: rest := by
    rw [List.append_assoc bs [c], List.cons_append, List.nil_append]
  have hok : runOK (bs ++ c :: u1 :: rest) = true := by
    rw [← hshape]; exact hwf.2.1 a
  have hdnotin : u1 ∉ bs ++ [c] :=
    nodup_mid_notmem u1 (bs ++ [c]) rest
      (by rw [hid, ← hshape]; exact runOK_nodup (hwf.2.1 a))
  have hexcl := tfc_below_fromCard_excl u1 (bs ++ [c]) (u1 :: rest) hdnotin
  have hbelow : below u1 ((st.piles a).faceUp) = bs ++ [c] := by
    have h1 := hexcl.1
    rw [below_cons_self, List.append_nil] at h1
    rw [hshape, ← hid]
    exact h1
  have hfrom : fromCard u1 ((st.piles a).faceUp) = u1 :: rest := by
    have h2 := hexcl.2
    rw [fromCard_head_eq] at h2
    rw [hshape, ← hid]
    exact h2
  -- the step literal, in the desired form
  have hz' : z = (st.setPile a (Pile.afterRunRemoved (st.piles a) (bs ++ [c]))).putRun
      (u1 :: rest) (Sum.inr c.twin) := by
    rw [hz, hbelow, hfrom]
  -- `putRun` re-resolves the twin's pile after the source edit
  have hmidpin : (st.setPile a
      (Pile.afterRunRemoved (st.piles a) (bs ++ [c]))).pileOfTop c.twin = some k :=
    by
      rw [← hbelow]
      exact setPile_afterRunRemoved_pileOfTop hwf htwinTop hka u1
  have hnonempty : bs ++ [c] ≠ [] := by simp
  have hAR : Pile.afterRunRemoved (st.piles a) (bs ++ [c])
      = { st.piles a with faceUp := bs ++ [c] } :=
    afterRunRemoved_ne hnonempty
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hz', putRun_piles_inr_ne _ _ _ _ hmidpin (Ne.symm hka), setPile_piles_self, hAR]
  · rw [hz', putRun_piles_inr_self _ _ _ _ hmidpin, setPile_piles_ne hka]
  · intro j hja hjk
    rw [hz', putRun_piles_inr_ne _ _ _ _ hmidpin hjk, setPile_piles_ne hja]
  · rw [hz', putRun_found, setPile_found]

/-! ## §C. R2 — the rank floor survives the raise -/

/-- Removing an empty prefix over an empty hidden deck leaves an empty
face-up run. -/
theorem afterRunRemoved_nil_faceUp {p : Pile} (hh : p.hidden = [])
    (hch : chop p.faceUp = []) :
    (Pile.afterRunRemoved p (chop p.faceUp)).faceUp = [] := by
  rw [hch]
  rw [Pile.afterRunRemoved_bare hh]


/-- **R2 — `rank_preserved`.**  Raising a card `c` of rank at least
`x.rank` cannot expose a new S-live card below the floor.  Exposure
argument: a card S-live at the endpoint is either

* of `c`'s suit — then its rank is `c.rank + 1` (the rung it must meet);
* in the raised pile — then it lies in `chop (faceUp)`, strictly below
  `c` (legal run descent), so its rank exceeds `c.rank`;
* in another pile — then its flat witness transfers verbatim to the
  pre-state, unless its twin topped the raised pile, in which case the
  same chop-descent bounds it.

Hence every S-live card at the endpoint has rank at least `c.rank`, and
`x.rank ≤ c.rank` closes the floor. -/
theorem floor_raise {u u' : State} {x c : Card}
    (huwf : u.WF) (hcan : CanRaise u c)
    (hrank : x.rank.toIdx ≤ c.rank.toIdx)
    (hstep : u.step (Move.tabToFound c) = some u')
    (hfloor : ∀ d, CanRaiseS u d → x.rank.toIdx ≤ d.rank.toIdx) :
    ∀ d, CanRaiseS u' d → x.rank.toIdx ≤ d.rank.toIdx := by
  intro d hd
  have hu'wf : u'.WF := step_wf huwf hstep
  obtain ⟨hnext', Q, bs, run, hshape', hseat', hdisj'⟩ := (canRaiseS_iff hu'wf).mp hd
  obtain ⟨-, a, hpa, hs⟩ := step_tabToFound_inv hstep
  -- the raised pile's new value
  have hpa' : u'.piles a = Pile.afterRunRemoved (u.piles a) (chop (u.piles a).faceUp) := by
    rw [hs]
    show (if a = a then
      Pile.afterRunRemoved (u.piles a) (chop (u.piles a).faceUp)
      else u.piles a) = _
    rw [if_pos rfl]
  -- the raise's own seat clause
  have hseatc : chop (u.piles a).faceUp ≠ [] ∨
      ((u.piles a).hidden = [] ∧ c.rank = Rank.king) := by
    obtain ⟨a0, hpa0, hseat0⟩ := hcan.2
    have ha0 : a0 = a := Option.some.inj (hpa0.symm.trans hpa)
    rwa [ha0] at hseat0
  -- the chop of the raised pile is nonempty as soon as its new face-up run is
  have hch_of_ne : (u'.piles a).faceUp ≠ [] → chop (u.piles a).faceUp ≠ [] := by
    intro hne
    by_cases hc0 : chop (u.piles a).faceUp = []
    · exfalso
      rcases hseatc with h | ⟨hhid, -⟩
      · exact h hc0
      · exact hne (by rw [hpa']; exact afterRunRemoved_nil_faceUp hhid hc0)
    · exact hc0
  -- descent along the raised pile's chop
  have htopc : lastOf (u.piles a).faceUp = some c := (pileOfTop_top hpa).2
  have hfacec : (u.piles a).faceUp = chop (u.piles a).faceUp ++ [c] :=
    lastOf_chop htopc
  have hok : runOK (chop (u.piles a).faceUp ++ [c]) = true := by
    rw [← hfacec]; exact huwf.2.1 a
  -- suit split
  by_cases hds : d.suit = c.suit
  · have hnextU : u.nextUp c = true := hcan.1
    have hcrank : c.rank.toIdx = (u.found c.suit).length := by
      simpa [State.nextUp, State.foundHeight] using of_decide_eq_true hnextU
    have hdrank : d.rank.toIdx = (u'.found d.suit).length := by
      simpa [State.nextUp, State.foundHeight] using of_decide_eq_true hnext'
    have hfound' : u'.found c.suit = u.found c.suit ++ [c] := by
      rw [hs]
      show (u.setFound c.suit (u.found c.suit ++ [c])).found c.suit = _
      rw [setFound_found_self]
    rw [hds, hfound', List.length_append, List.length_cons, List.length_nil] at hdrank
    omega
  · have hnextU : u.nextUp d = true := by
      have h1 : d.rank.toIdx = (u'.found d.suit).length := by
        simpa [State.nextUp, State.foundHeight] using of_decide_eq_true hnext'
      have hf : u'.found d.suit = u.found d.suit := by
        rw [hs]
        exact setFound_found_ne hds
      rw [hf] at h1
      unfold State.nextUp State.foundHeight
      exact decide_eq_true h1
    by_cases hQa : Q = a
    · -- `d` lies in the raised pile's remaining run
      have hmemU' : d ∈ (u'.piles a).faceUp := by
        rw [hQa] at hshape'
        rw [hshape']
        exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
      have hch : chop (u.piles a).faceUp ≠ [] :=
        hch_of_ne (by intro hnil; rw [hnil] at hmemU'; exact List.not_mem_nil hmemU')
      have hfaceA : (u'.piles a).faceUp = chop (u.piles a).faceUp := by
        rw [hpa']
        exact afterRunRemoved_faceUp_ne hch
      have hdch : d ∈ chop (u.piles a).faceUp := by
        rw [hfaceA] at hmemU'
        exact hmemU'
      have hlt : c.rank.toIdx < d.rank.toIdx :=
        runOK_desc hok hdch (List.mem_singleton_self c)
      omega
    · have hpileQ : u'.piles Q = u.piles Q := by
        rw [hs]
        show (if Q = a then
          Pile.afterRunRemoved (u.piles a) (chop (u.piles a).faceUp)
          else u.piles Q) = u.piles Q
        rw [if_neg hQa]
      have hshapeU : (u.piles Q).faceUp = bs ++ d :: run := by
        rw [← hpileQ]; exact hshape'
      have hseatU : bs ≠ [] ∨ ((u.piles Q).hidden = [] ∧ d.rank = Rank.king) := by
        rcases hseat' with h | h
        · exact Or.inl h
        · refine Or.inr ⟨?_, h.2⟩
          rw [← hpileQ]
          exact h.1
      rcases hdisj' with hrun | hsome
      · have hS : CanRaiseS u d := (canRaiseS_iff huwf).mpr
          ⟨hnextU, Q, bs, run, hshapeU, hseatU, Or.inl hrun⟩
        exact hfloor d hS
      · obtain ⟨k, hk⟩ := option_some_of_ne_none hsome
        by_cases hka : k = a
        · -- `d.twin` topped the raised pile: it lies in the chop
          have htopk : (u'.piles k).top = some d.twin := (pileOfTop_top hk).2
          have hmemk : d.twin ∈ (u'.piles k).faceUp := Pile.mem_of_top htopk
          have hmemA : d.twin ∈ (u'.piles a).faceUp := by
            rwa [hka] at hmemk
          have hch : chop (u.piles a).faceUp ≠ [] :=
            hch_of_ne (by intro hnil; rw [hnil] at hmemA; exact List.not_mem_nil hmemA)
          have hfaceA : (u'.piles a).faceUp = chop (u.piles a).faceUp := by
            rw [hpa']
            exact afterRunRemoved_faceUp_ne hch
          have hdtwin : d.twin ∈ chop (u.piles a).faceUp := by
            rw [hfaceA] at hmemA
            exact hmemA
          have hlt : c.rank.toIdx < d.twin.rank.toIdx :=
            runOK_desc hok hdtwin (List.mem_singleton_self c)
          have hreq : d.twin.rank.toIdx = d.rank.toIdx := rfl
          omega
        · -- the twin's pile is untouched: transfer the flat witness to `u`
          have hpilek : u'.piles k = u.piles k := by
            rw [hs]
            show (if k = a then
              Pile.afterRunRemoved (u.piles a) (chop (u.piles a).faceUp)
              else u.piles k) = u.piles k
            rw [if_neg hka]
          have htopk : (u.piles k).top = some d.twin := by
            rw [← hpilek]
            exact (pileOfTop_top hk).2
          have hsomeU : u.pileOfTop d.twin ≠ none := by
            rw [show u.pileOfTop d.twin = some k from (pileOfTop_eq_some_iff huwf).mpr htopk]
            exact Option.some_ne_none k
          have hS : CanRaiseS u d := (canRaiseS_iff huwf).mpr
            ⟨hnextU, Q, bs, run, hshapeU, hseatU, Or.inr hsomeU⟩
          exact hfloor d hS

/-! ## §D. The slide endpoint carries the invariant -/

/-- A floor-protected card is never in the `bs` below the blocked live `c`. -/
theorem not_mem_bs_of_floor {u : State} {x c : Card} (huwf : u.WF)
    (hfloor : ∀ d, CanRaiseS u d → x.rank.toIdx ≤ d.rank.toIdx)
    (hcS : CanRaiseS u c) {a : Anchor} {bs rest : List Card} {u1 : Card}
    (hshape : (u.piles a).faceUp = bs ++ c :: u1 :: rest) :
    x ∉ bs := by
  intro hmem
  have hok : runOK (bs ++ c :: u1 :: rest) = true := by
    rw [← hshape]; exact huwf.2.1 a
  have hlt : c.rank.toIdx < x.rank.toIdx :=
    runOK_desc hok hmem (List.mem_cons_self ..)
  have hge : x.rank.toIdx ≤ c.rank.toIdx := hfloor c hcS
  omega

/-- `c.twin ≠ x` from `c ≠ x.twin`. -/
theorem twin_ne_of_ne {c x : Card} (h : c ≠ x.twin) : c.twin ≠ x := by
  intro h2
  have h3 : c.twin.twin = x.twin := congrArg Card.twin h2
  rw [card_twin_twin] at h3
  exact h h3

/-- **The twin stays blocked across the slide.**  Either it rides inside the
moved run (then `twin_run_keeps_cover` keeps a card above it on the target
pile), or its pile is untouched, in which case any raise certificate at the
endpoint would already be one at the origin. -/
theorem not_canRaise_slide_twin {u z : State} {x c : Card} {u1 : Card}
    {a k : Anchor} {bs rest : List Card}
    (huwf : u.WF) (hT : CanRaiseS u x.twin) (hcS : CanRaiseS u c)
    (hct : c ≠ x.twin) (hcx : c ≠ x)
    (hblock : ¬ CanRaise u x.twin)
    (hfloor : ∀ d, CanRaiseS u d → x.rank.toIdx ≤ d.rank.toIdx)
    (hshape : (u.piles a).faceUp = bs ++ c :: u1 :: rest)
    (htwinTop : u.pileOfTop c.twin = some k)
    (hstep : u.step (Move.tabToTab u1 (Sum.inr c.twin)) = some z) :
    ¬ CanRaise z x.twin := by
  have hwfz : z.WF := step_wf huwf hstep
  obtain ⟨hpa, hpk, hother, hfnd⟩ := slide_frame huwf hshape htwinTop hstep
  have hnextT : u.nextUp x.twin = true := Drain.nextUp_of_canRaiseS hT
  by_cases hmem_run : x.twin ∈ u1 :: rest
  · -- the twin rides in the moved run: it keeps a card above it
    obtain ⟨⟨pre, post, hrun, hpostne⟩, -⟩ :=
      OneSlide.twin_run_keeps_cover huwf hct hnextT hblock hshape hmem_run
    intro hcan
    obtain ⟨-, e, hpe, -⟩ := hcan
    have htop_e : lastOf (z.piles e).faceUp = some x.twin :=
      (pileOfTop_top hpe).2
    have hmem_e : x.twin ∈ (z.piles e).faceUp := lastOf_mem htop_e
    have hmem_k : x.twin ∈ (z.piles k).faceUp := by
      rw [hpk]
      exact List.mem_append.mpr (Or.inr hmem_run)
    have hek : e = k := by
      by_cases h : e = k
      · exact h
      · exfalso
        exact (mem_faceUp_unique hwfz hmem_e k (Ne.symm h)).1 hmem_k
    rw [hek] at htop_e
    have hlast : lastOf (z.piles k).faceUp = some x.twin := htop_e
    rw [hpk] at hlast
    rw [hrun] at hlast
    rw [tfc_lastOf_append_ne (u.piles k).faceUp (by simp)] at hlast
    rw [tfc_lastOf_append_ne pre (List.cons_ne_nil x.twin post)] at hlast
    cases post with
    | nil => exact absurd rfl hpostne
    | cons p ps =>
        rw [show lastOf (x.twin :: p :: ps) = lastOf (p :: ps) from rfl] at hlast
        have hmem_post : x.twin ∈ p :: ps := lastOf_mem hlast
        have hok : runOK (bs ++ c :: u1 :: rest) = true := by
          rw [← hshape]; exact huwf.2.1 a
        have hshape' : (u.piles a).faceUp = bs ++ c :: (pre ++ x.twin :: p :: ps) := by
          rw [← hrun]; exact hshape
        have hsplit : bs ++ c :: (pre ++ x.twin :: p :: ps)
            = ((bs ++ [c]) ++ pre ++ [x.twin]) ++ (p :: ps) := by
          simp only [List.append_assoc, List.cons_append, List.nil_append]
        have hmem_left : x.twin ∈ ((bs ++ [c]) ++ pre ++ [x.twin]) :=
          List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
        have hok' : runOK (((bs ++ [c]) ++ pre ++ [x.twin]) ++ (p :: ps)) = true := by
          rw [← hsplit, ← hshape']
          exact huwf.2.1 a
        have hlt := runOK_desc hok' hmem_left hmem_post
        omega
  · -- the twin's pile is untouched by the slide
    obtain ⟨p, hholdp⟩ := Drain.pileHolding_of_canRaiseS huwf hT
    have hmem_p : x.twin ∈ (u.piles p).faceUp := pileHolding_mem hholdp
    have hp_ne_a : p ≠ a := by
      intro hpa'
      have hmemA : x.twin ∈ (u.piles a).faceUp := by
        rw [← hpa']; exact hmem_p
      rw [hshape] at hmemA
      rcases List.mem_append.mp hmemA with hbs | hrest
      · exact OneSlide.no_twin_below_c huwf hfloor hcS hshape hbs
      · rcases List.mem_cons.mp hrest with heq | hrun
        · exact hct heq.symm
        · exact hmem_run hrun
    have hp_ne_k : p ≠ k := by
      intro hpk'
      have hmemK : x.twin ∈ (u.piles k).faceUp := by
        rw [← hpk']; exact hmem_p
      have hxne : x.twin ≠ c.twin := by
        intro h
        have h2 : x = c := by
          have h3 : x.twin.twin = c.twin.twin := congrArg Card.twin h
          rwa [card_twin_twin, card_twin_twin] at h3
        exact hcx h2.symm
      have htopk : lastOf (u.piles k).faceUp = some c.twin :=
        (pileOfTop_top htwinTop).2
      have hfacek : (u.piles k).faceUp = chop (u.piles k).faceUp ++ [c.twin] :=
        lastOf_chop htopk
      have hmemChop : x.twin ∈ chop (u.piles k).faceUp := by
        rw [hfacek] at hmemK
        rcases List.mem_append.mp hmemK with h | h
        · exact h
        · exact absurd (List.mem_singleton.mp h) hxne
      have hokK : runOK (chop (u.piles k).faceUp ++ [c.twin]) = true := by
        rw [← hfacek]; exact huwf.2.1 k
      have hlt : c.twin.rank.toIdx < x.twin.rank.toIdx :=
        runOK_desc hokK hmemChop (List.mem_singleton_self c.twin)
      have hge : x.rank.toIdx ≤ c.rank.toIdx := hfloor c hcS
      have hcr : c.twin.rank.toIdx = c.rank.toIdx := rfl
      have hrt : x.twin.rank.toIdx = x.rank.toIdx := rfl
      omega
    have hpilep : z.piles p = u.piles p := hother p hp_ne_a hp_ne_k
    intro hcan
    have hnextz : z.nextUp x.twin = true := hcan.1
    obtain ⟨-, e, hpe, hseate⟩ := hcan
    have hmem_pz : x.twin ∈ (z.piles p).faceUp := by
      rw [hpilep]; exact hmem_p
    have hmem_e : x.twin ∈ (z.piles e).faceUp :=
      lastOf_mem (pileOfTop_top hpe).2
    have hep : e = p := by
      by_cases h : e = p
      · exact h
      · exfalso
        exact (mem_faceUp_unique hwfz hmem_e p (Ne.symm h)).1 hmem_pz
    rw [hep] at hpe hseate
    have htopu : (u.piles p).top = some x.twin := by
      have h := (pileOfTop_top hpe).2
      rw [hpilep] at h
      exact h
    have hpod_u : u.pileOfTop x.twin = some p :=
      (pileOfTop_eq_some_iff huwf).mpr htopu
    have hnextu : u.nextUp x.twin = true := by
      unfold State.nextUp at hnextz ⊢
      unfold State.foundHeight at hnextz ⊢
      rw [← hfnd]
      exact hnextz
    have hseat_u : chop (u.piles p).faceUp ≠ [] ∨
        ((u.piles p).hidden = [] ∧ x.twin.rank = Rank.king) := by
      rcases hseate with h | h
      · exact Or.inl (by rw [← hpilep]; exact h)
      · exact Or.inr ⟨by rw [← hpilep]; exact h.1, h.2⟩
    exact hblock ⟨hnextu, p, hpod_u, hseat_u⟩

/-! ## §E. `x` stays raisable across the slide -/

/-- **`x` stays raisable across the slide.**  Either `x` rides in the moved
run — then it is that run's last card and tops the target pile with company
beneath — or its pile is untouched, in which case the certificate is
literally the same. -/
theorem canRaise_slide_x {u z : State} {x c : Card} {u1 : Card}
    {a k : Anchor} {bs rest : List Card}
    (huwf : u.WF) (hx : CanRaise u x) (hcS : CanRaiseS u c)
    (hcx : c ≠ x) (hct : c ≠ x.twin)
    (hfloor : ∀ d, CanRaiseS u d → x.rank.toIdx ≤ d.rank.toIdx)
    (hshape : (u.piles a).faceUp = bs ++ c :: u1 :: rest)
    (htwinTop : u.pileOfTop c.twin = some k)
    (hstep : u.step (Move.tabToTab u1 (Sum.inr c.twin)) = some z) :
    CanRaise z x := by
  have hwfz : z.WF := step_wf huwf hstep
  obtain ⟨hpa, hpk, hother, hfnd⟩ := slide_frame huwf hshape htwinTop hstep
  obtain ⟨hnextx, q, hpq, hseatq⟩ := hx
  have hnextz : z.nextUp x = true := by
    unfold State.nextUp at hnextx ⊢
    unfold State.foundHeight at hnextx ⊢
    rw [hfnd]
    exact hnextx
  by_cases hmem_run : x ∈ u1 :: rest
  · -- `x` rides in the run and is its last card
    have hxmem_a : x ∈ (u.piles a).faceUp := by
      rw [hshape]
      exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem c hmem_run))
    have hqa : q = a := by
      by_cases h : q = a
      · exact h
      · exfalso
        have hmemq : x ∈ (u.piles q).faceUp := Pile.mem_of_top (pileOfTop_top hpq).2
        exact (mem_faceUp_unique huwf hxmem_a q h).1 hmemq
    have hlastrun : lastOf (u1 :: rest) = some x := by
      have htopa : lastOf (u.piles a).faceUp = some x := by
        rw [← hqa]
        exact (pileOfTop_top hpq).2
      rw [hshape] at htopa
      rw [tfc_lastOf_append_ne bs (by simp)] at htopa
      exact htopa
    have htopk : (z.piles k).top = some x := by
      rw [hpk]
      show lastOf ((u.piles k).faceUp ++ (u1 :: rest)) = some x
      rw [tfc_lastOf_append_ne (u.piles k).faceUp (by simp)]
      exact hlastrun
    have hpodz : z.pileOfTop x = some k := (pileOfTop_eq_some_iff hwfz).2 htopk
    have hchop : chop (z.piles k).faceUp ≠ [] := by
      apply OneSlide.chop_ne_nil_of_two_le
      have hzK : (z.piles k).faceUp = (u.piles k).faceUp ++ (u1 :: rest) := by
        rw [hpk]
      rw [hzK]
      have hmemct : c.twin ∈ (u.piles k).faceUp :=
        lastOf_mem (pileOfTop_top htwinTop).2
      have hlen : 0 < (u.piles k).faceUp.length := List.length_pos_of_mem hmemct
      simp only [List.length_append, List.length_cons]
      omega
    exact ⟨hnextz, k, hpodz, Or.inl hchop⟩
  · -- `x`'s pile is untouched
    have hxnotbs : x ∉ bs := not_mem_bs_of_floor huwf hfloor hcS hshape
    have hxnota : x ∉ (u.piles a).faceUp := by
      rw [hshape]
      intro hmem
      rcases List.mem_append.mp hmem with h | h
      · exact hxnotbs h
      · rcases List.mem_cons.mp h with heq | hrun
        · exact hcx heq.symm
        · exact hmem_run hrun
    have hqnea : q ≠ a := by
      intro hqa
      exact hxnota (by rw [← hqa]; exact Pile.mem_of_top (pileOfTop_top hpq).2)
    have hqnek : q ≠ k := by
      intro hqk
      have hmemk : x ∈ (u.piles k).faceUp := by
        rw [← hqk]; exact Pile.mem_of_top (pileOfTop_top hpq).2
      have hxne : x ≠ c.twin := by
        intro h
        have h2 : x.twin = c := by
          have h3 : x.twin = c.twin.twin := by rw [h]
          rwa [card_twin_twin] at h3
        exact hct h2.symm
      have htopk : lastOf (u.piles k).faceUp = some c.twin :=
        (pileOfTop_top htwinTop).2
      have hfacek : (u.piles k).faceUp = chop (u.piles k).faceUp ++ [c.twin] :=
        lastOf_chop htopk
      have hmemchop : x ∈ chop (u.piles k).faceUp := by
        rw [hfacek] at hmemk
        rcases List.mem_append.mp hmemk with h | h
        · exact h
        · exact absurd (List.mem_singleton.mp h) hxne
      have hokK : runOK (chop (u.piles k).faceUp ++ [c.twin]) = true := by
        rw [← hfacek]; exact huwf.2.1 k
      have hlt : c.twin.rank.toIdx < x.rank.toIdx :=
        runOK_desc hokK hmemchop (List.mem_singleton_self c.twin)
      have hge : x.rank.toIdx ≤ c.rank.toIdx := hfloor c hcS
      have hcr : c.twin.rank.toIdx = c.rank.toIdx := rfl
      omega
    have hpileq : z.piles q = u.piles q := hother q hqnea hqnek
    have htopq : (z.piles q).top = some x := by
      rw [hpileq]
      exact (pileOfTop_top hpq).2
    have hpodz : z.pileOfTop x = some q := (pileOfTop_eq_some_iff hwfz).2 htopq
    have hseatz : chop (z.piles q).faceUp ≠ [] ∨
        ((z.piles q).hidden = [] ∧ x.rank = Rank.king) := by
      rcases hseatq with h | h
      · exact Or.inl (by rw [hpileq]; exact h)
      · exact Or.inr ⟨by rw [hpileq]; exact h.1, h.2⟩
    exact ⟨hnextz, q, hpodz, hseatz⟩

/-! ## §F. The invariant at the slide endpoint -/

/-- **The slide endpoint carries the whole invariant.** -/
theorem invariant_after_slide {u z : State} {x c : Card}
    (huwf : u.WF) (hinv : Drain.DrainInvariant u x)
    (hcS : CanRaiseS u c) (hcx : c ≠ x) (hct : c ≠ x.twin)
    {u1 : Card} {a k : Anchor} {bs rest : List Card}
    (hshape : (u.piles a).faceUp = bs ++ c :: u1 :: rest)
    (htwinTop : u.pileOfTop c.twin = some k)
    (hstep : u.step (Move.tabToTab u1 (Sum.inr c.twin)) = some z)
    (hrev : reversibleAtW u (Move.tabToTab u1 (Sum.inr c.twin))) :
    Drain.DrainInvariant z x := by
  have hleg : CargoLeg u z := ⟨u1, Sum.inr c.twin, hstep, hrev⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact canRaise_slide_x huwf hinv.1 hcS hcx hct hinv.2.2.2
      hshape htwinTop hstep
  · exact canRaiseS_of_cargoLeg (u := z) (v := u) (d := x.twin)
      (cargoLeg_symm huwf hleg) hinv.2.1
  · exact not_canRaise_slide_twin huwf hinv.2.1 hcS hct hcx hinv.2.2.1
      hinv.2.2.2 hshape htwinTop hstep
  · exact floor_slide hleg hinv.2.2.2

/-! ## §G. The two drain letters -/

/-- A vanilla raise fires. -/
theorem step_tabToFound_fires {u : State} {c : Card} (h : CanRaise u c) :
    ∃ u', u.step (Move.tabToFound c) = some u' := by
  obtain ⟨hnext, a, hpa, -⟩ := h
  refine ⟨{ u.setFound c.suit (u.found c.suit ++ [c]) with
      piles := fun a' => if a' = a then
        Pile.afterRunRemoved (u.piles a) (chop (u.piles a).faceUp)
        else u.piles a' }, ?_⟩
  simp [State.step, hnext, hpa]

/-- **The vanilla drain letter.**  A raisable live card outside the pair is
raised directly; the invariant survives and the rank sum climbs by one. -/
theorem drain_step_raisable {u : State} {x c : Card}
    (huwf : u.WF) (hinv : Drain.DrainInvariant u x)
    (hc : CanRaise u c) (hcx : c ≠ x) (hct : c ≠ x.twin) :
    ∃ u', u'.WF ∧ sameOrbitSetoid.r u u' ∧ Drain.DrainInvariant u' x ∧
      Drain.rungSum u' = Drain.rungSum u + 1 := by
  obtain ⟨u', hstep⟩ := step_tabToFound_fires hc
  have hrank : x.rank.toIdx ≤ c.rank.toIdx :=
    hinv.2.2.2 c (CanRaiseS.now c hc)
  have hsu : x.suit ≠ c.suit :=
    Drain.suit_ne_of_nextUp hinv.1.1 hc.1 (Ne.symm hcx)
  obtain ⟨b, hholdx⟩ : ∃ b, u.pileHolding x = some b := by
    obtain ⟨-, a, hpa, -⟩ := hinv.1
    exact ⟨a, Drain.pileHolding_of_pileOfTop huwf hpa⟩
  have hCan' : CanRaise u' x :=
    Drain.canRaise_of_raise_high_fwd huwf hstep hsu (Ne.symm hcx) hrank hholdx hinv.1
  have hpair := OneSlide.CanRaiseS_preserved_proved huwf hinv.2.1 hinv.2.2.1
    hc hcx hct hinv.2.2.2 hstep
  have hfloor' := floor_raise huwf hc hrank hstep hinv.2.2.2
  have hrev : reversibleAtW u (Move.tabToFound c) :=
    reversibleAtW_tabToFound_of_canRaise huwf hc
  exact ⟨u', step_wf huwf hstep, Drain.sameOrbit_of_step hrev hstep,
    ⟨hCan', hpair.1, hpair.2, hfloor'⟩, rungSum_raise hstep⟩

/-- **The blocked drain letter.**  Slide the blocked live card's cover onto
its twin's pile (R1/R2), then raise it.  The invariant survives and the rank
sum climbs by one. -/
theorem drain_step_blocked {u : State} {x c : Card}
    (huwf : u.WF) (hinv : Drain.DrainInvariant u x)
    (hcS : CanRaiseS u c) (hcB : ¬ CanRaise u c)
    (hcx : c ≠ x) (hct : c ≠ x.twin) :
    ∃ u', u'.WF ∧ sameOrbitSetoid.r u u' ∧ Drain.DrainInvariant u' x ∧
      Drain.rungSum u' = Drain.rungSum u + 1 := by
  obtain ⟨hnext, a, bs, run, hshape, hseat, hdisj⟩ :=
    canRaiseS_flat_necessity huwf hcS
  have hrun : run ≠ [] := OneSlide.run_ne_nil huwf hnext hcB hshape hseat
  obtain ⟨k, htwinTop⟩ := OneSlide.twin_top_of_cover hrun hdisj
  cases run with
  | nil => exact absurd rfl hrun
  | cons u1 rest =>
      obtain ⟨z, hstep, hrev, hraise⟩ :=
        OneSlide.cover_slide_exists huwf hnext hshape hseat htwinTop
      have hwfz : z.WF := step_wf huwf hstep
      have hzInv : Drain.DrainInvariant z x :=
        invariant_after_slide huwf hinv hcS hcx hct hshape htwinTop hstep hrev
      obtain ⟨u', hstepr⟩ := step_tabToFound_fires hraise
      have hrank : x.rank.toIdx ≤ c.rank.toIdx := hzInv.2.2.2 c (CanRaiseS.now c hraise)
      have hpair := OneSlide.CanRaiseS_preserved_proved hwfz hzInv.2.1
        hzInv.2.2.1 hraise hcx hct hzInv.2.2.2 hstepr
      obtain ⟨b, hholdx⟩ : ∃ b, z.pileHolding x = some b := by
        obtain ⟨-, q, hpq, -⟩ := hzInv.1
        exact ⟨q, Drain.pileHolding_of_pileOfTop hwfz hpq⟩
      have hsu : x.suit ≠ c.suit :=
        Drain.suit_ne_of_nextUp hzInv.1.1 hraise.1 (Ne.symm hcx)
      have hCan' : CanRaise u' x :=
        Drain.canRaise_of_raise_high_fwd hwfz hstepr hsu (Ne.symm hcx) hrank
          hholdx hzInv.1
      have hfloor' := floor_raise hwfz hraise hrank hstepr hzInv.2.2.2
      have hrevr : reversibleAtW z (Move.tabToFound c) :=
        reversibleAtW_tabToFound_of_canRaise hwfz hraise
      refine ⟨u', step_wf hwfz hstepr, ?_,
        ⟨hCan', hpair.1, hpair.2, hfloor'⟩, ?_⟩
      · exact sameOrbitSetoid.iseqv.trans
          (Drain.sameOrbit_of_step hrev hstep)
          (Drain.sameOrbit_of_step hrevr hstepr)
      · rw [rungSum_raise hstepr, rungSum_slide hstep]

/-! ## §H. The unconditional drain-to-fork theorem -/

/-- **FORK EXISTENCE FROM THE TWIN ASYMMETRY.**  If `x` is vanilla-raisable,
`x.twin` is S-live but vanilla-blocked, and no S-live card sits below
`x`'s rank, then a fork exists in the `sameOrbitSetoid` class of `st`.

Termination measure: `52 - rungSum`.  Each drain letter (a vanilla raise, or
the cover slide followed by a raise) raises `rungSum` by exactly one (slides
leave the foundations alone, raises climb by one), and `rungSum ≤ 52` at
`WF`.  The terminal case is `drain_terminal_fork`. -/
theorem fork_exists_of_asymmetry {st : State} {x : Card}
    (hwf : st.WF)
    (hcan : CanRaise st x) (hlive : CanRaiseS st x.twin)
    (hblock : ¬ CanRaise st x.twin)
    (hfloor : ∀ c, CanRaiseS st c → x.rank.toIdx ≤ c.rank.toIdx) :
    ∃ F, sameOrbitSetoid.r st F ∧ forkState F := by
  have key : ∀ n, ∀ u, u.WF → Drain.DrainInvariant u x →
      52 - Drain.rungSum u = n → ∃ F, sameOrbitSetoid.r u F ∧ forkState F := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro u huwf hu hmeas
      cases hb : Drain.drainLiveB u x with
      | true =>
          have hterm : Drain.DrainTerminal u x :=
            ⟨hu, (Drain.drainLiveB_iff huwf x).mp hb⟩
          exact ⟨u, sameOrbitSetoid.iseqv.refl u,
            Drain.forkState_of_forkWitness (Drain.drain_terminal_fork hterm)⟩
      | false =>
          have hall : (Card.universe.all (fun c =>
              !(canRaiseSB u c) || decide (c = x) || decide (c = x.twin))) = false := hb
          obtain ⟨c, -, hcfalse⟩ := Drain.exists_of_all_false hall
          rw [Bool.or_eq_false_iff, Bool.or_eq_false_iff] at hcfalse
          obtain ⟨⟨hnot, hdeq⟩, hteq⟩ := hcfalse
          have hprobe : canRaiseSB u c = true := by
            cases hpc : canRaiseSB u c with
            | true => rfl
            | false => rw [hpc] at hnot; simp at hnot
          have hcx : c ≠ x := of_decide_eq_false hdeq
          have hct : c ≠ x.twin := of_decide_eq_false hteq
          have hSc : CanRaiseS u c := (canRaiseSB_iff huwf).mp hprobe
          obtain ⟨u', hu'wf, hrel, hu', hsum⟩ :
              ∃ u', u'.WF ∧ sameOrbitSetoid.r u u' ∧
                Drain.DrainInvariant u' x ∧
                Drain.rungSum u' = Drain.rungSum u + 1 := by
            by_cases hR : tabToFoundR u c = true
            · exact drain_step_raisable huwf hu
                (SatDifferCensus.canRaise_of_tabToFoundR hR) hcx hct
            · exact drain_step_blocked huwf hu hSc
                (fun hcon => hR (tabToFoundR_of_canRaise hcon)) hcx hct
          have hbound : Drain.rungSum u + 1 ≤ 52 := by
            have h52 := Drain.rungSum_le_52 hu'wf
            rwa [hsum] at h52
          have hlt : 52 - Drain.rungSum u' < n := by
            rw [hsum, ← hmeas]
            omega
          obtain ⟨F, hrF, hfork⟩ :=
            ih (52 - Drain.rungSum u') hlt u' hu'wf hu' rfl
          exact ⟨F, sameOrbitSetoid.iseqv.trans hrel hrF, hfork⟩
  exact key (52 - Drain.rungSum st) st hwf ⟨hcan, hlive, hblock, hfloor⟩ rfl

/-! ## §I. Closed forms: the frame rows and the `drain_to_fork` corollary -/

/-- **R1, top row.**  The source pile's new top is the covered card `c`. -/
theorem slide_frame_top {st z : State} {c u1 : Card} {rest bs : List Card}
    {a k : Anchor} (hwf : st.WF)
    (hshape : (st.piles a).faceUp = bs ++ c :: u1 :: rest)
    (htwinTop : st.pileOfTop c.twin = some k)
    (hstep : st.step (Move.tabToTab u1 (Sum.inr c.twin)) = some z) :
    (z.piles a).top = some c := by
  obtain ⟨hpa, -⟩ := slide_frame hwf hshape htwinTop hstep
  rw [hpa]
  exact lastOf_snoc

/-- **`drain_step_other_live`, CLOSED.**  The two-letter drain of a blocked
live card outside the protected pair preserves the whole invariant at the
raised endpoint (no frame or floor hypotheses left open). -/
theorem drain_step_other_live_closed {u : State} {x c : Card}
    (huwf : u.WF) (hinv : Drain.DrainInvariant u x)
    (hcS : CanRaiseS u c) (hcB : ¬ CanRaise u c)
    (hcx : c ≠ x) (hct : c ≠ x.twin) :
    ∃ u', sameOrbitSetoid.r u u' ∧
      CanRaiseS u' x.twin ∧ ¬ CanRaise u' x.twin ∧ CanRaise u' x ∧
      (∀ d, CanRaiseS u' d → x.rank.toIdx ≤ d.rank.toIdx) ∧
      Drain.rungSum u' = Drain.rungSum u + 1 := by
  obtain ⟨u', -, hrel, ⟨h1, h2, h3, h4⟩, hsum⟩ :=
    drain_step_blocked huwf hinv hcS hcB hcx hct
  exact ⟨u', hrel, h2, h3, h1, h4, hsum⟩

/-- **`drain_to_fork` with `hstep` discharged.**  The mission's
`Drain.drain_to_fork` conclusion, with the step provider supplied by the two
drain letters and the termination measure `52 - rungSum`.  `WF` is carried
along the induction (each letter is a `State.step`). -/
theorem drain_to_fork_discharged {st : State} {x : Card}
    (hwf : st.WF) (h : Drain.DrainInvariant st x) :
    ∃ F, sameOrbitSetoid.r st F ∧ forkState F := by
  obtain ⟨hcan, hlive, hblock, hfloor⟩ := h
  exact fork_exists_of_asymmetry hwf hcan hlive hblock hfloor

end DrainClose

#print axioms DrainClose.slide_frame_top
#print axioms DrainClose.drain_step_other_live_closed
#print axioms DrainClose.drain_to_fork_discharged

/-! ## Battery -/

#print axioms OneSlide.one_slide_of_blocked_live
#print axioms DrainClose.slide_frame
#print axioms DrainClose.slide_frame_top
#print axioms DrainClose.floor_slide
#print axioms DrainClose.floor_raise
#print axioms DrainClose.not_canRaise_slide_twin
#print axioms DrainClose.canRaise_slide_x
#print axioms DrainClose.invariant_after_slide
#print axioms DrainClose.drain_step_raisable
#print axioms DrainClose.drain_step_blocked
#print axioms DrainClose.drain_step_other_live_closed
#print axioms DrainClose.drain_to_fork_discharged
#print axioms DrainClose.fork_exists_of_asymmetry

#check @DrainClose.fork_exists_of_asymmetry
#check @DrainClose.drain_to_fork_discharged
#check @DrainClose.floor_raise
#check @DrainClose.slide_frame
