import Orig.ForkWeaker

/-!
# Orig.SFlatTransfer — the one-leg census transfer and the S-mate production

THE BRIEF (the flat-transfer card): at a maneuver-stable `forkState` whose
witness pair `{x, x.twin}` carries the trial shape — the twin `x.twin`
covered DIRECTLY by a fitting cargo `d` topping its pile `q` — the
one reversible cargo leg `tabToTab d (inr x)` (the vanilla
`forkState_slide_mate` move, the same slide, same parameter shape)
produces the MATE forkState with the witness FLIPPED, CargoPath
connected.  The load-bearing new content is the ONE-LEG CENSUS
TRANSFER (`S_census_one_leg`): after one cargo leg, every non-pair card
that was S-dead at the source stays S-dead at the successor — the
RunOrTwin freeze machinery extended from "both family cards un-topped"
to the full flat census.

THE CENSUS ROUTE (the → direction at the successor): a `CanRaiseS s' c`
at the leg's end unfolds through the landed flat characterization
(`canRaiseS_iff`) into nextUp, a pile position, a seat package, and the
run-or-twin read.  All four project BACKWARD through the one leg: the
founds never move (`slide_foundEq`), the seat's below-prefix and hidden
deck are leg-invariants on the touched piles (`below_snoc_of_mem`:
below reads stop at the first c, so a snoc after the whole list cannot
move them), and the twin-topping read transfers by the located-pile
census (`census_twin_top_st`: a twin topping the landing pile at s' IS
the landed cargo `d`, which topped its SOURCE pile at st; a twin
topping the source pile at s' is the exposed `x.twin`, forcing `c = x`;
any other pile is untouched).  The reassembled flat data fires
`canRaiseS_iff` BACKWARD at `st`, and the source S-iff kills `c`.

House compliance: additive leaf (`import Orig.ForkWeaker` only); the
in-tree interface consumed by name; zero sorry; audit battery below.
-/

/-! ## §0. The private kit (per-file copies, the house dedup discipline) -/

private theorem lastOf_cons_tail {w : Card} {L : List Card} (h : L ≠ []) :
    lastOf (w :: L) = lastOf L := by
  cases L with
  | nil => exact absurd rfl h
  | cons y t => rfl

private theorem lastOf_append_tail {t : List Card} (ht : t ≠ []) :
    ∀ (bs : List Card), lastOf (bs ++ t) = lastOf t := by
  intro bs
  induction bs with
  | nil => rfl
  | cons w ws ih =>
      have hne : ws ++ t ≠ [] := by
        intro hcon
        apply ht
        cases ws with
        | nil => rw [List.nil_append] at hcon; exact hcon
        | cons v vs => exact absurd hcon (by simp)
      rw [List.cons_append, lastOf_cons_tail hne, ih]

private theorem nodup_snoc_notmem :
    ∀ (bs : List Card) (d : Card) (_hnd : (bs ++ [d]).Nodup), d ∉ bs
  | [], _, _ => by
      intro hcon
      simp at hcon
  | b :: t, d, hnd => by
      intro hcon
      rcases List.mem_cons.mp hcon with hdb | hcon'
      · have hbmem : b ∈ t ++ [d] :=
          List.mem_append.mpr (Or.inr (List.mem_singleton.mpr hdb.symm))
        exact absurd hbmem ((List.nodup_cons.mp hnd).1)
      · exact nodup_snoc_notmem t d (List.nodup_cons.mp hnd).2 hcon'

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
      · exact ih rest (List.nodup_cons.mp hnd).2 hin

/-- A nodup list cannot host its cut card again inside the after-part. -/
private theorem nodup_dup_mem (y : Card) :
    ∀ (X R : List Card), (X ++ y :: R).Nodup → y ∈ R → False := by
  intro X
  induction X with
  | nil => intro R hnd hmem; exact (List.nodup_cons.mp hnd).1 hmem
  | cons v vs ih =>
      intro R hnd hmem
      exact ih R (List.nodup_cons.mp hnd).2 hmem

/-- Below reads stop at the first `c`, so a snoc past the whole list
cannot move them — the leg's below-prefix invariance. -/
private theorem below_snoc_of_mem (c : Card) :
    ∀ (L : List Card) (w : Card), c ∈ L → below c (L ++ [w]) = below c L := by
  intro L w
  induction L with
  | nil => intro hmem; cases hmem
  | cons y ys ih =>
      intro hmem
      by_cases hyc : y = c
      · rw [hyc, List.cons_append, below_cons_self, below_cons_self]
      · have hcys : c ∈ ys :=
          (List.mem_cons.mp hmem).resolve_left (fun hu => hyc hu.symm)
        rw [List.cons_append, below_cons_ne _ hyc, below_cons_ne _ hyc, ih hcys]

/-- A `tabToTab` never writes any foundation (the copy of the in-tree
private row; `putRun_found`, `setPile_found` are public). -/
private theorem slide_foundEq {st st' : State} {c : Card} {b : Base}
    (hstep : State.step st (Move.tabToTab c b) = some st') :
    ∀ σ, st'.found σ = st.found σ := by
  obtain ⟨a, _, _, _, hs⟩ := step_tabToTab_inv hstep
  intro σ
  rw [hs, putRun_found, setPile_found]

/-- The rung pin's nextUp read (the copy of the bridge chapter's row). -/
private theorem nextUp_of_rung {st : State} {c : Card}
    (hr : rungAt st c.suit = c.rank.toIdx) : st.nextUp c = true := by
  show decide (c.rank.toIdx = (st.found c.suit).length) = true
  exact decide_eq_true hr.symm

/-- A twin is never its own card (the copy of the in-tree private row). -/
private theorem card_twin_ne (c : Card) : c.twin ≠ c := by
  intro hcon
  exact Suit.twin_ne c.suit (congrArg Card.suit hcon)

/-! ## §1. The one-leg census transfer -/

/-- **THE LOCATED TWIN CENSUS** — a twin topping SOME pile at the leg's
end tops a pile at the source too: the landing pile's top at s' is the
landed cargo `d`, which topped its source pile `q` at `st`; the source
pile's top at s' is the exposed `x.twin`, which would force `c = x`; a
third pile is untouched. -/
private theorem census_twin_top_st {st s' : State} {c d x : Card}
    {p q b : Anchor}
    (hwf : st.WF)
    (hbtop : (s'.piles b).top = some c.twin)
    (hs'Ptop : (s'.piles p).top = some d)
    (hs'QT : (s'.piles q).top = some x.twin)
    (hdTopSt : st.pileOfTop d = some q)
    (hrest : ∀ y, y ≠ p → y ≠ q → s'.piles y = st.piles y)
    (hcx : c ≠ x) :
    st.pileOfTop c.twin ≠ none := by
  rcases Decidable.em (b = p) with rfl | hbp
  · -- the landing pile's s'-top is the landed cargo: it topped q at st
    have hctd : c.twin = d := Option.some.inj (hbtop.symm.trans hs'Ptop)
    intro hcon
    rw [hctd, hdTopSt] at hcon
    exact absurd hcon (by simp)
  · rcases Decidable.em (b = q) with rfl | hbq
    · -- the source pile's s'-top is the exposed twin: c IS the witness
      have hctx2 : c.twin = x.twin := Option.some.inj (hbtop.symm.trans hs'QT)
      have h2 : c.twin.twin = x.twin.twin := congrArg Card.twin hctx2
      rw [Card.twin_twin, Card.twin_twin] at h2
      exact absurd h2 hcx
    · -- any third pile is untouched
      intro hcon
      rw [(pileOfTop_eq_some_iff hwf).2
        (by rw [← hrest b hbp hbq]; exact hbtop)] at hcon
      exact absurd hcon (by simp)

/-- **THE ONE-LEG CENSUS TRANSFER** — the standalone transfer lemma the
mate row consumes (and `forkState_unique`'s G1 gate can cite): under the
one reversible cargo leg `tabToTab d (inr x)` (the slid-mate trial, the
vanilla `forkState_slide_mate` move), every card outside the pair that
was S-dead at the source is still S-dead at the successor.  The leg's
geometry is spelled as the package the step provides: the landing pile
`p` gains `[d]` on top of the witness's old pile, the source pile `q`
is the successor's q-pile plus `[d]`, every other pile is untouched,
and the founds never move. -/
theorem S_census_one_leg {st s' : State} {x d : Card} {p q : Anchor}
    (hwf : st.WF) (hwfs' : s'.WF)
    (hffound : ∀ σ, s'.found σ = st.found σ)
    (hs'QT : (s'.piles q).top = some x.twin)
    (hLp : s'.piles p = ⟨(st.piles p).hidden, (st.piles p).faceUp ++ [d]⟩)
    (hLq : st.piles q = ⟨(s'.piles q).hidden, (s'.piles q).faceUp ++ [d]⟩)
    (hrest : ∀ y, y ≠ p → y ≠ q → s'.piles y = st.piles y)
    (hdx : d ≠ x) (hdtx : d ≠ x.twin)
    (hdead : ∀ c, ¬(c = x ∨ c = x.twin) → ¬ CanRaiseS st c) :
    ∀ c, ¬(c = x ∨ c = x.twin) → ¬ CanRaiseS s' c := by
  intro c hcp hS
  have hcx : c ≠ x := fun h => hcp (Or.inl h)
  have hctx : c ≠ x.twin := fun h => hcp (Or.inr h)
  -- the pinned geography, read off the package
  have hs'QTpod : s'.pileOfTop x.twin = some q :=
    (pileOfTop_eq_some_iff hwfs').2 hs'QT
  obtain ⟨hs'Qne, -⟩ := pileOfTop_top hs'QTpod
  have hqF : (st.piles q).faceUp = (s'.piles q).faceUp ++ [d] := by
    rw [hLq]
  have hqH : (st.piles q).hidden = (s'.piles q).hidden := by
    rw [hLq]
  have hpF : (s'.piles p).faceUp = (st.piles p).faceUp ++ [d] := by
    rw [hLp]
  have hpH : (st.piles p).hidden = (s'.piles p).hidden := by
    rw [hLp]
  have hs'Ptop : (s'.piles p).top = some d := by
    show lastOf ((s'.piles p).faceUp) = some d
    rw [hpF]
    exact lastOf_snoc
  have hchopq : chop ((st.piles q).faceUp) ≠ [] := by
    rw [hqF, chop_snoc]
    exact hs'Qne
  have hdTopSt : st.pileOfTop d = some q :=
    (pileOfTop_eq_some_iff hwf).2 (by
      show lastOf ((st.piles q).faceUp) = some d
      rw [hqF]
      exact lastOf_snoc)
  -- the flat read at the successor
  obtain ⟨hnext', a, bs', run, hshape', hseat', hdisj⟩ :=
    (canRaiseS_iff hwfs').1 hS
  have hnext : st.nextUp c = true := by
    show decide (c.rank.toIdx = (st.found c.suit).length) = true
    rw [← hffound c.suit]
    exact hnext'
  have hcmemS : c ∈ (s'.piles a).faceUp := by
    rw [hshape']
    exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
  cases hrunE : run with
  | nil =>
    -- c TOPS its pile at s'
    have htopS : (s'.piles a).top = some c := by
      show lastOf ((s'.piles a).faceUp) = some c
      rw [hshape', hrunE]
      exact lastOf_snoc
    rcases Decidable.em (q = a) with rfl | hqa
    · -- the exposed twin's own top slot
      exact hctx (Option.some.inj (htopS.symm.trans hs'QT))
    rcases Decidable.em (p = a) with rfl | hpa
    · -- c = d: the cargo's nextUp would have licensed it at st already
      have hcd : c = d := Option.some.inj (htopS.symm.trans hs'Ptop)
      have hnextd : st.nextUp d = true := by
        show decide (d.rank.toIdx = (st.found d.suit).length) = true
        rw [← hcd, ← hffound c.suit]
        exact hnext'
      exact hdead d (fun hor => hor.elim hdx hdtx)
        (CanRaiseS.now d ⟨hnextd, q, hdTopSt, Or.inl hchopq⟩)
    · -- untouched pile: the vanilla license is already live at st
      have hPa : s'.piles a = st.piles a :=
        hrest a (fun h => hpa h.symm) (fun h => hqa h.symm)
      refine hdead c hcp (CanRaiseS.now c ⟨hnext, a,
        (pileOfTop_eq_some_iff hwf).2 (by rw [← hPa]; exact htopS), ?_⟩)
      rw [← hPa]
      rcases hseat' with hbs' | ⟨hhid, hk⟩
      · refine Or.inl ?_
        rw [hshape', hrunE, chop_snoc]
        exact hbs'
      · exact Or.inr ⟨hhid, hk⟩
  | cons r₀ rst =>
    -- c covered at s', the twin contract read at the end
    have htwinne : s'.pileOfTop c.twin ≠ none := by
      rcases hdisj with habs | hne
      · rw [hrunE] at habs
        exact absurd habs (by simp)
      · exact hne
    obtain ⟨b, hbpod⟩ := option_some_of_ne_none htwinne
    have hbt : (s'.piles b).top = some c.twin := (pileOfTop_top hbpod).2
    -- the flat below read: bs' IS the below-prefix
    have hndF : (bs' ++ c :: r₀ :: rst).Nodup := by
      have h := runOK_nodup (hwfs'.runOK_of a)
      rw [hshape', hrunE] at h
      exact h
    have hcNbs : c ∉ bs' := nodup_mid_notmem c bs' (r₀ :: rst) hndF
    have hbelowF : below c ((s'.piles a).faceUp) = bs' := by
      rw [hshape', hrunE]
      exact below_append_stop hcNbs
    -- the twin's location projects back
    have htst : st.pileOfTop c.twin ≠ none :=
      census_twin_top_st hwf hbt hs'Ptop hs'QT hdTopSt hrest hcx
    rcases Decidable.em (q = a) with rfl | hqa
    · -- the source pile at st is the s'-pile snoc d; below/seat transfer
      have hcmemST : c ∈ (st.piles q).faceUp := by
        rw [hqF]
        exact List.mem_append.mpr (Or.inl hcmemS)
      have hbl : below c ((st.piles q).faceUp) = bs' := by
        rw [hqF, below_snoc_of_mem c ((s'.piles q).faceUp) d hcmemS]
        exact hbelowF
      refine hdead c hcp ((canRaiseS_iff hwf).2
        ⟨hnext, q, below c ((st.piles q).faceUp),
          aboveIn c ((st.piles q).faceUp), below_aboveIn_split hcmemST, ?_,
          Or.inr htst⟩)
      rcases hseat' with hbs' | ⟨hhid, hk⟩
      · exact Or.inl (by rw [hbl]; exact hbs')
      · exact Or.inr ⟨hqH.trans hhid, hk⟩
    rcases Decidable.em (p = a) with rfl | hpa
    · -- the landing pile: the snoc kill keeps c off the cargo slot
      have hcneD : c ≠ d := by
        intro hcon
        have hlastS : lastOf ((s'.piles p).faceUp) = some d := by
          rw [hpF]
          exact lastOf_snoc
        have hlast1 : lastOf (bs' ++ c :: run) = some d := by
          rw [← hshape']
          exact hlastS
        rw [hcon, hrunE, lastOf_append_tail (by simp),
          lastOf_cons_tail (by simp)] at hlast1
        exact nodup_dup_mem d bs' (r₀ :: rst)
          (by rw [← hcon]; exact hndF) (lastOf_mem hlast1)
      have hcmemST : c ∈ (st.piles p).faceUp := by
        have hcmemP : c ∈ (st.piles p).faceUp ++ [d] := by
          rw [← hpF]
          exact hcmemS
        rcases List.mem_append.mp hcmemP with h | h
        · exact h
        · exact absurd (List.mem_singleton.mp h) hcneD
      have hbl : below c ((st.piles p).faceUp) = bs' := by
        have h2 : below c ((s'.piles p).faceUp)
            = below c ((st.piles p).faceUp) := by
          rw [hpF, below_snoc_of_mem c ((st.piles p).faceUp) d hcmemST]
        rw [← h2]
        exact hbelowF
      refine hdead c hcp ((canRaiseS_iff hwf).2
        ⟨hnext, p, below c ((st.piles p).faceUp),
          aboveIn c ((st.piles p).faceUp), below_aboveIn_split hcmemST, ?_,
          Or.inr htst⟩)
      rcases hseat' with hbs' | ⟨hhid, hk⟩
      · exact Or.inl (by rw [hbl]; exact hbs')
      · exact Or.inr ⟨hpH.trans hhid, hk⟩
    · -- untouched pile: everything transfers verbatim
      have hPa : s'.piles a = st.piles a :=
        hrest a (fun h => hpa h.symm) (fun h => hqa h.symm)
      have hcmemST : c ∈ (st.piles a).faceUp := by
        rw [← hPa]
        exact hcmemS
      have hbl : below c ((st.piles a).faceUp) = bs' := by
        rw [← hPa]
        exact hbelowF
      refine hdead c hcp ((canRaiseS_iff hwf).2
        ⟨hnext, a, below c ((st.piles a).faceUp),
          aboveIn c ((st.piles a).faceUp), below_aboveIn_split hcmemST, ?_,
          Or.inr htst⟩)
      rcases hseat' with hbs' | ⟨hhid, hk⟩
      · exact Or.inl (by rw [hbl]; exact hbs')
      · have hhidst : (st.piles a).hidden = [] := by
          rw [← hPa]
          exact hhid
        exact Or.inr ⟨hhidst, hk⟩

/-! ## §2. The step package — the slid-mate leg's pile-level anatomy -/

/-- The slid-mate leg package: firing `tabToTab d (inr x)` at the trial
shape produces the successor `s'` with the two touched-pile profiles
(the landing pile gains `[d]` over the witness's old shape, the source
pile keeps the exposed twin over its seat), the untouched-pile
invariance, the found non-write, and the leg's own reversibility (the
under-cell undo: the mirror slide back onto the exposed twin).  This is
the vanilla `forkState_slide_mate` machinery, verbatim, packaged for
the S-grade consumer. -/
private theorem mate_step_package {st : State} {x d : Card} {p q : Anchor}
    {bs : List Card}
    (hwf : st.WF)
    (hpox : st.pileOfTop x = some p)
    (hshape : (st.piles q).faceUp = bs ++ [x.twin, d])
    (hfit : canSitOn d x = true) :
    ∃ s', st.step (Move.tabToTab d (Sum.inr x)) = some s' ∧
      (∀ σ, s'.found σ = st.found σ) ∧
      s'.WF ∧
      reversibleAtW st (Move.tabToTab d (Sum.inr x)) ∧
      p ≠ q ∧
      d ≠ x ∧ d ≠ x.twin ∧
      s'.piles q = ⟨(st.piles q).hidden, bs ++ [x.twin]⟩ ∧
      s'.piles p = ⟨(st.piles p).hidden, (st.piles p).faceUp ++ [d]⟩ ∧
      st.piles q = ⟨(s'.piles q).hidden, (s'.piles q).faceUp ++ [d]⟩ ∧
      (∀ y, y ≠ p → y ≠ q → s'.piles y = st.piles y) := by
  -- the memberships and search pins at st
  have htwinmem : x.twin ∈ (st.piles q).faceUp := by
    rw [hshape]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
  have hdmem : d ∈ (st.piles q).faceUp := by
    rw [hshape]
    exact List.mem_append.mpr (Or.inr
      (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl))))
  have hdhold : st.pileHolding d = some q := (pileHolding_eq_some_iff hwf).2 hdmem
  have hassol : bs ++ [x.twin, d] = (bs ++ [x.twin]) ++ [d] :=
    (List.append_assoc bs [x.twin] [d]).symm
  have hdtopq : (st.piles q).top = some d := by
    show lastOf (st.piles q).faceUp = some d
    rw [hshape, hassol]
    exact lastOf_snoc
  have hpod : st.pileOfTop d = some q := (pileOfTop_eq_some_iff hwf).2 hdtopq
  -- the fit facts, the cargo outside the pair
  obtain ⟨hrank, hcolne⟩ := (canSitOn_eq d x).mp hfit
  have hdx : d ≠ x := by
    intro hcon
    rw [← hcon] at hrank
    omega
  have hdtx : d ≠ x.twin := by
    intro hcon
    rw [hcon, Card.twin_rank] at hrank
    omega
  -- the piles differ: the cargo tops q, the witness tops p
  have hpq : p ≠ q := by
    intro hcon
    have hLd : lastOf (st.piles p).faceUp = some d := by
      rw [hcon]
      exact hdtopq
    exact hdx (Option.some.inj (((pileOfTop_top hpox).2).symm.trans hLd)).symm
  -- the cut shapes, through the run discipline's duplicate-freedom
  have hndq : ((bs ++ [x.twin]) ++ [d]).Nodup := by
    have h := runOK_nodup (hwf.runOK_of q)
    rw [hshape, hassol] at h
    exact h
  have hdnotmem : d ∉ bs ++ [x.twin] := nodup_snoc_notmem _ d hndq
  have hbel : below d ((st.piles q).faceUp) = bs ++ [x.twin] := by
    rw [hshape, hassol]
    exact below_append_stop hdnotmem
  have hfrom : fromCard d ((st.piles q).faceUp) = [d] := by
    rw [hshape, hassol]
    exact fromCard_append_stop hdnotmem
  have hpre : bs ++ [x.twin] ≠ [] := by
    cases bs with
    | nil => simp
    | cons w ws => simp
  -- FIRE the slide; the successor is the literal
  have hsteplit : st.step (Move.tabToTab d (Sum.inr x)) = some
      ((st.setPile q (Pile.afterRunRemoved (st.piles q) (bs ++ [x.twin]))).putRun
        [d] (Sum.inr x)) := by
    show (match st.pileHolding d with
      | none => none
      | some a₂ =>
          if st.canPlace d (Sum.inr x) then
            match fromCard d ((st.piles a₂).faceUp) with
            | [] => none
            | run => some ((st.setPile a₂
                (Pile.afterRunRemoved (st.piles a₂)
                  (below d ((st.piles a₂).faceUp)))).putRun run (Sum.inr x))
          else none) = _
    rw [hdhold]
    simp only [canPlace_inr_located hpox, hfit]
    rw [hfrom, hbel]
    rfl
  obtain ⟨s', hs'eq, hstep⟩ : ∃ s', s' =
      (st.setPile q (Pile.afterRunRemoved (st.piles q) (bs ++ [x.twin]))).putRun
        [d] (Sum.inr x) ∧
      st.step (Move.tabToTab d (Sum.inr x)) = some s' :=
    ⟨_, rfl, hsteplit⟩
  -- the mid-state pile q: the twin exposed, the hidden deck kept
  have hmidq : (st.setPile q (Pile.afterRunRemoved (st.piles q) (bs ++ [x.twin]))).piles q
      = ⟨(st.piles q).hidden, bs ++ [x.twin]⟩ := by
    rw [setPile_piles_self, afterRunRemoved_ne hpre]
  -- the mid-state search pin for x at p (WF-free: the profile of tops)
  have hxmem : x ∈ (st.piles p).faceUp :=
    Pile.mem_of_top (pileOfTop_top hpox).2
  have hnoTx : ∀ y : Anchor, y ≠ p → (st.piles y).top ≠ some x := by
    intro y hyp htop
    exact (mem_faceUp_unique hwf hxmem y hyp).1 (Pile.mem_of_top htop)
  have hmidx :
      (st.setPile q (Pile.afterRunRemoved (st.piles q) (bs ++ [x.twin]))).pileOfTop x
        = some p := by
    show (firstWhere (fun a₂ =>
        decide ((st.setPile q
          (Pile.afterRunRemoved (st.piles q) (bs ++ [x.twin]))).topOf a₂ = some x))
      Anchor.all) = some p
    refine firstWhere_find (Anchor.mem_all p) ?_ ?_
    · show decide (((st.setPile q
          (Pile.afterRunRemoved (st.piles q) (bs ++ [x.twin]))).topOf p) = some x) = true
      rw [setPile_topOf_ne hpq]
      exact decide_eq_true (pileOfTop_top hpox).2
    · intro y _hyp hyne
      show decide (((st.setPile q
          (Pile.afterRunRemoved (st.piles q) (bs ++ [x.twin]))).topOf y) = some x) = false
      by_cases hyq : y = q
      · have hpqmid : ((st.setPile q
            (Pile.afterRunRemoved (st.piles q) (bs ++ [x.twin]))).piles q).top ≠ some x := by
          rw [setPile_piles_self, afterRunRemoved_ne hpre]
          show lastOf (bs ++ [x.twin]) ≠ some x
          intro hcon
          exact card_twin_ne x (Option.some.inj (lastOf_snoc.symm.trans hcon))
        exact decide_false_of_not (by rw [hyq]; exact hpqmid)
      · rw [setPile_topOf_ne hyq]
        exact decide_false_of_not (fun hcon => hnoTx y hyne
          (show (st.piles y).top = some x from hcon))
  -- the successor's pile profile
  have hmidp : (st.setPile q
      (Pile.afterRunRemoved (st.piles q) (bs ++ [x.twin]))).piles p = st.piles p :=
    setPile_piles_ne hpq
  have hs'l : s' = (st.setPile q
      (Pile.afterRunRemoved (st.piles q) (bs ++ [x.twin]))).setPile p
    { (st.piles p) with faceUp := (st.piles p).faceUp ++ [d] } := by
    rw [hs'eq, putRun_inr_eq hmidx, hmidp]
  have hs'p : s'.piles p = ⟨(st.piles p).hidden, (st.piles p).faceUp ++ [d]⟩ := by
    rw [hs'l, setPile_piles_self]
  have hs'q : s'.piles q = ⟨(st.piles q).hidden, bs ++ [x.twin]⟩ := by
    rw [hs'l, setPile_piles_ne (Ne.symm hpq), hmidq]
  have hs'others : ∀ y, y ≠ p → y ≠ q → s'.piles y = st.piles y := by
    intro y hyp hyq
    rw [hs'l, setPile_piles_ne hyp, setPile_piles_ne hyq]
  -- the founds and WF never leave the leg
  have hffound : ∀ σ, s'.found σ = st.found σ := fun _ => slide_foundEq hstep _
  have hwfs' : s'.WF := step_wf hwf hstep
  -- the st-side q profile in s'-terms
  have hqh : (st.piles q).hidden = (s'.piles q).hidden := by
    rw [hs'q]
  have hs'qF : (s'.piles q).faceUp = bs ++ [x.twin] := by
    rw [hs'q]
  have hLq : st.piles q = ⟨(s'.piles q).hidden, (s'.piles q).faceUp ++ [d]⟩ := by
    refine Pile.ext ?_ ?_
    · exact hqh
    · rw [hshape, hs'qF]
      exact hassol
  -- the leg is reversible: the under-cell, undo = slide back onto the twin
  have hbell : lastOf (below d ((st.piles q).faceUp)) = some x.twin := by
    rw [hbel]
    exact lastOf_snoc
  have hrankT : d.rank.toIdx + 1 = x.twin.rank.toIdx := by
    rw [Card.twin_rank]
    exact hrank
  have hcolT : d.suit.color ≠ x.twin.suit.color := by
    rw [show x.twin.suit.color = x.suit.color from
        (Suit.color_twin x.suit)]
    exact hcolne
  have hsitT : canSitOn d x.twin = true :=
    (canSitOn_eq d x.twin).2 ⟨hrankT, hcolT⟩
  have hholdp' : s'.pileHolding d = some p :=
    (pileHolding_eq_some_iff hwfs').2 (by
      rw [hs'p]
      show d ∈ (st.piles p).faceUp ++ [d]
      exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))
  have hcn2 : d ∉ (st.piles p).faceUp :=
    (mem_faceUp_unique hwf hdmem p hpq).1
  have hzonly : ∀ y, y ≠ q → (s'.piles y).top ≠ some x.twin := by
    intro y hyq htop
    by_cases hyp : y = p
    · rw [hyp] at htop
      rw [hs'p] at htop
      have hlast : lastOf ((st.piles p).faceUp ++ [d]) = some x.twin := htop
      exact hdtx (Option.some.inj (lastOf_snoc.symm.trans hlast))
    · have hP4 : s'.piles y = st.piles y := hs'others y hyp hyq
      rw [hP4] at htop
      exact (mem_faceUp_unique hwf htwinmem y hyq).1 (Pile.mem_of_top htop)
  have hzk : (st.piles p).top ≠ some x.twin :=
    fun htop => (mem_faceUp_unique hwf htwinmem p hpq).1 (Pile.mem_of_top htop)
  have hmidx2 : (st.setPile q
      (Pile.afterRunRemoved (st.piles q) (below d ((st.piles q).faceUp)))).pileOfTop x
        = some p := by
    rw [hbel]
    exact hmidx
  have hrev := tabToTab_undo_under hstep hdhold hbell hsitT hholdp'
    (Or.inr ⟨x, rfl, hmidx2⟩) (fun y hyq hyp => hs'others y hyp hyq) hcn2
    hzonly hzk
  exact ⟨s', hstep, hffound, hwfs', hrev, hpq, hdx, hdtx, hs'q, hs'p, hLq, hs'others⟩

/-! ## §3. The S-mate production -/

/-- **THE S-MATE PRODUCTION** — the slid mate of a strong forkState is a
strong forkState, witness flipped.  At the trial shape (the twin
`x.twin` covered directly by the fitting cargo `d`, `bs ++ [x.twin, d]`
at pile `q`, with the exposed twin's seat package), the one reversible
cargo leg `tabToTab d (inr x)` lands a mate where BOTH pair members are
S-live (the twin vanilla-tops its seat package; the witness is covered
by the fitting cargo and frees through `canRaiseS_free`), the vanilla
license pinned to the twin only (the witness stays covered), and every
non-pair card stays S-dead (`S_census_one_leg`).  CargoPath: the leg's
own `FlatStep.cargo` witness. -/
theorem forkState_mate_S {st : State} {x d : Card} {q : Anchor} {bs : List Card}
    (hwf : st.WF)
    (hiff : ∀ c, (c = x ∨ c = x.twin) ↔ CanRaiseS st c)
    (hnt : ¬ CanRaise st x.twin)
    (hshape : (st.piles q).faceUp = bs ++ [x.twin, d])
    (hfit : canSitOn d x = true)
    (hseat : bs ≠ [] ∨ ((st.piles q).hidden = [] ∧ x.twin.rank = Rank.king)) :
    ∃ s', st.step (Move.tabToTab d (Sum.inr x)) = some s' ∧
      forkState s' ∧ CargoPath st s' := by
  -- the geometry: the witness tops with the vanilla license
  have hcanx : CanRaise st x := forkState_witness_canRaise hwf hiff hnt
  obtain ⟨-, p, hpox, hxseat⟩ := id hcanx
  -- the leg package: the vanilla mate machinery, verbatim
  obtain ⟨s', hstep, hffound, hwfs', hrev, hpq, hdx, hdtx, hs'q, hs'p, hLq,
    hs'others⟩ := mate_step_package hwf hpox hshape hfit
  -- the successor's q-profile projections
  have hs'qF : (s'.piles q).faceUp = bs ++ [x.twin] := by rw [hs'q]
  have hqh : (st.piles q).hidden = (s'.piles q).hidden := by rw [hs'q]
  -- the rung data through the S-iff's pair-live halves
  have hL2 : (st.found x.twin.suit).length = x.twin.rank.toIdx :=
    canRaiseS_rung ((hiff x.twin).mp (Or.inr rfl))
  have hnexttwin : s'.nextUp x.twin = true := by
    show decide (x.twin.rank.toIdx = (s'.found x.twin.suit).length) = true
    rw [hffound x.twin.suit, hL2, Card.twin_rank]
    exact decide_eq_true rfl
  have hs'QT : (s'.piles q).top = some x.twin := by
    show lastOf ((s'.piles q).faceUp) = some x.twin
    rw [hs'qF]
    exact lastOf_snoc
  have hs'QTpod : s'.pileOfTop x.twin = some q :=
    (pileOfTop_eq_some_iff hwfs').2 hs'QT
  -- PAIR-LIVE: the twin, the vanilla now-leg over its seat package
  have hseattwin : chop (s'.piles q).faceUp ≠ [] ∨
      ((s'.piles q).hidden = [] ∧ x.twin.rank = Rank.king) := by
    rw [hs'qF, chop_snoc]
    rcases hseat with hbs | hhk
    · exact Or.inl hbs
    · exact Or.inr ⟨hqh.symm.trans hhk.1, hhk.2⟩
  have hlicensetwin : CanRaise s' x.twin :=
    ⟨hnexttwin, q, hs'QTpod, hseattwin⟩
  -- PAIR-LIVE: the witness, covered by the fitting cargo — the free
  obtain ⟨pre, hpreq⟩ := lastOf_eq_snoc (pileOfTop_top hpox).2
  have hLpF : (s'.piles p).faceUp = (st.piles p).faceUp ++ [d] := by rw [hs'p]
  have hnextxS : s'.nextUp x = true := by
    show decide (x.rank.toIdx = (s'.found x.suit).length) = true
    rw [hffound x.suit]
    exact hcanx.1
  have hseatx : pre ≠ [] ∨ ((s'.piles p).hidden = [] ∧ x.rank = Rank.king) := by
    rcases hxseat with hch | hhk
    · refine Or.inl ?_
      rw [hpreq, chop_snoc] at hch
      exact hch
    · refine Or.inr ⟨?_, hhk.2⟩
      rw [hs'p]
      exact hhk.1
  have hfreex : CanRaiseS s' x :=
    canRaiseS_free hwfs'
      (show (s'.piles p).faceUp = (pre ++ [x]) ++ (d :: ([] : List Card)) from by
        rw [hLpF, hpreq])
      hs'QTpod (Ne.symm hpq) hfit hnextxS hseatx
  -- THE PIN: the witness is covered at s', the license pinned to the twin
  have hnox : ¬ CanRaise s' x := by
    rintro ⟨-, a₂, hpo₂, -⟩
    have hxmem' : x ∈ (s'.piles p).faceUp := by
      rw [hLpF, hpreq]
      exact List.mem_append.mpr (Or.inl
        (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))))
    have hmema₂ : x ∈ (s'.piles a₂).faceUp :=
      Pile.mem_of_top ((pileOfTop_eq_some_iff hwfs').mp hpo₂)
    have hap : a₂ = p := pileHolding_inj ((pileHolding_eq_some_iff hwfs').2 hmema₂)
      ((pileHolding_eq_some_iff hwfs').2 hxmem')
    rw [hap] at hpo₂
    have htopp : (s'.piles p).top = some x := (pileOfTop_eq_some_iff hwfs').mp hpo₂
    have hlast : lastOf ((st.piles p).faceUp ++ [d]) = some x := by
      rw [← hLpF]
      exact htopp
    exact hdx (Option.some.inj (lastOf_snoc.symm.trans hlast))
  -- THE CENSUS: non-pair cards stay S-dead through the one leg
  have hdead : ∀ c, ¬(c = x ∨ c = x.twin) → ¬ CanRaiseS st c := by
    intro c hcp hSst
    rcases (hiff c).mpr hSst with rfl | rfl
    · exact hcp (Or.inl rfl)
    · exact hcp (Or.inr rfl)
  have hcensus := S_census_one_leg hwf hwfs' hffound hs'QT hs'p hLq hs'others
    hdx hdtx hdead
  -- the mate forkState: witness flipped, license flipped
  refine ⟨s', hstep, ⟨x.twin, ?_, ?_⟩, ?_⟩
  · intro c
    constructor
    · rintro (rfl | rfl)
      · exact CanRaiseS.now _ hlicensetwin
      · rw [Card.twin_twin]
        exact hfreex
    · intro hS
      rcases Decidable.em (c = x ∨ c = x.twin) with hor | hor
      · rcases hor with hcx | hctx
        · rw [hcx]
          exact Or.inr (Card.twin_twin x).symm
        · rw [hctx]
          exact Or.inl rfl
      · exact absurd hS (hcensus c hor)
  · rw [Card.twin_twin]
    exact hnox
  · exact CargoPath.cons (FlatStep.cargo d (Sum.inr x) hstep hrev)
      ⟨d, (Sum.inr x), hstep, hrev, rfl⟩ (CargoPath.refl s')

/-- The `forkState st`-packaged read: the trial shape travels with the
witness parcel (the witness, its orientation pin, and the slid-mate
trial at one existential), so the detection arrives as the single
premise `forkState st`-grade consumers hand over. -/
theorem forkState_mate_S' {st : State} (hwf : st.WF) (_h : forkState st)
    (htrial : ∃ x d q bs, (∀ c, (c = x ∨ c = x.twin) ↔ CanRaiseS st c) ∧
      ¬ CanRaise st x.twin ∧ (st.piles q).faceUp = bs ++ [x.twin, d] ∧
      canSitOn d x = true ∧
      (bs ≠ [] ∨ ((st.piles q).hidden = [] ∧ x.twin.rank = Rank.king))) :
    ∃ x d s', st.step (Move.tabToTab d (Sum.inr x)) = some s' ∧
      forkState s' ∧ CargoPath st s' := by
  obtain ⟨x, d, q, bs, hiff, hnt, hsh, hfit, hseat⟩ := htrial
  obtain ⟨s', hs, hfs, hcp⟩ := forkState_mate_S hwf hiff hnt hsh hfit hseat
  exact ⟨x, d, s', hs, hfs, hcp⟩

/-! ## The audit battery -/

#print axioms S_census_one_leg
#print axioms forkState_mate_S
#print axioms forkState_mate_S'
