import Orig.SFlatTransfer
import Orig.ConjugateProof

/-!
# Orig.SConjugate — the S-grade conjugate production

THE BRIEF: the physical-swap composite (`conjugateForkState`, the
raise–slide–pull letter whose endpoint is `w`) produces a forkState at
the S grade: from a `forkState st` (the maneuver-stable detection), the
letter's own firing records, and the same-orbit bookkeeping, the
endpoint `w` carries the full S-parcel — the pair saturation iff at
the {slide · raise} grade and the orientation pin.  The weak-grade
endpoint row is already banked (`conjugate_forkState_corrected` in
`Orig.ConjugateProof`; the endpoint's vanilla iff, net-flat founds,
re-licensed witness), so the load-bearing new content is the S-UPGRADE:

* §1 the twin's parcel: the S-live covered side reads through the flat
  characterization (`canRaiseS_iff`), giving the honest TwinSeat and
  location the banked anatomy demands.
* §2 the letter-pins plus THE ORBIT-GRADE JUNK GATE: the letter's
  raised card is the detection's own witness — outside the pair the
  firing's guard leaves only two corners, and BOTH are closed here:
  the OVER-HIDDEN reveal channel by the hidden totals against the
  class witness's per-pile hidden pin (`shuffle_hiddenPinned`), and
  the BARE-EMPTY channel by the first-refill-is-a-king pillar (the
  `Orig/PositionSeat` §1 block, transcribed verbatim as §3 with its
  play-lift §4) over the backward class witness.
* §5 the window packages: the composite's endpoint pile shapes, king
  channel and seated channel (the §4 anatomy of `Orig.ConjugateProof`,
  packaged for this card's consumers — the endpoints' licorice
  profile, net-flat founds, per-pile tails).
* §7 the channel assemblies: the endpoint pair re-licenses at the S
  grade — `x` vanilla-live by the relic, the twin covered by its own
  ride-along run (seated on the witness's old seat content, or the
  bare-king corner), and the orientation pin (the buried twin cannot
  lift: the run's nodup at the window's changed tops).
* §8 THE CENSUS RESIDUE: the one-leg census transfer
  (`S_census_one_leg`) rides a single reversible slide with a
  single-card cargo; the conjugate window's middle leg carries the
  WHOLE twin segment, so the transfer does not apply verbatim.  Both
  channel rows are this file's named residue, carried openly by the
  audit battery; the full route is priced in their docstrings.
* §9 THE MAIN ROW `forkState_conjugate_S`, assembled from the proved
  sections, with the audit battery.

House compliance: additive leaf (`import Orig.SFlatTransfer` and
`import Orig.ConjugateProof` only); the in-tree interface consumed by
real names; the private micro-kit re-lands the house's standard copies
(the `Orig/PositionSeat` §1 pillar block is transcribed verbatim, per
the dedup discipline); the audit battery names every residue honestly.
-/

/-! ## §0. The private kit (per-file copies, the house dedup discipline) -/

/-- A twin is never its own card (the house's standard copy). -/
private theorem card_twin_ne (c : Card) : c.twin ≠ c := by
  intro hcon
  exact Suit.twin_ne c.suit (congrArg Card.suit hcon)

/-- A nodup list cannot host its snoc card in the front part. -/
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

/-- A nodup list cannot host its mid card in the prefix. -/
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

/-- The nodup append bar: a member of the first part never occurs in
the second. -/
private theorem nodup_append_notmem {l₁ l₂ : List Card} {d : Card}
    (hnd : (l₁ ++ l₂).Nodup) (hmem : d ∈ l₁) : d ∉ l₂ := by
  obtain ⟨_, _, hdisj⟩ := List.nodup_append.mp hnd
  exact fun hcon => absurd rfl (hdisj d hmem d hcon)

/-- The below-part and the run from `c` reassemble the list (the copy
of the house's standard row). -/
private theorem below_join {c : Card} : ∀ (l : List Card),
    below c l ++ fromCard c l = l := by
  intro l
  induction l with
  | nil => rfl
  | cons y t ih =>
      rw [below_cons, fromCard]
      by_cases hyc : y = c
      · rw [if_pos hyc, if_pos hyc]
        rfl
      · rw [if_neg hyc, if_neg hyc]
        exact congrArg (y :: ·) ih

/-- Every element of the below-part is an element. -/
private theorem below_mem {c : Card} : ∀ {l : List Card} {x : Card},
    x ∈ below c l → x ∈ l := by
  intro l
  induction l with
  | nil => intro x h; cases h
  | cons y t ih =>
      intro x h
      rw [below_cons] at h
      by_cases hyc : y = c
      · rw [if_pos hyc] at h; cases h
      · rw [if_neg hyc] at h
        rcases List.mem_cons.1 h with rfl | hm
        · exact List.mem_cons.2 (Or.inl rfl)
        · exact List.mem_cons.2 (Or.inr (ih hm))

/-- Every element of the fromCard-part is an element. -/
private theorem fromCard_mem {c : Card} : ∀ {l : List Card} {x : Card},
    x ∈ fromCard c l → x ∈ l := by
  intro l
  induction l with
  | nil => intro x h; cases h
  | cons y t ih =>
      intro x h
      rw [fromCard] at h
      by_cases hyc : y = c
      · rw [if_pos hyc] at h
        rcases List.mem_cons.1 h with rfl | hm
        · exact List.mem_cons.2 (Or.inl rfl)
        · exact List.mem_cons.2 (Or.inr hm)
      · rw [if_neg hyc] at h
        exact List.mem_cons.2 (Or.inr (ih h))

/-- Below reads stop at the first `c`, so a snoc past the whole list
cannot move them (the copy of the S-transfer's private row). -/
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

/-- The last of an append is the second list's last (the house trivia,
re-landed for the pile-top reads). -/
private theorem lastOf_append {l₁ : List Card} :
    ∀ (l₂ : List Card), l₂ ≠ [] → ∀ (c : Card),
      lastOf (l₁ ++ l₂) = some c → lastOf l₂ = some c := by
  induction l₁ with
  | nil => intro l₂ _ c h; exact h
  | cons x t ih =>
      intro l₂ hne c h
      obtain ⟨z, zs, rfl⟩ := list_cons_of_ne_nil hne
      have hLne : (t ++ z :: zs) ≠ [] := by simp
      obtain ⟨u, us, hcu⟩ := list_cons_of_ne_nil hLne
      have h6 : lastOf (x :: u :: us) = some c := by
        rw [show (x :: t) ++ z :: zs = x :: (t ++ z :: zs) from rfl, hcu] at h
        exact h
      have h7 : lastOf (u :: us) = some c := h6
      rw [← hcu] at h7
      exact ih (z :: zs) (by simp) c h7

/-- The last-element lemma in equation form. -/
private theorem lastOf_cons_cons (u v : Card) (t : List Card) :
    lastOf (u :: v :: t) = lastOf (v :: t) := rfl

/-- The last of an append IS the second list's last. -/
private theorem lastOf_append_eq (l₁ : List Card) : ∀ (l₂ : List Card),
    l₂ ≠ [] → lastOf (l₁ ++ l₂) = lastOf l₂ := by
  induction l₁ with
  | nil => intro l₂ _; rfl
  | cons u t ih =>
      intro l₂ hne
      cases t with
      | nil =>
          rcases l₂ with _ | ⟨z, zs⟩
          · exact absurd rfl hne
          · exact lastOf_cons_cons u z zs
      | cons v vs =>
          exact (lastOf_cons_cons u v (vs ++ l₂)).trans (ih l₂ hne)

/-- In a nonempty-tail list the last skips the head. -/
private theorem lastOf_cons_tail {x : Card} {L : List Card} (h : L ≠ []) :
    lastOf (x :: L) = lastOf L := by
  cases L with
  | nil => exact absurd rfl h
  | cons y t => rfl

/-- The chop is empty exactly below length two. -/
private theorem chop_eq_nil_iff : ∀ (l : List Card), chop l = [] ↔ l.length ≤ 1
  | [] => by
      constructor
      · intro _; simp
      · intro _; rfl
  | [x] => by
      constructor
      · intro _; simp
      · intro _; rfl
  | x :: y :: t => by
      have hcl : chop (x :: y :: t) = x :: chop (y :: t) := rfl
      constructor
      · intro h
        rw [hcl] at h
        exact absurd h (by simp)
      · intro h
        have hlen : (x :: y :: t).length = 2 + t.length := by
          rw [List.length_cons, List.length_cons]
          omega
        rw [hlen] at h
        omega

/-- A two-or-longer list's chop is nonempty. -/
private theorem chop_ne_nil_of_len {l : List Card} (h : 2 ≤ l.length) :
    chop l ≠ [] := by
  intro hcon
  have h2 := (chop_eq_nil_iff l).1 hcon
  omega

/-- The bare vacate's computational meaning: an empty prefix split and
an empty hidden deck leave the bare empty pile. -/
private theorem afterRunRemoved_bareEmpty {p : Pile} (h : p.hidden = []) :
    Pile.afterRunRemoved p ([] : List Card) = ⟨[], ([] : List Card)⟩ := by
  rcases p with ⟨hlist, flist⟩
  cases hlist with
  | nil => rfl
  | cons x xs => exact absurd h (by simp)

/-- A nonempty prefix split keeps the prefix verbatim (the copy of the
PositionSeat private row; `rfl` through the split form). -/
private theorem afterRunRemoved_cons' {p : Pile} {x : Card} {xs : List Card} :
    Pile.afterRunRemoved p (x :: xs) = (⟨p.hidden, x :: xs⟩ : Pile) := rfl

/-- A nonempty `fromCard` run starts at its head card (the copy of the
PositionSeat private row). -/
private theorem fromCard_run_head' (e : Card) :
    ∀ (l : List Card), fromCard e l ≠ [] → ∃ tr, fromCard e l = e :: tr := by
  intro l
  induction l with
  | nil => intro h; exact absurd h (by simp [fromCard])
  | cons x xs ih =>
      intro h
      by_cases hxe : x = e
      · exact ⟨xs, by rw [hxe, fromCard_cons_self]⟩
      · rw [fromCard_cons_ne xs hxe] at h
        obtain ⟨tr, htr⟩ := ih h
        exact ⟨tr, by rw [fromCard_cons_ne xs hxe]; exact htr⟩

/-- The rung pin's nextUp read (the copy of the bridge chapter's row). -/
private theorem nextUp_of_rung {st : State} (c : Card)
    (hr : rungAt st c.suit = c.rank.toIdx) : st.nextUp c = true := by
  show decide (c.rank.toIdx = (st.found c.suit).length) = true
  exact decide_eq_true hr.symm

/-! ## §1. The twin's parcel — the S-live covered side in position -/

/-- **THE TWIN'S PARCEL** — the orientation pin's S-live twin reads
through the flat characterization: located, in shape, seated — and
COVERED (the run above is nonempty: a top with the package would lift
vanilla, against the pin). -/
theorem s_conjugate_twin_parcel {st : State} {x : Card}
    (hwf : st.WF) (hSCanT : CanRaiseS st x.twin)
    (hnt : ¬ CanRaise st x.twin) :
    ∃ q bs run, st.pileHolding x.twin = some q ∧
      (st.piles q).faceUp = bs ++ x.twin :: run ∧
      (bs ≠ [] ∨ ((st.piles q).hidden = [] ∧ x.twin.rank = Rank.king)) ∧
      run ≠ [] := by
  obtain ⟨hnext, a, bs, run, hshape, hseat, -⟩ := (canRaiseS_iff hwf).1 hSCanT
  have hmem : x.twin ∈ (st.piles a).faceUp := by
    rw [hshape]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
  have hcov : run ≠ [] := by
    cases hrun : run with
    | nil =>
        exfalso
        have htop : (st.piles a).top = some x.twin := by
          show lastOf (st.piles a).faceUp = some x.twin
          rw [hshape, hrun]
          exact lastOf_snoc
        have hseatCR : chop (st.piles a).faceUp ≠ [] ∨
            ((st.piles a).hidden = [] ∧ x.twin.rank = Rank.king) := by
          rcases hseat with hbs | hhk
          · exact Or.inl (by rw [hshape, hrun, chop_snoc]; exact hbs)
          · exact Or.inr hhk
        exact hnt ⟨hnext, a, (pileOfTop_eq_some_iff hwf).2 htop, hseatCR⟩
    | cons r t => exact List.cons_ne_nil r t
  exact ⟨a, bs, run, (pileHolding_eq_some_iff hwf).2 hmem, hshape, hseat, hcov⟩

/-! ## §3. The pillar block (per-file copy of `Orig/PositionSeat` §1)

The first-refill-is-a-king engine, verbatim: a pile which is fully
empty or king-headed over an empty hidden deck stays so through every
play (the `oneStep_pileInv` case tree lifted through
`emptyOrKindHead_play`).  The junk gate's bare-empty channel consumes
the play-lift on the class's backward witness. -/

/-- An empty-anchor landing requires a king (the copy of the
PositionSeat private row). -/
private theorem canPlace_inl_king' {s : State} {w : Card} {k : Anchor}
    (h : s.canPlace w (Sum.inl k) = true) : w.rank = Rank.king := by
  rw [State.canPlace, Bool.and_eq_true] at h
  exact of_decide_eq_true h.2

private theorem pileOfTop_of_piles' {s t : State} (z : Card)
    (hp : s.piles = t.piles) : s.pileOfTop z = t.pileOfTop z := by
  show (firstWhere (fun a' => decide ((s.piles a').top = some z)) Anchor.all) =
    (firstWhere (fun a' => decide ((t.piles a').top = some z)) Anchor.all)
  rw [hp]

/-- The empty-or-king-head shape survives the run-removal. -/
private theorem arr_Q' {P : Pile} {e : Card}
    (hmemE : e ∈ P.faceUp)
    (hQ : (P.faceUp = [] ∧ P.hidden = []) ∨
      ∃ K t, P.faceUp = K :: t ∧ K.rank = Rank.king ∧ P.hidden = []) :
    (Pile.afterRunRemoved P (below e P.faceUp)).faceUp = [] ∧
      (Pile.afterRunRemoved P (below e P.faceUp)).hidden = [] ∨
      ∃ K t, (Pile.afterRunRemoved P (below e P.faceUp)).faceUp = K :: t ∧
        K.rank = Rank.king ∧ (Pile.afterRunRemoved P (below e P.faceUp)).hidden = [] := by
  by_cases hpre : below e P.faceUp = []
  · have hhQ : P.hidden = [] := by
      rcases hQ with ⟨-, hh⟩ | ⟨-, -, -, -, hh⟩
      · exact hh
      · exact hh
    rw [hpre, afterRunRemoved_bareEmpty hhQ]
    exact Or.inl ⟨rfl, rfl⟩
  · obtain ⟨w, ws, hpc⟩ := list_cons_of_ne_nil hpre
    rw [hpc, afterRunRemoved_cons']
    rcases hQ with ⟨hfup, -⟩ | ⟨K, t, hfup, hK, hhA⟩
    · exfalso
      rw [hfup] at hmemE
      exact absurd hmemE (by simp)
    · by_cases hE : e = K
      · exfalso
        rw [hfup, hE, below_cons_self] at hpc
        exact absurd hpc (by simp)
      · rw [hfup, below_cons_ne t (fun hc => hE hc.symm)] at hpc
        injection hpc with hw hws
        rw [← hw, ← hws]
        exact Or.inr ⟨K, below e t, rfl, hK, hhA⟩

/-- The empty-or-king-head shape survives one step, every move. -/
private theorem oneStep_pileInv' {A : Anchor} {s s' : State} {m : Move}
    (hstep : State.step s m = some s')
    (hQ : ((s.piles A).faceUp = [] ∧ (s.piles A).hidden = []) ∨
      ∃ K t, (s.piles A).faceUp = K :: t ∧ K.rank = Rank.king ∧
        (s.piles A).hidden = []) :
    ((s'.piles A).faceUp = [] ∧ (s'.piles A).hidden = []) ∨
      ∃ K t, (s'.piles A).faceUp = K :: t ∧ K.rank = Rank.king ∧
        (s'.piles A).hidden = [] := by
  cases m with
  | draw =>
      have hd : s.stepDraw = some s' := hstep
      rw [stepDraw_piles hd]
      exact hQ
  | wasteToFound c =>
      obtain ⟨-, x, xs, hw, hs⟩ := step_wasteToFound_inv hstep
      rw [hs]
      have hp : (({s.setFound c.suit (s.found c.suit ++ [c]) with waste := xs} : State).piles A)
          = s.piles A := rfl
      rw [hp]
      exact hQ
  | wasteToTab c b =>
      obtain ⟨hg, x, xs, hw, hs⟩ := step_wasteToTab_inv hstep
      rw [Bool.and_eq_true] at hg
      rw [hs]
      cases b with
      | inl k =>
          have hp : (({s.putCard c (Sum.inl k) with waste := xs} : State).piles A)
              = (if A = k then (⟨[], [c]⟩ : Pile) else s.piles A) := rfl
          rw [hp]
          by_cases hAk : A = k
          · rw [ite_eq_left hAk]
            rcases hQ with ⟨hfup, -⟩ | ⟨K, t, hfup, -, hhA⟩
            · exact Or.inr ⟨c, [], rfl, canPlace_inl_king' hg.2, rfl⟩
            · exfalso
              obtain ⟨hemp, -⟩ := canPlace_inl hg.2
              rw [← hAk] at hemp
              have hfupE := ((Pile.isEmpty_eq _).mp hemp).2
              rw [hfup] at hfupE
              exact absurd hfupE (by simp)
          · rw [ite_eq_right hAk]
            exact hQ
      | inr z =>
          obtain ⟨kk, hpin, -⟩ := canPlace_inr hg.2
          have hp : (({s.putCard c (Sum.inr z) with waste := xs} : State).piles A)
              = (if A = kk then { s.piles kk with faceUp := (s.piles kk).faceUp ++ [c] }
                 else s.piles A) := by
            simp only [putCard_piles_inr _ _ _ _ hpin]
          rw [hp]
          by_cases hAk : A = kk
          · rw [ite_eq_left hAk]
            rw [hAk] at hQ
            rcases hQ with ⟨hfup, -⟩ | ⟨K, t, hfup, hK, hhA⟩
            · exfalso
              have hne := (pileOfTop_top hpin).1
              rw [hfup] at hne
              exact absurd hne (by simp)
            · refine Or.inr ⟨K, t ++ [c], ?_, hK, hhA⟩
              show (s.piles kk).faceUp ++ [c] = K :: (t ++ [c])
              rw [hfup, List.cons_append]
          · rw [ite_eq_right hAk]
            exact hQ
  | tabToFound c =>
      obtain ⟨-, k, hpod, hs⟩ := step_tabToFound_inv hstep
      have hpileEq : s'.piles A = (if A = k then
          Pile.afterRunRemoved (s.piles k) (chop (s.piles k).faceUp)
          else s.piles A) := by rw [hs]
      rw [hpileEq]
      by_cases hAk : A = k
      · rw [hAk] at hQ
        have hself : (if A = k then Pile.afterRunRemoved (s.piles k) (chop (s.piles k).faceUp)
            else s.piles A) = Pile.afterRunRemoved (s.piles k) (chop (s.piles k).faceUp) :=
          ite_eq_left hAk
        rw [hself]
        rcases hQ with ⟨hfup, hhA⟩ | ⟨K, t, hfup, hK, hhA⟩
        · have hch : chop (s.piles k).faceUp = [] := by rw [hfup]; rfl
          rw [hch, afterRunRemoved_bareEmpty hhA]
          exact Or.inl ⟨rfl, rfl⟩
        · cases t with
          | nil =>
              have hch : chop (s.piles k).faceUp = [] := by rw [hfup]; rfl
              rw [hch, afterRunRemoved_bareEmpty hhA]
              exact Or.inl ⟨rfl, rfl⟩
          | cons y ys =>
              have hch : chop (s.piles k).faceUp = K :: chop (y :: ys) := by rw [hfup]; rfl
              rw [hch, afterRunRemoved_cons']
              exact Or.inr ⟨K, chop (y :: ys), rfl, hK, hhA⟩
      · have helse : (if A = k then Pile.afterRunRemoved (s.piles k) (chop (s.piles k).faceUp)
            else s.piles A) = s.piles A := ite_eq_right hAk
        rw [helse]
        exact hQ
  | foundToTab c b =>
      obtain ⟨c', ht, heqc, hg, hs⟩ := step_foundToTab_inv hstep
      rw [hs]
      have hmidp : (s.setFound c.suit (chop (s.found c.suit))).piles = s.piles :=
        setFound_piles s c.suit (chop (s.found c.suit))
      cases b with
      | inl k =>
          have hp : (((s.setFound c.suit (chop (s.found c.suit))).putCard c (Sum.inl k)).piles A)
              = (if A = k then (⟨[], [c]⟩ : Pile) else s.piles A) := rfl
          rw [hp]
          by_cases hAk : A = k
          · rw [ite_eq_left hAk]
            rcases hQ with ⟨hfup, -⟩ | ⟨K, t, hfup, -, hhA⟩
            · exact Or.inr ⟨c, [], rfl, canPlace_inl_king' hg, rfl⟩
            · exfalso
              obtain ⟨hemp, -⟩ := canPlace_inl hg
              rw [← hAk] at hemp
              have hfupE := ((Pile.isEmpty_eq _).mp hemp).2
              rw [hfup] at hfupE
              exact absurd hfupE (by simp)
          · rw [ite_eq_right hAk]
            exact hQ
      | inr z =>
          obtain ⟨kk, hpin, -⟩ := canPlace_inr hg
          have hmidpin : (s.setFound c.suit (chop (s.found c.suit))).pileOfTop z = some kk := by
            rw [pileOfTop_of_piles' z hmidp]
            exact hpin
          have hp : (((s.setFound c.suit (chop (s.found c.suit))).putCard c (Sum.inr z)).piles A)
              = (if A = kk then { s.piles kk with faceUp := (s.piles kk).faceUp ++ [c] }
                 else s.piles A) := by
            simp only [putCard_piles_inr _ _ _ _ hmidpin]
            rw [hmidp]
          rw [hp]
          by_cases hAk : A = kk
          · rw [ite_eq_left hAk]
            rw [hAk] at hQ
            rcases hQ with ⟨hfup, -⟩ | ⟨K, t, hfup, hK, hhA⟩
            · exfalso
              have hne := (pileOfTop_top hpin).1
              rw [hfup] at hne
              exact absurd hne (by simp)
            · refine Or.inr ⟨K, t ++ [c], ?_, hK, hhA⟩
              show (s.piles kk).faceUp ++ [c] = K :: (t ++ [c])
              rw [hfup, List.cons_append]
          · rw [ite_eq_right hAk]
            exact hQ
  | tabToTab e b =>
      obtain ⟨Asrc, hhold, hcp, hfr, hs'⟩ := step_tabToTab_inv hstep
      have hmemE : e ∈ (s.piles Asrc).faceUp := pileHolding_mem hhold
      rw [hs']
      cases b with
      | inl k =>
          have hp : (((s.setPile Asrc (Pile.afterRunRemoved (s.piles Asrc)
                (below e ((s.piles Asrc).faceUp)))).putRun
              (fromCard e ((s.piles Asrc).faceUp)) (Sum.inl k)).piles A)
              = (if A = k then (⟨[], fromCard e ((s.piles Asrc).faceUp)⟩ : Pile)
                 else (s.setPile Asrc (Pile.afterRunRemoved (s.piles Asrc)
                    (below e ((s.piles Asrc).faceUp)))).piles A) := rfl
          rw [hp]
          by_cases hAk : A = k
          · rw [ite_eq_left hAk]
            obtain ⟨tr, hrun⟩ := fromCard_run_head' e ((s.piles Asrc).faceUp) hfr
            rcases hQ with ⟨hfup, -⟩ | ⟨K, t, hfup, -, hhA⟩
            · exact Or.inr ⟨e, tr, by rw [hrun], canPlace_inl_king' hcp, rfl⟩
            · exfalso
              obtain ⟨hemp, -⟩ := canPlace_inl hcp
              rw [← hAk] at hemp
              have hfupE := ((Pile.isEmpty_eq _).mp hemp).2
              rw [hfup] at hfupE
              exact absurd hfupE (by simp)
          · rw [ite_eq_right hAk]
            by_cases hAs : A = Asrc
            · rw [hAs] at hQ
              rw [hAs, setPile_afterRunRemoved_piles_self s Asrc e]
              exact arr_Q' hmemE hQ
            · rw [setPile_afterRunRemoved_piles_ne s Asrc e A hAs]
              exact hQ
      | inr z =>
          cases hz : (s.setPile Asrc (Pile.afterRunRemoved (s.piles Asrc)
              (below e ((s.piles Asrc).faceUp)))).pileOfTop z with
          | none =>
              rw [putRun_inr_none hz]
              by_cases hAs : A = Asrc
              · rw [hAs] at hQ
                rw [hAs, setPile_afterRunRemoved_piles_self s Asrc e]
                exact arr_Q' hmemE hQ
              · rw [setPile_afterRunRemoved_piles_ne s Asrc e A hAs]
                exact hQ
          | some kk =>
              rw [putRun_inr_eq hz]
              by_cases hAk : A = kk
              · rw [hAk, setPile_piles_self]
                have hneMid := (pileOfTop_top hz).1
                by_cases hAs : A = Asrc
                · rw [hAs] at hQ
                  have hka : kk = Asrc := hAk.symm.trans hAs
                  rw [hka, setPile_afterRunRemoved_piles_self s Asrc e] at hneMid ⊢
                  rcases arr_Q' hmemE hQ with ⟨h1, h2⟩ | ⟨K, tm, h1, hK, h2⟩
                  · exact absurd h1 hneMid
                  · refine Or.inr ⟨K, tm ++ fromCard e ((s.piles Asrc).faceUp), ?_, hK, h2⟩
                    rw [h1, List.cons_append]
                · have hmidA : (s.setPile Asrc (Pile.afterRunRemoved (s.piles Asrc)
                        (below e ((s.piles Asrc).faceUp)))).piles kk = s.piles A := by
                    rw [← hAk]
                    exact setPile_afterRunRemoved_piles_ne s Asrc e A hAs
                  rw [hmidA] at hneMid ⊢
                  rcases hQ with ⟨hfup, -⟩ | ⟨K, t, hfup, hK, hhA⟩
                  · exfalso
                    rw [hfup] at hneMid
                    exact absurd hneMid (by simp)
                  · refine Or.inr ⟨K, t ++ fromCard e ((s.piles Asrc).faceUp), ?_, hK, hhA⟩
                    rw [hfup, List.cons_append]
              · rw [setPile_piles_ne hAk]
                by_cases hAs : A = Asrc
                · rw [hAs] at hQ
                  rw [hAs, setPile_afterRunRemoved_piles_self s Asrc e]
                  exact arr_Q' hmemE hQ
                · rw [setPile_afterRunRemoved_piles_ne s Asrc e A hAs]
                  exact hQ

/-- The play-lift: the empty-or-king-head shape survives a whole play. -/
private theorem emptyOrKingHead_play' {A : Anchor} :
    ∀ (s : State) (play : List Move) (s' : State),
      ((s.piles A).faceUp = [] ∧ (s.piles A).hidden = [] ∨
        ∃ K t, (s.piles A).faceUp = K :: t ∧ K.rank = Rank.king ∧
          (s.piles A).hidden = []) →
      State.run s play = some s' →
      ((s'.piles A).faceUp = [] ∧ (s'.piles A).hidden = [] ∨
        ∃ K t, (s'.piles A).faceUp = K :: t ∧ K.rank = Rank.king ∧
          (s'.piles A).hidden = []) := by
  intro s play
  revert s
  induction play with
  | nil =>
      intro s s' hQ hrun
      have hred : (some s : Option State) = some s' := hrun
      injection hred with hcon
      rw [← hcon]
      exact hQ
  | cons p rest ih =>
      intro s s' hQ hrun
      obtain ⟨s₁, hstep, hrest⟩ := State.run_cons hrun
      exact ih s₁ s' (oneStep_pileInv' hstep hQ) hrest

/-! ## §5. The window packages — the endpoint's pile shapes per channel

The §4 anatomy of `Orig.ConjugateProof`, restated at the
`conjugateForkState` letter and packaged for this card's two
consumers (the twin's free and the census).  The king channel lands
the twin's run and the pulled king on empty anchors; the seated
channel pins both bases onto the exposed under-cards through the
packing pin.  Neither reads the endpoint iff. -/

/-- **THE KING-CHANNEL WINDOW** — when the raised card is a king, the
raise is a bare vacate, the slide lands the twin's whole run on an
empty anchor `m`, the pull lands the king on an empty anchor `kk`,
and every pile other than the two landing anchors returns either its
source shape or the fully-empty shape (its whole face-up content was
either `[x]` alone — pile `p` — or the twin's run — pile `q`). -/
private theorem s_conj_window_king {st w : State} {x : Card} {p q : Anchor}
    {st₁ st₂ : State} {ba bb : Base}
    (hwf : st.WF)
    (h₁step : st.step (Move.tabToFound x) = some st₁)
    (h₂step : st₁.step (Move.tabToTab x.twin ba) = some st₂)
    (h₃step : st₂.step (Move.foundToTab x bb) = some w)
    (hking : x.rank = Rank.king)
    (hiff : ∀ c, CanRaise st c ↔ c = x)
    (h₂rung : rungAt st x.twin.suit = x.rank.toIdx)
    (hpox : st.pileOfTop x = some p)
    (hlochold : st.pileHolding x.twin = some q)
    (hseat : TwinSeat st x q) :
    ∃ m kk covrest,
      ba = Sum.inl m ∧ bb = Sum.inl kk ∧
      covrest ≠ [] ∧ x.twin.rank = Rank.king ∧
      (st.piles q).faceUp = x.twin :: covrest ∧
      m ≠ kk ∧ m ≠ q ∧ p ≠ q ∧
      w.WF ∧
      (∀ σ, w.found σ = st.found σ) ∧
      w.piles m = ⟨[], x.twin :: covrest⟩ ∧
      w.piles kk = ⟨[], [x]⟩ ∧
      (∀ a', a' ≠ m → a' ≠ kk →
        ((a' = p ∨ a' = q) → w.piles a' = ⟨[], ([] : List Card)⟩) ∧
        (a' ≠ p ∧ a' ≠ q → w.piles a' = st.piles a')) := by
  -- x's own seat off the iff, read through the same pile
  have hseatx : chop (st.piles p).faceUp ≠ [] ∨
      ((st.piles p).hidden = [] ∧ x.rank = Rank.king) := by
    obtain ⟨-, a, hpoa, hs⟩ := (hiff x).2 rfl
    rw [pileOfTop_inj hpoa hpox] at hs
    exact hs
  have htopp : (st.piles p).top = some x := (pileOfTop_eq_some_iff hwf).mp hpox
  -- WF travels all three legs
  have hwf₁ : st₁.WF := step_wf hwf h₁step
  have hwfw : w.WF := step_wf (step_wf hwf₁ h₂step) h₃step
  -- the st₁ pile reads: p rewritten, everything else verbatim
  have hst₁pARR : st₁.piles p =
      Pile.afterRunRemoved (st.piles p) (chop (st.piles p).faceUp) := by
    obtain ⟨-, p₀, hp₀, hs₁⟩ := step_tabToFound_inv h₁step
    have hpq : p₀ = p := Option.some.inj (hp₀.symm.trans hpox)
    rw [hpq] at hs₁
    rw [hs₁]
    show (if p = p then
        Pile.afterRunRemoved (st.piles p) (chop (st.piles p).faceUp)
        else st.piles p) =
      Pile.afterRunRemoved (st.piles p) (chop (st.piles p).faceUp)
    rw [if_pos rfl]
  have hst₁p : st₁.piles p = ⟨[], ([] : List Card)⟩ := by
    have hc₀nil : chop (st.piles p).faceUp = [] := by
      by_cases hc₀ : chop (st.piles p).faceUp = []
      · exact hc₀
      · exfalso
        obtain ⟨z₀, hz₀last, hfitz₀⟩ := seated_top_under hwf htopp hc₀
        exact (no_fit_king hfitz₀) hking
    have hhidp : (st.piles p).hidden = [] := by
      rcases hseatx with hch | ⟨hh, hkk⟩
      · exfalso
        rw [hc₀nil] at hch
        exact hch rfl
      · exact hh
    rw [hst₁pARR, hc₀nil, afterRunRemoved_bareEmpty hhidp]
  have hst₁ne : ∀ a', a' ≠ p → st₁.piles a' = st.piles a' := by
    intro a' hne'
    obtain ⟨-, p₀, hp₀, hs₁⟩ := step_tabToFound_inv h₁step
    have hpq : p₀ = p := Option.some.inj (hp₀.symm.trans hpox)
    rw [hpq] at hs₁
    rw [hs₁]
    show (if a' = p then
        Pile.afterRunRemoved (st.piles p) (chop (st.piles p).faceUp)
        else st.piles a') = st.piles a'
    rw [if_neg hne']
  -- the pile parcels, as in the seated channel
  have htqmem : x.twin ∈ (st.piles q).faceUp := pileHolding_mem hlochold
  obtain ⟨covrest, hseg⟩ := fromCard_eq_head_of_mem htqmem
  have hjoin : below x.twin (st.piles q).faceUp ++ (x.twin :: covrest)
      = (st.piles q).faceUp := by
    rw [← hseg]
    exact below_join (st.piles q).faceUp
  have hpq : p ≠ q := by
    intro hcon
    have htqmem' : x.twin ∈ (st.piles p).faceUp := by rw [hcon]; exact htqmem
    exact twin_pile_ne hwf htopp htqmem'
  have hkingt : x.twin.rank = Rank.king := by rw [Card.twin_rank]; exact hking
  -- the twin is also king, so no face-up sits below it
  have hbsnil : below x.twin (st.piles q).faceUp = [] := by
    by_cases hbs : below x.twin (st.piles q).faceUp = []
    · exact hbs
    · exfalso
      obtain ⟨z₁, hz₁last⟩ := lastOf_exists hbs
      have hfit₁ : canSitOn x.twin z₁ = true :=
        runOK_join_head_sit _ covrest z₁ x.twin
          (by rw [hjoin]; exact hwf.runOK_of q) hz₁last
      exact (no_fit_king hfit₁) hkingt
  have hhidq : (st.piles q).hidden = [] ∧ x.twin.rank = Rank.king := by
    rcases hseat with hbs | ⟨hh, hkk⟩
    · exfalso
      rw [hbsnil] at hbs
      exact hbs rfl
    · exact ⟨hh, hkk⟩
  -- the twin is covered; the whole face-up of q is the run
  have hcovne : covrest ≠ [] := by
    intro hcovnil
    have htopqq : (st.piles q).top = some x.twin := by
      show lastOf (st.piles q).faceUp = some x.twin
      rw [hbsnil] at hjoin
      rw [hcovnil] at hjoin
      rw [← hjoin]
      exact lastOf_snoc
    exact twin_not_top hwf h₂rung hiff hlochold hseat htopqq
  have hsegeq : (st.piles q).faceUp = x.twin :: covrest := by
    rw [hbsnil] at hjoin
    exact hjoin.symm
  -- STEP 2's record: ba is forced to an empty anchor (kings fit nothing)
  obtain ⟨q₂, hhold₂, hcp₂, hseg₂ne, hs₂⟩ := step_tabToTab_inv h₂step
  have hhold₁ : st₁.pileHolding x.twin = some q :=
    (pileHolding_eq_some_iff hwf₁).2 (by
      rw [hst₁ne q (Ne.symm hpq)]
      exact htqmem)
  rw [pileHolding_inj hhold₂ hhold₁] at hs₂
  rw [show st₁.piles q = st.piles q from hst₁ne q (Ne.symm hpq)] at hs₂
  obtain ⟨m, hbaeq, hmempty⟩ : ∃ m, ba = Sum.inl m ∧ (st₁.piles m).isEmpty = true := by
    cases ba with
    | inl m =>
        obtain ⟨hempty, -⟩ := canPlace_inl hcp₂
        exact ⟨m, rfl, hempty⟩
    | inr y =>
        obtain ⟨k, hpoy, hfitY⟩ := canPlace_inr hcp₂
        exact absurd hkingt (no_fit_king hfitY)
  rw [hbaeq] at hs₂
  -- the vacated pile q empties without a reveal (no hidden), m receives the run
  have hst₁q : st₁.piles q = st.piles q := hst₁ne q (Ne.symm hpq)
  have hmq : m ≠ q := by
    intro hcon
    rw [hcon] at hmempty
    rw [hst₁q] at hmempty
    obtain ⟨-, hful⟩ := (Pile.isEmpty_eq _).mp hmempty
    rw [hsegeq] at hful
    exact absurd hful (List.cons_ne_nil x.twin covrest)
  -- st₂'s shape: m holds the twin's run, q is bare empty
  rw [hbsnil, hseg, afterRunRemoved_bareEmpty hhidq.1] at hs₂
  rw [putRun_eq_inl] at hs₂
  have hst₂exp : st₂ =
      (st₁.setPile q ⟨[], ([] : List Card)⟩).setPile m ⟨[], x.twin :: covrest⟩ :=
    hs₂
  have hst₂m : st₂.piles m = ⟨[], x.twin :: covrest⟩ := by
    rw [hst₂exp, setPile_piles_self]
  have hst₂q : st₂.piles q = ⟨[], ([] : List Card)⟩ := by
    rw [hst₂exp, setPile_piles_ne (show q ≠ m from Ne.symm hmq),
      setPile_piles_self]
  -- STEP 3's record: bb is forced to an empty anchor as well
  obtain ⟨c₃, hft, hc₃x, hcp₃, hs₃⟩ := step_foundToTab_inv h₃step
  obtain ⟨kk, hbbeq, hkempty⟩ : ∃ kk, bb = Sum.inl kk ∧ (st₂.piles kk).isEmpty = true := by
    cases bb with
    | inl kk =>
        obtain ⟨hempty, -⟩ := canPlace_inl hcp₃
        exact ⟨kk, rfl, hempty⟩
    | inr z =>
        obtain ⟨k', hpoz, hfitZ⟩ := canPlace_inr hcp₃
        exact absurd hking (no_fit_king hfitZ)
  rw [hbbeq] at hs₃
  -- kk receives x verbatim; the anchors m and kk are distinct
  have hmkk : m ≠ kk := by
    intro hcon
    rw [← hcon] at hkempty
    rw [hst₂m] at hkempty
    obtain ⟨-, hful⟩ := (Pile.isEmpty_eq _).mp hkempty
    exact absurd hful (List.cons_ne_nil x.twin covrest)
  have hwexp : w =
      (st₂.setFound x.suit (chop (st₂.found x.suit))).setPile kk ⟨[], [x]⟩ := by
    rw [hs₃, putCard_eq_inl]
  have hwkk : w.piles kk = ⟨[], [x]⟩ := by
    rw [hwexp, setPile_piles_self]
  have hwm : w.piles m = st₂.piles m := by
    rw [hwexp, setPile_piles_ne hmkk, setFound_piles]
  -- the founds ride net-flat (the banked loose composite row)
  have hflat : ∀ σ, w.found σ = st.found σ :=
    conjugate_endpoint_netflat ⟨x.twin, ba, bb, st₁, st₂, h₁step, h₂step, h₃step⟩
  refine ⟨m, kk, covrest, hbaeq, hbbeq, hcovne, hkingt, hsegeq, hmkk, hmq, hpq,
    hwfw, hflat, hwm.trans hst₂m, hwkk, ?_⟩
  intro a' hm' hkk'
  constructor
  · rintro (hap | haq)
    · subst hap
      rw [hwexp, setPile_piles_ne hkk', setFound_piles, hst₂exp,
        setPile_piles_ne hm', setPile_piles_ne hpq]
      exact hst₁p
    · subst haq
      rw [hwexp, setPile_piles_ne hkk', setFound_piles, hst₂exp,
        setPile_piles_ne hm', setPile_piles_self]
  · rintro ⟨hpne, hqne⟩
    rw [hwexp, setPile_piles_ne hkk', setFound_piles, hst₂exp,
      setPile_piles_ne hm', setPile_piles_ne hqne]
    exact hst₁ne a' hpne

/-- **THE SEATED-CHANNEL WINDOW** — when the raised card is not a king,
both of its seats are seated: the slide lands the twin's whole run on
the exposed under-card `z₀` of `x`'s own pile `p`, the pull lands `x`
on the exposed under-card `z₁` of the twin's old pile `q` (both bases
forced through the packing pin), and every other pile returns verbatim. -/
private theorem s_conj_window_seated {st w : State} {x : Card} {p q : Anchor}
    {st₁ st₂ : State} {ba bb : Base}
    (hwf : st.WF)
    (h₁step : st.step (Move.tabToFound x) = some st₁)
    (h₂step : st₁.step (Move.tabToTab x.twin ba) = some st₂)
    (h₃step : st₂.step (Move.foundToTab x bb) = some w)
    (hking : x.rank ≠ Rank.king)
    (hiff : ∀ c, CanRaise st c ↔ c = x)
    (h₂rung : rungAt st x.twin.suit = x.rank.toIdx)
    (hpox : st.pileOfTop x = some p)
    (hlochold : st.pileHolding x.twin = some q)
    (hseat : TwinSeat st x q) :
    ∃ z₀ z₁ covrest,
      ba = Sum.inr z₀ ∧ bb = Sum.inr z₁ ∧ z₀ ≠ z₁ ∧
      covrest ≠ [] ∧
      canSitOn x z₀ = true ∧ canSitOn x.twin z₁ = true ∧
      chop (st.piles p).faceUp ≠ [] ∧
      lastOf (chop (st.piles p).faceUp) = some z₀ ∧
      below x.twin (st.piles q).faceUp ≠ [] ∧
      lastOf (below x.twin (st.piles q).faceUp) = some z₁ ∧
      (st.piles q).faceUp = below x.twin (st.piles q).faceUp ++ (x.twin :: covrest) ∧
      w.WF ∧
      (∀ σ, w.found σ = st.found σ) ∧
      w.piles p = ⟨(st.piles p).hidden,
        chop (st.piles p).faceUp ++ (x.twin :: covrest)⟩ ∧
      w.piles q = ⟨(st.piles q).hidden,
        below x.twin (st.piles q).faceUp ++ [x]⟩ ∧
      (∀ a', a' ≠ p → a' ≠ q → w.piles a' = st.piles a') := by
  -- x's own seat off the iff: the king disjunct dies, so x is seated
  have hseatx : chop (st.piles p).faceUp ≠ [] ∨
      ((st.piles p).hidden = [] ∧ x.rank = Rank.king) := by
    obtain ⟨-, a, hpoa, hs⟩ := (hiff x).2 rfl
    rw [pileOfTop_inj hpoa hpox] at hs
    exact hs
  have htopp : (st.piles p).top = some x := (pileOfTop_eq_some_iff hwf).mp hpox
  have hc₀ne : chop (st.piles p).faceUp ≠ [] := by
    rcases hseatx with hch | ⟨-, hkk⟩
    · exact hch
    · exact absurd hkk hking
  have hfullp : (st.piles p).faceUp = chop (st.piles p).faceUp ++ [x] :=
    lastOf_chop (show lastOf (st.piles p).faceUp = some x from htopp)
  obtain ⟨z₀, hz₀last, hfitz₀⟩ := seated_top_under hwf htopp hc₀ne
  have hz₀mem : z₀ ∈ (st.piles p).faceUp := by
    rw [hfullp]
    exact List.mem_append.mpr (Or.inl (lastOf_mem hz₀last))
  -- WF travels
  have hwf₁ : st₁.WF := step_wf hwf h₁step
  have hwf₂ : st₂.WF := step_wf hwf₁ h₂step
  have hwfw : w.WF := step_wf hwf₂ h₃step
  -- pile q's parcel: the twin's segment and under-seat
  have htqmem : x.twin ∈ (st.piles q).faceUp := pileHolding_mem hlochold
  obtain ⟨covrest, hseg⟩ := fromCard_eq_head_of_mem htqmem
  have hjoin : below x.twin (st.piles q).faceUp ++ (x.twin :: covrest)
      = (st.piles q).faceUp := by
    rw [← hseg]
    exact below_join (st.piles q).faceUp
  have hsegne : x.twin :: covrest ≠ ([] : List Card) :=
    List.cons_ne_nil x.twin covrest
  have hbsne : below x.twin (st.piles q).faceUp ≠ [] := by
    rcases hseat with hbs | ⟨-, hkingt⟩
    · exact hbs
    · rw [Card.twin_rank] at hkingt
      exact absurd hkingt hking
  have hcovne : covrest ≠ [] := by
    intro hcovnil
    rw [hcovnil] at hseg
    have htopqq : (st.piles q).top = some x.twin := by
      show lastOf (st.piles q).faceUp = some x.twin
      rw [← hjoin, hcovnil]
      exact lastOf_snoc
    exact twin_not_top hwf h₂rung hiff hlochold hseat htopqq
  obtain ⟨z₁, hz₁last⟩ := lastOf_exists hbsne
  have hfit₁ : canSitOn x.twin z₁ = true :=
    runOK_join_head_sit _ covrest z₁ x.twin
      (by rw [hjoin]; exact hwf.runOK_of q) hz₁last
  have hpq : p ≠ q := by
    intro hcon
    have htqmem' : x.twin ∈ (st.piles p).faceUp := by rw [hcon]; exact htqmem
    exact twin_pile_ne hwf htopp htqmem'
  have hz₁memq : z₁ ∈ (st.piles q).faceUp := below_mem (lastOf_mem hz₁last)
  have hzz : z₀ ≠ z₁ := by
    intro hcon
    have hxz := (mem_faceUp_unique hwf hz₀mem q (Ne.symm hpq)).1
    rw [hcon] at hxz
    exact hxz hz₁memq
  -- the st₁ pile reads: p rewritten, everything else verbatim
  have hst₁pARR : st₁.piles p =
      Pile.afterRunRemoved (st.piles p) (chop (st.piles p).faceUp) := by
    obtain ⟨-, p₀, hp₀, hs₁⟩ := step_tabToFound_inv h₁step
    have hpqq : p₀ = p := Option.some.inj (hp₀.symm.trans hpox)
    rw [hpqq] at hs₁
    rw [hs₁]
    show (if p = p then
        Pile.afterRunRemoved (st.piles p) (chop (st.piles p).faceUp)
        else st.piles p) =
      Pile.afterRunRemoved (st.piles p) (chop (st.piles p).faceUp)
    rw [if_pos rfl]
  have hst₁ne : ∀ a', a' ≠ p → st₁.piles a' = st.piles a' := by
    intro a' hne'
    obtain ⟨-, p₀, hp₀, hs₁⟩ := step_tabToFound_inv h₁step
    have hpqq : p₀ = p := Option.some.inj (hp₀.symm.trans hpox)
    rw [hpqq] at hs₁
    rw [hs₁]
    show (if a' = p then
        Pile.afterRunRemoved (st.piles p) (chop (st.piles p).faceUp)
        else st.piles a') = st.piles a'
    rw [if_neg hne']
  -- STEP 2's record, located at st's lists (only pile p changed so far)
  obtain ⟨q₂, hhold₂, hcp₂, hseg₂ne, hs₂⟩ := step_tabToTab_inv h₂step
  have hhold₁ : st₁.pileHolding x.twin = some q :=
    (pileHolding_eq_some_iff hwf₁).2 (by
      rw [hst₁ne q (Ne.symm hpq)]
      exact htqmem)
  rw [pileHolding_inj hhold₂ hhold₁] at hs₂
  rw [show st₁.piles q = st.piles q from hst₁ne q (Ne.symm hpq)] at hs₂
  -- THE BASE PIN: ba is the exposed (x+1) under x
  have hbaz₀ : ba = Sum.inr z₀ := by
    cases ba with
    | inl m =>
        obtain ⟨-, hkingt⟩ := canPlace_inl hcp₂
        rw [Card.twin_rank] at hkingt
        exact absurd hkingt hking
    | inr y =>
        obtain ⟨k, hpoy, hfitY⟩ := canPlace_inr hcp₂
        have hfitXy : canSitOn x y = true := by
          obtain ⟨hrk, hcol⟩ := (canSitOn_eq x.twin y).mp hfitY
          rw [show x.twin.rank.toIdx = x.rank.toIdx from rfl] at hrk
          rw [show x.twin.suit.color = x.suit.color from
            Suit.color_twin x.suit] at hcol
          exact (canSitOn_eq x y).2 ⟨hrk, hcol⟩
        rcases conjugate_fit_pin hfitz₀ hfit₁ hzz hfitXy with hy | hy
        · exact congrArg Sum.inr hy
        · exfalso
          rw [hy] at hpoy
          have htopk : (st₁.piles k).top = some z₁ :=
            (pileOfTop_eq_some_iff hwf₁).mp hpoy
          by_cases hkq : k = q
          · rw [hkq, hst₁ne q (Ne.symm hpq)] at htopk
            have hlastq : lastOf (below x.twin (st.piles q).faceUp
                ++ (x.twin :: covrest)) = some z₁ := by
              rw [hjoin]
              exact htopk
            have hlastseg : lastOf (x.twin :: covrest) = some z₁ :=
              lastOf_append (x.twin :: covrest) hsegne z₁ hlastq
            have hz₁seg : z₁ ∈ x.twin :: covrest := lastOf_mem hlastseg
            have hnd : (below x.twin (st.piles q).faceUp
                ++ (x.twin :: covrest)).Nodup := by
              rw [hjoin]; exact runOK_nodup (hwf.runOK_of q)
            exact nodup_append_notmem hnd (lastOf_mem hz₁last) hz₁seg
          · by_cases hkp : k = p
            · rw [hkp, hst₁pARR, afterRunRemoved_ne hc₀ne] at htopk
              have hlastz₁ : lastOf (chop (st.piles p).faceUp) = some z₁ := htopk
              exact hzz (Option.some.inj (hz₀last.symm.trans hlastz₁))
            · rw [hst₁ne k (fun hc => hkp hc)] at htopk
              have hz₁k : z₁ ∈ (st.piles k).faceUp := Pile.mem_of_top htopk
              exact (mem_faceUp_unique hwf hz₁memq k (fun hc => hkq hc)).1 hz₁k
  rw [hbaz₀] at hs₂
  -- the intermediate search: z₀ still tops pile p, nothing else tops it
  have hpoz₀ : (st₁.setPile q (Pile.afterRunRemoved (st.piles q)
      (below x.twin (st.piles q).faceUp))).pileOfTop z₀ = some p := by
    refine firstWhere_find (Anchor.mem_all p) ?_ ?_
    · show decide (((st₁.setPile q (Pile.afterRunRemoved (st.piles q)
            (below x.twin (st.piles q).faceUp))).topOf p) = some z₀) = true
      rw [setPile_topOf_ne hpq]
      show decide ((st₁.piles p).top = some z₀) = true
      rw [hst₁pARR, afterRunRemoved_ne hc₀ne]
      exact decide_eq_true (show ({ st.piles p with
        faceUp := chop (st.piles p).faceUp } : Pile).top = some z₀ from hz₀last)
    · intro y _hy hyne
      show decide (((st₁.setPile q (Pile.afterRunRemoved (st.piles q)
            (below x.twin (st.piles q).faceUp))).topOf y) = some z₀) = false
      by_cases hyq : y = q
      · rw [hyq]
        show decide (((st₁.setPile q (Pile.afterRunRemoved (st.piles q)
              (below x.twin (st.piles q).faceUp))).piles q).top = some z₀) = false
        rw [setPile_piles_self, afterRunRemoved_ne hbsne]
        have htopz₁ : ({ st.piles q with
            faceUp := below x.twin (st.piles q).faceUp } : Pile).top = some z₁ :=
          hz₁last
        rw [htopz₁]
        exact decide_false_of_not
          (fun hcon => hzz (Option.some.inj hcon).symm)
      · rw [setPile_topOf_ne hyq]
        show decide ((st₁.piles y).top = some z₀) = false
        rw [hst₁ne y hyne]
        exact decide_false_of_not (fun htop =>
          (mem_faceUp_unique hwf hz₀mem y hyne).1 (Pile.mem_of_top htop))
  -- st₂'s pile profile: p holds the twin's run, q keeps its under-seat
  have hst₂p : st₂.piles p =
      ⟨(st.piles p).hidden,
        chop (st.piles p).faceUp ++ (x.twin :: covrest)⟩ := by
    rw [hs₂, putRun_inr_eq hpoz₀, setPile_piles_self,
      setPile_piles_ne (show p ≠ q from hpq),
      hst₁pARR, hseg, afterRunRemoved_ne hc₀ne]
  have hst₂q : st₂.piles q =
      ⟨(st.piles q).hidden, below x.twin (st.piles q).faceUp⟩ := by
    rw [hs₂, putRun_inr_eq hpoz₀,
      setPile_piles_ne (show q ≠ p from Ne.symm hpq), setPile_piles_self,
      afterRunRemoved_ne hbsne]
  have hst₂ne : ∀ a', a' ≠ p → a' ≠ q → st₂.piles a' = st.piles a' := by
    intro a' hne' hne'q
    rw [hs₂, putRun_inr_eq hpoz₀,
      setPile_piles_ne (show a' ≠ p from hne'),
      setPile_piles_ne (show a' ≠ q from hne'q),
      hst₁ne a' hne']
  -- STEP 3's record and THE SECOND BASE PIN: bb is the twin's exposed base
  obtain ⟨c₃, hft₂, hc'x, hcp₃, hs₃⟩ := step_foundToTab_inv h₃step
  have hbbz₁ : bb = Sum.inr z₁ := by
    cases bb with
    | inl kk =>
        obtain ⟨-, hkk⟩ := canPlace_inl hcp₃
        exact absurd hkk hking
    | inr zz =>
        obtain ⟨k, hpozz, hfitZZ⟩ := canPlace_inr hcp₃
        rcases conjugate_fit_pin hfitz₀ hfit₁ hzz hfitZZ with hzz₀ | hzz₁
        · exfalso
          rw [hzz₀] at hpozz
          have htopk : (st₂.piles k).top = some z₀ :=
            (pileOfTop_eq_some_iff hwf₂).mp hpozz
          by_cases hkq : k = q
          · rw [hkq, hst₂q] at htopk
            have h1 : lastOf (below x.twin (st.piles q).faceUp) = some z₁ :=
              hz₁last
            have h2 : lastOf (below x.twin (st.piles q).faceUp) = some z₀ :=
              htopk
            exact hzz (Option.some.inj (h1.symm.trans h2)).symm
          · by_cases hkp : k = p
            · rw [hkp, hst₂p] at htopk
              have hlastseg : lastOf (x.twin :: covrest) = some z₀ :=
                lastOf_append (x.twin :: covrest) hsegne z₀ htopk
              have hz₀seg : z₀ ∈ x.twin :: covrest := lastOf_mem hlastseg
              exact (mem_faceUp_unique hwf hz₀mem q (Ne.symm hpq)).1
                (fromCard_mem (by rw [hseg]; exact hz₀seg))
            · rw [hst₂ne k hkp (fun hc => hkq hc)] at htopk
              exact (mem_faceUp_unique hwf hz₀mem k hkp).1 (Pile.mem_of_top htopk)
        · exact congrArg Sum.inr hzz₁
  rw [hbbz₁] at hs₃
  -- z₁ tops pile q at st₂, so the pulled-back card lands verbatim on it
  have hpoz₁ : st₂.pileOfTop z₁ = some q :=
    (pileOfTop_eq_some_iff hwf₂).2 (by
      show (st₂.piles q).top = some z₁
      rw [hst₂q]
      exact hz₁last)
  have hwexp : w = (st₂.setFound x.suit (chop (st₂.found x.suit))).setPile q
      { st₂.piles q with faceUp := (st₂.piles q).faceUp ++ [x] } := by
    rw [hs₃]
    exact putCard_inr_eq
      (st := st₂.setFound x.suit (chop (st₂.found x.suit)))
      (show (st₂.setFound x.suit (chop (st₂.found x.suit))).pileOfTop z₁
          = some q from hpoz₁)
  have hwq : w.piles q =
      ⟨(st.piles q).hidden, below x.twin (st.piles q).faceUp ++ [x]⟩ := by
    rw [hwexp, setPile_piles_self, hst₂q]
  have hwp : w.piles p = st₂.piles p := by
    rw [hwexp, setPile_piles_ne (show p ≠ q from hpq)]
    rfl
  have hwne : ∀ a', a' ≠ p → a' ≠ q → w.piles a' = st.piles a' := by
    intro a' hne' hne'q
    rw [hwexp, setPile_piles_ne (show a' ≠ q from hne'q)]
    exact hst₂ne a' hne' hne'q
  -- the founds ride net-flat (the banked loose composite row)
  have hflat : ∀ σ, w.found σ = st.found σ :=
    conjugate_endpoint_netflat ⟨x.twin, ba, bb, st₁, st₂, h₁step, h₂step, h₃step⟩
  exact ⟨z₀, z₁, covrest, hbaz₀, hbbz₁, hzz, hcovne, hfitz₀, hfit₁, hc₀ne,
    hz₀last, hbsne, hz₁last, hjoin.symm, hwfw, hflat, hwp.trans hst₂p, hwq,
    hwne⟩

/-! ## §6. The junk gate's two channels, closed -/

/-- **THE BARE-EMPTY JUNK KILL** — the non-pair card raising off a
fully emptied seat cannot ride a class-preserving composite: the
letter empties pile `p` completely and no later leg can arrive at it
(the slide and the pull need a topped base, and the junk card was no
king), so `p` is fully empty at `w`; the backward class witness then
runs the pillar play-lift — `p` must be empty or king-headed at `st` —
but the raise's own record has it `[x]`-topped at a non-king over no
hidden deck. -/
private theorem s_conj_junk_bareEmpty {st w : State} {x : Card} {p : Anchor}
    (_hwf : st.WF) (hw : sameOrbitSetoid.r st w)
    (hsteps : ∃ ba bb st₁ st₂,
      st.step (Move.tabToFound x) = some st₁ ∧
      st₁.step (Move.tabToTab x.twin ba) = some st₂ ∧
      st₂.step (Move.foundToTab x bb) = some w)
    (hp : st.pileOfTop x = some p)
    (hch : chop (st.piles p).faceUp = [])
    (hhh : (st.piles p).hidden = [])
    (hk : x.rank ≠ Rank.king) : False := by
  obtain ⟨ba, bb, st₁, st₂, h₁step, h₂step, h₃step⟩ := hsteps
  -- the raise empties pile p completely
  obtain ⟨hnextx, p₀, hpox, hs₁⟩ := step_tabToFound_inv h₁step
  have hp₀ : p₀ = p := Option.some.inj (hpox.symm.trans hp)
  rw [hp₀] at hs₁
  have hst₁pARR : st₁.piles p =
      Pile.afterRunRemoved (st.piles p) (chop (st.piles p).faceUp) := by
    rw [hs₁]
    show (if p = p then
        Pile.afterRunRemoved (st.piles p) (chop (st.piles p).faceUp)
        else st.piles p) =
      Pile.afterRunRemoved (st.piles p) (chop (st.piles p).faceUp)
    rw [if_pos rfl]
  have hst₁p : st₁.piles p = ⟨[], ([] : List Card)⟩ := by
    rw [hst₁pARR, hch, afterRunRemoved_bareEmpty hhh]
  -- step 2's record: the twin rides from Asrc, and p is not it (p is
  -- fully empty at st₁, so it cannot hold the sliding twin)
  obtain ⟨Asrc, hhold, hcp₂, hfr, hs₂⟩ := step_tabToTab_inv h₂step
  have hsrcne : p ≠ Asrc := by
    intro hcon
    have hmem : x.twin ∈ (st₁.piles Asrc).faceUp := pileHolding_mem hhold
    rw [← hcon] at hmem
    rw [hst₁p] at hmem
    exact absurd hmem (by simp)
  have hmidp : (st₁.setPile Asrc (Pile.afterRunRemoved (st₁.piles Asrc)
      (below x.twin ((st₁.piles Asrc).faceUp)))).piles p
        = ⟨[], ([] : List Card)⟩ := by
    rw [setPile_piles_ne hsrcne]
    exact hst₁p
  -- step 2 leaves p fully empty: an inl arrival needs a king, an inr
  -- arrival needs a topped pile, and p tops nothing
  have hst₂p : st₂.piles p = ⟨[], ([] : List Card)⟩ := by
    rw [hs₂]
    cases ba with
    | inl k =>
        have hkne : p ≠ k := by
          intro hcon
          obtain ⟨-, hkingt⟩ := canPlace_inl hcp₂
          exact absurd hkingt (by rw [Card.twin_rank]; exact hk)
        rw [putRun_eq_inl, setPile_piles_ne hkne]
        exact hmidp
    | inr z =>
        cases hz : (st₁.setPile Asrc (Pile.afterRunRemoved (st₁.piles Asrc)
            (below x.twin ((st₁.piles Asrc).faceUp)))).pileOfTop z with
        | none =>
            rw [putRun_inr_none hz]
            exact hmidp
        | some kk =>
            rw [putRun_inr_eq hz]
            have hkkne : p ≠ kk := by
              intro hcon
              obtain ⟨hfu, -⟩ := pileOfTop_top hz
              rw [← hcon] at hfu
              rw [hmidp] at hfu
              exact absurd hfu (by simp)
            rw [setPile_piles_ne hkkne]
            exact hmidp
  -- step 3's record: the pull's landing is barred from p the same way
  obtain ⟨c₃, hft, hc₃x, hcp₃, hs₃⟩ := step_foundToTab_inv h₃step
  have hwp : w.piles p = ⟨[], ([] : List Card)⟩ := by
    rw [hs₃]
    cases bb with
    | inl k =>
        have hkne : p ≠ k := by
          intro hcon
          obtain ⟨-, hkingin⟩ := canPlace_inl hcp₃
          exact absurd hkingin hk
        rw [putCard_eq_inl, setPile_piles_ne hkne, setFound_piles]
        exact hst₂p
    | inr z =>
        cases hz : (st₂.setFound x.suit (chop (st₂.found x.suit))).pileOfTop z with
        | none =>
            have hid : (st₂.setFound x.suit (chop (st₂.found x.suit))).putCard x
                (Sum.inr z) = st₂.setFound x.suit (chop (st₂.found x.suit)) := by
              simp only [State.putCard, hz]
            rw [hid, setFound_piles]
            exact hst₂p
        | some kk =>
            rw [putCard_inr_eq hz]
            have hkkne : p ≠ kk := by
              intro hcon
              obtain ⟨hfu, -⟩ := pileOfTop_top hz
              rw [← hcon] at hfu
              rw [setFound_piles, hst₂p] at hfu
              exact absurd hfu (by simp)
            rw [setPile_piles_ne hkkne, setFound_piles]
            exact hst₂p
  -- the backward class witness: p fully empty at w stays empty-or-king-headed
  -- through the witness play, so it would be so at st — against the record
  obtain ⟨σ, hσ, -, -⟩ := hw
  have hrun : State.run w σ = some st := ShufflePlayW_run hσ
  have hQw : (w.piles p).faceUp = [] ∧ (w.piles p).hidden = [] := by
    rw [hwp]
    exact ⟨rfl, rfl⟩
  have hQst := emptyOrKingHead_play' w σ st (Or.inl hQw) hrun
  obtain ⟨hfu, hlast⟩ := pileOfTop_top hp
  have hfull : (st.piles p).faceUp = [] ++ [x] := by
    have h2 := lastOf_chop hlast
    rw [hch] at h2
    exact h2
  rcases hQst with ⟨hfe, -⟩ | ⟨K, t, hfup, hK, -⟩
  · rw [hfe] at hfu
    exact absurd rfl hfu
  · rw [hfup] at hfull
    injection hfull with hKx _
    rw [hKx] at hK
    exact hk hK

/-- **THE LETTER'S CARD IS THE WITNESS** — at a maneuver-stable
forkState, a class-preserving firing of the conjugate letter raises
exactly the detection's own witness: junk channels die against the
orbit gate (the reveal channel by the hidden totals, the bare-empty
channel by the pillar gate above), the covered twin cannot top (its
own parcel), and the vanilla iff names raisers uniquely.  The row
also emits the st-side parcel the production consumes: the re-anchored
S-iff, both rung pins, the vanilla iff, and the S-census premise. -/
theorem s_conjugate_letter {st w : State} {x u : Card}
    (hwf : st.WF)
    (hS : ∀ c, (c = u ∨ c = u.twin) ↔ CanRaiseS st c)
    (hnt : ¬ CanRaise st u.twin)
    (hw : sameOrbitSetoid.r st w)
    (hsteps : ∃ ba bb st₁ st₂,
      st.step (Move.tabToFound x) = some st₁ ∧
      st₁.step (Move.tabToTab x.twin ba) = some st₂ ∧
      st₂.step (Move.foundToTab x bb) = some w) :
    x = u ∧
    (∀ c, (c = x ∨ c = x.twin) ↔ CanRaiseS st c) ∧
    (rungAt st x.suit = x.rank.toIdx) ∧
    (rungAt st x.twin.suit = x.rank.toIdx) ∧
    (∀ c, CanRaise st c ↔ c = x) ∧
    (∀ c, ¬(c = x ∨ c = x.twin) → ¬ CanRaiseS st c) := by
  obtain ⟨ba, bb, st₁, st₂, h₁step, h₂step, h₃step⟩ := hsteps
  obtain ⟨hnextx, p, hpox, -⟩ := step_tabToFound_inv h₁step
  -- the weak-side bridge rows, from the S-parcel alone
  have huiff : ∀ c, CanRaise st c ↔ c = u := by
    obtain ⟨vu, hru, hvrt, hiff⟩ :
        ∃ x : Card, rungAt st x.suit = x.rank.toIdx ∧
          rungAt st x.twin.suit = x.rank.toIdx ∧
          (∀ c, CanRaise st c ↔ c = x) :=
      forkState_to_weak hwf ⟨u, hS, hnt⟩
    have hcru : CanRaise st u := forkState_witness_canRaise hwf hS hnt
    have hu : u = vu := (hiff u).1 hcru
    rw [hu]
    exact hiff
  -- THE JUNK GATE: outside the pair the raise digs or bare-empties
  have hpair : x = u ∨ x = u.twin := by
    rcases Decidable.em (x = u ∨ x = u.twin) with hpr | hcon
    · exact hpr
    · exfalso
      have hnox : ¬ CanRaise st x := fun h => hcon (Or.inl ((huiff x).1 h))
      rcases Decidable.em (chop (st.piles p).faceUp = []) with hch | hch
      · rcases Decidable.em ((st.piles p).hidden = []) with hh | hh
        · rcases Decidable.em (x.rank = Rank.king) with hk | hk
          · exact hnox ⟨hnextx, p, hpox, Or.inr ⟨hh, hk⟩⟩
          · exact s_conj_junk_bareEmpty hwf hw
              ⟨ba, bb, st₁, st₂, h₁step, h₂step, h₃step⟩ hpox hch hh hk
        · -- the reveal channel: the composite digs, the class pins
          have hA : hiddenTotal st₁ + 1 ≤ hiddenTotal st :=
            hiddenTotal_step_tabToFound_reveal h₁step hpox hch hh
          have hB : hiddenTotal st₂ ≤ hiddenTotal st₁ := hiddenTotal_step h₂step
          have hC : hiddenTotal w ≤ hiddenTotal st₂ := hiddenTotal_step h₃step
          obtain ⟨σ, -, τ, hτ⟩ := hw
          have hsum : hiddenTotal w = hiddenTotal st :=
            hiddenTotal_congr (shuffle_hiddenPinned hτ)
          omega
      · exact hnox ⟨hnextx, p, hpox, Or.inl hch⟩
  rcases hpair with hxu | hxut
  · -- the witness side: re-anchor the parcel at x
    rw [← hxu] at hS hnt huiff
    refine ⟨hxu, hS, ?_, ?_, huiff, ?_⟩
    · exact canRaiseS_rung ((hS x).mp (Or.inl rfl))
    · have hr := canRaiseS_rung ((hS x.twin).mp (Or.inr rfl))
      rwa [Card.twin_rank] at hr
    · intro c hcp hSC
      rcases (hS c).mpr hSC with hce | hct
      · exact hcp (Or.inl hce)
      · exact hcp (Or.inr hct)
  · -- the twin side: the covered twin cannot top the record's pile
    exfalso
    rw [hxut] at hpox
    have hSCanT : CanRaiseS st u.twin := (hS u.twin).mp (Or.inr rfl)
    obtain ⟨a, bs, run, hloc, hshape, hseat, -⟩ :=
      s_conjugate_twin_parcel hwf hSCanT hnt
    have hm : u.twin ∈ (st.piles p).faceUp :=
      Pile.mem_of_top ((pileOfTop_eq_some_iff hwf).mp hpox)
    have hpa : p = a :=
      pileHolding_inj ((pileHolding_eq_some_iff hwf).2 hm) hloc
    -- the seat package in TwinSeat form
    have hnd : (bs ++ u.twin :: run).Nodup := by
      rw [← hshape]
      exact runOK_nodup (hwf.runOK_of a)
    have hcNbs : u.twin ∉ bs := nodup_mid_notmem u.twin bs run hnd
    have hseatTS : TwinSeat st u a := by
      rcases hseat with hbs | hhk
      · refine Or.inl ?_
        rw [hshape, below_append_stop hcNbs]
        exact hbs
      · exact Or.inr hhk
    have hrung : rungAt st u.twin.suit = u.rank.toIdx := by
      have hr := canRaiseS_rung hSCanT
      rwa [Card.twin_rank] at hr
    have htp : (st.piles a).top = some u.twin := by
      rw [← hpa]
      exact (pileOfTop_eq_some_iff hwf).mp hpox
    exact twin_not_top hwf hrung huiff hloc hseatTS htp

/-! ## §8. THE CENSUS RESIDUE — the window's non-pair transport

The one-leg census transfer (`S_census_one_leg` in the S-transfer
card) rides a single reversible slide; the conjugate window is a
three-leg composite whose middle leg carries the WHOLE twin segment,
so the transfer does not apply verbatim.  The route below is priced;
both channel rows are the file's named residue.

ROUTE (king channel): a `CanRaiseS w c` unfolds through
`canRaiseS_iff` into nextUp, position, seat, and the twin-topping
read.  The nextUp read transports verbatim (the window's founds ride
net-flat).  The position cases: on the landing anchors `m` (the twin's
run) and `kk` (`[x]`) the card rides with the run — c ∈ covrest sits
in q's segment at `st`, covered there by its own `covrest`-tail with
the twin-topping read recovered at `st`'s `q`-top; on the emptied
`p`/`q` piles no card sits (membership kills); untouched piles
transfer verbatim (the license reassembles at `st` through
`canRaiseS_iff`'s sufficiency and dies against the st-side S-iff).  The
twin-topping sub-cases at `w`'s two changed tops (`m`'s run-top, `kk`)
either name the pair (killed) or reassemble at `st` as the `q`-top
(the `bowtie` kill for twins sharing the run's pile rides
`twin_pile_ne`).

ROUTE (seated channel): same skeleton with the two z-bases: the b = p
twin-topping case dies against the twins-share-a-pile law
(`twin_pile_ne` at `w` when c rode to p; at `st` when the c-below part
holds), the b = q cases name `x`, and the untouched/covered transports
ride `below_append_notmem` and the chop-shaped seats. -/

/-- **THE CENSUS, KING CHANNEL — the window's non-pair transport
(residue, routed above).** -/
private theorem s_conj_census_king {st w : State} {x : Card} {p q : Anchor}
    {st₁ st₂ : State} {ba bb : Base}
    (hwf : st.WF)
    (h₁step : st.step (Move.tabToFound x) = some st₁)
    (h₂step : st₁.step (Move.tabToTab x.twin ba) = some st₂)
    (h₃step : st₂.step (Move.foundToTab x bb) = some w)
    (hking : x.rank = Rank.king)
    (hSx : ∀ c, (c = x ∨ c = x.twin) ↔ CanRaiseS st c)
    (hiff : ∀ c, CanRaise st c ↔ c = x)
    (hpox : st.pileOfTop x = some p)
    (hlochold : st.pileHolding x.twin = some q)
    (hseatTS : TwinSeat st x q) :
    ∀ c, ¬(c = x ∨ c = x.twin) → ¬ CanRaiseS w c := by
  sorry

/-- **THE CENSUS, SEATED CHANNEL — the window's non-pair transport
(residue, routed above).** -/
private theorem s_conj_census_seated {st w : State} {x : Card} {p q : Anchor}
    {st₁ st₂ : State} {ba bb : Base}
    (hwf : st.WF)
    (h₁step : st.step (Move.tabToFound x) = some st₁)
    (h₂step : st₁.step (Move.tabToTab x.twin ba) = some st₂)
    (h₃step : st₂.step (Move.foundToTab x bb) = some w)
    (hking : x.rank ≠ Rank.king)
    (hSx : ∀ c, (c = x ∨ c = x.twin) ↔ CanRaiseS st c)
    (hiff : ∀ c, CanRaise st c ↔ c = x)
    (hpox : st.pileOfTop x = some p)
    (hlochold : st.pileHolding x.twin = some q)
    (hseatTS : TwinSeat st x q) :
    ∀ c, ¬(c = x ∨ c = x.twin) → ¬ CanRaiseS w c := by
  sorry

/-- The wrap: the pair's licenses plus the census make the detection. -/
private theorem s_conj_wrap {w : State} {x : Card}
    (hSwx : CanRaiseS w x) (hSwtx : CanRaiseS w x.twin)
    (hntw : ¬ CanRaise w x.twin)
    (hcensw : ∀ c, ¬(c = x ∨ c = x.twin) → ¬ CanRaiseS w c) :
    forkState w := by
  refine ⟨x, fun c => ⟨fun hc => ?_, fun hSc => ?_⟩, hntw⟩
  · rcases hc with rfl | rfl
    · exact hSwx
    · exact hSwtx
  · rcases Decidable.em (c = x ∨ c = x.twin) with hor | hor
    · exact hor
    · exact absurd hSc (hcensw c hor)

/-! ## §7. The endpoint's pin and the twin's free, per channel -/

/-- **THE KING CHANNEL'S ENDPOINT PARCEL** — the pair's two S-licenses
(at the endpoint `w`: `x` vanilla-live by the relic, the twin covered
by its own ride-along run over its king seat = the bare channel), the
orientation pin (the buried twin cannot lift), and the census residue
hook. -/
private theorem s_conj_assemble_king {st w : State} {x : Card} {p q : Anchor}
    {st₁ st₂ : State} {ba bb : Base}
    (hwf : st.WF)
    (h₁step : st.step (Move.tabToFound x) = some st₁)
    (h₂step : st₁.step (Move.tabToTab x.twin ba) = some st₂)
    (h₃step : st₂.step (Move.foundToTab x bb) = some w)
    (hking : x.rank = Rank.king)
    (hSx : ∀ c, (c = x ∨ c = x.twin) ↔ CanRaiseS st c)
    (hiff : ∀ c, CanRaise st c ↔ c = x)
    (hpox : st.pileOfTop x = some p)
    (hlochold : st.pileHolding x.twin = some q)
    (hseatTS : TwinSeat st x q) :
    (CanRaiseS w x ∧ CanRaiseS w x.twin ∧ ¬ CanRaise w x.twin) ∧
    (∀ c, ¬(c = x ∨ c = x.twin) → ¬ CanRaiseS w c) := by
  obtain ⟨m, kk, covrest, -, -, hcovne, hkingt, hsegeq, hmkk, hmq, hpq, hwfw,
    hflat, hwm, hwkk, hwots⟩ :=
    s_conj_window_king hwf h₁step h₂step h₃step hking hiff
      (canRaiseS_rung ((hSx x.twin).mp (Or.inr rfl)) |>.trans (by rw [Card.twin_rank]))
      hpox hlochold hseatTS
  -- the relic: x re-licenses at w, so it tops somewhere
  obtain ⟨hCRwx, -⟩ := conjugate_relic hwf ⟨ba, bb, st₁, st₂, h₁step, h₂step, h₃step⟩
  obtain ⟨ax, hxpo⟩ : ∃ a, w.pileOfTop x = some a := by
    obtain ⟨-, a, hpo, -⟩ := id hCRwx
    exact ⟨a, hpo⟩
  -- the twin's nextUp transports through the net-flat ride
  have hL2 : (st.found x.twin.suit).length = x.twin.rank.toIdx :=
    canRaiseS_rung ((hSx x.twin).mp (Or.inr rfl))
  have hnextT : w.nextUp x.twin = true := by
    show decide (x.twin.rank.toIdx = (w.found x.twin.suit).length) = true
    rw [hflat x.twin.suit, hL2]
    exact decide_eq_true rfl
  -- THE TWIN'S FREE: covered by its own run over the bare king anchor
  have hxtop : w.pileOfTop (x.twin).twin ≠ none := by
    rw [Card.twin_twin]
    intro hcon
    rw [hcon] at hxpo
    exact absurd hxpo (by simp)
  have hshapeM : (w.piles m).faceUp = [] ++ x.twin :: covrest := by
    rw [hwm]
    exact rfl
  have htwfree : CanRaiseS w x.twin :=
    (canRaiseS_iff hwfw).2
      ⟨hnextT, m, [], covrest, hshapeM,
        Or.inr ⟨by rw [hwm], hkingt⟩,
        Or.inr hxtop⟩
  -- THE PIN: the twin cannot lift at the endpoint
  have hntw : ¬ CanRaise w x.twin := by
    rintro ⟨-, a', hpo', -⟩
    have htopa : (w.piles a').top = some x.twin :=
      (pileOfTop_eq_some_iff hwfw).mp hpo'
    rcases Decidable.em (a' = m) with ham | ham
    · rw [ham] at htopa
      rw [hwm] at htopa
      have h8 : runOK (x.twin :: covrest) = true := by
        have h77 := hwfw.runOK_of m
        rw [hwm] at h77
        exact h77
      have hndw : (x.twin :: covrest).Nodup := runOK_nodup h8
      have h10 : lastOf (x.twin :: covrest) = some x.twin := htopa
      rw [lastOf_cons_tail hcovne] at h10
      exact (List.nodup_cons.mp hndw).1 (lastOf_mem h10)
    · rcases Decidable.em (a' = kk) with hkk' | hkk'
      · rw [hkk'] at htopa
        rw [hwkk] at htopa
        have h11 : lastOf ([x] : List Card) = some x.twin := htopa
        exact card_twin_ne x (Option.some.inj h11).symm
      · rcases Decidable.em (a' = p ∨ a' = q) with hpq' | hpq'
        · have hwpile := (hwots a' ham hkk').1 hpq'
          obtain ⟨hfuE, -⟩ := pileOfTop_top hpo'
          rw [hwpile] at hfuE
          exact hfuE rfl
        · have hwpile := (hwots a' ham hkk').2
            ⟨fun hc => hpq' (Or.inl hc), fun hc => hpq' (Or.inr hc)⟩
          rw [hwpile] at htopa
          have hmemST : x.twin ∈ (st.piles a').faceUp :=
            Pile.mem_of_top htopa
          have hqhold : st.pileHolding x.twin = some a' :=
            (pileHolding_eq_some_iff hwf).2 hmemST
          exact hpq' (Or.inr (pileHolding_inj hlochold hqhold).symm)
  refine ⟨⟨CanRaiseS.now x hCRwx, htwfree, hntw⟩, ?_⟩
  -- THE CENSUS: the residue hook, routed below
  exact s_conj_census_king hwf h₁step h₂step h₃step hking hSx hiff hpox
    hlochold hseatTS

/-- **THE SEATED CHANNEL'S ENDPOINT PARCEL** — the pair's two
S-licenses (x vanilla-live by the relic; the twin covered by its
ride-along run, seated on x's old under-seat content), the pin, and
the census hook. -/
private theorem s_conj_assemble_seated {st w : State} {x : Card} {p q : Anchor}
    {st₁ st₂ : State} {ba bb : Base}
    (hwf : st.WF)
    (h₁step : st.step (Move.tabToFound x) = some st₁)
    (h₂step : st₁.step (Move.tabToTab x.twin ba) = some st₂)
    (h₃step : st₂.step (Move.foundToTab x bb) = some w)
    (hking : x.rank ≠ Rank.king)
    (hSx : ∀ c, (c = x ∨ c = x.twin) ↔ CanRaiseS st c)
    (hiff : ∀ c, CanRaise st c ↔ c = x)
    (hpox : st.pileOfTop x = some p)
    (hlochold : st.pileHolding x.twin = some q)
    (hseatTS : TwinSeat st x q) :
    (CanRaiseS w x ∧ CanRaiseS w x.twin ∧ ¬ CanRaise w x.twin) ∧
    (∀ c, ¬(c = x ∨ c = x.twin) → ¬ CanRaiseS w c) := by
  obtain ⟨z₀, z₁, covrest, -, -, hzz, hcovne, hfitz₀, hfit₁, hc₀ne, hz₀last,
    hbsne, hz₁last, -, hwfw, hflat, hwpf, hwqf, hwne⟩ :=
    s_conj_window_seated hwf h₁step h₂step h₃step hking hiff
      (canRaiseS_rung ((hSx x.twin).mp (Or.inr rfl)) |>.trans (by rw [Card.twin_rank]))
      hpox hlochold hseatTS
  have hsegne : x.twin :: covrest ≠ ([] : List Card) :=
    List.cons_ne_nil x.twin covrest
  -- the relic
  obtain ⟨hCRwx, -⟩ := conjugate_relic hwf ⟨ba, bb, st₁, st₂, h₁step, h₂step, h₃step⟩
  obtain ⟨ax, hxpo⟩ : ∃ a, w.pileOfTop x = some a := by
    obtain ⟨-, a, hpo, -⟩ := id hCRwx
    exact ⟨a, hpo⟩
  have hL2 : (st.found x.twin.suit).length = x.twin.rank.toIdx :=
    canRaiseS_rung ((hSx x.twin).mp (Or.inr rfl))
  have hnextT : w.nextUp x.twin = true := by
    show decide (x.twin.rank.toIdx = (w.found x.twin.suit).length) = true
    rw [hflat x.twin.suit, hL2]
    exact decide_eq_true rfl
  -- THE TWIN'S FREE: covered by its run, seated on x's old chop
  have hxtop : w.pileOfTop (x.twin).twin ≠ none := by
    rw [Card.twin_twin]
    intro hcon
    rw [hcon] at hxpo
    exact absurd hxpo (by simp)
  have hshapeP : (w.piles p).faceUp =
      chop (st.piles p).faceUp ++ (x.twin :: covrest) := by
    rw [hwpf]
  have htwfree : CanRaiseS w x.twin :=
    (canRaiseS_iff hwfw).2
      ⟨hnextT, p, chop (st.piles p).faceUp, covrest, hshapeP, Or.inl hc₀ne,
        Or.inr hxtop⟩
  -- THE PIN
  have hntw : ¬ CanRaise w x.twin := by
    rintro ⟨-, a', hpo', -⟩
    have htopa : (w.piles a').top = some x.twin :=
      (pileOfTop_eq_some_iff hwfw).mp hpo'
    rcases Decidable.em (a' = p) with hap | hap
    · rw [hap] at htopa
      rw [hwpf] at htopa
      have h77 : runOK (chop (st.piles p).faceUp ++ x.twin :: covrest) = true := by
        have h8 := hwfw.runOK_of p
        rw [hwpf] at h8
        exact h8
      have hnd : ((chop (st.piles p).faceUp ++ [x.twin]) ++ covrest).Nodup := by
        rw [List.append_assoc]
        exact runOK_nodup h77
      have hmem1 : x.twin ∈ chop (st.piles p).faceUp ++ [x.twin] :=
        List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
      have hlast : lastOf (x.twin :: covrest) = some x.twin :=
        lastOf_append _ hsegne x.twin htopa
      rw [lastOf_cons_tail hcovne] at hlast
      exact nodup_append_notmem hnd hmem1 (lastOf_mem hlast)
    · rcases Decidable.em (a' = q) with haq | haq
      · rw [haq] at htopa
        rw [hwqf] at htopa
        have hxlast : lastOf ([x] : List Card) = some x.twin :=
          lastOf_append _ (List.cons_ne_nil x []) x.twin htopa
        exact card_twin_ne x (Option.some.inj hxlast).symm
      · have hwpile : w.piles a' = st.piles a' := hwne a' hap haq
        rw [hwpile] at htopa
        have hmemST : x.twin ∈ (st.piles a').faceUp :=
          Pile.mem_of_top htopa
        have hqhold : st.pileHolding x.twin = some a' :=
          (pileHolding_eq_some_iff hwf).2 hmemST
        exact haq (pileHolding_inj hlochold hqhold).symm
  refine ⟨⟨CanRaiseS.now x hCRwx, htwfree, hntw⟩, ?_⟩
  exact s_conj_census_seated hwf h₁step h₂step h₃step hking hSx hiff hpox
    hlochold hseatTS

/-! ## §9. The main row -/

/-- **THE S-GRADE CONJUGATE PRODUCTION** — the physical-swap composite
of a maneuver-stable forkState produces a forkState at the endpoint:
the letter's raised card is the detection's own witness (the orbit
gate's two junk channels are closed — the reveal channel by the
hidden totals against the class pin, the bare-empty channel by the
first-refill-is-a-king pillar), the endpoint's pair re-licenses at the
S grade (the witness vanilla-live by the relic; the twin covered by
its own ride-along run, seated on the witness's old seat content or
the bare-king corner), the orientation pin holds (the buried twin
cannot lift), and the census keeps every other card S-dead. -/
theorem forkState_conjugate_S {st w : State}
    (h : forkState st) (hwf : st.WF)
    (hc : conjugateForkState st w)
    (hw : sameOrbitSetoid.r st w) :
    forkState w := by
  obtain ⟨u, hS, hnt⟩ := h
  obtain ⟨x, ba, bb, st₁, st₂, -, h₁s, h₂s, h₃s⟩ := hc
  -- the letter's card and the st-side parcel
  obtain ⟨-, hSx, h₁rung, h₂rung, hiff, hcens⟩ :=
    s_conjugate_letter hwf hS hnt hw ⟨ba, bb, st₁, st₂, h₁s, h₂s, h₃s⟩
  have hSCanT : CanRaiseS st x.twin := (hSx x.twin).mp (Or.inr rfl)
  have hntx : ¬ CanRaise st x.twin := fun hcr =>
    card_twin_ne x ((hiff x.twin).1 hcr)
  obtain ⟨q, bsl, run, hlochold, hshp, hseatiff, -⟩ :=
    s_conjugate_twin_parcel hwf hSCanT hntx
  have hndq : (bsl ++ x.twin :: run).Nodup := by
    have h9 := runOK_nodup (hwf.runOK_of q)
    rw [hshp] at h9
    exact h9
  have hcNbs : x.twin ∉ bsl := nodup_mid_notmem x.twin bsl run hndq
  have hseatTS : TwinSeat st x q := by
    rcases hseatiff with hbs | hhk
    · refine Or.inl ?_
      rw [hshp, below_append_stop hcNbs]
      exact hbs
    · exact Or.inr hhk
  -- the raise's own pile record
  obtain ⟨-, p, hpox, -⟩ := step_tabToFound_inv h₁s
  -- the channel assembly
  rcases Decidable.em (x.rank = Rank.king) with hking | hking
  · obtain ⟨⟨hSwx, hSwtx, hntw⟩, hcensw⟩ :=
      s_conj_assemble_king hwf h₁s h₂s h₃s hking hSx hiff hpox hlochold hseatTS
    exact s_conj_wrap hSwx hSwtx hntw hcensw
  · obtain ⟨⟨hSwx, hSwtx, hntw⟩, hcensw⟩ :=
      s_conj_assemble_seated hwf h₁s h₂s h₃s hking hSx hiff hpox hlochold hseatTS
    exact s_conj_wrap hSwx hSwtx hntw hcensw

/-! ## The audit battery

`#print axioms` per fresh head.  The proved sections carry only
`[propext, Quot.sound]`; the main row carries `sorryAx` through the two
named census rows — the file's single, routed residue:

* `s_conj_census_king` — the king channel's non-pair transport;
* `s_conj_census_seated` — the seated channel's non-pair transport.

Everything else — the letter-pins, the orbit-grade junk gate (both
channels), the pillar block, both window packages, both channel
assemblies — is sorry-free. -/

#print axioms s_conjugate_twin_parcel
#print axioms s_conjugate_letter
#print axioms s_conj_census_king
#print axioms s_conj_census_seated
#print axioms s_conj_assemble_king
#print axioms s_conj_assemble_seated
#print axioms s_conj_wrap
#print axioms forkState_conjugate_S

/- APPEND-MARKER -/