import Orig.PairName

/-!
# Orig.ForkAscent — THE GREEDY SLIDE-STACK ASCENT (forks as exhaustion shapes)

The formalization of the owner's script-claim in the EXHAUSTION
semantics: *from a state below a reachable fork's fork point, greedily
stacking — never founding either member of an intact twin pair,
stacking all the other stuff until none is stackable — the exhaustion
state IS the fork shape: the stuckness is the saturation.*

Why exhaustion beats halt-triggering (v1's design, corrected by the
owner): a run that merely STOPS when twins are detected must still
argue the rest of the board is blocked.  A run that stacks EVERYTHING
ELSE UNTIL IT CANNOT has manufactured the fork's saturation as its own
termination analysis — the only cards left S-live at exhaustion are
guarded pair members, which is literally the `ForkWitness` iff.  No
defusing hypothesis survives.

The claim's anatomy (each piece a definition below):

* **§0 THE VOCABULARY** — the full-time no-eat guard (`MobileTwin`,
  `AscentMove`), the run relation, the exhaustion read (`AscentStuck`),
  and the DELIVERED SHAPE (`TwinSlideHalt`, no longer a trigger: it is
  what the exhaustion must produce — a double-hot intact pair with the
  cover seat fit).
* **§1 THE ORIENTATION ASSEMBLY** (assembled at the orientation pass:
  two of three arms PROVED — the snap (the state itself is the fork
  whenever the twin is not vanilla-live) and the cover slide (the
  one-move geometric restore makes each saturation iff-half a single
  `CanRaiseS.via` prepend, the covered twin carrying the pin); the
  sole survivor is the NAMED BARE-COVER CORNER
  `orientation_barecover_corner` [M-mini] — the first-faced cover
  whose named slide commits (reveal/burn), priced with the
  resurrection mode in its docstring, never forced).
* **§2 THE EXHAUSTION ROW** (restructured at the exhaustion-shrink
  pass: the row's own body is pure assembly over three named pieces
  — `ascent_climb_delivery` [H-mini], `ascent_stuck_saturation`
  [H-mini], `ascent_cover_read` [H-mini] — plus the BANKED
  STUCKNESS COLLAPSE `ascent_stuck_collapse`, proved here: at a
  stuck state every `via` leg is a refused slide, so `CanRaiseS`
  collapses to `CanRaise`; the leg-stuck ⇒ S-stuck bridge's proved
  half is in).  The main claim: from a below-frontier start whose
  reachable fork's pair members are already mobile, every ascent
  run to leg-exhaustion delivers the shape: an intact double-hot
  pair, S-saturation (`CanRaiseS` iff the pair), a fitting mobile
  cover — hence a fork one slide away (§1 assembles it).

Owner-phrase-to-conjunct map (the `pullEscape` lesson: every
hypothesis load-bearing and documented):

* "don't stack either of them" — the NO-EAT GUARD is FULL-TIME, not a
  halt condition: `AscentMove`'s raise arm declines any member of any
  intact mobile twin pair, at every state along the way.
* "stack other stuff until none is possible" — the END is exhaustion,
  not detection: `AscentStuck` reads "no guarded stackable move is
  legal" (raises and arrangement slides alike); "possible" is graded
  in the §2 route as the SLIDE-AWARE possibility (`CanRaiseS`, the
  program's own {slide · raise} grade): a card raisable after slides
  counts as possible, and the leg-stuck ⇒ S-stuck bridge is the
  row's named hard content.
* "will surely reach a fork state" — confluence grade: EVERY
  exhausted run delivers the shape.
* "below the fork point" (`hbelow`) — the two suits of the reachable
  fork's family sit at-or-below its rank at the start, and BOTH PAIR
  MEMBERS ARE MOBILE AT THE START (face-up).  The mobility premise is
  load-bearing and closes the reveal-gap: a deck whose target pair is
  hidden at the start is fork-reachable only through reveal-commits,
  which the stacking process never performs — no slides or raises of
  the script surface hidden cards — so the claim does not cover it.
  (The fourth suit floats, unconditioned: forks pin only their two
  family suits.)

House compliance: additive leaf (`import Orig.PairName`); definitions
statement-facing; both residues carry complete routes; fresh heads
audited.  Decidability note: all §0 predicates are finite enumerations
over `Card.universe`/`Anchor.all` in the pattern of
`Orig/ForkStateSB.lean`'s `forkStateSB` decider.
-/

/-! ## §0. The vocabulary -/

/-- **THE DOUBLE-HOT READ** — a card and its twin are both face-up on
the tableau, each sitting exactly at its own suit's frontier (each is
that suit's next-up card).  Neither member can be founded at this
configuration: founding is index-exact. -/
def DoubleHot (st : State) (x : Card) : Prop :=
  ∃ (a b : Anchor),
    x ∈ (st.piles a).faceUp ∧
      x.twin ∈ (st.piles b).faceUp ∧
      x.rank.toIdx = st.foundHeight x.suit ∧
      x.twin.rank.toIdx = st.foundHeight x.twin.suit

/-- **THE INTACT-PAIR MOBILITY READ** — `c` pairs with a mobile twin:
`c` and `c.twin` are both face-up and both unfounded, so founding
either member would kill that pair's fork forever.  The guard below
declines any raise of any member of any intact mobile pair. -/
def MobileTwin (st : State) (c : Card) : Prop :=
  (∃ (a : Anchor), c ∈ (st.piles a).faceUp) ∧
    c.rank.toIdx ≥ st.foundHeight c.suit ∧
    (∃ (b : Anchor), c.twin ∈ (st.piles b).faceUp) ∧
    c.twin.rank.toIdx ≥ st.foundHeight c.twin.suit

/-- **THE ASCENT STEP** — the script's full-time stacking discipline
at `st`: either a RAISE of a hot, face-up card that is NOT a member of
any intact mobile twin pair (the no-eat guard, full-time), or a SLIDE
(the arrangement move: expose buried raisables, free seats, open
cover lanes).  The script never pulls (unstacking is the sibling
descent program). -/
def AscentMove (st : State) (m : Move) : Prop :=
  (∃ (c : Card),
      m = Move.tabToFound c ∧
        c.rank.toIdx = st.foundHeight c.suit ∧
        (∃ (a : Anchor), c ∈ (st.piles a).faceUp) ∧
        ∀ (y : Card), MobileTwin st y → c ≠ y ∧ c ≠ y.twin) ∨
  (∃ (c : Card) (b : Base), m = Move.tabToTab c b)

/-- **THE ASCENT RUN** — a finite sequence of ascent steps. -/
inductive AscentRun : State → List Move → State → Prop
  | nil (st : State) : AscentRun st [] st
  | cons {st : State} {m : Move} {s' W : State} {ρ : List Move}
      (hm : AscentMove st m) (hstep : State.step st m = some s')
      (hrest : AscentRun s' ρ W) :
      AscentRun st (m :: ρ) W

/-- **THE EXHAUSTION READ** — the owner's "until none is possible":
no ascent move is legal at `st` (raises and slides alike).  THIS IS
THE ONLY END: the process has no detection-based trigger; it runs
until stuck. -/
def AscentStuck (st : State) : Prop :=
  ∀ (m : Move), AscentMove st m → State.step st m = none

/-- **THE DELIVERED SHAPE** — what an exhaustion state must produce
(the shape the v1 design mistook for a trigger): a double-hot intact
pair together with a fitting, mobile, unfounded COVER — one cargo
slide `tabToTab d (inr x.twin)` away from the covered-twin
orientation. -/
def TwinSlideHalt (st : State) : Prop :=
  ∃ (x d : Card),
    DoubleHot st x ∧
      d.rank.toIdx + 1 = x.rank.toIdx ∧
      d.suit.color ≠ x.suit.color ∧
      d.rank.toIdx ≥ st.foundHeight d.suit ∧
      (∃ (c : Anchor), d ∈ (st.piles c).faceUp) ∧
      canSitOn d x.twin = true

/-! ## §0b. The assembly kit (private, per-file copies)

The house dedup discipline: the four list/geometry rows below are
this file's private copies of the kit families other chapters carry
(`Orig/ForkStateS.lean`, `Orig/Integrity.lean`); the orientation row
consumes them at the letter grade. -/

/-- A list member splits positionally (the cons-split extraction the
positional pile decompositions ride). -/
private theorem ascent_mem_split {x : Card} : ∀ (l : List Card), x ∈ l →
    ∃ t1 t2, l = t1 ++ x :: t2 := by
  intro l
  induction l with
  | nil => intro h; exact absurd h (by simp)
  | cons y t ih =>
      intro h
      rcases List.mem_cons.mp h with heq | hm
      · rw [heq]
        exact ⟨[], t, rfl⟩
      · obtain ⟨t1, t2, hs⟩ := ih hm
        exact ⟨y :: t1, t2, by rw [hs, List.cons_append]⟩

/-- A mid-run nodup bar: no element of the snoc-before-position
repeats in the prefix (relativized to a rest suffix). -/
private theorem ascent_nodup_mid_notmem (d : Card) :
    ∀ (l rest : List Card), (l ++ d :: rest).Nodup → d ∉ l := by
  intro l
  induction l with
  | nil => intro rest _ hm; exact absurd hm (by simp)
  | cons v vs ih =>
      intro rest hnd hm
      rcases List.mem_cons.mp hm with heq | hin
      · subst heq
        exact absurd (List.mem_append.mpr (Or.inr (List.mem_cons_self ..)))
          (List.nodup_cons.mp hnd).1
      · exact ih rest (List.nodup_cons.mp hnd).2 hin

/-- The `fromCard` mid-run split: the run from a card not in the
prefix starts at the card's position. -/
private theorem ascent_fromCard_mid (c : Card) :
    ∀ (l rest : List Card), c ∉ l →
      fromCard c (l ++ c :: rest) = c :: rest := by
  intro l
  induction l with
  | nil => intro rest _; rw [List.nil_append]; exact fromCard_head_eq
  | cons y t ih =>
      intro rest hnu
      have hyt : y ≠ c := by
        intro hcon
        exact hnu (by rw [hcon]; exact List.mem_cons_self ..)
      rw [List.cons_append,
        show fromCard c (y :: (t ++ c :: rest))
            = fromCard c (t ++ c :: rest) from fromCard_cons_ne _ hyt]
      exact ih rest (fun hcon => hnu (List.mem_cons.mpr (Or.inr hcon)))

/-- The `below` companion: the prefix strictly below a card not in
the list's earlier part. -/
private theorem ascent_below_stop (c : Card) :
    ∀ (l rest : List Card), c ∉ l → below c (l ++ c :: rest) = l := by
  intro l
  induction l with
  | nil =>
      intro rest _
      show below c (c :: rest) = []
      rw [below_cons, ite_eq_left rfl]
  | cons y t ih =>
      intro rest hnu
      have hyt : y ≠ c := by
        intro hcon
        exact hnu (by rw [hcon]; exact List.mem_cons_self ..)
      rw [List.cons_append, below_cons, ite_eq_right hyt]
      exact congrArg (y :: ·) (ih rest (fun hcon => hnu (List.mem_cons.mpr (Or.inr hcon))))

/-- A twin is never its own card (the copy of the kit row). -/
private theorem ascent_card_twin_ne (c : Card) : c.twin ≠ c := by
  intro hcon
  exact Suit.twin_ne c.suit (congrArg Card.suit hcon)

/-- The adjacent-fit base: the run starting at the pair itself. -/
private theorem ascent_runOK_adjacent_base (c e : Card) : ∀ (R : List Card),
    runOK ([] ++ c :: e :: R) = true → canSitOn e c = true := by
  intro R h
  cases R with
  | nil =>
      rw [show runOK ([] ++ c :: e :: []) =
          (canSitOn e c && true) from rfl, Bool.and_eq_true] at h
      exact h.1
  | cons u R' =>
      rw [show runOK ([] ++ c :: e :: u :: R') =
          (canSitOn e c && runOK (e :: u :: R')) from rfl, Bool.and_eq_true] at h
      exact h.1

/-- An adjacent fitted pair anywhere in a legal run fits (the run's
descent discipline; the copy of the kit row). -/
private theorem ascent_runOK_adjacent_fit (c e : Card) :
    ∀ (X R : List Card), runOK (X ++ c :: e :: R) = true →
      canSitOn e c = true := by
  intro X
  induction X with
  | nil => intro R h; exact ascent_runOK_adjacent_base c e R h
  | cons w t ih =>
      intro R h
      cases t with
      | nil =>
          rw [show runOK ((w :: []) ++ c :: e :: R) =
              (canSitOn c w && runOK (([]) ++ c :: e :: R)) from rfl,
            Bool.and_eq_true] at h
          exact ascent_runOK_adjacent_base c e R h.2
      | cons u t' =>
          rw [show runOK ((w :: u :: t') ++ c :: e :: R) =
              (canSitOn u w && runOK ((u :: t') ++ c :: e :: R)) from rfl,
            Bool.and_eq_true] at h
          exact ih R h.2

/-- Cards above a legal run's head sit strictly below the head in
rank (the copy of the `runOK_head_gt` kit row). -/
private theorem ascent_runOK_head_gt : ∀ {t : List Card} {v e : Card},
    runOK (v :: t) = true → e ∈ t → e.rank.toIdx < v.rank.toIdx := by
  intro t
  induction t with
  | nil => intro v e _ hm; cases hm
  | cons w t' ih =>
      intro v e h hm
      rw [show runOK (v :: w :: t') = (canSitOn w v && runOK (w :: t')) from rfl,
        Bool.and_eq_true] at h
      rcases List.mem_cons.mp hm with heq | hin
      · rw [heq]
        have hwv := (canSitOn_eq w v).mp h.1
        omega
      · have hwv := (canSitOn_eq w v).mp h.1
        have hew := ih (v := w) h.2 hin
        omega

/-! ## §1b. The already-oriented snap -/

/-- **THE SNAP** — the orientation row's trivial arm, isolated: when
the covered side's vanilla license already fails at `W`, the state
itself is the fork; the parcel's saturation clause is the hypothesis
verbatim and the failed license is the pin.  (The twin-flipped
orientation's iff is the same pair read through `Card.twin_twin`.) -/
private theorem ascent_snap {W : State} {x : Card}
    (hsat : ∀ (c : Card), (c = x ∨ c = x.twin) ↔ CanRaiseS W c)
    (hnc : ¬ CanRaise W x.twin) :
    ∃ (F : State) (τ : List Move) (x' : Card),
      W.run τ = some F ∧ ForkWitness F x' := by
  exact ⟨W, [], x, rfl, hsat, hnc⟩

/-! ## §1c. The cover-slide assembly (both licenses live, cover seated) -/

/-- **THE PREFIX-TAIL RUN ROW** (private kit): the run below any
position of a legal run is legal. -/
private theorem ascent_runOK_prefix : ∀ (l rest : List Card),
    runOK (l ++ rest) = true → runOK rest = true := by
  intro l
  induction l with
  | nil => intro rest h; exact h
  | cons v t ih =>
      intro rest h
      exact ih rest (runOK_cons_tail (show runOK (v :: (t ++ rest)) = true from h))

/-- **THE TOP-SEARCH HELPER** (private kit): the anchored top-search
resolves a card that tops one named pile and no other. -/
private theorem ascent_topSearch (st : State) {zm : Card} {hb : Anchor}
    (htopb : (st.piles hb).top = some zm)
    (hbar : ∀ y ∈ Anchor.all, y ≠ hb → (st.piles y).top ≠ some zm) :
    st.pileOfTop zm = some hb := by
  show firstWhere (fun a₂ => decide (st.topOf a₂ = some zm)) Anchor.all = some hb
  refine firstWhere_find (Anchor.mem_all hb) ?_ ?_
  · show decide ((st.piles hb).top = some zm) = true
    rw [htopb]
    exact decide_eq_true rfl
  · intro y hy hyne
    show decide ((st.piles y).top = some zm) = false
    exact decide_false_of_not (hbar y hy hyne)


/-- The last of an appended nonempty suffix is the suffix's last
(the `lastOf` kit row for the append reads). -/
private theorem ascent_lastOf_append : ∀ (l m : List Card), m ≠ [] →
    lastOf (l ++ m) = lastOf m := by
  intro l
  induction l with
  | nil => intro m _; rfl
  | cons u t ih =>
      intro m hm
      cases m with
      | nil => exact absurd rfl hm
      | cons w ws =>
          cases t with
          | nil => rfl
          | cons v s => exact ih (w :: ws) hm

/-- A put-run keeps the two-zone cycle (the copy of the zone kit row). -/
private theorem ascent_putRun_zone (s : State) (run : List Card) (b : Base) :
    (s.putRun run b).stock = s.stock ∧ (s.putRun run b).waste = s.waste ∧
    (s.putRun run b).drawStep = s.drawStep := by
  cases b with
  | inl n => exact ⟨rfl, rfl, rfl⟩
  | inr zm =>
      simp only [State.putRun]
      split <;> exact ⟨rfl, rfl, rfl⟩

/-- **THE COVER-SLIDE ASSEMBLY** (private): the orientation row's main
arm — at a state whose saturation is exactly the pair, when the
twin's vanilla license holds (it tops its pile) and the fitting
cover `d` sits with under-content in its own pile, the ONE cargo
slide `tabToTab d (inr x.twin)` lands the full `ForkWitness` parcel.

ROUTE (each step banked or this file's kit above):

1. THE FORWARD SLIDE — `d`'s holding search (`pileHolding_eq_some_iff`)
   and the twin's top seat give legality (`canPlace_inr_located`);
   the successor is the two-pile write.
2. THE ONE-MOVE RESTORE — the twin's exposed under-card `z` (the last
   of `d`'s under-content) re-fits `d` by the run discipline
   (`ascent_runOK_adjacent_fit`), and sliding the moved run back onto
   the exposed pile-`a` top restores every field exactly: the
   back-slide is legal at the successor AND lands on `W` outright.
3. THE SATURATION TRANSFER — with both one-move facts in hand, each
   iff-half is a single `CanRaiseS.via` prepend (the grade is the
   {slide · raise} closure by construction, so class-mates' S-sets
   are equal); the delivered iff needs nothing else.
4. THE PIN — at the slid state the twin is covered by the run's
   head, still resides in its pile alone (WF uniqueness), and the
   run is nonempty, so the twin tops no pile and the vanilla license
   fails there. -/
private theorem ascent_cover_slide_fork {W : State} (hwf : W.WF)
    {x d : Card}
    (hsat : ∀ (c : Card), (c = x ∨ c = x.twin) ↔ CanRaiseS W c)
    (hrank : d.rank.toIdx + 1 = x.rank.toIdx)
    (hdxt : d ≠ x.twin)
    (hctt : CanRaise W x.twin)
    (hfit : canSitOn d x.twin = true)
    {a : Anchor} {L₁ L₂ : List Card}
    (hspl : (W.piles a).faceUp = L₁ ++ d :: L₂)
    (hpre : L₁ ≠ []) :
    ∃ (F : State) (τ : List Move) (x' : Card),
      W.run τ = some F ∧ ForkWitness F x' := by
  -- the twin's topped pile, off the vanilla license
  obtain ⟨-, k, hk, -⟩ := hctt
  have hktwin : (W.piles k).top = some x.twin :=
    (pileOfTop_eq_some_iff hwf).1 hk
  have hmemT : x.twin ∈ (W.piles k).faceUp := Pile.mem_of_top hktwin
  obtain ⟨frontK, hfrontk⟩ : ∃ f, (W.piles k).faceUp = f ++ [x.twin] :=
    Pile.top_eq_lastOf_iff.mp hktwin
  -- the cover's residence and the nodup discipline
  have hmemD : d ∈ (W.piles a).faceUp := by
    rw [hspl]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
  have hdhold : W.pileHolding d = some a := (pileHolding_eq_some_iff hwf).2 hmemD
  have hndface : (L₁ ++ d :: L₂).Nodup := by
    have h := runOK_nodup (hwf.2.1 a)
    rw [hspl] at h
    exact h
  have hdL₁ : d ∉ L₁ := ascent_nodup_mid_notmem d L₁ L₂ hndface
  have hbel : below d ((W.piles a).faceUp) = L₁ := by
    rw [hspl]
    exact ascent_below_stop d L₁ L₂ hdL₁
  have hfrom : fromCard d ((W.piles a).faceUp) = d :: L₂ := by
    rw [hspl]
    exact ascent_fromCard_mid d L₁ L₂ hdL₁
  -- the twin's pile is not the cover's pile (a shared pile would put
  -- the run above the twin, and the descent discipline prices that
  -- impossible)
  have hka : k ≠ a := by
    intro hcon
    subst hcon
    cases L₂ with
    | nil =>
        have htopT : lastOf ((W.piles k).faceUp) = some x.twin := hktwin
        rw [hspl, lastOf_snoc] at htopT
        exact hdxt (Option.some.inj htopT)
    | cons w t =>
        have hxtin : x.twin ∈ w :: t := by
          have hLastT : lastOf ((W.piles k).faceUp) = some x.twin := hktwin
          rw [hspl, ascent_lastOf_append L₁ (d :: w :: t) (by simp)] at hLastT
          exact lastOf_mem hLastT
        have hrk := ascent_runOK_prefix L₁ (d :: w :: t)
          (by rw [← hspl]; exact hwf.2.1 k)
        have hgt := ascent_runOK_head_gt hrk hxtin
        rw [Card.twin_rank] at hgt
        omega
  -- the forward slide: legality and successor
  have hcan : W.canPlace d (Sum.inr x.twin) = true := by
    rw [canPlace_inr_located hk]
    exact hfit
  have hstepf : State.step W (Move.tabToTab d (Sum.inr x.twin)) = some
      ((W.setPile a (Pile.afterRunRemoved (W.piles a) L₁)).putRun (d :: L₂)
        (Sum.inr x.twin)) := by
    show (match W.pileHolding d with
      | none => none
      | some a₂ =>
          if W.canPlace d (Sum.inr x.twin) then
            match fromCard d ((W.piles a₂).faceUp) with
            | [] => none
            | run => some ((W.setPile a₂
                (Pile.afterRunRemoved (W.piles a₂)
                  (below d ((W.piles a₂).faceUp)))).putRun run (Sum.inr x.twin))
          else none) = _
    rw [hdhold]
    simp only [canPlace_inr_located hk, hfit]
    rw [hfrom, hbel]
    rfl
  -- the mid-state and the successor's pile reads
  have hmida : (W.setPile a (Pile.afterRunRemoved (W.piles a) L₁)).piles a
      = ⟨(W.piles a).hidden, L₁⟩ := by
    rw [setPile_piles_self, afterRunRemoved_ne hpre]
  obtain ⟨z, hzla⟩ := lastOf_exists hpre
  have hzmem : z ∈ (W.piles a).faceUp := by
    have hzlmem : z ∈ L₁ := lastOf_mem hzla
    rw [hspl]
    exact List.mem_append.mpr (Or.inl hzlmem)
  have hzxt : z ≠ x.twin := fun hcon =>
    (mem_faceUp_unique hwf hmemT a (fun h => hka h.symm)).1
      (hcon ▸ hzmem)
  have hzsit : canSitOn d z = true := by
    obtain ⟨preZ, hsplZ⟩ := lastOf_eq_snoc hzla
    refine ascent_runOK_adjacent_fit z d preZ L₂ ?_
    have hr := hwf.2.1 a
    rw [hspl, hsplZ] at hr
    rw [List.append_assoc, List.singleton_append] at hr
    exact hr
  have hmidx : (W.setPile a (Pile.afterRunRemoved (W.piles a) L₁)).pileOfTop
      x.twin = some k := by
    refine ascent_topSearch _ (by rw [setPile_piles_ne hka]; exact hktwin) ?_
    intro y hy hyne
    by_cases hya : y = a
    · have hmidtop : ((W.setPile a (Pile.afterRunRemoved (W.piles a) L₁)).piles a).top
          ≠ some x.twin := by
        rw [hmida]
        show lastOf L₁ ≠ some x.twin
        intro hcon
        exact hzxt (Option.some.inj (hcon.symm.trans hzla)).symm
      rw [hya]
      exact hmidtop
    · rw [setPile_piles_ne hya]
      exact fun hcon =>
        (mem_faceUp_unique hwf hmemT y hyne).1 (Pile.mem_of_top hcon)
  obtain ⟨F, hsF, hFexp⟩ : ∃ F, State.step W (Move.tabToTab d (Sum.inr x.twin))
      = some F ∧ F = (W.setPile a (Pile.afterRunRemoved (W.piles a) L₁)).putRun
        (d :: L₂) (Sum.inr x.twin) := ⟨_, hstepf, rfl⟩
  have hwfF : F.WF := step_wf hwf hsF
  have hhin : a ≠ k := fun h => hka h.symm
  have hmidb : (W.setPile a (Pile.afterRunRemoved (W.piles a) L₁)).piles k
      = W.piles k := setPile_piles_ne hka
  have hFa : F.piles a = ⟨(W.piles a).hidden, L₁⟩ := by
    rw [hFexp, putRun_inr_eq hmidx, setPile_piles_ne hhin, hmida]
  have hFk : F.piles k
      = ⟨(W.piles k).hidden, (W.piles k).faceUp ++ (d :: L₂)⟩ := by
    rw [hFexp, putRun_inr_eq hmidx, setPile_piles_self, hmidb]
  have hFo : ∀ y, y ≠ a → y ≠ k → F.piles y = W.piles y := by
    intro y hya hyk
    rw [hFexp, putRun_piles_inr_ne _ _ _ k hmidx hyk, setPile_piles_ne hya]
  -- the back-slide at the successor, landing exactly W
  have hkn : d ∉ (W.piles k).faceUp :=
    fun hm => (mem_faceUp_unique hwf hmemD k hka).1 hm
  have hknF : d ∉ frontK ++ [x.twin] := by
    have hz := hkn
    rw [hfrontk] at hz
    exact hz
  have hFkshape : (F.piles k).faceUp = (frontK ++ [x.twin]) ++ (d :: L₂) := by
    have h1 : (F.piles k).faceUp = (W.piles k).faceUp ++ (d :: L₂) := by
      rw [hFk]
    rw [h1, hfrontk]
  have hbelF : below d ((F.piles k).faceUp) = frontK ++ [x.twin] := by
    rw [hFkshape]
    exact ascent_below_stop d (frontK ++ [x.twin]) L₂ hknF
  have hfromF : fromCard d ((F.piles k).faceUp) = d :: L₂ := by
    rw [hFkshape]
    exact ascent_fromCard_mid d (frontK ++ [x.twin]) L₂ hknF
  have hdholdF : F.pileHolding d = some k := by
    refine (pileHolding_eq_some_iff hwfF).2 ?_
    rw [hFkshape]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
  have htopFa : (F.piles a).top = some z := by
    rw [hFa]
    exact hzla
  have hpotFz : F.pileOfTop z = some a :=
    (pileOfTop_eq_some_iff hwfF).2 htopFa
  have hcanF : F.canPlace d (Sum.inr z) = true := by
    rw [canPlace_inr_located hpotFz]
    exact hzsit
  have hstepb : State.step F (Move.tabToTab d (Sum.inr z)) = some
      ((F.setPile k (Pile.afterRunRemoved (F.piles k) (frontK ++ [x.twin]))).putRun
        (d :: L₂) (Sum.inr z)) := by
    show (match F.pileHolding d with
      | none => none
      | some a₂ =>
          if F.canPlace d (Sum.inr z) then
            match fromCard d ((F.piles a₂).faceUp) with
            | [] => none
            | run => some ((F.setPile a₂
                (Pile.afterRunRemoved (F.piles a₂)
                  (below d ((F.piles a₂).faceUp)))).putRun run (Sum.inr z))
          else none) = _
    rw [hdholdF]
    simp only [canPlace_inr_located hpotFz, hzsit]
    rw [hfromF, hbelF]
    rfl
  have hbasek : frontK ++ [x.twin] ≠ [] := by
    intro hc
    have hx : x.twin ∈ frontK ++ [x.twin] := by rw [← hfrontk]; exact hmemT
    rw [hc] at hx
    exact absurd hx (by simp)
  -- the twin never rides the cover's deck
  have hxtfk : x.twin ∉ frontK := fun hcon =>
    ascent_nodup_mid_notmem x.twin frontK []
      (by have h := runOK_nodup (hwf.2.1 k); rw [hfrontk] at h; exact h) hcon
  have hxtL₂ : x.twin ∉ L₂ := fun hcon =>
    (mem_faceUp_unique hwf hmemT a (fun h => hka h.symm)).1
      (by rw [hspl]
          exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hcon))))
  -- the restored intermediate's pile search
  have hpotB₀ : (F.setPile k { (F.piles k) with faceUp := frontK ++ [x.twin] }).pileOfTop z
      = some a := by
    refine ascent_topSearch _ (by rw [setPile_piles_ne hhin]; exact htopFa) ?_
    intro y _hy hyne
    by_cases hyk : y = k
    · have htopk : ({ (F.piles k) with faceUp := frontK ++ [x.twin] } : Pile).top
          ≠ some z := by
        show lastOf (frontK ++ [x.twin]) ≠ some z
        intro hcon
        rw [lastOf_snoc] at hcon
        exact hzxt (Option.some.inj hcon).symm
      rw [hyk, setPile_piles_self]
      exact htopk
    · have hBy : (F.setPile k { (F.piles k) with faceUp := frontK ++ [x.twin] }).piles y
          = W.piles y := by
        rw [setPile_piles_ne hyk, hFo y hyne hyk]
      have hWy : (W.piles y).top ≠ some z := fun hcon =>
        (mem_faceUp_unique hwf hzmem y hyne).1 (Pile.mem_of_top hcon)
      rw [hBy]
      exact hWy
  -- the back-slide lands exactly W (the geometric restore)
  have hback : State.step F (Move.tabToTab d (Sum.inr z)) = some W := by
    rw [hstepb, afterRunRemoved_ne hbasek, putRun_inr_eq hpotB₀]
    have hB₀a' : (F.setPile k { (F.piles k) with faceUp := frontK ++ [x.twin] }).piles a
        = F.piles a := setPile_piles_ne hhin
    rw [hB₀a', hFa]
    rw [show { (⟨(W.piles a).hidden, L₁⟩ : Pile) with
          faceUp := (⟨(W.piles a).hidden, L₁⟩ : Pile).faceUp ++ (d :: L₂) }
          = (⟨(W.piles a).hidden, L₁ ++ (d :: L₂)⟩ : Pile) from rfl]
    rw [← hspl]
    apply congrArg some
    apply State.ext
    · funext σ
      have h1 : ((F.setPile k { (F.piles k) with faceUp := frontK ++ [x.twin] }).setPile a
            ⟨(W.piles a).hidden, (W.piles a).faceUp⟩).found σ
          = F.found σ := rfl
      rw [h1, hFexp, putRun_found]
      rfl
    · funext y
      by_cases hya : y = a
      · rw [hya, setPile_piles_self]
      · by_cases hyk : y = k
        · rw [hyk, setPile_piles_ne hka,
            setPile_piles_self]
          apply Pile.ext
          · rw [hFk]
          · rw [hfrontk]
        · rw [setPile_piles_ne hya, setPile_piles_ne hyk, hFo y hya hyk]
    · rw [show ((F.setPile k { (F.piles k) with faceUp := frontK ++ [x.twin] }).setPile a
          ⟨(W.piles a).hidden, (W.piles a).faceUp⟩).stock = F.stock from rfl,
        hFexp]
      rw [(ascent_putRun_zone _ _ (Sum.inr x.twin)).1]
      rfl
    · rw [show ((F.setPile k { (F.piles k) with faceUp := frontK ++ [x.twin] }).setPile a
          ⟨(W.piles a).hidden, (W.piles a).faceUp⟩).waste = F.waste from rfl,
        hFexp]
      rw [(ascent_putRun_zone _ _ (Sum.inr x.twin)).2.1]
      rfl
    · rw [show ((F.setPile k { (F.piles k) with faceUp := frontK ++ [x.twin] }).setPile a
          ⟨(W.piles a).hidden, (W.piles a).faceUp⟩).drawStep = F.drawStep from rfl,
        hFexp]
      rw [(ascent_putRun_zone _ _ (Sum.inr x.twin)).2.2]
      rfl
  -- the saturation transfer: each iff-half is one via-prepend
  have hrevW : reversibleAtW W (Move.tabToTab d (Sum.inr x.twin)) :=
    ⟨F, [Move.tabToTab d (Sum.inr z)], hsF, run_one hback⟩
  have hrevF : reversibleAtW F (Move.tabToTab d (Sum.inr z)) :=
    ⟨W, [Move.tabToTab d (Sum.inr x.twin)], hback, run_one hsF⟩
  have hiffF : ∀ (c : Card), (c = x ∨ c = x.twin) ↔ CanRaiseS F c := by
    intro c
    constructor
    · intro hp
      have hW := (hsat c).mp hp
      exact CanRaiseS.via c ⟨d, Sum.inr z, hback, hrevF⟩ hW
    · intro hF'
      exact (hsat c).mpr
        (CanRaiseS.via c ⟨d, Sum.inr x.twin, hsF, hrevW⟩ hF')
  -- the pin: the covered twin tops nothing at the landing
  have hTopk : (F.piles k).top ≠ some x.twin := by
    obtain ⟨y, hy⟩ := lastOf_exists (show (d :: L₂) ≠ [] from by simp)
    have hyl : y ∈ (d :: L₂) := lastOf_mem hy
    show lastOf ((F.piles k).faceUp) ≠ some x.twin
    rw [hFkshape, ascent_lastOf_append _ _ (by simp), hy]
    rcases List.mem_cons.mp hyl with heq | hin
    · exact fun hc => hdxt (by
        have h1 : y = x.twin := Option.some.inj hc
        rw [heq] at h1
        exact h1)
    · exact fun hc => hxtL₂ (by
        have h1 : y = x.twin := Option.some.inj hc
        rw [h1] at hin
        exact hin)
  have hNoTwinF : ∀ q : Anchor, (F.piles q).top ≠ some x.twin := by
    intro q htopq
    by_cases hqk : q = k
    · exact hTopk (hqk ▸ htopq)
    · by_cases hqa : q = a
      · have hmemLa : x.twin ∈ (F.piles a).faceUp :=
          Pile.mem_of_top (hqa ▸ htopq)
        have hmemLL : x.twin ∈ L₁ := by
          rw [hFa] at hmemLa
          exact hmemLa
        exact (mem_faceUp_unique hwf hmemT a (fun h => hka h.symm)).1
          (by rw [hspl]; exact List.mem_append.mpr (Or.inl hmemLL))
      · have hFq : F.piles q = W.piles q := hFo q hqa hqk
        rw [hFq] at htopq
        exact (mem_faceUp_unique hwf hmemT q (fun h => hqk h)).1
          (Pile.mem_of_top htopq)
  have hPin : ¬ CanRaise F x.twin := by
    rintro ⟨-, p, hp, -⟩
    exact hNoTwinF p ((pileOfTop_eq_some_iff hwfF).1 hp)
  exact ⟨F, [Move.tabToTab d (Sum.inr x.twin)], x, run_one hsF, ⟨hiffF, hPin⟩⟩

/-- **THE BARE-COVER CORNER RESIDUE** `orientation_barecover_corner`
[M, named at the assembly pass] — the orientation row's sole surviving
corner, isolated with the exact landed state: the twin's vanilla
license holds (it tops its pile), the saturation is the pair, and the
fitting cover sits FIRST-FACED in its own pile (no face-up card below
it, so the named slide's moved run departs an empty face).

WHAT FIGHTS HERE (priced honestly at the traced shape):

* THE COMMIT — the named slide peels the cover's run off an emptied
  face: `afterRunRemoved` at an empty pre either reveals a hidden
  card (the reveal bar: the leg never rides a witness journey again,
  `journey_tabToTab_never_reveal`-family) or burns the pile outright;
  the one-move mirror has no landing (a non-king return onto the
  empty seat is impossible — the cover is never a king here, since
  its rank is one below the pair's).  The saturation transfer, which
  rides the one-move round trip, is therefore UNAVAILABLE at this
  corner: the slid state's S-set is not class-pinned to `W`'s.
* THE RESURRECTION MODE (the falsification flavor found on the thin
  boards): the committed landing seats the cover on the twin with
  CONTENT below, so a cover that was seat-blocked at `W` (bare,
  non-king, never-`CanRaise`-able) can re-acquire a seat at the
  landing and, if its rung is hot, re-enter the S-set OUTSIDE the
  pair — the landing's iff-round-side needs a capability census of
  the reveal/burn effects that the climb's ledger does not price.
* THE REMAINING CONTENT — either a longer `τ` reaches a fork (the
  draw/reveal search — the exhaustion row's own machinery is the
  natural closer), or a census argument shows the residue corner
  unreachable from every world the exhaustion row delivers (the
  cover-cell mobility read at the exhaustion state may bar
  first-faced covers outright).  Both routes are §2-grade; the corner
  is priced here, not forced. -/
private theorem orientation_barecover_corner {W : State} (hwf : W.WF)
    {x d : Card}
    (hsat : ∀ (c : Card), (c = x ∨ c = x.twin) ↔ CanRaiseS W c)
    (hctt : CanRaise W x.twin)
    (hrank : d.rank.toIdx + 1 = x.rank.toIdx)
    (hdxt : d ≠ x.twin)
    (hfit : canSitOn d x.twin = true)
    {a : Anchor} {L₂ : List Card}
    (hspl : (W.piles a).faceUp = d :: L₂) :
    ∃ (F : State) (τ : List Move) (x' : Card),
      W.run τ = some F ∧ ForkWitness F x' := by
  sorry

set_option linter.unusedVariables false in
/-- **THE ORIENTATION ASSEMBLY ROW** — from a state whose S-liveness
is exactly an intact pair (the saturation clause of `ForkWitness`,
already delivered) together with a fitting mobile cover, a fork is
reached — ONE cargo slide away whenever the cover is seated, the
state itself whenever the twin is not vanilla-live.

ROUTE (as landed at the assembly pass; the statement is byte-frozen):

1. THE SNAP — when `¬CanRaise W x.twin` already holds, the state ITSELF
   is the fork: the parcel's saturation clause is the hypothesis
   verbatim (`W.run [] = some W`) and the failed vanilla license is
   the pin.  Every covered-twin or seat-blocked-twin world closes
   here with no move at all (`ascent_snap`).
2. THE COVER SLIDE — otherwise the twin tops its pile
   (`canRaiseB`'s decidable probe decides the arm), and the cover
   `d` is face-up in its own pile (`hcover`'s residence, the WF-exact
   holding search).  When the cover has face-up CONTENT below it,
   the named slide `tabToTab d (inr x.twin)` fires; its one-move
   mirror (the exposed under-card re-fits the run and the run back
   onto the exposed pile top restores every field exactly) makes
   each saturation iff-half a single `CanRaiseS.via` prepend, and the
   landing carries the full parcel with the twin covered — the pin
   (`ascent_cover_slide_fork`, zero own open content).
3. THE BARE-COVER CORNER — when the cover sits FIRST-FACED (the
   positional split's `L₁ = []` arm), the named slide commits (the
   reveal/burn modes), and the row rides the named residue
   `orientation_barecover_corner [M]` — the exact surviving content,
   priced in its docstring, never forced.

HONEST GRADE NOTES: `hdhot` is not consumed by the assembly (the
iff's both-members liveness rides the saturation hypothesis; the
twin's hotness enters through the flat characterization only in the
residue's route); the cover's color and un-founded clauses are
consumed only by the residue (the slide arm needs merely the fit,
the residence, and the rank arithmetic).  The decidable arm-split
uses `canRaiseB` (the probe), so no classical choice enters. -/
theorem orientation_assembly_fork {W : State} (hwf : W.WF)
    {x d : Card}
    (hsat : ∀ (c : Card), (c = x ∨ c = x.twin) ↔ CanRaiseS W c)
    (hdhot : DoubleHot W x)
    (hcover : d.rank.toIdx + 1 = x.rank.toIdx ∧
      d.suit.color ≠ x.suit.color ∧
      d.rank.toIdx ≥ W.foundHeight d.suit ∧
      (∃ (c : Anchor), d ∈ (W.piles c).faceUp) ∧
      canSitOn d x.twin = true) :
    ∃ (F : State) (τ : List Move) (x' : Card),
      W.run τ = some F ∧ ForkWitness F x' := by
  cases hb : canRaiseB W x.twin with
  | false =>
      exact ascent_snap hsat (fun hcr => by
        rw [(canRaiseB_true_iff).mpr hcr] at hb
        simp at hb)
  | true =>
      have hctt : CanRaise W x.twin := (canRaiseB_true_iff).1 hb
      obtain ⟨c₀, hdface⟩ := hcover.2.2.2.1
      obtain ⟨L₁, L₂, hspl⟩ := ascent_mem_split _ hdface
      have hrank := hcover.1
      have hdxt : d ≠ x.twin := by
        intro hcon
        rw [hcon, Card.twin_rank] at hrank
        omega
      cases L₁ with
      | nil =>
          rw [List.nil_append] at hspl
          exact orientation_barecover_corner hwf hsat hctt hrank hdxt
            hcover.2.2.2.2 hspl
      | cons w ws =>
          exact ascent_cover_slide_fork hwf hsat hrank hdxt hctt
            hcover.2.2.2.2 hspl (by simp)

/-! ## §2b. The stuckness collapse (banked) -/

/-- (§2 private kit) The positional partition: every list splits at the
first occurrence into the below prefix and the `fromCard` run (the
two reads stop at the same first hit, duplicates or not). -/
private theorem ascent_split_mem (d : Card) :
    ∀ (l : List Card), l = below d l ++ fromCard d l := by
  intro l
  induction l with
  | nil => rfl
  | cons x t ih =>
      by_cases hxd : x = d
      · rw [below_cons, ite_eq_left hxd, fromCard, ite_eq_left hxd,
          List.nil_append]
      · rw [below_cons, ite_eq_right hxd, fromCard, ite_eq_right hxd]
        exact congrArg (x :: ·) ih

/-- **THE FACE-UP PRESERVATION, RAISE ARM** (private kit): a licensed
raise removes exactly the raised top; every OTHER face-up card stays
face-up — the chopped pile keeps its below-content, the untouched
piles carry over. -/
private theorem ascent_faceUp_raise {st st' : State} {c z : Card}
    (hstep : State.step st (Move.tabToFound z) = some st')
    (hne : c ≠ z) (hmem : ∃ a, c ∈ (st.piles a).faceUp) :
    ∃ a', c ∈ (st'.piles a').faceUp := by
  obtain ⟨a, hm⟩ := hmem
  obtain ⟨-, k, hk, hsuc⟩ := step_tabToFound_inv hstep
  by_cases hak : a = k
  · rw [hak] at hm
    have htopz : lastOf (st.piles k).faceUp = some z := (pileOfTop_top hk).2
    have hchop : (st.piles k).faceUp
        = chop (st.piles k).faceUp ++ [z] := lastOf_chop htopz
    have hcchop : c ∈ chop (st.piles k).faceUp := by
      rw [hchop] at hm
      rcases List.mem_append.mp hm with h1 | h2
      · exact h1
      · rcases List.mem_cons.mp h2 with hc | hc
        · exact absurd hc hne
        · cases hc
    have hchne : chop (st.piles k).faceUp ≠ [] := by
      intro hc
      rw [hc] at hcchop
      cases hcchop
    have hpilek : st'.piles k
        = Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp) := by
      rw [hsuc]
      show (if k = k then
          Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
          else st.piles k)
          = Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
      rw [ite_eq_left rfl]
    refine ⟨k, ?_⟩
    rw [hpilek, afterRunRemoved_ne hchne]
    exact hcchop
  · refine ⟨a, ?_⟩
    have hpile : st'.piles a = st.piles a := by
      rw [hsuc]
      show (if a = k then
          Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
          else st.piles a) = st.piles a
      rw [ite_eq_right (fun h => hak h)]
    rw [hpile]
    exact hm

/- **THE SLIDE-ARM PRESERVATION GAP** (route note, priced honestly at
the semantic-census pass): the face-up-preservation row for slide
arms is NOT bankable in this mechanization — a `tabToTab` leg whose
landing target rides the moved run can SELF-LAND: the mid-state's
`pileOfTop` reads `none` for the target (the run's cards have left
the board at the intermediate write), `putRun`'s `none` arm is the
identity, and the moved run CONSUMES ITSELF — face-up cards riding
the run genuinely vanish from the tableau.  This is the burn mode
the census files name (`witness_tabToTab_never_burn`'s family: a
committed slide reveals or burns a bare source's seat — here traced
to the self-landing corner, where the run itself is the burn).  Any
census row that needs member face-up-preservation along ascent runs
(the climb-delivery residue's guard-persistence step) must therefore
price the self-landing corners: the run's rank discipline confines
the riding cards to strictly-lower ranks than the head, so the
pair-riding corners are rank-bounded and the no-eat guard's
persistence analysis survives only with the census's seat ledger. -/

/-- The ascent run preserves WF (each leg steps; `step_wf` chains). -/
private theorem ascent_run_wf {s : State} (hwf : s.WF) :
    ∀ {ρ : List Move} {W : State}, AscentRun s ρ W → W.WF := by
  intro ρ W h
  induction h with
  | nil st => exact hwf
  | @cons st m s' W' ρ' hm hstep hrest ih => exact ih (step_wf hwf hstep)

/-- **THE STUCKNESS COLLAPSE** (banked at the exhaustion-shrink pass)
— at an exhausted state the S-grade collapses to the vanilla grade:
every `CanRaiseS` certificate is `now`-only, because any `via` leg
would be a cargo slide — and `AscentStuck`'s slide arm refuses EVERY
`tabToTab` outright (every slide is an ascent move, whether or not
its guards read legal).  This is the LEG-STUCK ⇒ S-STUCK BRIDGE's
proved half: the slide-exhaustion prunes the {slide · raise} prefix
before it starts. -/
theorem ascent_stuck_collapse {st : State} (hstuck : AscentStuck st)
    {c : Card} (h : CanRaiseS st c) : CanRaise st c := by
  induction h with
  | now c₀ hcan => exact hcan
  | @via stc s₂ c₀ hl hrest ih =>
      obtain ⟨d, b, hstep, -⟩ := hl
      have hnone : State.step stc (Move.tabToTab d b) = none :=
        hstuck (Move.tabToTab d b) (Or.inr ⟨d, b, rfl⟩)
      rw [hstep] at hnone
      exact absurd hnone (by simp)

/-- **THE STUCK UNBLOCKED READ** (banked): at an exhausted state an
S-live card CANNOT escape the full-time no-eat guard — if it were
no mobile pair's member, its vanilla license would fire, the raise
would be a legal ascent move, and the stuckness would fail.  This is
the leg-stuck ⇒ S-stuck bridge's second proved half: the unguarded
stock cannot persist at exhaustion (the negative form — the
membership form needs the census's pair counting, never classical
choice). -/
theorem ascent_stuck_unblocked {st : State} (hstuck : AscentStuck st)
    {c : Card} (h : CanRaiseS st c)
    (hnot : ∀ y, MobileTwin st y → c ≠ y ∧ c ≠ y.twin) : False := by
  obtain ⟨hnext, k, hk, -⟩ := ascent_stuck_collapse hstuck h
  have hfaceup : ∃ a, c ∈ (st.piles a).faceUp :=
    ⟨k, lastOf_mem (pileOfTop_top hk).2⟩
  have hnone := hstuck (Move.tabToFound c)
    (Or.inl ⟨c, rfl, of_decide_eq_true hnext, hfaceup,
      fun y hy => hnot y hy⟩)
  rw [step_tabToFound_splice hnext hk] at hnone
  exact absurd hnone (by simp)

/-! ## §2c. The exhaustion row's named pieces -/

/-- **THE CLIMB DELIVERY RESIDUE** `ascent_climb_delivery` [H-mini,
named at the exhaustion-shrink pass] — step (i) of the row's route,
isolated: the index-exact climb with the full-time no-eat guard
traps the reachable fork's family at-or-below its rank along the
WHOLE run, and the exhaustion parks both family frontiers at the
frontier rank with the pair emerging DOUBLE-HOT (face-up, next-up,
mobile).

ROUTE (each step priced; the banked rows cited per piece):

* THE GUARD PERSISTS — `AscentMove`'s raise arm declines every
  member of every intact mobile pair at every state of the run; the
  run's own moves never hide or found a pair mate (raises depart
  face-up tops — the RAISE-ARM FACE-UP PRESERVATION IS BANKED in
  this file as `ascent_faceUp_raise`; the slide arms carry the
  SELF-LANDING BURN corner priced in the route note above — face-up
  cards riding a self-landing run genuinely vanish, so the
  slide-arm persistence needs the census's seat ledger and the
  run's rank discipline), so a pair mobile at the start stays
  mobile at every prefix state (`MobileTwin` persists along
  `AscentRun` — the raise legs intact, the slide legs priced).
* THE RUNGS ARE INDEX-EXACT — a raise of suit σ climbs its rung by
  exactly one (`step_tabToFound_inv`'s foundation-prepend read, the
  `census`/ledger family), and crossing rank r on a FAMILY suit
  requires founding the r-indexed member — which the guard declines
  forever; so both family rungs freeze at-or-below r along the run
  (`witness_rung_census`-grade walk: no pull ever runs either, the
  climb letter is raise-only).
* THE PARKING CONTRADICTION — at the exhausted state a family rung
  parked strictly below r had its frontier card hot and face-up (the
  mitteler mobility premise delivered it face-up, and the run's
  moves never bury a face-up card), hence a stackable raise UNLESS
  guarded — and below r the guard does not apply (the mate only
  turns guard-relevant when the pair parks at r, so the frontier
  card is not any mobile pair's member there; the guarded half is
  priced against the calibration census) — against `AscentStuck`
  (the finer stuckness reads are BANKED here as
  `ascent_stuck_collapse` and `ascent_stuck_unblocked`).  Both
  family frontiers therefore read exactly r, and both members are
  next-up at their piles: the pair emerges double-hot, with the
  same-suit pins `rungAt W x.suit = x.rank.toIdx` the `DoubleHot`
  read carries. -/
private theorem ascent_climb_delivery {s : State} (hwf : s.WF)
    (hbelow : ∃ (F : State) (x : Card) (π : List Move),
      s.run π = some F ∧ ForkWitness F x ∧
        rungAt s x.suit ≤ x.rank.toIdx ∧
        rungAt s x.twin.suit ≤ x.rank.toIdx ∧
        (∃ (a : Anchor), x ∈ (s.piles a).faceUp) ∧
        (∃ (b : Anchor), x.twin ∈ (s.piles b).faceUp))
    {ρ : List Move} {W : State}
    (hrun : AscentRun s ρ W)
    (hstuck : AscentStuck W) :
    ∃ (x : Card), DoubleHot W x ∧ MobileTwin W x ∧
      rungAt W x.suit ≤ x.rank.toIdx ∧
      rungAt W x.twin.suit ≤ x.rank.toIdx := by
  sorry

/-- **THE STUCK-SATURATION RESIDUE** `ascent_stuck_saturation`
[H-mini, named at the exhaustion-shrink pass] — step (ii) of the
row's route, isolated: the exhaustion state's S-set is EXACTLY the
delivered pair (the row's saturation conjunct), given the climb
delivery's pair.

ROUTE (the banked collapse plus the priced census content):

* THE (⇐) HALF — the pair members ARE S-live at the exhausted
  state: the delivery pins them hot at their piles; the covered or
  seated member carries its certificate through the flat
  characterization's arms (`canRaiseS_iff_or`'s readable form), the
  free lemma's two-sided read consuming `canRaiseS_rung` and the
  covered-shape's twin-topping side condition (`canRaiseS_free`,
  `canRaiseS_runOrTwin`).
* THE (⇒) HALF — every non-pair card is S-dead: by the BANKED
  STUCKNESS COLLAPSE (`ascent_stuck_collapse`, this file) any S-live
  card is already vanilla-live, and by the BANKED UNBLOCKED READ
  (`ascent_stuck_unblocked`, this file) it must then be a member of
  some intact mobile pair — the surviving census content is the
  MULTI-PAIR EXCLUSION: every other mobile pair parked at the
  exhaustion is priced away by the frontiers' census (the `cf0`
  no-left-lift juries and the census's seat-exhaustion
  contrapositive, the `excursion_issues_noNewSeat` engine of
  `Orig/HostCensus.lean`, price which seats the delivered
  arrangement carries, and the frontier bookkeeping of the delivery
  residue leaves exactly one intact mobile pair at r; a SECOND
  mobile pair's parked hot raise would fire unblocked against
  `AscentStuck` unless every member is declined — the census names
  the exception shapes).
* THE REVEAL-GAP NOTE stays a live premise, carried by the delivery:
  the members were face-up at `s` and no ascent letter reveals, so
  they are face-up at `W`. -/
private theorem ascent_stuck_saturation {s : State} (hwf : s.WF)
    (hbelow : ∃ (F : State) (x : Card) (π : List Move),
      s.run π = some F ∧ ForkWitness F x ∧
        rungAt s x.suit ≤ x.rank.toIdx ∧
        rungAt s x.twin.suit ≤ x.rank.toIdx ∧
        (∃ (a : Anchor), x ∈ (s.piles a).faceUp) ∧
        (∃ (b : Anchor), x.twin ∈ (s.piles b).faceUp))
    {ρ : List Move} {W : State}
    (hrun : AscentRun s ρ W)
    (hstuck : AscentStuck W)
    {x : Card}
    (hxdel : DoubleHot W x ∧ MobileTwin W x ∧
      rungAt W x.suit ≤ x.rank.toIdx ∧
      rungAt W x.twin.suit ≤ x.rank.toIdx) :
    ∀ (c : Card), (c = x ∨ c = x.twin) ↔ CanRaiseS W c := by
  sorry

/-- **THE COVER-CELL CENSUS RESIDUE** `ascent_cover_cell` [H-mini²,
named at the cover-shrink pass] — the cover-read's sole surviving
content, isolated: at the exhausted delivered state, ONE of the two
`r−1`-indexed cells of the pair's opposite color family is UNFOUNDED
and FACE-UP.

ROUTE (the honest census):

* THE CELL INVENTORY — the deck's two `r−1` cells of the opposite
  family are the only fitting candidates (rank and color are pure
  arithmetic); the census prices (a) UNFOUNDEDNESS — at least one
  cell was not founded by the climb (the founded cells sit below
  their family rungs; both founded reads both opposite rungs past
  `r−1`, and the delivered pair's saturation (the `hiff` hypothesis)
  pins the opposite family's next-ups: their hot-and-live raises
  would fire unblocked against `AscentStuck` unless their pairs are
  intact — the multi-pair census of the saturation residue), and (b)
  FACE-UPNESS — a buried cover is a loan seat, and the
  seat-exhaustion census (`excursion_issues_noNewSeat`-grade) prices
  which cover cells the climb's slides can bury without repayment;
  the SELF-LANDING burn corner (this file's route note) prices the
  slide legs that genuinely consume face-up cards. -/
private theorem ascent_cover_cell {W : State} (hwf : W.WF)
    (hstuck : AscentStuck W)
    {x : Card}
    (hxdel : DoubleHot W x ∧ MobileTwin W x ∧
      rungAt W x.suit ≤ x.rank.toIdx ∧
      rungAt W x.twin.suit ≤ x.rank.toIdx)
    (hiff : ∀ (c : Card), (c = x ∨ c = x.twin) ↔ CanRaiseS W c) :
    ∃ (d : Card),
      d.rank.toIdx + 1 = x.rank.toIdx ∧
      d.suit.color ≠ x.suit.color ∧
      d.rank.toIdx ≥ W.foundHeight d.suit ∧
      (∃ (c : Anchor), d ∈ (W.piles c).faceUp) := by
  sorry

/-- **THE COVER-READ RESIDUE** `ascent_cover_read` [H-mini → shrunk to
a one-clause assembly at the cover-shrink pass] — steps (iii)/(iv)
of the row's route: the exhausted delivered state admits a FITTING,
MOBILE, UNFOUNDED cover.  The row's own body is now PURE ARITHMETIC
off the named census piece: the cell row
(`ascent_cover_cell` [H-mini²]) hands the four census clauses; the
fit clause (`canSitOn d x.twin`) is twin-blind rank-and-color
arithmetic (`canSitOn_eq`, `Card.twin_rank`, `Suit.color_twin`), so
the row itself carries no open content beyond the cell census. -/
private theorem ascent_cover_read {W : State} (hwf : W.WF)
    (hstuck : AscentStuck W)
    {x : Card}
    (hxdel : DoubleHot W x ∧ MobileTwin W x ∧
      rungAt W x.suit ≤ x.rank.toIdx ∧
      rungAt W x.twin.suit ≤ x.rank.toIdx)
    (hiff : ∀ (c : Card), (c = x ∨ c = x.twin) ↔ CanRaiseS W c) :
    ∃ (d : Card),
      d.rank.toIdx + 1 = x.rank.toIdx ∧
      d.suit.color ≠ x.suit.color ∧
      d.rank.toIdx ≥ W.foundHeight d.suit ∧
      (∃ (c : Anchor), d ∈ (W.piles c).faceUp) ∧
      canSitOn d x.twin = true := by
  obtain ⟨d, hd1, hd2, hd3, hd4⟩ := ascent_cover_cell hwf hstuck hxdel hiff
  refine ⟨d, hd1, hd2, hd3, hd4, ?_⟩
  exact (canSitOn_eq d x.twin).2
    ⟨by rw [Card.twin_rank]; omega,
     by rw [Card.twin_suit, Suit.color_twin]; exact hd2⟩

/-- The delivered shape as an explicit pair-plus-cover read (the
`TwinSlideHalt` existential restructured for the exhaustion row's
conclusion binders). -/
def ExhaustShape (st : State) (x d : Card) : Prop :=
  DoubleHot st x ∧
    d.rank.toIdx + 1 = x.rank.toIdx ∧
    d.suit.color ≠ x.suit.color ∧
    d.rank.toIdx ≥ st.foundHeight d.suit ∧
    (∃ (c : Anchor), d ∈ (st.piles c).faceUp) ∧
    canSitOn d x.twin = true

/-- **THE EXHAUSTION-FORKS ROW** — the owner's claim, in the
exhaustion semantics and the confluence grade: from any WF state
below a reachable fork's frontier whose pair members are already
mobile at the start, EVERY ascent run that runs to leg-exhaustion
delivers the shape — an intact double-hot pair whose members are the
only S-live cards, together with a fitting mobile cover — hence a
fork one slide away (§1 assembles it).

ROUTE (restructured at the exhaustion-shrink pass into three named
pieces plus a banked bridge — the row's own body is pure assembly;
each piece carries its complete priced route where it is declared):

1. THE CLIMB DELIVERY — `ascent_climb_delivery` [H-mini]: the
   guard-persistence and index-exact rung walk park both family
   frontiers at the fork's rank, the pair emerging double-hot and
   mobile (the full-time no-eat guard, the rung ledger, the
   parking-below-r contradiction).
2. THE STUCK-SATURATION — `ascent_stuck_saturation` [H-mini]: the
   exhausted state's S-set is exactly the delivered pair — riding the
   BANKED STUCKNESS COLLAPSE (`ascent_stuck_collapse`, proved in this
   file: at a stuck state every `via` leg is a refused slide, so
   `CanRaiseS` collapses to `CanRaise`) and the census seat
   machinery for the outside-tops' guard rejections.
3. THE COVER READ — `ascent_cover_read` [H-mini]: the `r−1`-cell
   cover inventory minus the climb's seating loans, the fit by
   `canSitOn`, the guard-freedom by the frontier census.
4. THE ASSEMBLY — the row's body composes the three pieces into the
   delivered `ExhaustShape` plus the saturation iff; §1 then
   assembles the fork one slide further.

Falsification boards (the refuter-first targets): ladder-exhaustion
decks — greedy slide-wasting runs, buried-cover exhaustions,
multi-pair frontiers — assigned to the probe program alongside the
descent program's boards. -/
theorem ascent_exhaustion_forks {s : State} (hwf : s.WF)
    (hbelow : ∃ (F : State) (x : Card) (π : List Move),
      s.run π = some F ∧ ForkWitness F x ∧
        rungAt s x.suit ≤ x.rank.toIdx ∧
        rungAt s x.twin.suit ≤ x.rank.toIdx ∧
        (∃ (a : Anchor), x ∈ (s.piles a).faceUp) ∧
        (∃ (b : Anchor), x.twin ∈ (s.piles b).faceUp))
    {ρ : List Move} {W : State}
    (hrun : AscentRun s ρ W)
    (hstuck : AscentStuck W) :
    ∃ (x d : Card),
      ExhaustShape W x d ∧
      (∀ (c : Card), (c = x ∨ c = x.twin) ↔ CanRaiseS W c) := by
  obtain ⟨x, hdel⟩ := ascent_climb_delivery hwf hbelow hrun hstuck
  have hiff : ∀ (c : Card), (c = x ∨ c = x.twin) ↔ CanRaiseS W c :=
    ascent_stuck_saturation hwf hbelow hrun hstuck hdel
  obtain ⟨d, hd1, hd2, hd3, hd4, hd5⟩ :=
    ascent_cover_read (ascent_run_wf hwf hrun) hstuck hdel hiff
  exact ⟨x, d, ⟨hdel.1, hd1, hd2, hd3, hd4, hd5⟩, hiff⟩

/-! ## The audit battery

`#print axioms` per fresh head: the §0 vocabulary rows are
statement-facing definitions elaborated here.  The §1 assembly row
carries ONLY the named bare-cover corner's `sorryAx` (plus the
`Quot.sound` of the via-transfer's class welding); its proved
sub-rows — the snap, the cover-slide assembly with the one-move
geometric restore, the saturation transfer — are private per the
house discipline and audited through the main row's own profile.
The §2 machinery now banks THREE zero-sorry rows
(`ascent_stuck_collapse`, `ascent_stuck_unblocked`, and the private
raise-arm face-up preservation kit) and shrinks `ascent_cover_read`
to pure arithmetic over the named cover-cell census; the remaining
open content sits in the four named pieces (bare-cover corner,
climb delivery, stuck saturation, cover-cell census), each with its
complete route in the docstring. -/

#print axioms orientation_assembly_fork
#print axioms ascent_stuck_collapse
#print axioms ascent_stuck_unblocked
#print axioms ascent_exhaustion_forks
