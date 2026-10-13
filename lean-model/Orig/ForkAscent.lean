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

TAKEOVER LANDINGS (2026-10-13, the successor session): the §0
decidability promise is cashed (`mobileTwinB`, the `MobileTwin`
decider, feeding the constructive `ascent_stuck_live_member` — an
S-live card at an exhaustion is an intact mobile pair's member,
extracted by the finite search, no classical choice); the
saturation's two halves are priced apart — the COLLAPSE IFF
(`ascent_stuck_collapse_iff`, the S-grade IS the vanilla grade at
exhaustions) and the COVER/TWIN-TOP BAR (`ascent_stuck_coverTwinbar`,
a covered card's twin cannot top at a stuck state — the one new
lattice row of the day) plus the §2d falsification-economy boards
`fa0`/`fa1` (decide-witnessed WF boards showing both the multi-pair
exclusion and the member-liveness are `hbelow`-carried, not
exhausted-state-local); the β-staging of §2e (the `ExhaustShapeRec`
shape, the PROVED one-legged `ascent_cover_pullback`, the PROVED
router `ascent_cover_read_rec` — the owner's recoverable-disjunct
ratification becomes a one-line swap); and the bare-cover commit
read `ascent_barecover_commit` (§1d), proving the corner's named
slide fires with its successor spelled in the two priced modes.
The frozen statements and the main rows' bodies are byte-untouched;
the named residues carry re-priced routes that name what is provable
kernel, what is `hbelow`-carried open, and why (never-force
discipline).
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
  is priced here, not forced.

TAKEOVER PASS (2026-10-13): the commit is now PROVED DETAIL —
`ascent_barecover_commit` (§1d below) spells the named slide's
successor exactly: the covering run lands whole on the twin's pile
(the twin covered beneath the cover's head), the emptied source pile
reveals its hidden head or burns to the bare empty record (the two
priced modes, the WF hidden/face-up disjointness carrying the
reveal-side's freshness), every other pile untouched.  The
restoration census — the landed state's S-set re-read (the
RESURRECTION MODE above: whether the emptied side's fresh seat can
re-admit a hot card outside the pair) — remains the corner's named
open; the one-line return onto the empty seat stays barred by rank
arithmetic (the cover is a rank-`r−1` card, never a king), so the
saturation transfer's round trip cannot ride. -/
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

/- **THE SELF-LANDING REFUTATION** (route-note correction, proved here):
the earlier draft note of this section priced a "self-landing burn" —
a `tabToTab` whose landing target rides the moved run, with the
mid-state's `pileOfTop` reading `none` so that `putRun`'s `none` arm
returns the identity and the run CONSUMES ITSELF.  THE ANALYSIS WAS
WRONG: the placement guard reads `pileOfTop z` at the STEP'S OWN
start, and the fit arithmetic is a rank CONTRADICTION — every rider
of a legal run sits strictly BELOW its head in rank, while
`canSitOn d z` demands the head sit on the target, i.e. the target
be exactly one rank ABOVE the head.  A run rider can never be the
landing base: the step refuses at its own guard read, `putRun`'s
`none` arm is unreachable from WF starts, and `step_wf`'s
card-count preservation corroborates the refutation.  The row below
proves the arithmetic bar outright; the slide-arm face-up
preservation loses its feared semantic obstruction (its remaining
content is the mid-state `pileOfTop` re-identification of outside
bases, ordinary census work). -/
theorem ascent_selfland_refuted {st : State} (hwf : st.WF)
    {d z : Card} {a : Anchor}
    (hh : st.pileHolding d = some a)
    (hzin : z ∈ fromCard d ((st.piles a).faceUp))
    (hne : z ≠ d) :
    st.canPlace d (Sum.inr z) = false := by
  have hrok := hwf.2.1 a
  have hspl : (st.piles a).faceUp
      = below d ((st.piles a).faceUp) ++ fromCard d ((st.piles a).faceUp) :=
    ascent_split_mem d ((st.piles a).faceUp)
  have hrrun : runOK (fromCard d ((st.piles a).faceUp)) = true :=
    ascent_runOK_prefix _ _ (by rw [← hspl]; exact hrok)
  obtain ⟨t, ht⟩ := fromCard_eq_head_of_mem (pileHolding_mem hh)
  have hzink : z ∈ fromCard d ((st.piles a).faceUp) := hzin
  rw [ht] at hzink hrrun
  have hgtr : z.rank.toIdx < d.rank.toIdx := by
    rcases List.mem_cons.mp hzink with heq | htail
    · exact absurd heq hne
    · exact ascent_runOK_head_gt hrrun htail
  cases hp : st.pileOfTop z with
  | none =>
      rw [show st.canPlace d (Sum.inr z)
          = (match st.pileOfTop z with
             | some _ => canSitOn d z
             | none => false) from rfl, hp]
  | some k =>
      have hfit : canSitOn d z = false := by
        cases hcs : canSitOn d z with
        | true =>
            have hr := (canSitOn_eq d z).mp hcs
            exact absurd hr.1 (by omega)
        | false => rfl
      rw [show st.canPlace d (Sum.inr z)
          = (match st.pileOfTop z with
             | some _ => canSitOn d z
             | none => false) from rfl, hp, hfit]

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

/-! ### The stuck-state lattice kit (the saturation's provable kernels)

The takeover pass (2026-10-13) priced the saturation residue's two
halves and separated what is provable at the exhausted state ALONE
from what rides `hbelow`.  These rows are the provable part, banked:

* the COLLAPSE IFF — at an exhaustion the S-grade and the vanilla
  grade coincide outright (the stuckness collapse read as the
  biconditional; the saturation iff is literally the vanilla
  membership read);
* the LIVE-MEMBER READ — every S-live card at an exhausted state is
  the member of SOME intact mobile pair, the finite search supplying
  the witness constructively (the §0 decidability note's
  `MobileTwin` mirror does the enumeration; no classical choice);
* the COVER/TWIN-TOP BAR — at an exhausted state a covered card
  whose twin tops anywhere is impossible: the run's cover fits the
  card by the run discipline, and the twin-blind fit arithmetic
  slides the cover's run onto the twin's top — a legal ascent slide
  against `AscentStuck`.  This is the row the saturation's (⇐) half
  rides whenever a member is covered: the exhausted pair can only
  stand BOTH-TOPPING, BOTH-COVERED-with-untopped-twins, or mixed —
  the covered-and-live shapes are barred outright. -/

/-- **THE COLLAPSE IFF** (banked kit): at an exhausted state the
S-grade and the vanilla grade coincide — the collapse forward, the
`now` leg backward. -/
private theorem ascent_stuck_collapse_iff {st : State} (hstuck : AscentStuck st)
    (c : Card) : CanRaiseS st c ↔ CanRaise st c :=
  ⟨fun h => ascent_stuck_collapse hstuck h, fun h => CanRaiseS.now c h⟩

/-- The finite-search mirror of `List.any` (the decider kit's search
row). -/
private theorem ascent_any_iff {α : Type} (p : α → Bool) :
    ∀ (l : List α), l.any p = true ↔ ∃ x ∈ l, p x = true := by
  intro l
  induction l with
  | nil =>
      constructor
      · intro h; simp [List.any] at h
      · intro h
        obtain ⟨x, hx, -⟩ := h
        cases hx
  | cons y t ih =>
      show (p y || t.any p) = true ↔ ∃ x ∈ y :: t, p x = true
      rw [Bool.or_eq_true]
      constructor
      · rintro (hy | ht)
        · exact ⟨y, List.mem_cons_self .., hy⟩
        · obtain ⟨x, hx, hp⟩ := ih.mp ht
          exact ⟨x, List.mem_cons.mpr (Or.inr hx), hp⟩
      · rintro ⟨x, hx, hp⟩
        rcases List.mem_cons.mp hx with heq | hin
        · rw [heq] at hp; exact Or.inl hp
        · exact Or.inr (ih.mpr ⟨x, hin, hp⟩)

/-- The `[x]`-splice reshape (the kit's append bridge). -/
private theorem ascent_append_singleton (x : Card) :
    ∀ (pre post : List Card), pre ++ x :: post = (pre ++ [x]) ++ post := by
  intro pre
  induction pre with
  | nil => intro post; rfl
  | cons y t ih =>
      intro post
      rw [List.cons_append, List.cons_append, List.cons_append, ih post]

/-- Completeness of the finite search (the per-file private copy of
the `firstWhere` completeness kit row). -/
private theorem ascent_firstWhere_none_complete {α : Type} {p : α → Bool} :
    ∀ {l : List α}, firstWhere p l = none → ∀ c ∈ l, p c = false := by
  intro l
  induction l with
  | nil => intro _ c hc; cases hc
  | cons y t ih =>
      intro h c hc
      cases hp : p y with
      | true =>
          have h' : firstWhere p (y :: t) = some y := by
            show (match p y with
              | true => some y | false => firstWhere p t) = some y
            rw [hp]
          rw [h'] at h
          exact absurd h (by simp)
      | false =>
          have h' : firstWhere p (y :: t) = firstWhere p t := by
            show (match p y with
              | true => some y | false => firstWhere p t) = firstWhere p t
            rw [hp]
          rw [h'] at h
          rcases List.mem_cons.mp hc with heq | hin
          · rw [heq]; exact hp
          · exact ih h c hin

/-- **THE `MobileTwin` DECIDER** (the §0 decidability note's promise,
mirrored Bool-side for the finite witness searches; the
parenthesization mirrors `MobileTwin`'s own right-nested
conjunction). -/
private def mobileTwinB (st : State) (c : Card) : Bool :=
  Anchor.all.any (fun a => decide (c ∈ (st.piles a).faceUp)) &&
  (decide (c.rank.toIdx ≥ st.foundHeight c.suit) &&
  (Anchor.all.any (fun a => decide (c.twin ∈ (st.piles a).faceUp)) &&
  decide (c.twin.rank.toIdx ≥ st.foundHeight c.twin.suit)))

private theorem ascent_anchorMem_iff (st : State) (c : Card) :
    Anchor.all.any (fun a => decide (c ∈ (st.piles a).faceUp)) = true ↔
      ∃ (a : Anchor), c ∈ (st.piles a).faceUp := by
  rw [ascent_any_iff (fun a => decide (c ∈ (st.piles a).faceUp)) Anchor.all]
  constructor
  · rintro ⟨a, -, hp⟩
    exact ⟨a, of_decide_eq_true hp⟩
  · rintro ⟨a, hm⟩
    exact ⟨a, Anchor.mem_all a, decide_eq_true hm⟩

/-- The decider agrees with the read. -/
private theorem mobileTwinB_iff (st : State) (c : Card) :
    mobileTwinB st c = true ↔ MobileTwin st c := by
  constructor
  · intro h
    simp only [mobileTwinB, Bool.and_eq_true, ascent_anchorMem_iff,
      decide_eq_true_iff] at h
    exact h
  · intro h
    simp only [mobileTwinB, Bool.and_eq_true, ascent_anchorMem_iff,
      decide_eq_true_iff]
    exact h

/-- The searched predicate: `y` is an intact mobile pair of which `c`
is a member. -/
private def pairMemberB (st : State) (c y : Card) : Bool :=
  mobileTwinB st y && (decide (c = y) || decide (c = y.twin))

private theorem pairMemberB_iff (st : State) (c y : Card) :
    pairMemberB st c y = true ↔
      (MobileTwin st y ∧ (c = y ∨ c = y.twin)) := by
  rw [pairMemberB, Bool.and_eq_true, Bool.or_eq_true,
    mobileTwinB_iff, decide_eq_true_iff, decide_eq_true_iff]

/-- **THE LIVE-MEMBER READ** (banked kit, the saturation's (⇒)-kernel):
every S-live card at an exhausted state is the member of SOME intact
mobile pair — the flat extraction of the banked unblocked read, the
finite search supplying the witness without classical choice. -/
private theorem ascent_stuck_live_member {st : State} (hstuck : AscentStuck st)
    {c : Card} (h : CanRaiseS st c) :
    ∃ (y : Card), MobileTwin st y ∧ (c = y ∨ c = y.twin) := by
  cases hw : firstWhere (pairMemberB st c) Card.universe with
  | none =>
      exfalso
      refine ascent_stuck_unblocked hstuck h ?_
      intro y hy
      have hdecl :=
        ascent_firstWhere_none_complete hw y (Card.mem_universe y)
      have hor : (decide (c = y) || decide (c = y.twin)) = false := by
        cases hx : (decide (c = y) || decide (c = y.twin)) with
        | true =>
            exfalso
            have hboth : pairMemberB st c y = true := by
              rw [pairMemberB, (mobileTwinB_iff st y).mpr hy, hx]; rfl
            rw [hboth] at hdecl
            exact absurd hdecl (by simp)
        | false => rfl
      have hd1 : decide (c = y) = false := by
        cases hq : decide (c = y) with
        | true => rw [hq] at hor; exact absurd hor (by simp)
        | false => rfl
      have hd2 : decide (c = y.twin) = false := by
        cases hq : decide (c = y.twin) with
        | true => rw [hq] at hor; exact absurd hor (by simp)
        | false => rfl
      refine ⟨fun hcon => ?_, fun hcon => ?_⟩
      · rw [hcon] at hd1; simp at hd1
      · rw [hcon] at hd2; simp at hd2
  | some y =>
      exact ⟨y, (pairMemberB_iff st c y).mp (firstWhere_sound _ hw)⟩

/-- **THE COVER/TWIN-TOP BAR** (banked kit, the saturation's sharp
lattice row): at an exhausted state a covered card whose twin tops
anywhere is impossible — the card directly above fits by the run
discipline, the twin-blind fit arithmetic slides that cover's run
onto the twin's top, and the slide is a legal ascent move, against
`AscentStuck`. -/
private theorem ascent_stuck_coverTwinbar {st : State} (hwf : st.WF)
    (hstuck : AscentStuck st) {x d : Card} {a k : Anchor}
    {pre rest : List Card}
    (hspl : (st.piles a).faceUp = pre ++ x :: d :: rest)
    (htwin : st.pileOfTop x.twin = some k) : False := by
  -- the cover fits the covered card by the run discipline
  have hrok : runOK (pre ++ x :: d :: rest) = true := by
    rw [← hspl]; exact hwf.2.1 a
  have hfit : canSitOn d x = true := ascent_runOK_adjacent_fit x d pre rest hrok
  obtain ⟨hr1, hc1⟩ := (canSitOn_eq d x).mp hfit
  have hfitT : canSitOn d x.twin = true :=
    (canSitOn_eq d x.twin).2
      ⟨by rw [Card.twin_rank]; exact hr1,
       by rw [Card.twin_suit, Suit.color_twin]; exact hc1⟩
  -- the cover's residence and the nonempty run
  have hmemD : d ∈ (st.piles a).faceUp := by
    rw [hspl]
    exact List.mem_append.mpr (Or.inr
      (List.mem_cons.mpr (Or.inr List.mem_cons_self)))
  have hhold : st.pileHolding d = some a := (pileHolding_eq_some_iff hwf).2 hmemD
  have hnd : ((pre ++ [x]) ++ d :: rest).Nodup := by
    have h := runOK_nodup (hwf.2.1 a)
    rw [hspl, ascent_append_singleton x pre (d :: rest)] at h
    exact h
  have hdnotmem : d ∉ pre ++ [x] :=
    ascent_nodup_mid_notmem d (pre ++ [x]) rest hnd
  have hfrom : fromCard d (st.piles a).faceUp = d :: rest := by
    rw [hspl, ascent_append_singleton x pre (d :: rest)]
    exact ascent_fromCard_mid d (pre ++ [x]) rest hdnotmem
  -- the slide is legal at the twin's top
  have hcan : st.canPlace d (Sum.inr x.twin) = true := by
    rw [canPlace_inr_located htwin]
    exact hfitT
  -- and it fires, against the stuckness
  have hnone := hstuck (Move.tabToTab d (Sum.inr x.twin))
    (Or.inr ⟨d, Sum.inr x.twin, rfl⟩)
  rw [step_tabToTab_eq, hhold] at hnone
  simp only [hcan] at hnone
  rw [hfrom] at hnone
  simp at hnone

/-! ## §2c. The exhaustion row's named pieces -/

/-- **THE CLIMB DELIVERY RESIDUE** `ascent_climb_delivery` [H-mini,
named at the exhaustion-shrink pass; parking regraded at the
2026-10-13 takeover] — step (i) of the row's route, isolated: the
index-exact climb with the full-time no-eat guard traps the
reachable fork's family at-or-below its rank along the WHOLE run,
and the exhaustion parks both family frontiers at the frontier rank
with the pair emerging DOUBLE-HOT (face-up, next-up, mobile).

ROUTE (re-priced at the takeover; the provable kernels are named,
the parking is priced open — never forced):

* THE GUARD PERSISTS — the provable half of the leg-work: the run's
  RAISE legs never remove a face-up card other than the raised one
  (the banked `ascent_faceUp_raise`), the raised card is never a
  member of an intact mobile pair (the full-time guard declines it
  in the raise arm's own quantifier), and the SLIDE legs relocate
  face-up runs whole (below-content stays in place, the moved run
  lands face-up — the commit-read machinery of §1d prices exactly
  these writes), so a pair mobile at the start stays paired and
  face-up at every prefix.  [kernel status: priced, next pass]
* THE RUNGS ARE INDEX-EXACT — the provable freeze: a raise of suit
  σ climbs its rung by exactly one (the splice's
  `setFound`-prepend read), and crossing rank r on a FAMILY suit
  requires founding the rank-r member — guard-declined forever
  (the guard persists, per the kernel above) — so both family rungs
  stay ≤ r along the whole run.  [kernel status: priced, next pass]
* **THE PARKING-AT-r [OPEN, `hbelow`-carried]** — the residue's own
  surviving content: the strict-parking argument claimed at the
  exhaustion-shrink pass (a rung parked strictly below r forces a
  hot face-up frontier raise) does NOT close from the exhausted
  state + member clauses alone: the frontier card may sit boarded
  or covered without its mate, hidden, or stocked — a stalled rung
  is stuck-consistent at every such shape (the same seat/
  cover-starvation the probe's boards priced), so the parking must
  ride `hbelow` — the fork-reachability census, the probe's
  declared open (§5 verdict).  Named here: `ascent_frontier_parking`
  [H, hbelow-carried]; the two kernels above are the bankable
  halves of its leg-work, sized and ready for the next pass. -/
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
[H-mini, named at the exhaustion-shrink pass, residue-graded at the
2026-10-13 takeover] — step (ii) of the row's route, isolated: the
exhaustion state's S-set is EXACTLY the delivered pair (the row's
saturation conjunct), given the climb delivery's pair.

ROUTE (re-priced at the takeover pass; the pre-takeover draft's
belief — members arrive covered-or-seated, the multi-pair exclusion
a frontier-lattice consequence — was tested by the write attempt and
REFUTED as W-local content; the boards `fa0`/`fa1` of §2d are the
decide-witnesses):

* THE COLLAPSE REDUCTION — at the exhausted state the iff IS the
  vanilla membership read: `ascent_stuck_collapse_iff` (this file)
  reduces every `CanRaiseS` to `CanRaise`, so the (⇐) half is
  literally "both members top a pile with a refillable seat at `W`"
  and the (⇒) half is literally "every vanilla-live card is in the
  pair".
* THE (⇐) HALF [OPEN, `hbelow`-carried] — member liveness is NOT a
  consequence of the exhausted state alone: `fa1` is a WF, stuck,
  double-hot, intact board whose members are vanilla-dead (bare,
  seatless, non-king — `fa1_membersDead`, `fa1_iff_point_false`).
  At a stuck state the covered member's flat arm is barred outright
  by `ascent_stuck_coverTwinbar` (the covered card's twin cannot
  top), so liveness can only ride the START economy — the
  fork-reachability census, the same wide-open computation the probe
  declines to decide.
* THE (⇒) HALF [OPEN, `hbelow`-carried] — the banked kernels carry
  the content down to the named exclusion: `ascent_stuck_collapse`
  makes every S-live card vanilla-live, and
  `ascent_stuck_live_member` (this file) extracts, constructively,
  the intact mobile pair it must belong to.  The surviving content
  is exactly the MULTI-PAIR EXCLUSION — named here
  `ascent_multiPair_exclusion` [H, hbelow-carried] — and it is NOT
  W-local: `fa0` is a WF, stuck, double-hot board carrying a SECOND
  intact mobile pair with a vanilla-live member outside the
  delivered pair (`fa0_multiPair`, `fa0_iff_point_false`).  The
  exclusion must ride `hbelow` — the fork-reachability census near
  hot two-pair boards starves (the pulled-ace cover recursion the
  boards exhibit), and that computation is the probe's declared open.
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
named at the cover-shrink pass; α-armor citation refined at the
2026-10-13 takeover] — the cover-read's sole surviving
content, isolated: at the exhausted delivered state, ONE of the two
`r−1`-indexed cells of the pair's opposite color family is UNFOUNDED
and FACE-UP.

ROUTE (the honest census; the α-armor datapoints are EVIDENCE on
record, not imports — the probe tree is below this leaf and must
never be consumed here — and the β-companion staging of §2e below
carries the same census's recoverable arm):

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
  which cover cells the climb's slides can bury without repayment
  (the feared slide-consumption is REFUTED by
  `ascent_selfland_refuted` — cells cannot ride a run into the
  `putRun` identity; the genuine burial modes are FUNDING and
  pre-boarded hiddenness, and the founding route is barred by the
  CELL GUARD TRAP while the cell pair starts
  `MobileTwin`-intact — the hunt's structural read, priced against
  the cover-burial probe `Orig/ForkAscentProbe.lean`).
* THE α-ARMOR (takeover citation): the probe's `ab2`-board rows —
  `ab2_cellMobile` (the intact cover-cell pair reads `MobileTwin`
  verbatim) and `ab2_raiseNotAscent` (the guard declines founding
  either cell outright) — witness that the FUNDING burial mode is
  guard-barred whenever the cells arrive INTACT; and the probe's
  `ab0`/`ab1` rows witness the founding burial building at a
  PRE-BROKEN cell economy that lands stuck with NO standing cover
  (`TwinSlideHalt ab1` decide-false).  The census's surviving open —
  whether any `hbelow`-satisfying board ever arrives pre-broken — is
  the probe's own declared open (its §5 verdict); the residue is
  graded with that reachability content named, and the β-staging of
  §2e routes the recoverable side of the same census. -/
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

/-! ## §2d. The falsification-economy boards (takeover evidence)

Two decide-witness boards, priced at the 2026-10-13 takeover pass per
the falsification-first assignment in the exhaustion row's route
below (multi-pair frontiers, bare-pair exhaustions — the probe leaf
is read-only at this pass, so the boards stage in-file).  What they
witness is NOT a counterexample to any frozen statement: the frozen
rows' `hbelow` premises are untouched by these decks, and whether
each board admits a reachable fork at all is the wide-open
full-alphabet computation `Orig/ForkAscentProbe.lean` itself declines
to decide (its §5 verdict).  What they DO witness — decide-verified,
WF-exact — is that the saturation residue's two halves are NOT
consequences of the exhausted state ALONE; both ride `hbelow`:

* `fa0` (the multi-pair frontier board): a WF, STUCK board whose
  delivered black two-pair is DOUBLE-HOT and intact, while a SECOND
  intact mobile pair (the red twos) stands with a VANILLA-LIVE member
  OUTSIDE the delivered pair — the (⇒) half's multi-pair exclusion
  cannot be W-local.
* `fa1` (the bare-pair board): a WF, STUCK board whose delivered ace
  pair is DOUBLE-HOT and intact while BOTH MEMBERS ARE VANILLA-DEAD
  (bare, seatless, non-king) — the (⇐) half's member-liveness cannot
  be W-local either (rank-0 cells can never seat or cover: the
  exhaustion row's `r = 1` rigidity, at the row's own floor).

Together with the banked kit above (the collapse iff, the
live-member read, the cover/twin-top bar) these seat the saturation's
residue grade honestly: the named content that remains is
`hbelow`-carried on BOTH sides, exactly as the cover census is (the
probe's ab0/ab1 burial economy). -/

/-- The house card-maker (the boards' private copy). -/
private def faCrd (s : Suit) (r : Rank) : Card := ⟨s, r⟩

/-- A suit's foundation prefix at height `n` (the boards' copy). -/
private def faTakeUp (s : Suit) (n : Nat) : List Card := s.upCards.take n

private def faS2 : Card := faCrd .spade .two
private def faC2 : Card := faCrd .club .two
private def faH2 : Card := faCrd .heart .two
private def faD2 : Card := faCrd .diamond .two
private def faH3 : Card := faCrd .heart .three
private def faD3 : Card := faCrd .diamond .three
private def faS3 : Card := faCrd .spade .three
private def faC3 : Card := faCrd .club .three

/-- **THE MULTI-PAIR FRONTIER BOARD `fa0`** — all four rungs at one;
the black twos seated over the red threes; the red twos seated over
the black threes; both pairs double-hot and intact; everything else
sunk in the stock; every hidden deck empty. -/
private def fa0 : State where
  found := fun s => faTakeUp s 1
  piles := fun a => match a with
    | .p0 => ⟨[], [faH3, faS2]⟩
    | .p1 => ⟨[], [faC3, faD2]⟩
    | .p2 => ⟨[], [faS3, faH2]⟩
    | .p3 => ⟨[], []⟩
    | .p4 => ⟨[], []⟩
    | .p5 => ⟨[], [faD3, faC2]⟩
    | .p6 => ⟨[], []⟩
  stock :=
    [faCrd .spade .four, faCrd .spade .five, faCrd .spade .six,
     faCrd .spade .seven, faCrd .spade .eight, faCrd .spade .nine,
     faCrd .spade .ten, faCrd .spade .jack, faCrd .spade .queen,
     faCrd .spade .king,
     faCrd .heart .four, faCrd .heart .five, faCrd .heart .six,
     faCrd .heart .seven, faCrd .heart .eight, faCrd .heart .nine,
     faCrd .heart .ten, faCrd .heart .jack, faCrd .heart .queen,
     faCrd .heart .king,
     faCrd .diamond .four, faCrd .diamond .five, faCrd .diamond .six,
     faCrd .diamond .seven, faCrd .diamond .eight, faCrd .diamond .nine,
     faCrd .diamond .ten, faCrd .diamond .jack, faCrd .diamond .queen,
     faCrd .diamond .king,
     faCrd .club .four, faCrd .club .five, faCrd .club .six,
     faCrd .club .seven, faCrd .club .eight, faCrd .club .nine,
     faCrd .club .ten, faCrd .club .jack, faCrd .club .queen,
     faCrd .club .king]
  waste := []
  drawStep := 1

private theorem fa0_wf_found : ∀ s : Suit, ∃ n, fa0.found s = s.upCards.take n := by
  intro s
  cases s <;> exact ⟨1, rfl⟩

private theorem fa0_wf_runs : ∀ a : Anchor, runOK (fa0.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

private theorem fa0_wf_count : ∀ c ∈ Card.universe, fa0.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

/-- The multi-pair frontier board is `WF` (kernel-decided). -/
theorem fa0_wf : fa0.WF :=
  ⟨fa0_wf_found, fa0_wf_runs, fa0_wf_count, by decide⟩

private theorem fa0_p0 : fa0.piles .p0 = ⟨[], [faH3, faS2]⟩ := rfl
private theorem fa0_p1 : fa0.piles .p1 = ⟨[], [faC3, faD2]⟩ := rfl
private theorem fa0_p2 : fa0.piles .p2 = ⟨[], [faS3, faH2]⟩ := rfl
private theorem fa0_p3 : fa0.piles .p3 = ⟨[], []⟩ := rfl
private theorem fa0_p4 : fa0.piles .p4 = ⟨[], []⟩ := rfl
private theorem fa0_p5 : fa0.piles .p5 = ⟨[], [faD3, faC2]⟩ := rfl
private theorem fa0_p6 : fa0.piles .p6 = ⟨[], []⟩ := rfl

/-- **THE FACE-UP INVENTORY AT `fa0`**: exactly the two pairs and
their four seats. -/
theorem fa0_faceUp : ∀ c ∈ Card.universe,
    (∃ a, c ∈ (fa0.piles a).faceUp) →
      c = faS2 ∨ c = faC2 ∨ c = faH2 ∨ c = faD2 ∨
      c = faH3 ∨ c = faD3 ∨ c = faS3 ∨ c = faC3 := by
  intro c _ ⟨a, hc⟩
  cases a with
  | p0 =>
      rw [fa0_p0] at hc; simp at hc
      rcases hc with h | h
      · subst h; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · subst h; exact Or.inl rfl
  | p1 =>
      rw [fa0_p1] at hc; simp at hc
      rcases hc with h | h
      · subst h
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          rfl))))))
      · subst h; exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | p2 =>
      rw [fa0_p2] at hc; simp at hc
      rcases hc with h | h
      · subst h
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl rfl))))))
      · subst h; exact Or.inr (Or.inr (Or.inl rfl))
  | p3 => rw [fa0_p3] at hc; cases hc
  | p4 => rw [fa0_p4] at hc; cases hc
  | p5 =>
      rw [fa0_p5] at hc; simp at hc
      rcases hc with h | h
      · subst h; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      · subst h; exact Or.inr (Or.inl rfl)
  | p6 => rw [fa0_p6] at hc; cases hc

/-- **THE STUCK BOARD**: `fa0` is exhausted — every hot face-up card
is guard-declined (each of the eight standing cards is a member of
an intact mobile pair: the twos pair with twos, the threes pair
with threes), and no slide places (the only face-up tops are the
four twos, all rank one: no face-up ace exists to sit on them, and
no empty pile takes a non-king). -/
theorem fa0_stuck : AscentStuck fa0 := by
  intro m hm
  rcases hm with ⟨c, hmEq, hhot, hface, hguard⟩ | ⟨c, b, hmEq⟩
  · rcases fa0_faceUp c (Card.mem_universe c) hface with h | h | h | h | h | h | h | h
    all_goals subst h
    all_goals exact absurd rfl (hguard _ ((mobileTwinB_iff _ _).mp (by decide))).1
  · rw [hmEq]
    cases b with
    | inl n =>
        rcases c with ⟨cs, cr⟩ <;> cases cs <;> cases cr <;> cases n <;> decide
    | inr z =>
        rcases c with ⟨cs, cr⟩ <;> rcases z with ⟨zs, zr⟩ <;>
          cases cs <;> cases cr <;> cases zs <;> cases zr <;> decide

/-- **THE DELIVERED PAIR STANDS**: the black twos are double-hot and
intact at the exhausted board (kernel-decided). -/
theorem fa0_pairDelivered : DoubleHot fa0 faS2 ∧ MobileTwin fa0 faS2 :=
  ⟨⟨Anchor.p0, Anchor.p5, by decide, by decide, by decide, by decide⟩,
    ⟨⟨Anchor.p0, by decide⟩, by decide, ⟨Anchor.p5, by decide⟩, by decide⟩⟩

/-- **THE MULTI-PAIR WITNESS**: the red twos stand as a SECOND intact
mobile pair, and `faH2` is VANILLA-LIVE — hot, topping its pile over
its seat — outside the delivered black pair entirely. -/
theorem fa0_multiPair :
    MobileTwin fa0 faH2 ∧ CanRaise fa0 faH2 ∧
      faH2 ≠ faS2 ∧ faH2 ≠ faC2 :=
  ⟨⟨⟨Anchor.p2, by decide⟩, by decide, ⟨Anchor.p1, by decide⟩, by decide⟩,
    ⟨by decide, Anchor.p2, by decide, Or.inl (by decide : chop (fa0.piles Anchor.p2).faceUp ≠ [])⟩,
    by decide, by decide⟩

/-- **THE (⇒)-LOCAL FALSIFICATION**: the saturation iff fails at
`faH2` on the nose — outside the delivered pair, vanilla-live — at
an exhausted WF board; the multi-pair exclusion rides `hbelow`, not
the exhausted state alone. -/
theorem fa0_iff_point_false :
    ¬ ((faH2 = faS2 ∨ faH2 = faC2) ↔ CanRaiseS fa0 faH2) := by
  intro hiff
  have hL : faH2 = faS2 ∨ faH2 = faC2 :=
    hiff.mpr (CanRaiseS.now _ fa0_multiPair.2.1)
  rcases hL with h | h
  · exact fa0_multiPair.2.2.1 h
  · exact fa0_multiPair.2.2.2 h

private def faAS : Card := faCrd .spade .ace
private def faAC : Card := faCrd .club .ace

/-- **THE BARE-PAIR BOARD `fa1`** — rungs all empty; the black aces
bare over empty hidden decks (rank-0 cells: nothing can ever seat or
cover them); everything else sunk in the stock. -/
private def fa1 : State where
  found := fun _ => []
  piles := fun a => match a with
    | .p0 => ⟨[], [faAS]⟩
    | .p1 => ⟨[], [faAC]⟩
    | .p2 => ⟨[], []⟩
    | .p3 => ⟨[], []⟩
    | .p4 => ⟨[], []⟩
    | .p5 => ⟨[], []⟩
    | .p6 => ⟨[], []⟩
  stock :=
    [faCrd .spade .two, faCrd .spade .three, faCrd .spade .four,
     faCrd .spade .five, faCrd .spade .six, faCrd .spade .seven,
     faCrd .spade .eight, faCrd .spade .nine, faCrd .spade .ten,
     faCrd .spade .jack, faCrd .spade .queen, faCrd .spade .king,
     faCrd .heart .ace, faCrd .heart .two, faCrd .heart .three,
     faCrd .heart .four, faCrd .heart .five, faCrd .heart .six,
     faCrd .heart .seven, faCrd .heart .eight, faCrd .heart .nine,
     faCrd .heart .ten, faCrd .heart .jack, faCrd .heart .queen,
     faCrd .heart .king,
     faCrd .diamond .ace, faCrd .diamond .two, faCrd .diamond .three,
     faCrd .diamond .four, faCrd .diamond .five, faCrd .diamond .six,
     faCrd .diamond .seven, faCrd .diamond .eight, faCrd .diamond .nine,
     faCrd .diamond .ten, faCrd .diamond .jack, faCrd .diamond .queen,
     faCrd .diamond .king,
     faCrd .club .two, faCrd .club .three, faCrd .club .four,
     faCrd .club .five, faCrd .club .six, faCrd .club .seven,
     faCrd .club .eight, faCrd .club .nine, faCrd .club .ten,
     faCrd .club .jack, faCrd .club .queen, faCrd .club .king]
  waste := []
  drawStep := 1

private theorem fa1_wf_found : ∀ s : Suit, ∃ n, fa1.found s = s.upCards.take n := by
  intro s
  cases s <;> exact ⟨0, rfl⟩

private theorem fa1_wf_runs : ∀ a : Anchor, runOK (fa1.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

private theorem fa1_wf_count : ∀ c ∈ Card.universe, fa1.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

/-- The bare-pair board is `WF` (kernel-decided). -/
theorem fa1_wf : fa1.WF :=
  ⟨fa1_wf_found, fa1_wf_runs, fa1_wf_count, by decide⟩

private theorem fa1_p0 : fa1.piles .p0 = ⟨[], [faAS]⟩ := rfl
private theorem fa1_p1 : fa1.piles .p1 = ⟨[], [faAC]⟩ := rfl
private theorem fa1_p2 : fa1.piles .p2 = ⟨[], []⟩ := rfl
private theorem fa1_p3 : fa1.piles .p3 = ⟨[], []⟩ := rfl
private theorem fa1_p4 : fa1.piles .p4 = ⟨[], []⟩ := rfl
private theorem fa1_p5 : fa1.piles .p5 = ⟨[], []⟩ := rfl
private theorem fa1_p6 : fa1.piles .p6 = ⟨[], []⟩ := rfl

/-- **THE FACE-UP INVENTORY AT `fa1`**: only the bare pair stands. -/
theorem fa1_faceUp : ∀ c ∈ Card.universe,
    (∃ a, c ∈ (fa1.piles a).faceUp) → c = faAS ∨ c = faAC := by
  intro c _ ⟨a, hc⟩
  cases a with
  | p0 => rw [fa1_p0] at hc; simp at hc; exact Or.inl hc
  | p1 => rw [fa1_p1] at hc; simp at hc; exact Or.inr hc
  | p2 => rw [fa1_p2] at hc; simp at hc
  | p3 => rw [fa1_p3] at hc; simp at hc
  | p4 => rw [fa1_p4] at hc; simp at hc
  | p5 => rw [fa1_p5] at hc; simp at hc
  | p6 => rw [fa1_p6] at hc; simp at hc

/-- **THE STUCK BOARD**: `fa1` is exhausted — the raise arm declines
by the pair's own guard (each ace's twin stands face-up intact, so
founding either member would eat the pair, which the full-time guard
refuses), and no slide places (the two face-up tops fit neither each
other — same rank — nor an empty king seat — neither is a king). -/
theorem fa1_stuck : AscentStuck fa1 := by
  intro m hm
  rcases hm with ⟨c, hmEq, hhot, hface, hguard⟩ | ⟨c, b, hmEq⟩
  · rcases fa1_faceUp c (Card.mem_universe c) hface with h | h
    all_goals subst h
    all_goals exact absurd rfl (hguard _ ((mobileTwinB_iff _ _).mp (by decide))).1
  · rw [hmEq]
    cases b with
    | inl n =>
        rcases c with ⟨cs, cr⟩ <;> cases cs <;> cases cr <;> cases n <;> decide
    | inr z =>
        rcases c with ⟨cs, cr⟩ <;> rcases z with ⟨zs, zr⟩ <;>
          cases cs <;> cases cr <;> cases zs <;> cases zr <;> decide

/-- **THE DELIVERED PAIR STANDS**: the black aces are double-hot and
intact at the exhausted board (kernel-decided). -/
theorem fa1_pairDelivered : DoubleHot fa1 faAS ∧ MobileTwin fa1 faAS :=
  ⟨⟨Anchor.p0, Anchor.p1, by decide, by decide, by decide, by decide⟩,
    ⟨⟨Anchor.p0, by decide⟩, by decide, ⟨Anchor.p1, by decide⟩, by decide⟩⟩

/-- **THE (⇐)-LOCAL FALSIFICATION, PREP**: both bare members are
VANILLA-DEAD at the exhausted board — ace cells can never seat
(no face-up content below, aces not kings) and can never be covered
(nothing sits on a rank-0 cell), so the vanilla license fails at
each member outright. -/
theorem fa1_membersDead : ¬ CanRaise fa1 faAS ∧ ¬ CanRaise fa1 faAC := by
  constructor
  · rintro ⟨-, k, hk, (hchop | ⟨-, hking⟩)⟩
    · rw [show fa1.pileOfTop faAS = some Anchor.p0 from by decide] at hk
      have hkP0 : k = Anchor.p0 := (Option.some.inj hk).symm
      rw [hkP0, show (fa1.piles Anchor.p0).faceUp = [faAS] from rfl,
        show chop [faAS] = ([] : List Card) from rfl] at hchop
      exact absurd rfl hchop
    · exact absurd hking (by decide)
  · rintro ⟨-, k, hk, (hchop | ⟨-, hking⟩)⟩
    · rw [show fa1.pileOfTop faAC = some Anchor.p1 from by decide] at hk
      have hkP1 : k = Anchor.p1 := (Option.some.inj hk).symm
      rw [hkP1, show (fa1.piles Anchor.p1).faceUp = [faAC] from rfl,
        show chop [faAC] = ([] : List Card) from rfl] at hchop
      exact absurd rfl hchop
    · exact absurd hking (by decide)

/-- **THE (⇐)-LOCAL FALSIFICATION**: the saturation iff fails at
`faAS` on the nose — inside the delivered pair, yet S-dead (the
collapse iff turns the S-read into the vanilla read, and both
members are vanilla-dead) — at an exhausted WF board; the
member-liveness half also rides `hbelow`, not the exhausted state
alone. -/
theorem fa1_iff_point_false :
    ¬ ((faAS = faAS ∨ faAS = faAC) ↔ CanRaiseS fa1 faAS) := by
  intro hiff
  have hR : CanRaiseS fa1 faAS := hiff.mp (Or.inl rfl)
  exact fa1_membersDead.1
    ((ascent_stuck_collapse_iff fa1_stuck faAS).mp hR)

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

/-! ## §1d. The bare-cover commit read (the corner's priced leg)

The corner's remaining §1-grade datum, priced at the takeover pass:
the corner's named slide FIRES, and the successor's shape is the
spelled commit — the covering run lands whole on the twin's pile
(the twin covered beneath the cover's head), and the emptied source
pile either reveals its hidden head or burns to the bare empty
pile.  The one-move RESTORE is unavailable except through a fitting
revealed card (the seated-corner's below-content fit is gone at the
bare shape), so the saturation transfer cannot ride — this is the
resurrection mode the corner's docstring prices. -/

/-- The emptied pile's flip at a revealing hidden deck (the commit's
burn-mode companion kit row). -/
private theorem ascent_afterRunRemoved_reveal {p : Pile} {z : Card} {t : List Card}
    (h : p.hidden = z :: t) :
    Pile.afterRunRemoved p [] = ⟨t, [z]⟩ := by
  simp only [Pile.afterRunRemoved, Pile.revealTop, h]
  rfl

/-- The emptied pile's burn at an empty hidden deck (the commit's
burn-mode kit row). -/
private theorem ascent_afterRunRemoved_burn {p : Pile}
    (h : p.hidden = []) :
    Pile.afterRunRemoved p [] = ⟨[], []⟩ := by
  simp only [Pile.afterRunRemoved, Pile.revealTop, h]

/-- **THE BARE-COVER COMMIT READ** (the corner's priced leg): at the
corner's shape — the twin topping its pile (the vanilla license's
own read), the fitting cover FIRST-FACED in its own pile — the named
slide `tabToTab d (Sum.inr x.twin)` FIRES, and the successor's shape
is the spelled commit: the covering run lands whole on the twin's
pile (the twin covered beneath `d`), the emptied source pile reveals
its hidden head or burns to the bare empty pile (the two priced
modes), every other pile untouched. -/
private theorem ascent_barecover_commit {W : State} (hwf : W.WF)
    {x d : Card}
    (hrank : d.rank.toIdx + 1 = x.rank.toIdx)
    (hfit : canSitOn d x.twin = true)
    (hctt : CanRaise W x.twin)
    {a : Anchor} {L₂ : List Card}
    (hspl : (W.piles a).faceUp = d :: L₂) :
    ∃ (W₁ : State) (k : Anchor),
      State.step W (Move.tabToTab d (Sum.inr x.twin)) = some W₁ ∧
      (W.piles k).top = some x.twin ∧
      W₁.piles k
        = ⟨(W.piles k).hidden, (W.piles k).faceUp ++ (d :: L₂)⟩ ∧
      ((∃ z t, (W.piles a).hidden = z :: t ∧
          W₁.piles a = ⟨t, [z]⟩) ∨
        ((W.piles a).hidden = [] ∧ W₁.piles a = ⟨[], []⟩)) ∧
      (∀ y, y ≠ a → y ≠ k → W₁.piles y = W.piles y) := by
  -- the twin tops its pile, read off the vanilla license
  obtain ⟨-, k, hk, -⟩ := hctt
  have hktwin : (W.piles k).top = some x.twin :=
    (pileOfTop_eq_some_iff hwf).1 hk
  have hmemT : x.twin ∈ (W.piles k).faceUp := Pile.mem_of_top hktwin
  -- the cover is never its own twin (the fit arithmetic)
  have hdxt : d ≠ x.twin := by
    intro hcon
    obtain ⟨hr1, -⟩ := (canSitOn_eq d x.twin).mp hfit
    rw [hcon, Card.twin_rank] at hr1
    omega
  -- the cover's residence and the fires-shape
  have hmemD : d ∈ (W.piles a).faceUp := by
    rw [hspl]; exact List.mem_cons_self
  have hhold : W.pileHolding d = some a := (pileHolding_eq_some_iff hwf).2 hmemD
  have hcan : W.canPlace d (Sum.inr x.twin) = true := by
    rw [canPlace_inr_located hk]
    exact hfit
  have hfrom : fromCard d (W.piles a).faceUp = d :: L₂ := by
    rw [hspl]
    exact ascent_fromCard_mid d [] L₂ (by intro hc; cases hc)
  have hbel : below d (W.piles a).faceUp = [] := by
    rw [hspl]
    exact ascent_below_stop d [] L₂ (by intro hc; cases hc)
  -- the step is the spelled splice
  obtain ⟨W₁, hstep, hW₁⟩ : ∃ W₁, State.step W (Move.tabToTab d (Sum.inr x.twin))
      = some W₁ ∧
      W₁ = (W.setPile a (Pile.afterRunRemoved (W.piles a) [])).putRun
        (d :: L₂) (Sum.inr x.twin) := by
    refine ⟨_, ?_, rfl⟩
    show (match W.pileHolding d with
      | none => none
      | some a₂ =>
          if W.canPlace d (Sum.inr x.twin) then
            match fromCard d (W.piles a₂).faceUp with
            | [] => none
            | run => some ((W.setPile a₂
                (Pile.afterRunRemoved (W.piles a₂)
                  (below d ((W.piles a₂).faceUp)))).putRun run (Sum.inr x.twin))
          else none) = _
    rw [hhold]
    simp only [hcan]
    rw [hfrom, hbel]
    rfl
  -- the twin's pile is not the cover's emptied pile
  have hka : k ≠ a := by
    intro hcon
    rw [hcon] at hmemT
    have hinspl : x.twin ∈ d :: L₂ := by rw [← hspl]; exact hmemT
    rcases List.mem_cons.mp hinspl with heq | hin
    · exact hdxt heq.symm
    · have hrok : runOK (d :: L₂) = true := by rw [← hspl]; exact hwf.2.1 a
      have hgt := ascent_runOK_head_gt hrok hin
      rw [Card.twin_rank] at hgt
      omega
  have hak : a ≠ k := fun h => hka h.symm
  -- the landing search pins the twin's pile at the mid state
  have hpotM : (W.setPile a (Pile.afterRunRemoved (W.piles a) [])).pileOfTop x.twin
      = some k := by
    refine ascent_topSearch _ ?_ ?_
    · rw [setPile_piles_ne hka]
      exact hktwin
    · intro y hy hyne
      by_cases hya : y = a
      · rw [hya, setPile_piles_self]
        show Pile.top (Pile.afterRunRemoved (W.piles a) []) ≠ some x.twin
        cases hhid : (W.piles a).hidden with
        | cons z t =>
            have hzmem : z ∈ (W.piles a).hidden := by
              rw [hhid]; exact List.mem_cons_self
            have hzne : z ≠ x.twin := fun hcon =>
              (mem_hidden_unique hwf hzmem k hka).2.1
                (by rw [hcon]; exact hmemT)
            have hflip := ascent_afterRunRemoved_reveal hhid
            rw [hflip]
            show lastOf ([z] : List Card) ≠ some x.twin
            exact fun hcon => hzne (Option.some.inj hcon)
        | nil =>
            have hflip := ascent_afterRunRemoved_burn hhid
            rw [hflip]
            exact fun hcon => absurd hcon (by simp [Pile.top, lastOf])
      · rw [setPile_piles_ne hya]
        exact fun hcon =>
          (mem_faceUp_unique hwf hmemT y hyne).1 (Pile.mem_of_top hcon)
  -- the successor's pile writes
  have hpK : W₁.piles k
      = ⟨(W.piles k).hidden, (W.piles k).faceUp ++ (d :: L₂)⟩ := by
    rw [hW₁, putRun_inr_eq hpotM, setPile_piles_self, setPile_piles_ne hka]
  have hpAeq : W₁.piles a
      = Pile.afterRunRemoved (W.piles a) [] := by
    rw [hW₁, putRun_piles_inr_ne _ _ _ k hpotM hak, setPile_piles_self]
  have hpA : (∃ z t, (W.piles a).hidden = z :: t ∧
      W₁.piles a = ⟨t, [z]⟩) ∨
      ((W.piles a).hidden = [] ∧ W₁.piles a = ⟨[], []⟩) := by
    cases hhid : (W.piles a).hidden with
    | cons z t =>
        refine Or.inl ⟨z, t, rfl, ?_⟩
        rw [hpAeq, ascent_afterRunRemoved_reveal hhid]
    | nil =>
        refine Or.inr ⟨rfl, ?_⟩
        rw [hpAeq, ascent_afterRunRemoved_burn hhid]
  have hpOther : ∀ y, y ≠ a → y ≠ k → W₁.piles y = W.piles y := by
    intro y hya hyk
    rw [hW₁, putRun_piles_inr_ne _ _ _ k hpotM hyk, setPile_piles_ne hya]
  exact ⟨W₁, k, hstep, hktwin, hpK, hpA, hpOther⟩

/-! ## §2e. The β-staging (takeover pass, evidence on record)

The owner-facing shape decision staged at the 2026-10-13 takeover
per the probe's repair-β draft: the delivered shape's cover clauses
weakened to a RECOVERABLE disjunct — the founded-at-frontier cell,
one licensed `foundToTab` return away — with the probe's `ab2`
armor and `ab1` recoverability certificates ON RECORD as evidence,
and the owner's ratification shaped as a ONE-LINE SWAP (consume
`ExhaustShapeRec` and this section's rows in place of the frozen
`ExhaustShape` legs; the frozen statements themselves are untouched
and nothing below is consumed until the owner decides):

(i) the α-armor datum, in the cell census's route note
    (`ascent_cover_cell` above, refined): the probe's `ab2_cellMobile`
    and `ab2_raiseNotAscent` witness the CELL GUARD TRAP — intact
    cover cells are founding-barred by the no-eat guard outright;
(ii) the β-companion rows, here: `ExhaustShapeRec` (the
    witness-restructured `TwinSlideHaltRec`) with the staged
    recoverable cover-read `ascent_cover_read_rec` [open, both arms
    `hbelow`-carried with the saturation residue], and the PROVED
    β-pullback `ascent_cover_pullback`: whatever the census
    delivers, the founded-cell side collapses to the standing shape
    in ONE licensed leg. -/

/-- **THE RECOVERABLE-SHAPE STAGING** — the β-delivery shape drafted
for the owner's ratification (the probe's `TwinSlideHaltRec`
witness-restructured to track the frozen `ExhaustShape`'s binder
shape): the standing cover clauses DISJOINED with the
founded-at-frontier clauses. -/
def ExhaustShapeRec (st : State) (x d : Card) : Prop :=
  DoubleHot st x ∧
    d.rank.toIdx + 1 = x.rank.toIdx ∧
    d.suit.color ≠ x.suit.color ∧
    canSitOn d x.twin = true ∧
    ((d.rank.toIdx ≥ st.foundHeight d.suit ∧
        (∃ (c : Anchor), d ∈ (st.piles c).faceUp)) ∨
      (st.foundTop d.suit = some d ∧
        d.rank.toIdx + 1 = st.foundHeight d.suit ∧
        ∃ (e : Card), st.canPlace d (Sum.inr e) = true))

/-- The chop of a list with a last card (the kit row for the
founded-row length reads; the abstract statement avoids the
self-referential reshape). -/
private theorem ascent_lastOf_chop_length {l : List Card} {c : Card}
    (h : lastOf l = some c) :
    (chop l).length + 1 = l.length := by
  obtain ⟨fr, hfe⟩ := lastOf_eq_snoc h
  rw [hfe, chop_snoc, List.length_append]
  simp

/-- The top-search reads only piles (the per-file private congr
row, the `pileHolding_congr` twin). -/
private theorem ascent_pileOfTop_congr {st s' : State} {c : Card}
    (hp : st.piles = s'.piles) : st.pileOfTop c = s'.pileOfTop c := by
  show firstWhere (fun a => decide (Pile.top (st.piles a) = some c)) Anchor.all = _
  rw [hp]
  rfl

/-- **THE β-PULLBACK ROW** (takeover staging, PROVED): the
recoverable-cover parcel PULLS BACK to the standing shape in ONE
licensed `foundToTab` leg — a cover founded at its suit's frontier,
with a licensed return base present at the same state, lands the
frozen `ExhaustShape` at the successor: the pull writes only the
cover's own foundation row and the return base's pile (the pair's
family rungs and members untouched), so the pair stays double-hot
and the cover re-seats face-up one above the founded cell. -/
theorem ascent_cover_pullback {W : State} {x d e : Card}
    (hrank : d.rank.toIdx + 1 = x.rank.toIdx)
    (hcol : d.suit.color ≠ x.suit.color)
    (hfit : canSitOn d x.twin = true)
    (hdh : DoubleHot W x)
    (hfront : W.foundTop d.suit = some d)
    (hfh : d.rank.toIdx + 1 = W.foundHeight d.suit)
    (hbase : W.canPlace d (Sum.inr e) = true) :
    ∃ (W' : State), State.step W (Move.foundToTab d (Sum.inr e)) = some W' ∧
      ExhaustShape W' x d := by
  -- the licensed base locates the return pile
  obtain ⟨k, hk⟩ : ∃ k, W.pileOfTop e = some k := by
    by_cases hp : W.pileOfTop e = none
    · rw [canPlace_inr_eq, hp] at hbase
      simp at hbase
    · obtain ⟨k, hk₀⟩ := option_some_of_ne_none hp
      exact ⟨k, hk₀⟩
  -- the pull fires; the successor is the spelled splice
  obtain ⟨W', hstep, hW'⟩ : ∃ W', State.step W (Move.foundToTab d (Sum.inr e))
      = some W' ∧
      W' = (W.setFound d.suit (chop (W.found d.suit))).putCard d (Sum.inr e) :=
    ⟨(W.setFound d.suit (chop (W.found d.suit))).putCard d (Sum.inr e),
      step_foundToTab_splice hfront hbase, rfl⟩
  -- the successor's writes: pile `k` gains the cover, every other
  -- zone is untouched except the cover's own foundation row
  have hpilesEq : (W.setFound d.suit (chop (W.found d.suit))).piles
      = W.piles := rfl
  have hpotM : (W.setFound d.suit (chop (W.found d.suit))).pileOfTop e
      = some k := by
    rw [ascent_pileOfTop_congr hpilesEq]
    exact hk
  have hMspl : (W.setFound d.suit (chop (W.found d.suit))).putCard d (Sum.inr e)
      = (W.setFound d.suit (chop (W.found d.suit))).setPile k
        { W.piles k with faceUp := (W.piles k).faceUp ++ [d] } := by
    rw [putCard_inr_eq hpotM]
    rfl
  have hpK : W'.piles k
      = { W.piles k with faceUp := (W.piles k).faceUp ++ [d] } := by
    rw [hW', hMspl, setPile_piles_self]
  have hpOther : ∀ y, y ≠ k → W'.piles y = W.piles y := by
    intro y hne
    rw [hW', hMspl, setPile_piles_ne hne]
    rfl
  have hFD : W'.found d.suit = chop (W.found d.suit) := by
    rw [hW', putCard_inr_found, setFound_found_self]
  have hFO : ∀ s, s ≠ d.suit → W'.found s = W.found s := by
    intro s hne
    rw [hW', putCard_inr_found, setFound_found_ne hne]
  -- the cover's height clause at the successor: exactly its rank
  have hW'D : (W'.found d.suit).length = d.rank.toIdx := by
    rw [hFD]
    have hl := ascent_lastOf_chop_length
      (show lastOf (W.found d.suit) = some d from hfront)
    have h1 : d.rank.toIdx + 1 = (W.found d.suit).length := hfh
    omega
  -- the family rungs survive: the pull wrote only the cover's suit
  have hxne : x.suit ≠ d.suit := by
    intro hcon
    rw [hcon] at hcol
    exact hcol rfl
  have hxtcol : x.twin.suit.color = x.suit.color := by
    rw [Card.twin_suit, Suit.color_twin]
  have hxtne : x.twin.suit ≠ d.suit := by
    intro hcon
    apply hcol
    rw [← hcon, hxtcol]
  -- the pair members stay face-up and hot
  obtain ⟨a, b, hxa, hxtb, hxr, hxtr⟩ := hdh
  have hxa' : x ∈ (W'.piles a).faceUp := by
    by_cases ha : a = k
    · rw [ha, hpK]
      exact List.mem_append.mpr (Or.inl (by rw [← ha]; exact hxa))
    · rw [hpOther a ha]; exact hxa
  have hxtb' : x.twin ∈ (W'.piles b).faceUp := by
    by_cases hb : b = k
    · rw [hb, hpK]
      exact List.mem_append.mpr (Or.inl (by rw [← hb]; exact hxtb))
    · rw [hpOther b hb]; exact hxtb
  have hxr' : x.rank.toIdx = (W'.found x.suit).length := by
    rw [hFO x.suit hxne]; exact hxr
  have hxtr' : x.twin.rank.toIdx = (W'.found x.twin.suit).length := by
    rw [hFO x.twin.suit hxtne]; exact hxtr
  -- the cover's own seating clause
  have hdm : d ∈ (W'.piles k).faceUp := by
    rw [hpK]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  have hge : d.rank.toIdx ≥ (W'.found d.suit).length := by
    rw [hW'D]; exact Nat.le_refl _
  exact ⟨W', hstep, ⟨⟨a, b, hxa', hxtb', hxr', hxtr'⟩, hrank, hcol,
    hge, ⟨k, hdm⟩, hfit⟩⟩

/-- **THE RECOVERABLE COVER-READ, STAGED** `ascent_cover_read_rec`
(staged at the takeover pass for the owner's ratification — the
β-companion of `ascent_cover_read` above, byte-shaped for the
one-line swap): at the exhausted delivered state, a fitting cover is
delivered whose cover clauses read EITHER standing (the frozen
α-clauses) OR founded-at-frontier with a licensed return base (the
burial case the probe's `ab1` witness makes load-bearing).

ROUTE (a pure router over the α-census, PROVED here modulo the named
α-residue — the standing clauses are literally the left disjunct, so
the row's own body is assembly):

* THE STANDING ARM is the α-content verbatim (`ascent_cover_read`,
  riding `ascent_cover_cell`'s census); the arm's W-local
  falsifiability is the probe's own `ab1` evidence (a genuine stuck
  exhaustion with NO standing fitting cover — the board is
  `hbelow`-undecided, so the frozen row survives; only the census's
  reachability content is open).
* THE β-LINK IS PROVED (`ascent_cover_pullback` above): whatever the
  census eventually delivers on the recoverable side — the burial
  case priced by the probe's `ab2` armor (`ab2_cellMobile`,
  `ab2_raiseNotAscent`: intact cells are founding-barred outright,
  so the founding mode needs a pre-broken cell pair, and whether
  `hbelow`'s boards ever arrive pre-broken is the probe's declared
  open, its §5 verdict) — pulls back to the standing shape in ONE
  licensed `foundToTab`.  A ratification of `ExhaustShapeRec`
  consumes the climb-saturation pieces and this census unchanged;
  the exhaustion row's own body swaps legs by name, not by rebuild. -/
private theorem ascent_cover_read_rec {W : State} (hwf : W.WF)
    (hstuck : AscentStuck W)
    {x : Card}
    (hxdel : DoubleHot W x ∧ MobileTwin W x ∧
      rungAt W x.suit ≤ x.rank.toIdx ∧
      rungAt W x.twin.suit ≤ x.rank.toIdx)
    (hiff : ∀ (c : Card), (c = x ∨ c = x.twin) ↔ CanRaiseS W c) :
    ∃ (d : Card), ExhaustShapeRec W x d := by
  obtain ⟨d, hd1, hd2, hd3, hd4, hd5⟩ :=
    ascent_cover_read hwf hstuck hxdel hiff
  exact ⟨d, hxdel.1, hd1, hd2, hd5, Or.inl ⟨hd3, hd4⟩⟩

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
geometric restore, the saturation transfer, and (takeover) the
bare-cover COMMIT READ with its reveal/burn mode kit — are private
per the house discipline and audited through the main row's own
profile.  The §2 machinery banks the zero-sorry collapse pair
(`ascent_stuck_collapse`, `ascent_stuck_unblocked`), the
SELF-LANDING REFUTATION `ascent_selfland_refuted`, and (takeover)
the stuck-state lattice kit — the collapse iff, the `MobileTwin`
decider and the constructive live-member read, the cover/twin-top
bar — all private, no classical choice, riding `propext` only.  The
takeover's public fresh heads: the §2d falsification-economy boards
(decide-grade, empty axiom profile — kernel-witnessed WF, stuckness,
delivery, and the two pointed iff-witnesses), and the β-pullback
`ascent_cover_pullback` (WF-free, banked reading rows only).  The
remaining open content sits in the four named pieces (bare-cover
corner, climb delivery, stuck saturation, cover-cell census), each
with its complete re-priced route where it is declared: the
saturation's and the parking's `hbelow`-carried halves are named
with their boards' evidence; the β-companion's swap is staged in
§2e, nothing consumed until the owner ratifies. -/

#print axioms orientation_assembly_fork
#print axioms ascent_stuck_collapse
#print axioms ascent_stuck_unblocked
#print axioms ascent_selfland_refuted
#print axioms ascent_cover_pullback
#print axioms fa0_wf
#print axioms fa0_stuck
#print axioms fa0_pairDelivered
#print axioms fa0_multiPair
#print axioms fa0_iff_point_false
#print axioms fa1_wf
#print axioms fa1_stuck
#print axioms fa1_pairDelivered
#print axioms fa1_membersDead
#print axioms fa1_iff_point_false
#print axioms ascent_exhaustion_forks
