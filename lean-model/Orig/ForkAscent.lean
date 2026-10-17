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

SECOND SUCCESSION PASS (2026-10-13, session 4): the mission's named
induction — `ascent_pair_persists` (§2c-pre, the persistent pair) —
is BANKED with its full kit: the slide-arm face-up preservation
(`ascent_slide_faceUp`, over the mid-state landing pin
`ascent_slideLanding`, the burn bar `ascent_slideBase_ne` off the
self-landing refutation, and the rung freeze `ascent_slide_rung`),
the index-exact cap arithmetic (`ascent_idxCap_of_ne`), and the
`MobileTwin` re-pack (`ascent_persist_mobile`); the two §1d
emptied-pile mode rows (`ascent_afterRunRemoved_reveal/burn`) moved
to the kit's site, single-homed.  Both climb-delivery kernels are
now BANKED and their route text says so; the saturation's
reveal-gap note is now banked leg-work with the witness tracked to
`W` itself.  The four frozen residues keep their grades — the
parking-at-r, the multi-pair exclusion, the member-liveness, the
cover-cell census, and the resurrection-mode corner all still ride
`hbelow`/the probe's declared open, exactly as their routes say
(never forced).  Zero `Classical.choice`; battery extended to the
new heads.

THIRD SUCCESSION PASS (2026-10-13, session 5, the falsification
economy's first frozen kill): the cover-cell mini falls to
FALSIFICATION — the board `fa2` and the certified negation
`ascent_cover_cell_refuted` below: the cover-cell census's frozen
statement is W-LOCAL and FALSE — it carries no `hbelow` premise to
retreat behind — and the refutation is decide-grade in-file (all
four aces founded; the black twos double-hot, intact and seated over
the red threes; both red twos stocked outside the tableau's reach; a
WF, stuck, saturated board — `fa2_iff` is the file's first CERTIFIED
SATURATION WITNESS — with NO fitting cover: the only `r−1`
opposite-family cells are the red aces, both founded below their
frontiers).  The residue keeps its sorry — the honest witness of a
FALSE row, on the `Orig/ForkDescent.lean` §3R precedent.  The
bare-cover corner gains its second banked leg
(`ascent_barecover_landing_pin`: the commit's successor carries the
pin outright, isolating the corner's open to the landing's saturation
half); the climb and saturation minis keep their `hbelow`-carried
verdicts — both routes terminate at the probe's declared open, with
`fa0`/`fa1` the W-local falsification witnesses and `fa2` the
positive complement.  The four frozen statements are byte-untouched;
battery extended to the new heads.

THIRD-SUCCESSION CEILING LANDING (2026-10-13, the second lander of
the third succession): the UNIVERSAL CONSTANT behind the `fa2` kill
is banked — **THE LIVE-CARD COVER-FIRES BAR**
(`ascent_stuck_livecover_bar`): at a stuck state a vanilla-live
card admits NO face-up card that fits it, because the fitting
cover's slide onto the live card's top is an ascent move that FIRES
(the `ascent_tabToTab_fires` kit) against the exhaustion.
Consequences landed as rows, not prose: the **EXHAUSTION-SHAPE
CEILING** (`ascent_exhaust_shape_impossible`) — the frozen
exhaustion row's own conclusion (standing cover + saturation iff)
is impossible at EVERY `WF` stuck state, so the row's only live
futures are vacuity or the owner's `ExhaustShapeRec`
β-ratification, whose licensed founded-cell return base is exactly
the topped twin the iff's liveness forces; the **CORNER-BAR**
(`ascent_barecover_barred_atStuck`) — the bare-cover corner's
hypotheses are contradictory at every stuck world, so the corner's
surviving content is cold-assembly-only; and the staged reductions
for the two `hbelow`-carried minis (the climb's parking row
`ascent_climb_of_parked`, the saturation's decomposition
`ascent_stuck_sat_of_excLive`, the cell-armor row
`ascent_cell_armor`) — each names exactly its remaining premise.
The four frozen statements stay byte-untouched; the four sorries
stay; zero `Classical.choice`; battery extended to the new heads.

FOURTH SUCCESSION PASS (2026-10-17, session 6): the frontier's priced
kernels land as rows and the four frozen residues keep their grades,
unchanged.  THE CORNER's assembly content below the census is fully
staged — `ascent_tilted_snap` (the twin-flipped snap: when the
witness side's vanilla license already fails, the state itself is the
fork at the TILTED orientation, no move played) and
`ascent_barecover_of_landingiff` (the named-premise reduction: the
banked commit read plus the landing pin reduce the corner to
EXACTLY the pair's saturation iff at the commit's successor), so the
corner's surviving content is exactly the BOTH-LIVE cold census.
THE SATURATION's `fa1` axis is shrunk W-locally —
`ascent_stuck_memberLive_split` (with the banked cover/twin-top bar,
one vanilla-live member forces the other member to TOP, so its
liveness can fail only at a LITERALLY BARE non-king seat — the `fa1`
shape extracted as the one remaining read, with the twin-flip
re-pack rows for the mirror instantiation).  THE β-FUTURE is
witnessed end-to-end — `ascent_rec_base_of_iff` (at any stuck
saturated world the founded cover's licensed return base is the
iff-forced topped twin, the ceiling prose's named constant, landed
public), `fa2_shapeRec` (the file's own saturated board fa2 DELIVERS
the recoverable shape: the β-arm is nonvacuous at a genuine stuck
exhaustion) and `fa2_pullWitness` (the licensed `foundToTab` pull
fires at fa2, landing the standing `ExhaustShape` in one leg).  The
four frozen statements stay byte-untouched; the four sorries stay;
zero `Classical.choice`; battery extended to the new heads.

SIXTH-SUCCESSION CENSUS ECONOMY PASS (2026-10-17, session 8): the
fifth succession's census verdict gains its staged general rows —
the landing site census `ascent_barecover_res_sites` (the commit
landing's face-up cards sit in exactly the three spelled sites: the
twin's pile, the emptied source's revealed head or nothing, and
third piles restored verbatim), the GENERAL member half
`ascent_barecover_landing_sat` (at every both-live world both pair
members stay S-live at the commit landing — the hotness by the rung
freeze, the covered member's kept seat with the exit re-armed by the
exposed member's top, the exposed member riding its own license
through the third-pile restore leg or the moved run's rider), and
the census cut `ascent_barecover_corner_of_nores` (the both-live arm
closes given exactly one datum: no card outside the pair is S-live
at the landing — `fa3_resurrected` refutes that datum at a
corner-shaped world, so the corner's sorry stands as the census
verdict's honest residue).  The four frozen statements stay
byte-untouched; the four sorries stay; zero `Classical.choice`;
battery extended to the new heads.
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

/-- **THE TILTED SNAP** (the orientation row's second zero-move arm,
banked at the fourth succession): when the pair's saturation clauses
hold but the WITNESS side's vanilla license fails (the twin's holds),
the state itself is the fork — at the TWIN-FLIPPED orientation.  The
saturation clause is the same iff read through the twin flip
(`Card.twin_twin` plus the commutative left disjunct), and the pin is
the failed license verbatim (the orientation row's `ascent_snap`,
twin-flipped).  The bare-cover corner consumes this below: whenever
`¬ CanRaise W x` holds alongside its own `hctt`, the corner closes
with NO move at all, so its surviving content is exactly the
BOTH-LIVE cold shape. -/
private theorem ascent_tilted_snap {W : State} {x : Card}
    (hsat : ∀ (c : Card), (c = x ∨ c = x.twin) ↔ CanRaiseS W c)
    (hnx : ¬ CanRaise W x) :
    ∃ (F : State) (τ : List Move) (x' : Card),
      W.run τ = some F ∧ ForkWitness F x' := by
  refine ⟨W, [], x.twin, rfl, ⟨?_, by rw [Card.twin_twin]; exact hnx⟩⟩
  intro c
  constructor
  · rintro (rfl | h)
    · exact (hsat x.twin).mp (Or.inr rfl)
    · rw [Card.twin_twin] at h
      exact (hsat c).mp (Or.inl h)
  · intro hS
    rcases (hsat c).mpr hS with h | h
    · exact Or.inr (by rw [h, Card.twin_twin])
    · exact Or.inl h

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
saturation transfer's round trip cannot ride.

THIRD-SUCCESSION LANDING (2026-10-13, session 5): the landed PIN
half is banked as `ascent_barecover_landing_pin` (§1d): the commit's
successor carries `¬ CanRaise W₁ x.twin` outright — the covered twin
tops no pile at the landed state (its own pile is capped by the moved
run's rider, the emptied source either reveals a hidden card or
burns to the bare empty pile, and WF uniqueness forbids every other
pile), so the corner's remaining open is EXACTLY the saturation half
at the landing (the resurrection census above, no larger).

SECOND-LANDER ADDENDUM: the corner is now BARRED at every stuck
world outright — `ascent_barecover_barred_atStuck` (the twin's
vanilla license together with ANY face-up card fitting it contradicts
`AscentStuck` via the live-cover bar): the route-note's second
branch ("a census argument shows the residue corner unreachable
from every world the exhaustion row delivers") is decided — no
stuck world carrying a fitting face-up cover can reach the corner,
and every world the saturation-iff row would feed the assembly
carries one.  The landing pin above plus this bar leave the corner's
[M] content exactly the COLD (non-stuck) assembly worlds.

FOURTH-SUCCESSION ROUTE TRUING (2026-10-17): the corner's assembly
content below the census is now FULLY STAGED as rows — the free
tilt `ascent_tilted_snap` above (when the witness side's license
`CanRaise W x` fails, the state itself forks at the `x.twin`
orientation, so the corner's hypotheses are THEN closed outright),
and the NAMED LANDING PREMISE `ascent_barecover_of_landingiff`
(§1d, below: the banked commit read together with the landing pin
reduce the corner to EXACTLY the pair's saturation iff at the
commit's successor state `W₁`).  The surviving open is thereby the
BOTH-LIVE cold census alone — both members vanilla-live at `W`, the
named commit firing, and the emptied side's reveal/burn seat open to
re-admitting S-live cards outside the pair at `W₁` (the resurrection
census priced above), at the reduced one-premise shape the new row
names.

FIFTH-SUCCESSION CENSUS VERDICT (2026-10-17, session 7): the
both-live cold resurrection census is now DECIDED at the kernel —
REFUTED as universally staged.  The witness board `fa3` (§2f below)
carries this row's every hypothesis at the census's own both-live
scope (both queens vanilla-live), the named slide fires, and the
emptied side's reveal tops a card whose buried mate — hot and seated
since `W` — re-enters the S-set through the flat characterization's
covered-leg exit channel (`canRaiseS_iff`'s twin-top disjunct): at
the commit's successor the pair's saturation iff FAILS at a third
card (`fa3_census_refuted`).  So the staged route — commit + landing
pin + `ascent_barecover_of_landingiff`'s named premise — cannot
close this residue universally; the recourse is statement-level (an
emptied-side exclusion premise, or the exhaustion row's longer
search).  The row keeps its sorry honestly, on the `fa2`/§3R
precedent — the frozen statement is untouched, and the sorry count
stays exactly FOUR.

SIXTH-SUCCESSION CENSUS ECONOMY (2026-10-17, session 8): the
verdict's cut surface is now staged as rows (§1d below) — the site
census `ascent_barecover_res_sites` (the landing's face-up cards sit
in exactly the three spelled sites), the member half
`ascent_barecover_landing_sat` (the ⇐ half, now GENERAL: at every
both-live world, both members stay S-live at the commit landing —
`fa3_membersLive` is its board instance, no longer the only
evidence), and the census cut `ascent_barecover_corner_of_nores`
(the both-live arm closes given EXACTLY ONE datum: no card outside
the pair is S-live at the landing).  That datum is what the `fa3`
board refutes at a corner-shaped world (`fa3_resurrected`), so the
cut's premise is not W-forcible — the honest census is now complete:
the pair half holds universally, the third-card half is the named
non-forcing datum, and this row keeps its sorry for the owner's
statement-level recourse. -/
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

/-- **THE SLIDE-FIRES KIT** (private): at a `WF` state, a face-up
card with an accepted placement FIRES — the `tabToTab` branch of the
step never answers `none` (the holding search locates the card, the
placement guard accepts, and the run from the card is nonempty since
the card itself heads it).  The row the stuck-state bars cite. -/
private theorem ascent_tabToTab_fires {st : State} (hwf : st.WF)
    {d : Card} {b : Base} (hmem : ∃ a, d ∈ (st.piles a).faceUp)
    (hcan : st.canPlace d b = true) :
    State.step st (Move.tabToTab d b) ≠ none := by
  obtain ⟨a, hm⟩ := hmem
  have hhold : st.pileHolding d = some a :=
    (pileHolding_eq_some_iff hwf).2 hm
  obtain ⟨t, ht⟩ := fromCard_eq_head_of_mem hm
  intro hnone
  rw [step_tabToTab_eq, hhold] at hnone
  simp only [hcan] at hnone
  rw [ht] at hnone
  simp at hnone

/-- **THE LIVE-CARD COVER-FIRES BAR** (the third succession's
universal row): at a STUCK state a vanilla-live card admits NO
face-up card that fits it — the slide of the fitting card onto the
live card's top is an ascent move (the slide arm is unconditional),
the placement is accepted (the live card's own license tops a
located pile and the fit is the placement guard's own arithmetic),
and the step FIRES by the kit above — against `AscentStuck`.  This
is the row behind all three delivered-world falsifications at once:
the exhaustion row's own conclusion (`ExhaustShape` demands exactly
this standing cover beside the iff's live twin), the cover-cell
census's face-up conclusion at any saturated board (the census's
`d` fits the live twin by twin-blind rank-and-color arithmetic), and
the bare-cover corner's `hctt` (the corner's own hypotheses are
contradictory at every stuck world carrying the cover datum). -/
theorem ascent_stuck_livecover_bar {W : State} (hwf : W.WF)
    (hstuck : AscentStuck W)
    {t d : Card}
    (hcr : CanRaise W t)
    (hmem : ∃ a, d ∈ (W.piles a).faceUp)
    (hfit : canSitOn d t = true) : False := by
  obtain ⟨-, k, hk, -⟩ := hcr
  have hcan : W.canPlace d (Sum.inr t) = true := by
    rw [canPlace_inr_located hk]
    exact hfit
  have hnone := hstuck (Move.tabToTab d (Sum.inr t))
    (Or.inr ⟨d, Sum.inr t, rfl⟩)
  exact ascent_tabToTab_fires hwf hmem hcan hnone

/-- **THE CORNER IS BARRED AT STUCK WORLDS** (the corner route's
second named content, landed as a kernel row — not prose): the
bare-cover corner's own hypotheses — the twin's vanilla license
together with ANY face-up card fitting it — are CONTRADICTORY at
every exhausted state, because the corner's named slide is exactly
the bar's refused slide.  The residue's "either a longer τ reaches a
fork, or a census argument shows the residue corner unreachable from
every world the exhaustion row delivers" is thereby decided on its
second branch: NO stuck world carrying a fitting face-up cover can
reach the corner, and every world the saturation-iff row would feed
the assembly carries one.  The corner's [M] residue keeps its
content for the COLD assembly worlds only (states that are not
stuck), where the commit row and the landing pin still leave the
saturation half at the landing open. -/
private theorem ascent_barecover_barred_atStuck {W : State} (hwf : W.WF)
    (hstuck : AscentStuck W)
    {x d : Card}
    (hctt : CanRaise W x.twin)
    (hfit : canSitOn d x.twin = true)
    (hdface : ∃ a, d ∈ (W.piles a).faceUp) : False :=
  ascent_stuck_livecover_bar hwf hstuck hctt hdface hfit

/-! ### The persistent pair (the guard-persistence and index-exact
kernels, banked)

The two kernels the climb and saturation routes priced "[priced, next
pass]" at the 2026-10-13 takeover, banked here as ONE induction:

* **THE GUARD PERSISTS** — every ascent leg is a raise (the no-eat
  guard declines every intact pair's member; the banked
  `ascent_faceUp_raise` keeps every other face-up card face-up) or a
  slide (face-up material relocates WHOLE: every face-up card of the
  pre-state is face-up at the successor — `ascent_slide_faceUp`, the
  slide-arm twin of the raise row, landed here with the mid-state
  landing pin `ascent_slideLanding` and the burn-bar
  `ascent_slideBase_ne` refuting the own-pile base read via the
  self-landing refutation);
* **THE RUNGS ARE INDEX-EXACT** — a raise climbs its suit's rung by
  exactly one (the next-up guard), and crossing a family member's
  rank would require founding the member itself (same suit + same
  index IS the card), which the guard declines while the pair stands
  intact: `ascent_idxCap_of_ne` prices the arithmetic;
* **THE PERSISTENT PAIR** — a card and its twin, both face-up at the
  start and both at-or-above their family rungs there, stay
  face-up, paired, and capped at the start's margins along EVERY
  ascent run (`ascent_pair_persists`); `ascent_persist_mobile`
  re-packs the four surviving clauses as `MobileTwin` at the landing.

These rows carry NO stuckness and NO `hbelow` content — they are pure
leg-work: the climb delivery's parking argument, the saturation's
reveal-gap note, and the multi-pair residue's start-economy all rest
on them without consuming any open census. -/

/-- The rung read and the foundation-height read are the same
function (the glue the cap rows cite). -/
private theorem ascent_rung_height (w : State) (σ : Suit) :
    rungAt w σ = w.foundHeight σ := rfl

/-- **THE INDEX-EXACT CAP ARITHMETIC**: a card of the SAME suit whose
index sits at-or-below a family member's, and which is not that
member, sits strictly below it (crossing the member's index would
require being the member: suit and index name the card). -/
private theorem ascent_idxCap_of_ne {x z : Card}
    (hcap : z.rank.toIdx ≤ x.rank.toIdx)
    (hsuit : z.suit = x.suit) (hne : z ≠ x) :
    z.rank.toIdx + 1 ≤ x.rank.toIdx := by
  obtain ⟨zs, zr⟩ := z
  obtain ⟨xs, xr⟩ := x
  have hss : zs = xs := hsuit
  by_cases hr : zr.toIdx = xr.toIdx
  · refine absurd ?_ hne
    show (⟨zs, zr⟩ : Card) = ⟨xs, xr⟩
    rw [hss, Rank.toIdx_inj hr]
  · have hcap' : zr.toIdx ≤ xr.toIdx := hcap
    have hne' : zr.toIdx ≠ xr.toIdx := hr
    have hgoal : zr.toIdx + 1 ≤ xr.toIdx := by omega
    exact hgoal

/-- A cargo leg's landing never touches the foundations (the rung
passthrough at the put level). -/
private theorem ascent_putRun_foundHeight (w : State) (run : List Card)
    (b : Base) (σ : Suit) :
    (w.putRun run b).foundHeight σ = w.foundHeight σ := by
  cases b with
  | inl a => rfl
  | inr z =>
      show (match w.pileOfTop z with
             | some k => w.setPile k { w.piles k with faceUp := (w.piles k).faceUp ++ run }
             | none => w).foundHeight σ = w.foundHeight σ
      cases hpz : w.pileOfTop z with
      | some k => rfl
      | none => rfl

/-- **THE RUNG FREEZE, SLIDE ARM**: a fired slide leaves every
suit's rung exactly where it stood. -/
private theorem ascent_slide_rung {st s' : State} {d : Card} {b : Base}
    (hstep : State.step st (Move.tabToTab d b) = some s') (σ : Suit) :
    rungAt s' σ = rungAt st σ := by
  obtain ⟨a, -, -, -, hspl⟩ := step_tabToTab_inv hstep
  rw [hspl, ascent_rung_height _ σ, ascent_putRun_foundHeight,
    ascent_rung_height st σ]
  rfl

/-- **THE BURN BAR** (the self-landing refutation's own-pile read):
at a `WF` state, a fired slide's `inr` landing base tops a pile
OTHER than the departed run's source — the base cannot be the run's
own last rider (the guard's fit arithmetic is the rank contradiction
`ascent_selfland_refuted` prices). -/
private theorem ascent_slideBase_ne {st : State} (hwf : st.WF) {d z : Card}
    {a k : Anchor}
    (hhold : st.pileHolding d = some a)
    (hpot : st.pileOfTop z = some k)
    (hcan : st.canPlace d (Sum.inr z) = true) : k ≠ a := by
  intro hcon
  rw [hcon] at hpot
  obtain ⟨-, -, hfit⟩ := canPlace_inr hcan
  have hznd : z ≠ d := fun hcon' => by
    obtain ⟨hr, -⟩ := (canSitOn_eq d z).mp hfit
    rw [← hcon'] at hr
    omega
  have hzrun : z ∈ fromCard d ((st.piles a).faceUp) := by
    have hlast0 : lastOf ((st.piles a).faceUp) = some z := (pileOfTop_top hpot).2
    have hdmem : d ∈ (st.piles a).faceUp := pileHolding_mem hhold
    obtain ⟨t, ht⟩ := fromCard_eq_head_of_mem hdmem
    have hrnne : fromCard d ((st.piles a).faceUp) ≠ [] := by
      rw [ht]
      simp
    rw [ascent_split_mem d ((st.piles a).faceUp),
      ascent_lastOf_append _ _ hrnne] at hlast0
    exact lastOf_mem hlast0
  have hfalse := ascent_selfland_refuted hwf hhold hzrun hznd
  rw [hcan] at hfalse
  simp at hfalse

/-- The emptied pile's flip at a revealing hidden deck (the reveal
mode of both the mid-state landing pin below and the §1d commit
read; single-homed here, the first consumer site). -/
private theorem ascent_afterRunRemoved_reveal {p : Pile} {z : Card} {t : List Card}
    (h : p.hidden = z :: t) :
    Pile.afterRunRemoved p [] = ⟨t, [z]⟩ := by
  simp only [Pile.afterRunRemoved, Pile.revealTop, h]
  rfl

/-- The emptied pile's burn at an empty hidden deck (the burn mode —
companion of the reveal row above). -/
private theorem ascent_afterRunRemoved_burn {p : Pile}
    (h : p.hidden = []) :
    Pile.afterRunRemoved p [] = ⟨[], []⟩ := by
  simp only [Pile.afterRunRemoved, Pile.revealTop, h]

/-- **THE MID-STATE LANDING PIN**: after the departed run's source
pile is rewritten, the landing base still tops exactly the pile it
topped (the emptied-or-revealing source cannot pretend; the kept
prefix's cards are face-up in no other pile). -/
private theorem ascent_slideLanding {st : State} (hwf : st.WF) {d z : Card}
    {a k : Anchor}
    (hka : k ≠ a)
    (hpot : st.pileOfTop z = some k) :
    (st.setPile a
        (Pile.afterRunRemoved (st.piles a) (below d ((st.piles a).faceUp)))).pileOfTop z
      = some k := by
  refine ascent_topSearch _ (by
    rw [setPile_piles_ne hka]
    exact (pileOfTop_eq_some_iff hwf).1 hpot) ?_
  intro y _hy hyne
  by_cases hya : y = a
  · rw [hya, setPile_piles_self]
    show Pile.top
        (Pile.afterRunRemoved (st.piles a) (below d ((st.piles a).faceUp))) ≠ some z
    cases hpre : below d ((st.piles a).faceUp) with
    | nil =>
        cases hhid : (st.piles a).hidden with
        | nil =>
            rw [ascent_afterRunRemoved_burn hhid]
            exact fun hcon => absurd hcon (by simp [Pile.top, lastOf])
        | cons h t =>
            have hhmem : h ∈ (st.piles a).hidden := by
              rw [hhid]
              exact List.mem_cons_self ..
            have hzne : h ≠ z := fun hcon =>
              (mem_hidden_unique hwf hhmem k hka).2.1
                (by rw [hcon]; exact lastOf_mem (pileOfTop_top hpot).2)
            rw [ascent_afterRunRemoved_reveal hhid]
            intro hcon
            have hlasth : (⟨t, [h]⟩ : Pile).top = some h := rfl
            rw [hlasth] at hcon
            exact hzne (Option.some.inj hcon)
    | cons w ws =>
        rw [afterRunRemoved_ne (by simp)]
        intro hcon
        have hbr : ({ (st.piles a) with faceUp := w :: ws } : Pile).top
            = lastOf (w :: ws) := rfl
        rw [hbr] at hcon
        have hzin : z ∈ (st.piles a).faceUp :=
          mem_below ((st.piles a).faceUp) (by
            rw [hpre]
            exact lastOf_mem hcon)
        exact (mem_faceUp_unique hwf (lastOf_mem (pileOfTop_top hpot).2) a
          (fun hq => hka hq.symm)).1 hzin
  · rw [setPile_piles_ne hya]
    intro hcon
    have hsome := (pileOfTop_eq_some_iff hwf).2 hcon
    rw [hpot] at hsome
    injection hsome with hq
    exact hyne hq.symm

/-- **THE FACE-UP PRESERVATION, SLIDE ARM** (the raise row's twin):
along a FIRED slide at a `WF` state, every face-up card of the
pre-state is face-up at the successor — the kept below-content stays
in the emptied source pile, the moved run lands whole at the base
pile, and every untouched pile carries over. -/
private theorem ascent_slide_faceUp {st s' : State} (hwf : st.WF) {d : Card}
    {b : Base}
    (hstep : State.step st (Move.tabToTab d b) = some s')
    {c : Card} {p : Anchor} (hmem : c ∈ (st.piles p).faceUp) :
    ∃ p', c ∈ (s'.piles p').faceUp := by
  obtain ⟨a, hhold, hcan, -, hsplq⟩ := step_tabToTab_inv hstep
  rw [hsplq]
  by_cases hpa : p = a
  · rw [hpa] at hmem
    have hcm : c ∈ below d ((st.piles a).faceUp) ++
        fromCard d ((st.piles a).faceUp) := by
      rw [← ascent_split_mem d ((st.piles a).faceUp)]
      exact hmem
    by_cases hcmem : c ∈ below d ((st.piles a).faceUp)
    · have hprene : below d ((st.piles a).faceUp) ≠ [] := by
        intro hc
        rw [hc] at hcmem
        cases hcmem
      cases b with
      | inl n =>
          have hdmem : d ∈ (st.piles a).faceUp := pileHolding_mem hhold
          obtain ⟨hemp, -⟩ := canPlace_inl hcan
          obtain ⟨-, hfn⟩ := (Pile.isEmpty_eq _).mp hemp
          have hna : a ≠ n := by
            intro hcon
            rw [hcon] at hdmem
            rw [hfn] at hdmem
            cases hdmem
          exact ⟨a, by
            rw [putRun_eq_inl, setPile_piles_ne hna, setPile_piles_self,
              afterRunRemoved_ne hprene]
            exact hcmem⟩
      | inr z =>
          obtain ⟨k, hpotk, -⟩ := canPlace_inr hcan
          have hka : k ≠ a := ascent_slideBase_ne hwf hhold hpotk hcan
          have hhak : a ≠ k := fun hq => hka hq.symm
          have hpotM := ascent_slideLanding (d := d) hwf hka hpotk
          exact ⟨a, by
            rw [putRun_piles_inr_ne _ _ _ k hpotM hhak, setPile_piles_self,
              afterRunRemoved_ne hprene]
            exact hcmem⟩
    · have hcmemr : c ∈ fromCard d ((st.piles a).faceUp) := by
        rcases List.mem_append.mp hcm with h' | h'
        · exact absurd h' hcmem
        · exact h'
      cases b with
      | inl n =>
          exact ⟨n, by rw [putRun_eq_inl, setPile_piles_self]; exact hcmemr⟩
      | inr z =>
          obtain ⟨k, hpotk, -⟩ := canPlace_inr hcan
          have hka : k ≠ a := ascent_slideBase_ne hwf hhold hpotk hcan
          have hpotM := ascent_slideLanding (d := d) hwf hka hpotk
          exact ⟨k, by
            rw [putRun_inr_eq hpotM, setPile_piles_self]
            exact List.mem_append.mpr (Or.inr hcmemr)⟩
  · cases b with
    | inl n =>
        by_cases hpn : p = n
        · obtain ⟨hemp, -⟩ := canPlace_inl hcan
          obtain ⟨-, hfn⟩ := (Pile.isEmpty_eq _).mp hemp
          rw [hpn, hfn] at hmem
          cases hmem
        · exact ⟨p, by
            rw [putRun_eq_inl, setPile_piles_ne hpn, setPile_piles_ne hpa]
            exact hmem⟩
    | inr z =>
        obtain ⟨k, hpotk, -⟩ := canPlace_inr hcan
        have hka : k ≠ a := ascent_slideBase_ne hwf hhold hpotk hcan
        have hpotM := ascent_slideLanding (d := d) hwf hka hpotk
        by_cases hpk : p = k
        · rw [hpk] at hmem
          exact ⟨k, by
            rw [putRun_inr_eq hpotM, setPile_piles_self, setPile_piles_ne hka]
            exact List.mem_append.mpr (Or.inl hmem)⟩
        · exact ⟨p, by
            rw [putRun_piles_inr_ne _ _ _ k hpotM hpk, setPile_piles_ne hpa]
            exact hmem⟩

/-- **THE PERSISTENT PAIR** (the mission's named induction, banked):
a card and its twin both face-up at the start and both at-or-above
their family rungs there, remain face-up and rung-capped at the
start's margins at EVERY state an ascent run reaches — the raise
legs never remove a member (the full-time no-eat guard declines
them via the pair's own intact mobility, which the leg-work itself
preserves: breaking a member's face-up-ness or crossing its rank
would have required founding it), the slide legs relocate face-up
material whole, the rungs climb index-exactly, and the caps ride
`ascent_idxCap_of_ne`. -/
private theorem ascent_pair_persists {s : State} (hwf : s.WF) {x : Card}
    (hfu₁ : ∃ a, x ∈ (s.piles a).faceUp)
    (hfu₂ : ∃ b, x.twin ∈ (s.piles b).faceUp)
    (hrg₁ : rungAt s x.suit ≤ x.rank.toIdx)
    (hrg₂ : rungAt s x.twin.suit ≤ x.twin.rank.toIdx) :
    ∀ {ρ : List Move} {W : State}, AscentRun s ρ W →
      (∃ a, x ∈ (W.piles a).faceUp) ∧
        (∃ b, x.twin ∈ (W.piles b).faceUp) ∧
        rungAt W x.suit ≤ x.rank.toIdx ∧
        rungAt W x.twin.suit ≤ x.twin.rank.toIdx := by
  intro ρ W hrun
  induction hrun with
  | nil st =>
      exact ⟨hfu₁, hfu₂, hrg₁, hrg₂⟩
  | @cons st m s' W' ρ' hm hstep hrest ih =>
      have hmob : MobileTwin st x := ⟨hfu₁, hrg₁, hfu₂, hrg₂⟩
      rcases hm with ⟨c, hmEq, hhot, hface, hguard⟩ | ⟨c, bb, hmEq⟩
      · -- the raise leg: the guard declines both members; rungs climb one
        rw [hmEq] at hstep
        obtain ⟨hn, a₀, hpo₀, hspl⟩ := step_tabToFound_inv hstep
        have hnext : c.rank.toIdx = st.foundHeight c.suit := of_decide_eq_true hn
        have hne1 : c ≠ x := (hguard x hmob).1
        have hne2 : c ≠ x.twin := (hguard x hmob).2
        have H₁ : ∃ a, x ∈ (s'.piles a).faceUp :=
          ascent_faceUp_raise hstep (fun hq => hne1 hq.symm) hfu₁
        have H₂ : ∃ a, x.twin ∈ (s'.piles a).faceUp :=
          ascent_faceUp_raise hstep (fun hq => hne2 hq.symm) hfu₂
        have hFself : s'.found c.suit = st.found c.suit ++ [c] := by
          rw [hspl]
          exact setFound_found_self
        have hFne : ∀ σ : Suit, σ ≠ c.suit → s'.found σ = st.found σ := by
          intro σ hσ
          rw [hspl]
          exact setFound_found_ne hσ
        have H₃ : rungAt s' x.suit ≤ x.rank.toIdx := by
          by_cases hxs : c.suit = x.suit
          · have hcxlen : (st.found c.suit).length = c.rank.toIdx := by
              rw [hnext]
              rfl
            have hcxle : c.rank.toIdx ≤ x.rank.toIdx := by
              rw [hnext, hxs]
              exact hrg₁
            have hcxcap : c.rank.toIdx + 1 ≤ x.rank.toIdx :=
              ascent_idxCap_of_ne hcxle hxs hne1
            show (s'.found x.suit).length ≤ x.rank.toIdx
            rw [show s'.found x.suit = st.found c.suit ++ [c] from by
                rw [← hxs]
                exact hFself, List.length_append, hcxlen]
            exact hcxcap
          · have hxs' : x.suit ≠ c.suit := fun hq => hxs hq.symm
            show (s'.found x.suit).length ≤ x.rank.toIdx
            rw [hFne x.suit hxs']
            exact hrg₁
        have H₄ : rungAt s' x.twin.suit ≤ x.twin.rank.toIdx := by
          by_cases hxs : c.suit = x.twin.suit
          · have hcxlen : (st.found c.suit).length = c.rank.toIdx := by
              rw [hnext]
              rfl
            have hcxle : c.rank.toIdx ≤ x.twin.rank.toIdx := by
              rw [hnext, hxs]
              exact hrg₂
            have hcxcap : c.rank.toIdx + 1 ≤ x.twin.rank.toIdx :=
              ascent_idxCap_of_ne hcxle hxs hne2
            show (s'.found x.twin.suit).length ≤ x.twin.rank.toIdx
            rw [show s'.found x.twin.suit = st.found c.suit ++ [c] from by
                rw [← hxs]
                exact hFself, List.length_append, hcxlen]
            exact hcxcap
          · have hxs' : x.twin.suit ≠ c.suit := fun hq => hxs hq.symm
            show (s'.found x.twin.suit).length ≤ x.twin.rank.toIdx
            rw [hFne x.twin.suit hxs']
            exact hrg₂
        exact ih (step_wf hwf hstep) H₁ H₂ H₃ H₄
      · -- the slide leg: face-up material relocates whole; rungs freeze
        rw [hmEq] at hstep
        obtain ⟨p₁, hmem₁⟩ := hfu₁
        obtain ⟨p₂, hmem₂⟩ := hfu₂
        have H₁ : ∃ a, x ∈ (s'.piles a).faceUp := by
          obtain ⟨q, hq⟩ := ascent_slide_faceUp hwf hstep hmem₁
          exact ⟨q, hq⟩
        have H₂ : ∃ a, x.twin ∈ (s'.piles a).faceUp := by
          obtain ⟨q, hq⟩ := ascent_slide_faceUp hwf hstep hmem₂
          exact ⟨q, hq⟩
        have H₃ : rungAt s' x.suit ≤ x.rank.toIdx := by
          rw [ascent_slide_rung hstep x.suit]
          exact hrg₁
        have H₄ : rungAt s' x.twin.suit ≤ x.twin.rank.toIdx := by
          rw [ascent_slide_rung hstep x.twin.suit]
          exact hrg₂
        exact ih (step_wf hwf hstep) H₁ H₂ H₃ H₄

/-- The four persistent clauses re-packed as the mobility read (the
residue routes' `MobileTwin` glue). -/
private theorem ascent_persist_mobile {st : State} {x : Card}
    (h₁ : ∃ a, x ∈ (st.piles a).faceUp)
    (h₂ : ∃ b, x.twin ∈ (st.piles b).faceUp)
    (h₃ : rungAt st x.suit ≤ x.rank.toIdx)
    (h₄ : rungAt st x.twin.suit ≤ x.twin.rank.toIdx) :
    MobileTwin st x := ⟨h₁, h₃, h₂, h₄⟩

/-- **THE CELL-ARMOR ROW** (the α-repair's start-economy premise,
landed as lemma-level work — the mission's ab2-armor enrichment): a
cover-cell pair that arrives INTACT at the start — both cells
face-up and at-or-above their suits' rungs there — survives EVERY
ascent run whole: at the landing both cells are still face-up,
`MobileTwin`, at-or-above their rungs, and UNFOUNDED (the face-up
residence excludes every foundation row at `WF`; founding a cell
along the way would strand it off the face, against the persistent
clauses).  Read together with the live-cover bar this row is the
α-side of the armor: at any STUCK landing carrying the saturation
iff the cover cells can NEVER stand face-up (the bar kills the
standing cover beside the live twin), so an intact-at-start cell
economy makes the delivered iff UND ELIVERABLE — the `hbelow` worlds
that genuinely deliver must break the cells before the run, the
probe's decisive open with the α-shape priced impossible at every
delivered world rather than open. -/
private theorem ascent_cell_armor {s : State} (hwf : s.WF)
    {d : Card}
    (hcell₁ : ∃ a, d ∈ (s.piles a).faceUp)
    (hcell₂ : ∃ b, d.twin ∈ (s.piles b).faceUp)
    (hrung₁ : rungAt s d.suit ≤ d.rank.toIdx)
    (hrung₂ : rungAt s d.twin.suit ≤ d.rank.toIdx)
    {ρ : List Move} {W : State}
    (hrun : AscentRun s ρ W) :
    MobileTwin W d ∧
      W.foundHeight d.suit ≤ d.rank.toIdx ∧
      (∃ c, d ∈ (W.piles c).faceUp) ∧
      d ∉ W.found d.suit := by
  obtain ⟨h1, h2, h3, h4⟩ := ascent_pair_persists hwf hcell₁ hcell₂ hrung₁
    (by rw [Card.twin_rank]; exact hrung₂) hrun
  rw [ascent_rung_height] at h3
  rw [ascent_rung_height] at h4
  have hwfW : W.WF := ascent_run_wf hwf hrun
  refine ⟨⟨h1, h3, h2, h4⟩, h3, h1, ?_⟩
  obtain ⟨c, hc⟩ := h1
  exact (mem_faceUp_only hwfW hc).2.2.2.2 d.suit

/-- **THE CLIMB REDUCTION TO THE PARKING** (the climb mini's named
residue, staged as a kernel row): the climb-delivery conclusion — a
delivered `DoubleHot` mobile pair, capped at its family's rungs at
the landing — is PURE ASSEMBLY off the persistent-pair induction
plus the TWO FRONTIER-PARKING EQUALITIES (both family rungs of the
witnessed pair sit EXACTLY at the pair's rank at the exhaustion).
The named open `ascent_frontier_parking` [H, `hbelow`-carried] is
EXACTLY those two equalities: parking them in closes the delivery
with no further content — the staged shape a future census-proof
or the owner's repair consumes by name, not by rebuild. -/
private theorem ascent_climb_of_parked {s : State} (hwf : s.WF)
    {x : Card}
    (hfu₁ : ∃ a, x ∈ (s.piles a).faceUp)
    (hfu₂ : ∃ b, x.twin ∈ (s.piles b).faceUp)
    (hrg₁ : rungAt s x.suit ≤ x.rank.toIdx)
    (hrg₂ : rungAt s x.twin.suit ≤ x.rank.toIdx)
    {ρ : List Move} {W : State}
    (hrun : AscentRun s ρ W)
    (hpark₁ : rungAt W x.suit = x.rank.toIdx)
    (hpark₂ : rungAt W x.twin.suit = x.rank.toIdx) :
    ∃ (y : Card), DoubleHot W y ∧ MobileTwin W y ∧
      rungAt W y.suit ≤ y.rank.toIdx ∧
      rungAt W y.twin.suit ≤ y.rank.toIdx := by
  obtain ⟨h1, h2, h3, h4⟩ := ascent_pair_persists hwf hfu₁ hfu₂ hrg₁
    (by rw [Card.twin_rank]; exact hrg₂) hrun
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  refine ⟨x, ⟨a, b, ha, hb, ?_, ?_⟩,
    ⟨⟨a, ha⟩, ?_, ⟨b, hb⟩, ?_⟩, ?_, ?_⟩
  · exact hpark₁.symm.trans (ascent_rung_height W x.suit)
  · exact (congrArg Rank.toIdx (Card.twin_rank x)).trans
      (hpark₂.symm.trans (ascent_rung_height W x.twin.suit))
  · exact Nat.le_of_eq
      (hpark₁.symm.trans (ascent_rung_height W x.suit)).symm
  · rw [ascent_rung_height] at h4
    exact h4
  · exact Nat.le_of_eq hpark₁
  · exact Nat.le_of_eq hpark₂

/-- **THE SATURATION DECOMPOSITION, FORWARD HALF** (the saturation
mini's two carried axes, staged as a kernel row): the saturation iff
at a stuck state is pure assembly off TWO named premises — the
MEMBER-LIVENESS (the delivered pair's members are vanilla-live at
the landing: the `fa1` axis) and the LIVE-PAIR EXCLUSION (every
intact mobile pair with a live member at the exhaustion IS the
delivered pair: the `fa0` axis, live-grade).  The (⇒) half rides the
banked stuckness collapse and the constructive live-member read; the
(⇐) half is the `now`-grade of the liveness.  The named
`hbelow`-carried open is EXACTLY the two premises — `fa0` and `fa1`
decide them SEPARATELY at the exhausted state alone, so closing
either premise is a self-contained sub-mission a future pass or the
owner's repair plugs in by name. -/
private theorem ascent_stuck_sat_of_excLive {W : State} (hstuck : AscentStuck W)
    {x : Card}
    (hlive : CanRaise W x ∧ CanRaise W x.twin)
    (hexc : ∀ y, MobileTwin W y →
      (CanRaiseS W y ∨ CanRaiseS W y.twin) → y = x ∨ y = x.twin) :
    ∀ (c : Card), (c = x ∨ c = x.twin) ↔ CanRaiseS W c := by
  intro c
  constructor
  · rintro (rfl | rfl)
    · exact CanRaiseS.now _ hlive.1
    · exact CanRaiseS.now _ hlive.2
  · intro hs
    have hcr : CanRaise W c := ascent_stuck_collapse hstuck hs
    obtain ⟨y, hmy, hcy⟩ := ascent_stuck_live_member hstuck hs
    have hys : CanRaiseS W y ∨ CanRaiseS W y.twin := by
      rcases hcy with rfl | rfl
      · exact Or.inl hs
      · exact Or.inr hs
    rcases hexc y hmy hys with rfl | rfl
    · rcases hcy with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rcases hcy with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl (Card.twin_twin x)

/-! ### The fourth-succession saturation kernels (the `fa1` axis,
W-locally shrunk)

The saturation residue's member-liveness premise (the `fa1` axis,
`hbelow`-carried) is priced further by the banked cover/twin-top bar,
in four rows: the pair-reads' twin-flip re-packs (`DoubleHot`,
`MobileTwin`), the FORCED TOPPING (one vanilla-live member of any
intact mobile pair makes the OTHER member top its pile — the covered
shape is barred outright at stuckness), the seat-⟹-license assembly
(a hot topping member is vanilla-live given exactly the license's own
seat disjunct), and the MEMBER-LIVE SPLIT (the dichotomy the future
pass imports: either the twin is vanilla-live, or it stands on a
literally bare non-king seat — the `fa1` shape extracted as the ONLY
remaining read).  No row consumes `hbelow`; the residue's carried
verdicts stand unchanged. -/

/-- The double-hot read is twin-flip symmetric (both orientations
name the same face-up pair at the same rungs). -/
private theorem ascent_doublehot_twinflip {st : State} {x : Card}
    (hdh : DoubleHot st x) : DoubleHot st x.twin := by
  obtain ⟨a, b, hx, hxt, hrx, hrxt⟩ := hdh
  exact ⟨b, a, hxt, by rw [Card.twin_twin]; exact hx, hrxt,
    by rw [Card.twin_twin]; exact hrx⟩

/-- The mobility read is twin-flip symmetric (re-pack for the mirror
instantiation of the split below). -/
private theorem ascent_mobile_twinflip {st : State} {x : Card}
    (hm : MobileTwin st x) : MobileTwin st x.twin := by
  refine ⟨hm.2.2.1, hm.2.2.2, by rw [Card.twin_twin]; exact hm.1, ?_⟩
  rw [Card.twin_twin]
  exact hm.2.1

/-- **THE FORCED TOPPING** (fourth succession): at an exhausted state
one vanilla-live member of an intact mobile pair forces the OTHER
member to TOP its pile — the member's own license tops its pile, and
a covered twin would make the banked cover/twin-top bar's fitting
slide fire against the stuckness.  Serves the saturation's
member-liveness split below and the exclusion's shape analysis alike
(read at any second pair: its live member forces its own twin to
top, the both-covered-live shape is barred everywhere). -/
private theorem ascent_stuck_liveForcesTwinTop {W : State} (hwf : W.WF)
    (hstuck : AscentStuck W) {y : Card}
    (hmob : MobileTwin W y)
    (hly : CanRaise W y) :
    ∃ (q : Anchor), (W.piles q).top = some y.twin := by
  obtain ⟨q, hmem⟩ := hmob.2.2.1
  obtain ⟨t1, t2, hspl⟩ := ascent_mem_split _ hmem
  cases t2 with
  | nil =>
      refine ⟨q, ?_⟩
      show lastOf (W.piles q).faceUp = some y.twin
      rw [hspl, lastOf_snoc]
  | cons d' rest =>
      obtain ⟨-, j, hpotj, -⟩ := hly
      have hcover : False :=
        ascent_stuck_coverTwinbar hwf hstuck hspl
          (by rw [Card.twin_twin]; exact hpotj)
      exact hcover.elim

/-- **THE SEAT ASSEMBLY** (fourth succession, pure license
arithmetic): a hot twin topping its pile is vanilla-live given
EXACTLY the license's own third clause — the seat disjunct (face-up
content below, or the bare-king read).  Combined with the forced
topping above this is the whole W-local content of the iff's
member-liveness half; what can still fail is one seat read. -/
private theorem ascent_liveTwin_of_seat {W : State} (hwf : W.WF)
    {x : Card} (hdh : DoubleHot W x) {q : Anchor}
    (htop : (W.piles q).top = some x.twin)
    (hseat : chop (W.piles q).faceUp ≠ [] ∨
      ((W.piles q).hidden = [] ∧ x.twin.rank = Rank.king)) :
    CanRaise W x.twin := by
  obtain ⟨-, -, -, -, -, hxt⟩ := hdh
  exact ⟨decide_eq_true hxt, q, (pileOfTop_eq_some_iff hwf).2 htop, hseat⟩

/-- **THE MEMBER-LIVE SPLIT** (fourth succession, the `fa1` axis
W-locally shrunk): at the exhausted delivered world, one member's
vanilla liveness forces the other member either to be vanilla-live
too, or to stand on a LITERALLY BARE non-king seat — face-up exactly
`[the member]`, with the seat's refill clause failing in
`CanRaise`'s own terms (hidden deck nonempty, or the member not a
king).  The `fa1` board witnesses the bare-seat read satisfiable at
a stuck exhaustion, so the premise stays `hbelow`-carried; but a
future pass importing the saturation's `hlive` premise now needs only
the bare-seat census, not the full member-liveness read. -/
private theorem ascent_stuck_memberLive_split {W : State} (hwf : W.WF)
    (hstuck : AscentStuck W) {x : Card}
    (hdh : DoubleHot W x) (hmob : MobileTwin W x)
    (hlx : CanRaise W x) :
    CanRaise W x.twin ∨
      (∃ (q : Anchor), (W.piles q).faceUp = [x.twin] ∧
        ((W.piles q).hidden ≠ [] ∨ x.twin.rank ≠ Rank.king)) := by
  obtain ⟨q, htop⟩ := ascent_stuck_liveForcesTwinTop hwf hstuck hmob hlx
  obtain ⟨front, hf⟩ := Pile.top_eq_lastOf_iff.mp htop
  have hchopsn : chop ((W.piles q).faceUp) = front := by
    rw [hf]
    exact chop_snoc
  by_cases hchop : chop ((W.piles q).faceUp) = []
  · have hfront : front = [] := hchopsn.symm.trans hchop
    by_cases hking : (W.piles q).hidden = [] ∧ x.twin.rank = Rank.king
    · exact Or.inl (ascent_liveTwin_of_seat hwf hdh htop (Or.inr hking))
    · refine Or.inr ⟨q, ?_, ?_⟩
      · rw [hf, hfront, List.nil_append]
      · by_cases hhid : (W.piles q).hidden = []
        · exact Or.inr (fun hk => hking ⟨hhid, hk⟩)
        · exact Or.inl hhid
  · exact Or.inl (ascent_liveTwin_of_seat hwf hdh htop
      (Or.inl (fun hc => hchop hc)))

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
  lands face-up — `ascent_slide_faceUp`, the slide-arm preservation
  banked in the §2c-pre persistent-pair section), so a pair mobile at
  the start stays paired and face-up at every prefix.  [kernel
  status: BANKED — `ascent_pair_persists`, the 2026-10-13 session-4
  pass]
* THE RUNGS ARE INDEX-EXACT — the provable freeze: a raise of suit
  σ climbs its rung by exactly one (the splice's
  `setFound`-prepend read), and crossing rank r on a FAMILY suit
  requires founding the rank-r member — guard-declined forever
  (the guard persists, per the kernel above) — so both family rungs
  stay ≤ r along the whole run.  [kernel status: BANKED — the
  per-leg cap rides `ascent_idxCap_of_ne` inside
  `ascent_pair_persists`; `ascent_slide_rung` is the slide-arm
  freeze]
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
  [H, hbelow-carried]; the two kernels above are banked, and the
  persistent-pair row hands the parking BOTH members' face-up
  mobility intact at every prefix, so only the ≤-to-= frontier
  upgrade remains.

THIRD-SUCCESSION STAGING (the second lander): the delivery is now
REDUCED-KERNEL, named row `ascent_climb_of_parked` — the
persistent-pair clauses plus the TWO FRONTIER-PARKING EQUALITIES
(both family rungs exactly at the pair's rank at the exhaustion)
close the row's conclusion with no further content; the named
residue is exactly those two equalities. -/
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
  they are face-up at `W` — this is no longer a priced promise but
  BANKED leg-work: the persistent-pair row
  (`ascent_pair_persists`, §2c-pre, the 2026-10-13 session-4 pass)
  carries the `hbelow` witness's own pair face-up, intact
  (`ascent_persist_mobile` re-packs the four clauses), and
  rung-capped at BOTH members' margins along the whole run, so both
  halves' `hbelow`-carried content starts from a surviving,
  constructively-tracked start pair: the (⇒) exclusion may now
  name `hbelow`'s witness AT `W` (not merely at `s`), and the (⇐)
  member-liveness census reads a pair whose mobility never died in
  transit.  What still rides the probe's declared open, unchanged:
  the fork-reachability coupling itself.

THIRD-SUCCESSION STAGING (the second lander): the iff's remaining
content is now DECOMPOSED-KERNEL, named row
`ascent_stuck_sat_of_excLive` — the member-liveness premise (the
`fa1` axis) plus the live-pair exclusion premise (the `fa0` axis,
live-grade) close the iff by pure assembly over the banked collapse
and the constructive live-member read; the `hbelow`-carried open is
exactly the two premises, separately W-decided by the two boards.

FOURTH-SUCCESSION ADDENDUM (the `fa1` axis, W-locally shrunk): with
the banked cover/twin-top bar read through the delivered pair, the
member-liveness premise `hlive` is FORCED down to a one-seat read —
`ascent_stuck_memberLive_split` (below, §2b): one vanilla-live member
makes the other member TOP its pile (the covered-twin shape is
barred outright at stuckness), so `CanRaise W x.twin` can fail only
on the LITERALLY BARE non-king seat (the delivered member standing
solo, its pile's face-up list exactly `[the member]` — the `fa1`
shape extracted at the pair's own pile).  The `hbelow`-carried
verdict stands (`fa1` witnesses the bare-seat read satisfiable); a
future pass mounting the iff now imports the bare-seat census alone.
The `fa0` axis is unchanged; its shapes gain one read for free —
`ascent_stuck_liveForcesTwinTop` forces every second live pair's own
twin to top too, so the exclusion's live intruders always present
BOTH-TOPPING at the exhaustion (the `fa0` red twos exhibit exactly
that). -/
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
  §2e routes the recoverable side of the same census.

THIRD-SUCCESSION VERDICT (2026-10-13, session 5): the row is
REFUTED at its byte-frozen statement — the refutation board `fa2`
below witnesses it decide-grade (`ascent_cover_cell_refuted`,
zero-sorry): a WF, STUCK, saturated, delivered board — all four aces
founded, the black twos double-hot, intact and seated over the red
threes, both red twos stocked — that admits NO cover: the only
`r−1` opposite-family cards are the red aces, both FOUNDED below
their suits' frontiers, so the un-founded clause fails on every
candidate.  WHAT THIS PRICES: the census's W-local content was never
true — the route's un-foundedness half leaned on a reachability the
frozen statement never carried (no `hbelow` premise rides this
row).  THE LEDGER: the row keeps its sorry (the row as stated is
FALSE, the `fa2` record, on the `Orig/ForkDescent.lean` §3R
precedent); the exhaustion row `ascent_exhaustion_forks` is
UNCHANGED in content — its `hbelow` premise now carries the whole
cover story, and its truth requires exactly that the reachability
census bars `fa2`-shaped worlds, the probe's declared open; the
cover-read assembly below (`ascent_cover_read`, a pure assembly over
this row) inherits the W-local falsity, and the β-staged
`ascent_cover_read_rec` with it; the owner's recourse is
statement-level — tie the cover cells' fate to `hbelow` (the probe's
α-repair), or adopt the β-recoverable disjunct (the probe's β-draft,
staged in §2e; the β-pullback `ascent_cover_pullback` stays banked
and true).

SECOND-LANDER ADDENDUM (the universal constant behind the board):
the `fa2` kill is not a board accident —
`ascent_exhaust_shape_impossible` proves the cover conclusion
impossible at EVERY stuck state carrying the saturation iff (the
census's `d` fits the live twin by twin-blind rank-and-color
arithmetic, the iff forces the twin vanilla-live by the stuckness
collapse, and the live-cover bar refuses the pair), so the α-arm of
this census is dead at every hypothesis-satisfying world, not
merely at `fa2`; and the β-recoverable arm (`ascent_cover_read_rec`,
§2e) is thereby the only standing grade, with its licensed return
base — the topped twin — forced by the very iff that kills the
standing cover.

FOURTH-SUCCESSION β-EVIDENCE (2026-10-17): the β-recoverable future
is now WITNESSED, not merely staged — `fa2_shapeRec` (§2e, decide
grade) reads `ExhaustShapeRec fa2 faS2 faHA` TRUE at this file's own
certified saturated board (the heart ace: founded at its frontier,
fitting the black deuce pair, return base licensed), and
`fa2_pullWitness` runs the banked β-pullback there, landing the
standing `ExhaustShape` in one licensed `foundToTab`.  The forced
return base is itself a row now (`ascent_rec_base_of_iff`: at ANY
stuck saturated world a fitting cover's return base is the iff-forced
topped twin).  Post-β-ratification the `fa2` class stops being an
obstruction class and becomes a DELIVERY class; the α-arm stays
kernel-dead per the ceiling below. -/
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
probe's ab0/ab1 burial economy).

THIRD-SUCCESSION ADDITION (below): the board `fa2` — unlike `fa0`
and `fa1`, a genuinely DECIDED falsification — kills a frozen
statement outright (the cover-cell census carries no `hbelow`
premise to retreat behind), on the `Orig/ForkDescent.lean` §3R
precedent. -/

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

/-! ### The cover-cell refutation board `fa2` (the third succession's
frozen kill, 2026-10-13)

The FIRST decided kill of a frozen residue in this leaf — UNLIKE
`fa0`/`fa1` above, this board IS a counterexample to a frozen
statement: the cover-cell census `ascent_cover_cell` carries NO
`hbelow` premise, so its W-local falsity refutes it outright.  THE
ECONOMY: all four aces FOUNDED (every suit's rung at one); the black
twos DOUBLE-HOT, intact and seated over the red threes (`3♥ / 2♠`
and `3♦ / 2♣`); both RED TWOS stocked — hot at their rungs but
outside the tableau's reach; everything else sunk in the stock.  THE
WITNESS LEDGER:

* STUCK — the only hot face-up cards are the twos, both
  guard-declined by their own intact mobile pair; the red threes are
  un-hot by one index; every slide is refused by enumeration (the
  two face-up tops host only red aces — founded — nothing fits any
  top, and no empty seat takes a non-king).
* SATURATED — `fa2_iff`: the S-set is EXACTLY the black twos, the
  file's first certified saturation witness; every other hot card is
  stocked (dead), the threes un-hot by one index.
* DELIVERED — `fa2_pairDelivered`: double-hot, mobile, capped.
* NO COVER — the `r−1` opposite-family candidates are exactly the
  red aces, both FOUNDED below their frontiers: the census's
  un-founded clause fails on every candidate, so the existential is
  false — the refutation `ascent_cover_cell_refuted` below, on the
  `Orig/ForkDescent.lean` §3R pattern (the residue keeps its sorry
  as the honest witness of a FALSE row). -/

private def fa2 : State where
  found := fun s => faTakeUp s 1
  piles := fun a => match a with
    | .p0 => ⟨[], [faH3, faS2]⟩
    | .p1 => ⟨[], [faD3, faC2]⟩
    | .p2 => ⟨[], []⟩
    | .p3 => ⟨[], []⟩
    | .p4 => ⟨[], []⟩
    | .p5 => ⟨[], []⟩
    | .p6 => ⟨[], []⟩
  stock :=
    [faCrd .spade .three, faCrd .spade .four, faCrd .spade .five,
     faCrd .spade .six, faCrd .spade .seven, faCrd .spade .eight,
     faCrd .spade .nine, faCrd .spade .ten, faCrd .spade .jack,
     faCrd .spade .queen, faCrd .spade .king,
     faCrd .heart .two, faCrd .heart .four, faCrd .heart .five,
     faCrd .heart .six, faCrd .heart .seven, faCrd .heart .eight,
     faCrd .heart .nine, faCrd .heart .ten, faCrd .heart .jack,
     faCrd .heart .queen, faCrd .heart .king,
     faCrd .diamond .two, faCrd .diamond .four, faCrd .diamond .five,
     faCrd .diamond .six, faCrd .diamond .seven, faCrd .diamond .eight,
     faCrd .diamond .nine, faCrd .diamond .ten, faCrd .diamond .jack,
     faCrd .diamond .queen, faCrd .diamond .king,
     faCrd .club .three, faCrd .club .four, faCrd .club .five,
     faCrd .club .six, faCrd .club .seven, faCrd .club .eight,
     faCrd .club .nine, faCrd .club .ten, faCrd .club .jack,
     faCrd .club .queen, faCrd .club .king]
  waste := []
  drawStep := 1

private theorem fa2_wf_found : ∀ s : Suit, ∃ n, fa2.found s = s.upCards.take n := by
  intro s
  cases s <;> exact ⟨1, rfl⟩

private theorem fa2_wf_runs : ∀ a : Anchor, runOK (fa2.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

private theorem fa2_wf_count : ∀ c ∈ Card.universe, fa2.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

/-- The cover-cell refutation board is `WF` (kernel-decided). -/
theorem fa2_wf : fa2.WF :=
  ⟨fa2_wf_found, fa2_wf_runs, fa2_wf_count, by decide⟩

private theorem fa2_p0 : fa2.piles .p0 = ⟨[], [faH3, faS2]⟩ := rfl
private theorem fa2_p1 : fa2.piles .p1 = ⟨[], [faD3, faC2]⟩ := rfl
private theorem fa2_p2 : fa2.piles .p2 = ⟨[], []⟩ := rfl
private theorem fa2_p3 : fa2.piles .p3 = ⟨[], []⟩ := rfl
private theorem fa2_p4 : fa2.piles .p4 = ⟨[], []⟩ := rfl
private theorem fa2_p5 : fa2.piles .p5 = ⟨[], []⟩ := rfl
private theorem fa2_p6 : fa2.piles .p6 = ⟨[], []⟩ := rfl

/-- **THE FACE-UP INVENTORY AT `fa2`**: exactly the seated pair and
their two seats. -/
theorem fa2_faceUp : ∀ c ∈ Card.universe,
    (∃ a, c ∈ (fa2.piles a).faceUp) →
      c = faH3 ∨ c = faS2 ∨ c = faD3 ∨ c = faC2 := by
  intro c _ ⟨a, hc⟩
  cases a with
  | p0 =>
      rw [fa2_p0] at hc; simp at hc
      rcases hc with h | h
      · subst h; exact Or.inl rfl
      · subst h; exact Or.inr (Or.inl rfl)
  | p1 =>
      rw [fa2_p1] at hc; simp at hc
      rcases hc with h | h
      · subst h; exact Or.inr (Or.inr (Or.inl rfl))
      · subst h; exact Or.inr (Or.inr (Or.inr rfl))
  | p2 => rw [fa2_p2] at hc; cases hc
  | p3 => rw [fa2_p3] at hc; cases hc
  | p4 => rw [fa2_p4] at hc; cases hc
  | p5 => rw [fa2_p5] at hc; cases hc
  | p6 => rw [fa2_p6] at hc; cases hc

/-- **THE STUCK BOARD**: `fa2` is exhausted — the only hot face-up
cards are the twos, each guard-declined by its own intact mobile
pair; the red threes are un-hot by one index; and no slide places
(the two face-up tops host only red aces — founded — nothing fits
any top, and no empty seat takes a non-king). -/
theorem fa2_stuck : AscentStuck fa2 := by
  intro m hm
  rcases hm with ⟨c, hmEq, hhot, hface, hguard⟩ | ⟨c, b, hmEq⟩
  · rcases fa2_faceUp c (Card.mem_universe c) hface with h | h | h | h
    · subst h; exact absurd hhot (by decide)
    · subst h
      exact absurd rfl (hguard _ ((mobileTwinB_iff _ _).mp (by decide))).1
    · subst h; exact absurd hhot (by decide)
    · subst h
      exact absurd rfl (hguard _ ((mobileTwinB_iff _ _).mp (by decide))).1
  · rw [hmEq]
    cases b with
    | inl n =>
        rcases c with ⟨cs, cr⟩ <;> cases cs <;> cases cr <;> cases n <;> decide
    | inr z =>
        rcases c with ⟨cs, cr⟩ <;> rcases z with ⟨zs, zr⟩ <;>
          cases cs <;> cases cr <;> cases zs <;> cases zr <;> decide

/-- **THE DELIVERED PAIR STANDS, FULL PARCEL**: the black twos are
double-hot, intact, and capped at their family's rungs — the cover-cell
census's own delivered hypotheses, certified at the board. -/
theorem fa2_pairDelivered :
    DoubleHot fa2 faS2 ∧ MobileTwin fa2 faS2 ∧
      rungAt fa2 faS2.suit ≤ faS2.rank.toIdx ∧
      rungAt fa2 faS2.twin.suit ≤ faS2.twin.rank.toIdx :=
  ⟨⟨Anchor.p0, Anchor.p1, by decide, by decide, by decide, by decide⟩,
    ⟨⟨Anchor.p0, by decide⟩, by decide, ⟨Anchor.p1, by decide⟩, by decide⟩,
    by decide, by decide⟩

/-- **THE SATURATION IS CERTIFIED**: the S-set at the stuck board is
EXACTLY the delivered pair — the file's first certified saturation
witness.  Both members are vanilla-live (hot, topping their seated
piles); every other hot card is stocked, invisible to the license;
the red threes are un-hot by one index. -/
theorem fa2_iff :
    ∀ (c : Card), (c = faS2 ∨ c = faS2.twin) ↔ CanRaiseS fa2 c := by
  intro c
  constructor
  · intro h
    rcases h with rfl | rfl
    · exact CanRaiseS.now _
        ⟨by decide, Anchor.p0, by decide, Or.inl (by decide)⟩
    · exact CanRaiseS.now _
        ⟨by decide, Anchor.p1, by decide, Or.inl (by decide)⟩
  · intro hS
    obtain ⟨hnext, k, hk, -⟩ := ascent_stuck_collapse fa2_stuck hS
    have hmem : c ∈ (fa2.piles k).faceUp :=
      lastOf_mem (pileOfTop_top hk).2
    rcases fa2_faceUp c (Card.mem_universe c) ⟨k, hmem⟩ with h | h | h | h
    · rw [h] at hnext
      exact absurd (of_decide_eq_true hnext) (by decide)
    · exact Or.inl h
    · rw [h] at hnext
      exact absurd (of_decide_eq_true hnext) (by decide)
    · exact Or.inr h

/-- **THE COVER-CELL RESIDUE IS REFUTED** — the cover-cell census's
frozen statement is FALSE, decide-witnessed: the exhibited WF, stuck,
saturated, delivered board `fa2` admits NO cover — the `r−1`
opposite-family cells are the red aces, both founded below their
frontiers, so the un-founded clause fails on every candidate.  The
residue `ascent_cover_cell` above therefore cannot land — its sorry
is the honest witness of a FALSE statement, and the owner's recourse
is statement-level (the α/β repairs priced in the row's verdict
note). -/
theorem ascent_cover_cell_refuted :
    ¬ ∀ (W : State) (x : Card), W.WF → AscentStuck W →
      (DoubleHot W x ∧ MobileTwin W x ∧
        rungAt W x.suit ≤ x.rank.toIdx ∧
        rungAt W x.twin.suit ≤ x.twin.rank.toIdx) →
      (∀ (c : Card), (c = x ∨ c = x.twin) ↔ CanRaiseS W c) →
      ∃ (d : Card),
        d.rank.toIdx + 1 = x.rank.toIdx ∧
        d.suit.color ≠ x.suit.color ∧
        d.rank.toIdx ≥ W.foundHeight d.suit ∧
        (∃ (c : Anchor), d ∈ (W.piles c).faceUp) := by
  intro h
  obtain ⟨d, hd1, -, hd3, -⟩ :=
    h fa2 faS2 fa2_wf fa2_stuck fa2_pairDelivered fa2_iff
  have h0 : faS2.rank.toIdx = 1 := rfl
  rw [h0] at hd1
  have h0' : d.rank.toIdx = 0 := by omega
  have h1 : fa2.foundHeight d.suit = 1 := by cases d.suit <;> rfl
  rw [h0', h1] at hd3
  omega

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
resurrection mode the corner's docstring prices.

(The two emptied-pile kit rows the commit's reveal/burn modes cite
sit EARLIER in this file — §2c-pre, the persistent-pair section —
since the mid-state landing pin consumes them first.) -/

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

/-- **THE BARE-COVER LANDING PIN** (the corner's second banked leg,
the third succession's isolation): at the commit's successor the
covered twin is VANILLA-DEAD outright — the pin half of the
`ForkWitness W₁ x` parcel, banked so the corner's remaining open is
exactly the saturation half (the resurrection census: whether the
emptied side's fresh seat can re-admit a hot card outside the pair).
The twin tops no pile at the landing: its own pile is capped by the
moved run's rider, the emptied source either reveals a hidden card
(fresh by the WF hidden/face-up disjointness) or burns to the bare
empty record, and WF face-up uniqueness forbids every other pile. -/
private theorem ascent_barecover_landing_pin {W : State} (hwf : W.WF)
    {x d : Card}
    (hrank : d.rank.toIdx + 1 = x.rank.toIdx)
    (hfit : canSitOn d x.twin = true)
    (hctt : CanRaise W x.twin)
    {a : Anchor} {L₂ : List Card}
    (hspl : (W.piles a).faceUp = d :: L₂) :
    ∃ (W₁ : State), State.step W (Move.tabToTab d (Sum.inr x.twin)) = some W₁ ∧
      ¬ CanRaise W₁ x.twin := by
  obtain ⟨W₁, k, hstep, hktw, hpK, hpA, hpOther⟩ :=
    ascent_barecover_commit hwf hrank hfit hctt hspl
  have hwf₁ : W₁.WF := step_wf hwf hstep
  have hmemT : x.twin ∈ (W.piles k).faceUp := Pile.mem_of_top hktw
  have hdxt : d ≠ x.twin := by
    intro hcon
    obtain ⟨hr1, -⟩ := (canSitOn_eq d x.twin).mp hfit
    rw [hcon, Card.twin_rank] at hr1
    omega
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
  -- the twin tops no pile at the landing
  have hnoTop : ∀ q : Anchor, (W₁.piles q).top ≠ some x.twin := by
    intro q
    by_cases hqk : q = k
    · rw [hqk, hpK]
      show lastOf ((W.piles k).faceUp ++ (d :: L₂)) ≠ some x.twin
      obtain ⟨y, hy⟩ := lastOf_exists (show (d :: L₂) ≠ [] from by simp)
      rw [ascent_lastOf_append _ _ (show (d :: L₂) ≠ [] from by simp), hy]
      intro hcon
      have hyc : y = x.twin := Option.some.inj hcon
      rcases List.mem_cons.mp (lastOf_mem hy) with heq | hin
      · rw [heq] at hyc
        exact hdxt hyc
      · rw [hyc] at hin
        exact (mem_faceUp_unique hwf hmemT a (fun h => hka h.symm)).1
          (by rw [hspl]; exact List.mem_cons.mpr (Or.inr hin))
    · by_cases hqa : q = a
      · rcases hpA with ⟨z, t, hhid, hpa⟩ | ⟨hhid, hpa⟩
        · rw [hqa, hpa]
          show lastOf ([z] : List Card) ≠ some x.twin
          intro hcon
          have hzmem : z ∈ (W.piles a).hidden := by
            rw [hhid]; exact List.mem_cons_self ..
          have hzne : z ≠ x.twin := fun hc =>
            (mem_hidden_unique hwf hzmem k hka).2.1
              (by rw [hc]; exact hmemT)
          have h2 : (some z : Option Card) = some x.twin := hcon
          injection h2 with hzz
          exact hzne hzz
        · rw [hqa, hpa]
          exact fun hcon => absurd hcon (by simp [Pile.top, lastOf])
      · rw [hpOther q hqa hqk]
        intro hcon
        exact (mem_faceUp_unique hwf hmemT q hqk).1
          (Pile.mem_of_top hcon)
  refine ⟨W₁, hstep, ?_⟩
  rintro ⟨-, k', hk', -⟩
  exact hnoTop k' ((pileOfTop_eq_some_iff hwf₁).1 hk')

/-- **THE CORNER'S NAMED-PREMISE REDUCTION** (fourth succession): the
bare-cover corner closes outright given the saturation iff at the
named slide's successor — the banked commit pins the covered twin
vanilla-dead at ANY successor of `Move.tabToTab d (Sum.inr x.twin)`
(the step is a function, so the successor is this row's own `W₁`),
and the parcel assembles in ONE line.  Read with the free tilt
(`ascent_tilted_snap`) and the at-stuck bar
(`ascent_barecover_barred_atStuck`), the corner's surviving open is
now EXACTLY its one named premise — the pair's iff at the commit
landing, the resurrection census priced in the corner's route note
(whether the emptied side's fresh seat can re-admit S-live cards
outside the pair at the cold landing)

SIXTH-PASS TRUEING: the premise's ⇐ half is now a banked general row
(`ascent_barecover_landing_sat` below: at every both-live world both
members are S-live at the commit landing), so the surviving half of
the named premise is exactly its third-card exclusion — the datum the
census cut below consumes and the `fa3` board refutes as W-forcible. -/
private theorem ascent_barecover_of_landingiff {W W₁ : State} (hwf : W.WF)
    {x d : Card}
    (hrank : d.rank.toIdx + 1 = x.rank.toIdx)
    (hfit : canSitOn d x.twin = true)
    (hctt : CanRaise W x.twin)
    {a : Anchor} {L₂ : List Card}
    (hspl : (W.piles a).faceUp = d :: L₂)
    (hstep : State.step W (Move.tabToTab d (Sum.inr x.twin)) = some W₁)
    (hiff₁ : ∀ (c : Card), (c = x ∨ c = x.twin) ↔ CanRaiseS W₁ c) :
    ∃ (F : State) (τ : List Move) (x' : Card),
      W.run τ = some F ∧ ForkWitness F x' := by
  obtain ⟨W₁', hstep', hpin⟩ :=
    ascent_barecover_landing_pin hwf hrank hfit hctt hspl
  have hEq : W₁ = W₁' := Option.some.inj (hstep.symm.trans hstep')
  subst hEq
  exact ⟨W₁, [Move.tabToTab d (Sum.inr x.twin)], x, run_one hstep,
    ⟨hiff₁, hpin⟩⟩

/-- **THE LANDING SITE CENSUS** (the restore-geometry surgery's site
half, landed at the census-economy pass): at the commit's spelled
successor every face-up card sits in one of exactly three sites — the
twin's pile (its old face-up run plus the moved run), the emptied
source (the revealed head alone in the reveal mode, nothing in the
burn mode), or a third pile restored verbatim.  Pure list surgery over
the spelled writes; the member half and the `fa3` evidence below both
sit on this geometry. -/
private theorem ascent_barecover_res_sites {W W₁ : State}
    {d : Card} {k a : Anchor} {L₂ : List Card}
    (hpK : W₁.piles k
        = ⟨(W.piles k).hidden, (W.piles k).faceUp ++ (d :: L₂)⟩)
    (hpA : (∃ z t, (W.piles a).hidden = z :: t ∧
          W₁.piles a = ⟨t, [z]⟩) ∨
        ((W.piles a).hidden = [] ∧ W₁.piles a = ⟨[], []⟩))
    (hpOther : ∀ y, y ≠ a → y ≠ k → W₁.piles y = W.piles y)
    {p : Anchor} {c : Card}
    (hmem : c ∈ (W₁.piles p).faceUp) :
    (p = k ∧ (c ∈ (W.piles k).faceUp ∨ c ∈ d :: L₂)) ∨
    (∃ z t, (W.piles a).hidden = z :: t ∧ W₁.piles a = ⟨t, [z]⟩ ∧
      p = a ∧ c = z) ∨
    (p ≠ a ∧ p ≠ k ∧ c ∈ (W.piles p).faceUp) := by
  by_cases hpa : p = a
  · rcases hpA with ⟨z, t, hhid, hpl⟩ | ⟨hhid, hpl⟩
    · rw [hpa, hpl] at hmem
      refine Or.inr (Or.inl ⟨z, t, hhid, hpl, hpa, ?_⟩)
      have h : c ∈ ([z] : List Card) := hmem
      rcases List.mem_cons.mp h with hc | hc
      · exact hc
      · exact absurd hc (by simp)
    · rw [hpa, hpl] at hmem
      have h : c ∈ ([] : List Card) := hmem
      exact absurd h (by simp)
  · by_cases hpk : p = k
    · refine Or.inl ⟨hpk, ?_⟩
      have h : c ∈ ((W.piles k).faceUp ++ d :: L₂) := by
        rw [hpk, hpK] at hmem
        exact hmem
      rcases List.mem_append.mp h with hc | hc
      · exact Or.inl hc
      · exact Or.inr hc
    · refine Or.inr (Or.inr ⟨hpa, hpk, ?_⟩)
      rw [hpOther p hpa hpk] at hmem
      exact hmem

/-- **THE BOTH-LIVE LANDING SATURATION** (the census's ⇐ half, now
GENERAL — the member half of the landing iff at every both-live
world): both pair members are S-live at the commit's spelled
successor.  The exposed member rides its own vanilla license —
through the third-pile restore leg when it tops an untouched pile,
or through the moved run's rider when it topped the emptied source;
the covered member keeps its seat (the splice writes behind its
position) and re-arms the exit clause through the exposed member's
top at the landing; both stay hot by the rung freeze (the slide
never touches a foundation).  `fa3_membersLive` below is this row's
board instance; this row removes the instancehood. -/
private theorem ascent_barecover_landing_sat {W W₁ : State} (hwf : W.WF)
    {x d : Card}
    (hstep : State.step W (Move.tabToTab d (Sum.inr x.twin)) = some W₁)
    (hrank : d.rank.toIdx + 1 = x.rank.toIdx)
    (hctt : CanRaise W x.twin)
    (hboth : CanRaise W x)
    {a k : Anchor} {L₂ : List Card}
    (hspl : (W.piles a).faceUp = d :: L₂)
    (hktw : (W.piles k).top = some x.twin)
    (hpK : W₁.piles k
        = ⟨(W.piles k).hidden, (W.piles k).faceUp ++ (d :: L₂)⟩)
    (hpOther : ∀ y, y ≠ a → y ≠ k → W₁.piles y = W.piles y) :
    CanRaiseS W₁ x ∧ CanRaiseS W₁ x.twin := by
  have hwf₁ : W₁.WF := step_wf hwf hstep
  -- the rung freeze
  have hfreeze : ∀ (σ : Suit), W₁.foundHeight σ = W.foundHeight σ := by
    intro σ
    rw [← ascent_rung_height W₁ σ, ascent_slide_rung hstep σ,
      ascent_rung_height W σ]
  have hnext₁ : ∀ {c : Card}, W.nextUp c = true → W₁.nextUp c = true := by
    intro c h
    show decide (c.rank.toIdx = W₁.foundHeight c.suit) = true
    rw [hfreeze c.suit]
    exact h
  -- the vanilla licenses, unpacked
  obtain ⟨hnextT, k', hpodT, hchopT⟩ := hctt
  obtain ⟨hnextX, b, hpodX, hchopX⟩ := hboth
  have htopT' : (W.piles k').top = some x.twin :=
    (pileOfTop_eq_some_iff hwf).1 hpodT
  have htopX : (W.piles b).top = some x := (pileOfTop_eq_some_iff hwf).1 hpodX
  -- the twin's license names the same pile the spell names
  have hkk' : k = k' := by
    by_cases hcon : k = k'
    · exact hcon
    · have hb := mem_faceUp_unique hwf (Pile.mem_of_top hktw) k'
        (fun h => hcon h.symm)
      exact absurd (Pile.mem_of_top htopT') hb.1
  rw [← hkk'] at hchopT
  -- the twin-pile writes, flat
  have hfaceK : (W₁.piles k).faceUp
      = (W.piles k).faceUp ++ d :: L₂ := by
    rw [hpK]
  have hhidK : (W₁.piles k).hidden = (W.piles k).hidden := by rw [hpK]
  have hlT : lastOf (W.piles k).faceUp = some x.twin := hktw
  obtain ⟨pre, hsnocT⟩ := lastOf_eq_snoc hlT
  -- the exposed member at the landing
  obtain ⟨satX, hpodX₁⟩ :
      CanRaiseS W₁ x ∧ ∃ (B : Anchor), W₁.pileOfTop x = some B := by
    by_cases hba : b = a
    · have hdx : d ≠ x := by
        intro hcon
        rw [← hcon] at hrank
        omega
      rw [hba] at htopX
      -- it rode the emptied source's run into the twin's pile
      have hlA : lastOf (d :: L₂) = some x := by
        rw [← hspl]
        exact htopX
      obtain ⟨pfx, hsnocA⟩ := lastOf_eq_snoc hlA
      have hdpfx : d ∈ pfx := by
        rcases List.mem_append.mp
          (show d ∈ pfx ++ [x] by
            rw [← hsnocA]; exact List.mem_cons_self ..) with h | h
        · exact h
        · rcases List.mem_cons.mp h with h' | h'
          · exact absurd h' hdx
          · exact absurd h' (by simp)
      have hne : d :: L₂ ≠ [] := by simp
      have htopXk : (W₁.piles k).top = some x := by
        show lastOf ((W₁.piles k).faceUp) = some x
        rw [hfaceK, ascent_lastOf_append _ _ hne]
        exact hlA
      have hshapeX : (W₁.piles k).faceUp
          = ((W.piles k).faceUp ++ pfx) ++ x :: [] := by
        rw [hfaceK, hsnocA, List.append_assoc]
      have hseatX : ((W.piles k).faceUp ++ pfx) ≠ [] ∨
          ((W₁.piles k).hidden = [] ∧ x.rank = Rank.king) :=
        Or.inl
          (fun hcon =>
            absurd (List.mem_append.mpr (Or.inr hdpfx))
              (by rw [hcon]; simp))
      exact ⟨(canRaiseS_iff hwf₁).2 ⟨hnext₁ hnextX, k,
        (W.piles k).faceUp ++ pfx, [], hshapeX, hseatX, Or.inl rfl⟩,
        ⟨k, (pileOfTop_eq_some_iff hwf₁).2 htopXk⟩⟩
    · by_cases hbk : b = k
      · rw [hbk] at htopX
        have hxx : x = x.twin := Option.some.inj (htopX.symm.trans hktw)
        exact absurd hxx.symm (Card.twin_ne x)
      · -- the third-pile restore leg
        have hhlX : lastOf (W.piles b).faceUp = some x := htopX
        obtain ⟨pre, hsnocX⟩ := lastOf_eq_snoc hhlX
        have hfaceB : (W₁.piles b).faceUp = (W.piles b).faceUp := by
          rw [hpOther b hba hbk]
        have hshapeX : (W₁.piles b).faceUp = pre ++ x :: [] := by
          rw [hfaceB, hsnocX]
        have hseatX : pre ≠ [] ∨
            ((W₁.piles b).hidden = [] ∧ x.rank = Rank.king) := by
          rcases hchopX with hc | hh
          · rw [hsnocX, chop_snoc] at hc
            exact Or.inl hc
          · refine Or.inr ⟨?_, hh.2⟩
            rw [hpOther b hba hbk]
            exact hh.1
        have htopXb : (W₁.piles b).top = some x := by
          show lastOf ((W₁.piles b).faceUp) = some x
          rw [hfaceB]
          exact hhlX
        exact ⟨(canRaiseS_iff hwf₁).2 ⟨hnext₁ hnextX, b, pre, [], hshapeX,
          hseatX, Or.inl rfl⟩,
          ⟨b, (pileOfTop_eq_some_iff hwf₁).2 htopXb⟩⟩
  -- the covered member at the landing
  have hseatT : pre ≠ [] ∨
      ((W₁.piles k).hidden = [] ∧ x.twin.rank = Rank.king) := by
    rcases hchopT with hc | hh
    · rw [hsnocT, chop_snoc] at hc
      exact Or.inl hc
    · refine Or.inr ⟨?_, hh.2⟩
      rw [hhidK]
      exact hh.1
  have hshapeT : (W₁.piles k).faceUp = pre ++ x.twin :: d :: L₂ := by
    rw [hfaceK, hsnocT, List.append_assoc]
    rfl
  refine ⟨satX, ?_⟩
  refine (canRaiseS_iff hwf₁).2
    ⟨hnext₁ hnextT, k, pre, d :: L₂, hshapeT, hseatT, ?_⟩
  refine Or.inr ?_
  rw [Card.twin_twin]
  obtain ⟨B, hB⟩ := hpodX₁
  rw [hB]
  exact Option.some_ne_none B

/-- **THE CENSUS CUT** (the verdict's exact cutting surface): in the
both-live scope the corner closes given EXACTLY ONE datum — no card
outside the pair is S-live at the commit landing.  The member half of
that datum is already banked (`ascent_barecover_landing_sat`, no
census needed); the third-card half is the named residue, and the
`fa3` board refutes it at a corner-shaped world (`fa3_resurrected`:
the emptied side's reveal CAN re-admit a hot buried mate through the
covered-leg exit channel), so the datum is NOT W-forcible — never
forced here.  Read with the free tilt (`ascent_tilted_snap`), this row
says the corner's surviving open is exactly one premise, and what that
premise costs. -/
private theorem ascent_barecover_corner_of_nores {W W₁ : State} (hwf : W.WF)
    {x d : Card}
    (hstep : State.step W (Move.tabToTab d (Sum.inr x.twin)) = some W₁)
    (hrank : d.rank.toIdx + 1 = x.rank.toIdx)
    (hfit : canSitOn d x.twin = true)
    (hctt : CanRaise W x.twin)
    (hboth : CanRaise W x)
    {a : Anchor} {L₂ : List Card}
    (hspl : (W.piles a).faceUp = d :: L₂)
    (hnores : ∀ (c : Card), c ≠ x → c ≠ x.twin → ¬ CanRaiseS W₁ c) :
    ∃ (F : State) (τ : List Move) (x' : Card),
      W.run τ = some F ∧ ForkWitness F x' := by
  obtain ⟨W₁', k, hstep', hktw, hpK, -, hpOther⟩ :=
    ascent_barecover_commit hwf hrank hfit hctt hspl
  have hEq : W₁ = W₁' := Option.some.inj (hstep.symm.trans hstep')
  subst hEq
  obtain ⟨satX, satT⟩ :=
    ascent_barecover_landing_sat hwf hstep hrank hctt hboth hspl hktw hpK
      hpOther
  have hiff₁ : ∀ (c : Card), (c = x ∨ c = x.twin) ↔ CanRaiseS W₁ c := by
    intro c
    constructor
    · rintro (rfl | rfl)
      · exact satX
      · exact satT
    · intro hcS
      by_cases hcx : c = x
      · exact Or.inl hcx
      · by_cases hctx : c = x.twin
        · exact Or.inr hctx
        · exact absurd hcS (hnores c hcx hctx)
  exact ascent_barecover_of_landingiff hwf hrank hfit hctt hspl hstep hiff₁

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

/-- **THE FORCED RETURN BASE** (fourth succession, the ceiling's
named constant landed): at any exhausted world carrying the pair's
saturation iff, a fitting cover's `canPlace` onto the topped twin
reads TRUE outright — the iff's membership half forces the twin
S-live (the stuckness collapse makes it vanilla-live, so its pile's
top it is), and the placement guard is the fit verbatim.  This is the
row the β-arm rides: whatever the census delivers on the founded
side, its licensed `foundToTab` return base — the topped twin — is
forced by the very iff that kills the standing cover, so the
`ExhaustShapeRec` founded-arm's `∃ e` clause can never be the
obstruction.  (The row is WF-unconditioned: the collapse, the license
read and the placement guard consume no WF.) -/
theorem ascent_rec_base_of_iff {W : State}
    (hstuck : AscentStuck W) {x d : Card}
    (hiff : ∀ (c : Card), (c = x ∨ c = x.twin) ↔ CanRaiseS W c)
    (hfit : canSitOn d x.twin = true) :
    W.canPlace d (Sum.inr x.twin) = true := by
  obtain ⟨-, k, hk, -⟩ :=
    ascent_stuck_collapse hstuck ((hiff x.twin).mp (Or.inr rfl))
  rw [canPlace_inr_located hk]
  exact hfit

/-- The first founded cell of the heart row (the fa2 board's only
standing cover candidate: founded, rank-`0`, opposite-family to both
black deuces). -/
private def faHA : Card := faCrd .heart .ace

/-- **THE β-SHAPE IS DELIVERED AT `fa2`** (fourth succession, decide
grade): the file's first certified saturation witness
(`fa2_wf`, `fa2_stuck`, `fa2_iff`, `fa2_pairDelivered`) DELIVERS the
recoverable shape — the heart ace founded at its frontier (the heart
row's `foundTop`, rank-`0`-at-height-`1`), fitting the black deuce
pair by twin-blind arithmetic, with the licensed return base the
topped spade deuce itself.  THE EVIDENCE: after the owner's
β-ratification (the `ExhaustShapeRec` swap staged in §2e), the `fa2`
class of boards stops being an obstruction to the exhaustion row (the
ceiling killed only the STANDING cover) and becomes a genuine
DELIVERY class — the β-future is nonvacuous at a real stuck
exhaustion, witnessed `decide`-clean rather than argued in prose. -/
theorem fa2_shapeRec : ExhaustShapeRec fa2 faS2 faHA := by
  refine ⟨fa2_pairDelivered.1, by decide, by decide, by decide, Or.inr ?_⟩
  exact ⟨by decide, by decide, faS2, by decide⟩

/-- **THE β-PULL FIRES AT `fa2`** (fourth succession, riding the
banked pullback): the licensed `foundToTab` return of the heart ace
onto the spade deuce's top FIRES at the saturated board and lands
the standing `ExhaustShape` in ONE leg — the β-recoverable
delivery witnessed end-to-end at the kernel (the standing shape the
ceiling barred at `fa2` itself, recovered by the one licensed hop
the recoverable disjunct licensed). -/
theorem fa2_pullWitness :
    ∃ (W' : State), State.step fa2 (Move.foundToTab faHA (Sum.inr faS2)) = some W' ∧
      ExhaustShape W' faS2 faHA := by
  have hrank : faHA.rank.toIdx + 1 = faS2.rank.toIdx := by decide
  have hcol : faHA.suit.color ≠ faS2.suit.color := by decide
  have hfit : canSitOn faHA faS2.twin = true := by decide
  have hfront : fa2.foundTop faHA.suit = some faHA := by decide
  have hfh : faHA.rank.toIdx + 1 = fa2.foundHeight faHA.suit := by decide
  have hbase : fa2.canPlace faHA (Sum.inr faS2) = true := by decide
  exact ascent_cover_pullback hrank hcol hfit fa2_pairDelivered.1 hfront hfh hbase

/-- **THE EXHAUSTION-SHAPE CEILING** (the third succession's
universal row): at a `WF` STUCK state, the exhaustion row's own
conclusion — a delivered `ExhaustShape` pair with its STANDING
face-up cover, together with the saturation iff — is IMPOSSIBLE.
The iff's membership half forces the twin vanilla-live at `W` (its
left side is trivially true at the member; the stuckness collapses
the S-grade onto the vanilla one), the shape's standing cover is
face-up and fits the twin by its own clauses, and the live-cover bar
refuses the pair: the cover's slide onto the live twin's top would
FIRE against the stuckness.

READ THIS AS THE UNIVERSAL CONSTANT BEHIND THE `fa2` KILL: the
crew's `ascent_cover_cell_refuted` decides the census false at ONE
board; the ceiling proves the row's ENTIRE conclusion (standing
cover AND pair-saturation) impossible at EVERY `WF` stuck state —
the α-arm of the delivered shape can never stand at any exhaustion
that carries the saturation, not merely at `fa2`.  The frozen row
`ascent_exhaustion_forks` is therefore dead at every one of its own
hypothesis-satisfying worlds: its only live futures are VACUITY (no
`hbelow` start ever ascends into a stuck exhaustion — the very
reachability census the probe declines to decide) or the owner's
β-ratification (the `ExhaustShapeRec` recoverable disjunct staged in
§2e: a cover FOUNDED at its suit's frontier is invisible to the
bar, and its licensed return base — the topped twin — is exactly
what the iff's liveness forces, so the β-arm is precisely the shape
the living rows leave standing).  The frozen statements are
untouched; this row is additive evidence on the
`Orig/ForkDescent.lean` §3R precedent — a negative constant
retired at the kernel, not in prose. -/
theorem ascent_exhaust_shape_impossible {W : State} (hwf : W.WF)
    (hstuck : AscentStuck W) :
    ¬ (∃ (x d : Card), ExhaustShape W x d ∧
        (∀ (c : Card), (c = x ∨ c = x.twin) ↔ CanRaiseS W c)) := by
  rintro ⟨x, d, hex, hiff⟩
  exact ascent_stuck_livecover_bar hwf hstuck
    (ascent_stuck_collapse hstuck ((hiff x.twin).mp (Or.inr rfl)))
    hex.2.2.2.2.1 hex.2.2.2.2.2

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
descent program's boards.

THIRD-SUCCESSION CEILING NOTICE: the row's own conclusion is now
kernel-known IMPOSSIBLE at every `WF` stuck state
(`ascent_exhaust_shape_impossible`: the standing cover plus the
saturation iff are jointly refused by the live-cover bar — the
iff's membership half makes the twin vanilla-live under the
stuckness collapse, and the shape's face-up fitting cover would
slide onto it, firing against `AscentStuck`).  The row therefore
holds only VACUOUSLY — no `hbelow` start ever ascends into a stuck
exhaustion, the very census the probe declares open — and any
non-vacuous delivery requires the owner's β-ratification (the
`ExhaustShapeRec` swap staged in §2e, whose licensed return base is
the topped twin itself).  The four named pieces keep their residues
and grades; the row's statement stays byte-frozen, its body
untouched.

FOURTH-SUCCESSION β-NOTICE (2026-10-17): the vacuity-or-β fork is now
WITNESSED on the β side at the kernel — `fa2_shapeRec` delivers the
recoverable shape at this file's own certified saturated board and
`fa2_pullWitness` lands the standing `ExhaustShape` from it in one
licensed leg, while `ascent_rec_base_of_iff` proves the founded
cover's return base is forced by the very iff that kills the standing
cover (the ONLY obstacle the founded arm could have carried).  The
head keeps its sorry: its non-vacuous future remains the owner's
ratification of the staged swap, its vacuous future remains the
probe's reachability census — both routes document the whole gap, and
neither is forced here. -/
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
§2e, nothing consumed until the owner ratifies.  The session-4
persistent-pair kit (private, additive, no consumers yet) is
audited directly below — the induction carries only `Quot.sound`
off `step_wf`'s WF transport.

THIRD-SUCCESSION ADDITIONS (2026-10-13, session 5): the cover-cell
mini's verdict is now DECIDED — the refutation board rows below
(`fa2`: WF, stuck, delivered, saturated — decide-grade) and the
certified negation `ascent_cover_cell_refuted`, ZERO-sorry: the
cover-cell residue keeps its sorry (the row as stated is FALSE, the
`fa2` record, on the `Orig/ForkDescent.lean` §3R precedent), so the
sorry count stays exactly FOUR and every earlier profile stands.
The corner's landing pin (`ascent_barecover_landing_pin`, private,
banked for the corner's route) reads the commit's own parcel —
expected `[propext, Quot.sound]`-grade off the banked kit, no
Classical inflow.

SECOND-LANDER ADDITIONS (the third succession's universal rows):
the live-cover bar `ascent_stuck_livecover_bar` and the
exhaustion-shape ceiling `ascent_exhaust_shape_impossible` are
PUBLIC, audited directly below alongside the earlier heads; the
support kit and the three staging rows are private (the
slide-fires kit feeding the bar, the corner's stuck-world bar, the
cell-armor persistence row, the climb parking reduction, the
saturation decomposition) and ride the same banked grades — zero
`Classical.choice` (all splits on the bar's decidable license
reads), zero new `sorryAx`, the sorry count stays exactly FOUR.

FOURTH-SUCCESSION ADDITIONS (2026-10-17, session 6): ten fresh rows
land zero-sorry — the free tilt `ascent_tilted_snap` and
the corner's named-premise reduction
`ascent_barecover_of_landingiff` (both private, the corner's last
assembly legs); the twin-flip re-packs
`ascent_doublehot_twinflip`/`ascent_mobile_twinflip` with the
forced-topping row `ascent_stuck_liveForcesTwinTop` and the
member-live split `ascent_stuck_memberLive_split` (private, the
`fa1` axis W-locally shrunk to the bare-seat read, its seat
assembly `ascent_liveTwin_of_seat`); and the three public β-evidence
heads — `ascent_rec_base_of_iff` (the forced return base),
`fa2_shapeRec` and `fa2_pullWitness` (decide grade on the banked
pullback).  All read `[propext]`-or-`[propext, Quot.sound]`
grades, audited below; zero `Classical.choice`, zero new `sorryAx`.
The rows that carry `sorryAx` remain EXACTLY the §1 assembly
(`orientation_assembly_fork`, through the bare-cover corner's named
premise) and the §2 head (`ascent_exhaustion_forks`, through the
climb/saturation/cover pieces — the cover piece now through the
refuted W-local census per the `fa2` record); the sorry count stays
exactly FOUR and every earlier profile stands. -/

#print axioms orientation_assembly_fork
#print axioms ascent_stuck_collapse
#print axioms ascent_stuck_unblocked
#print axioms ascent_selfland_refuted
#print axioms ascent_cover_pullback
#print axioms ascent_pair_persists
#print axioms ascent_slide_faceUp
#print axioms ascent_slideLanding
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
#print axioms fa2_wf
#print axioms fa2_stuck
#print axioms fa2_pairDelivered
#print axioms fa2_iff
#print axioms ascent_cover_cell_refuted
#print axioms ascent_barecover_landing_pin
#print axioms ascent_stuck_livecover_bar
#print axioms ascent_exhaust_shape_impossible
#print axioms ascent_tabToTab_fires
#print axioms ascent_barecover_barred_atStuck
#print axioms ascent_cell_armor
#print axioms ascent_climb_of_parked
#print axioms ascent_stuck_sat_of_excLive
#print axioms ascent_exhaustion_forks
#print axioms ascent_tilted_snap
#print axioms ascent_barecover_of_landingiff
#print axioms ascent_doublehot_twinflip
#print axioms ascent_mobile_twinflip
#print axioms ascent_stuck_liveForcesTwinTop
#print axioms ascent_liveTwin_of_seat
#print axioms ascent_stuck_memberLive_split
#print axioms ascent_rec_base_of_iff
#print axioms fa2_shapeRec
#print axioms fa2_pullWitness

/-! ## §2f. The both-live cold-resurrection census board `fa3` (2026-10-17, session 7)

CENSUS VERDICT: **REFUTED** as universally staged — decide-witnessed,
on the `fa2`/§3R pattern.  The bare-cover corner's remaining open
after the banked route (the BOTH-LIVE cold census: is the pair's
saturation iff restorable at the named slide's commit successor?) is
now DECIDED FALSE at a corner-shaped board: the landed cover itself
CAN re-enter the S-set outside the pair — through the resurrection
mode the corner's own route note prices (a cover that was
seat-blocked at the start, bare and non-king over a hidden deck,
re-acquires a seat at the landing: its rung hot, the twin's own seat
content now below it, and its exit clause open as the landed run's
own rider).

THE WITNESS ECONOMY: the queens' pair double-live and saturated at
rung eleven (`faQH`/`faQD`, hearts and diamonds founded A–J); the
cover `faJS` FIRST-FACED at `p1` over the hidden `faC5`, hot at its
own rung ten (spades founded A–10), seat-blocked at the start (bare,
non-king, the hidden deck below it — `fa3_coverDead`); the black
kings seat both queens (`faKS` at `p0`, `faKC` at `p3`, both
un-hot — club at rung four, spade past its jack); eleven cards sunk
in the stock, invisible to the license.  THE COMMIT: the named
slide fires into `fa3L` (the reveal mode realized — `faC5` exposed
atop the emptied `p1`, the cover whole on the twin at `p0`); at
`fa3L` BOTH MEMBERS REMAIN S-LIVE (the member half SURVIVES —
`fa3_membersLive`) while the cover RESURRECTS
(`fa3_resurrected`): re-seated atop the twin's pile (`faKS` and
`faQD` below it), hot at its own rung, its exit open as the run's
own rider, a THIRD card sits S-live outside the pair — so
`ascent_barecover_of_landingiff`'s saturation premise is not
universally restorable (`fa3_census_refuted`) and the corner's staged
route is DEAD at the witness.  The frozen rows are untouched; the
fresh heads are all decide/`rfl`-grade off the banked flat
characterization; the sorry count stays exactly FOUR. -/

/-- The census board's named cards (the `fa` house style). -/
private def faQH : Card := faCrd .heart .queen
private def faQD : Card := faCrd .diamond .queen
private def faJS : Card := faCrd .spade .jack
private def faKS : Card := faCrd .spade .king
private def faKC : Card := faCrd .club .king
private def faD6 : Card := faCrd .diamond .six
private def faH4 : Card := faCrd .heart .four
private def faS5 : Card := faCrd .spade .five
private def faC5 : Card := faCrd .club .five

/-- **THE BOTH-LIVE COLD-CENSUS BOARD `fa3`** — the queens' pair
double-live and saturated at rung eleven; the cover `faJS` first-faced
over the hidden `faC5` at `p1`, hot at its own rung ten (spades
founded A–10) but seat-blocked there (bare, non-king, the hidden
deck below); the black kings seat both queens; everything else sunk
in the stock or founded. -/
private def fa3 : State where
  found := fun s => match s with
    | .spade => faTakeUp s 10
    | .club => faTakeUp s 4
    | .heart | .diamond => faTakeUp s 11
  piles := fun a => match a with
    | .p0 => ⟨[], [faKS, faQD]⟩
    | .p1 => ⟨[faC5], [faJS]⟩
    | .p2 => ⟨[], []⟩
    | .p3 => ⟨[], [faKC, faQH]⟩
    | .p4 => ⟨[], []⟩
    | .p5 => ⟨[], []⟩
    | .p6 => ⟨[], []⟩
  stock :=
    [faCrd .spade .queen,
     faCrd .club .six, faCrd .club .seven, faCrd .club .eight,
     faCrd .club .nine, faCrd .club .ten, faCrd .club .jack,
     faCrd .club .queen,
     faCrd .heart .king, faCrd .diamond .king]
  waste := []
  drawStep := 1

private theorem fa3_wf_found : ∀ s : Suit, ∃ n, fa3.found s = s.upCards.take n := by
  intro s
  cases s with
  | spade => exact ⟨10, rfl⟩
  | heart => exact ⟨11, rfl⟩
  | diamond => exact ⟨11, rfl⟩
  | club => exact ⟨4, rfl⟩

private theorem fa3_wf_runs : ∀ a : Anchor, runOK (fa3.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

private theorem fa3_wf_count : ∀ c ∈ Card.universe, fa3.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

/-- The both-live census board is `WF` (kernel-decided). -/
theorem fa3_wf : fa3.WF :=
  ⟨fa3_wf_found, fa3_wf_runs, fa3_wf_count, by decide⟩

private theorem fa3_p0 : fa3.piles .p0 = ⟨[], [faKS, faQD]⟩ := rfl
private theorem fa3_p1 : fa3.piles .p1 = ⟨[faC5], [faJS]⟩ := rfl
private theorem fa3_p2 : fa3.piles .p2 = ⟨[], []⟩ := rfl
private theorem fa3_p3 : fa3.piles .p3 = ⟨[], [faKC, faQH]⟩ := rfl
private theorem fa3_p4 : fa3.piles .p4 = ⟨[], []⟩ := rfl
private theorem fa3_p5 : fa3.piles .p5 = ⟨[], []⟩ := rfl
private theorem fa3_p6 : fa3.piles .p6 = ⟨[], []⟩ := rfl

/-- **THE FACE-UP INVENTORY AT `fa3`**: exactly the seated pair, the
two kings, and the first-faced cover. -/
theorem fa3_faceUp : ∀ c ∈ Card.universe,
    (∃ a, c ∈ (fa3.piles a).faceUp) →
      c = faQH ∨ c = faQD ∨ c = faJS ∨ c = faKS ∨ c = faKC := by
  intro c _ ⟨a, hc⟩
  cases a with
  | p0 =>
      rw [fa3_p0] at hc; simp at hc
      rcases hc with h | h
      · rw [h]; simp
      · rw [h]; simp
  | p1 =>
      rw [fa3_p1] at hc; simp at hc
      rw [hc]; simp
  | p2 =>
      rw [fa3_p2] at hc
      cases hc
  | p3 =>
      rw [fa3_p3] at hc; simp at hc
      rcases hc with h | h
      · rw [h]; simp
      · rw [h]; simp
  | p4 => rw [fa3_p4] at hc; cases hc
  | p5 => rw [fa3_p5] at hc; cases hc
  | p6 => rw [fa3_p6] at hc; cases hc

/-- **THE COVER IS SEAT-BLOCKED AT THE START**: the first-faced `faJS`
is S-dead at `fa3` — the flat characterization's seat clause can't
arm: bare below (nothing face-up under it), never a king, and the
hidden deck below is nonempty.  This is the census's pivot cell —
the card the saturation keeps dead for its seat becomes live at the
re-seated landing. -/
private theorem fa3_coverDead : ¬ CanRaiseS fa3 faJS := by
  intro hS
  obtain ⟨-, a, bs, run, hshape, hseat, -⟩ := (canRaiseS_iff fa3_wf).mp hS
  have hmema : faJS ∈ (fa3.piles a).faceUp := by
    rw [hshape]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
  have hmem1 : faJS ∈ (fa3.piles .p1).faceUp := by
    rw [fa3_p1]
    exact List.mem_cons_self ..
  have hap1 : a = Anchor.p1 := by
    by_cases hcon : a = Anchor.p1
    · exact hcon
    · have hb := mem_faceUp_unique fa3_wf hmem1 a hcon
      exact absurd hmema hb.1
  rw [hap1, fa3_p1] at hshape
  have hl : 1 = bs.length + (run.length + 1) := by
    have h2 := congrArg List.length hshape
    simpa using h2
  have hbs : bs = [] := by
    cases bs with
    | nil => rfl
    | cons e r =>
        rw [List.length_cons] at hl
        omega
  rw [hbs] at hseat
  rcases hseat with hne | hh
  · exact hne rfl
  · rw [hap1, fa3_p1] at hh
    exact absurd hh.1 (by decide)

/-- **THE SATURATION IS CERTIFIED AT THE BOTH-LIVE BOARD**: the S-set
at `fa3` is EXACTLY the queens' pair — both members vanilla-live;
every other face-up card un-hot; the cover `faJS` hot at its own
rung but seat-blocked (`fa3_coverDead`); the stocked eleven
invisible to the license; founded cards top nothing. -/
theorem fa3_iff : ∀ (c : Card), (c = faQH ∨ c = faQH.twin) ↔ CanRaiseS fa3 c := by
  intro c
  constructor
  · rintro (rfl | rfl)
    · exact CanRaiseS.now _
        ⟨by decide, Anchor.p3, by decide, Or.inl (by decide)⟩
    · exact CanRaiseS.now _
        ⟨by decide, Anchor.p0, by decide, Or.inl (by decide)⟩
  · intro hS
    have hnext : fa3.nextUp c = true := ((canRaiseS_iff fa3_wf).mp hS).1
    obtain ⟨a, bs, run, hshape, -, -⟩ :=
      ((canRaiseS_iff fa3_wf).mp hS).2
    have hmem : c ∈ (fa3.piles a).faceUp := by
      rw [hshape]
      exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
    rcases fa3_faceUp c (Card.mem_universe c) ⟨a, hmem⟩ with
      h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by rw [h]; rfl)
    · rw [h] at hS
      exact absurd hS fa3_coverDead
    · rw [h] at hnext; exact absurd (of_decide_eq_true hnext) (by decide)
    · rw [h] at hnext; exact absurd (of_decide_eq_true hnext) (by decide)

/-- **BOTH-LIVE**: the census's own scope witnessed — both queens
vanilla-live at `fa3` (hot, topping seated piles). -/
theorem fa3_bothLive : CanRaise fa3 faQH ∧ CanRaise fa3 faQD :=
  ⟨⟨by decide, Anchor.p3, by decide, Or.inl (by decide)⟩,
   ⟨by decide, Anchor.p0, by decide, Or.inl (by decide)⟩⟩

/-- **THE WITNESS WORLD IS CORNER-SHAPED** (both-live grade): `fa3`
carries every hypothesis the bare-cover corner consumes — the
saturation iff (pair exactly the queens), the twin's vanilla
license, the cover's rank/fit/first-faced shape — AND the census's
own both-live scope (the witness queen also vanilla-live). -/
theorem fa3_cornerWorld :
    fa3.WF ∧
      (∀ (c : Card), (c = faQH ∨ c = faQH.twin) ↔ CanRaiseS fa3 c) ∧
      CanRaise fa3 faQH ∧ CanRaise fa3 faQH.twin ∧
      (faJS.rank.toIdx + 1 = faQH.rank.toIdx) ∧
      (faJS ≠ faQH.twin) ∧
      (canSitOn faJS faQH.twin = true) ∧
      ∃ (a : Anchor), (fa3.piles a).faceUp = faJS :: ([] : List Card) := by
  refine ⟨fa3_wf, fa3_iff, fa3_bothLive.1, fa3_bothLive.2, by decide,
    by decide, by decide, ⟨Anchor.p1, rfl⟩⟩

/-- **THE COMMIT'S SUCCESSOR `fa3L`** — the named slide
`tabToTab faJS (inr faQD)` fired: the cover whole on the twin's pile
(`p0`), the emptied `p1` revealing `faC5`, everything else — both
foundation frontiers and the stock included — untouched. -/
private def fa3L : State :=
  (fa3.setPile Anchor.p1
      (Pile.afterRunRemoved (fa3.piles Anchor.p1) [])).putRun
    [faJS] (Sum.inr faQD)

/-- **THE NAMED SLIDE FIRES INTO `fa3L`**: the bare-cover commit's
spelled successor, realized at the board — the covering run lands
whole on the twin's pile, the emptied source reveals its hidden head,
every other pile and field untouched (the reveal mode of
`ascent_barecover_commit`). -/
theorem fa3_commit :
    State.step fa3 (Move.tabToTab faJS (Sum.inr faQD)) = some fa3L := by
  have hhold : fa3.pileHolding faJS = some Anchor.p1 := by decide
  have hcan : fa3.canPlace faJS (Sum.inr faQD) = true := by decide
  have hfrom : fromCard faJS (fa3.piles Anchor.p1).faceUp
      = [faJS] := by decide
  have hbel : below faJS (fa3.piles Anchor.p1).faceUp = [] := by decide
  rw [step_tabToTab_eq, hhold]
  simp only [hcan]
  rw [hfrom, hbel]
  simp only [ite_true]
  rfl

/-- The commit's successor is `WF` (the banked WF transport). -/
theorem fa3L_wf : fa3L.WF := step_wf fa3_wf fa3_commit

/-- **THE MEMBER HALF SURVIVES AT THE COMMIT LANDING**: both pair
members remain S-live at `fa3L` — `faQH` still vanilla (its pile
untouched), `faQD` through the covered-leg exit (buried under the
landed cover, its mate still topping at `p3`).  The census's failure
at this board is EXACTLY the exclusion half. -/
theorem fa3_membersLive : CanRaiseS fa3L faQH ∧ CanRaiseS fa3L faQD :=
  ⟨(canRaiseS_iff fa3L_wf).2
      ⟨by decide, Anchor.p3, [faKC], [], rfl, Or.inl (by simp), Or.inl rfl⟩,
    (canRaiseS_iff fa3L_wf).2
      ⟨by decide, Anchor.p0, [faKS], [faJS], rfl, Or.inl (by simp),
        Or.inr (by decide)⟩⟩

/-- **THE RESURRECTION, DECIDE-WITNESSED**: at the commit landing the
first-faced cover `faJS` — hot since `fa3`, seat-blocked bare over
the hidden deck — RE-ENTERS the S-set through the re-seating: the
landed run seats it atop the twin's pile (`faKS` and `faQD` below
it), the seat clause arms, and its exit stands open as the run's own
rider.  A THIRD card, S-live at `fa3L`, outside the pair. -/
theorem fa3_resurrected :
    CanRaiseS fa3L faJS ∧ faJS ≠ faQH ∧ faJS ≠ faQH.twin :=
  ⟨(canRaiseS_iff fa3L_wf).2
      ⟨by decide, Anchor.p0, [faKS, faQD], [], rfl, Or.inl (by simp),
        Or.inl rfl⟩,
    by decide, by decide⟩

/-- **THE BOTH-LIVE CENSUS IS REFUTED**: the pair's saturation iff
FAILS at the commit's own landing — the board `fa3` satisfies every
bare-cover-corner hypothesis at the census's both-live scope
(`fa3_cornerWorld`), the named slide fires into `fa3L` and both
members stay S-live (`fa3_membersLive`), yet the resurrected cover
`faJS` sits S-live OUTSIDE the pair (`fa3_resurrected`):
`ascent_barecover_of_landingiff`'s named premise is not universally
restorable, and the corner's staged route cannot close the residue —
the honest recourse is statement-level (an emptied-side exclusion
premise, or the exhaustion row's longer search).  The frozen row
keeps its sorry, on the `fa2`/§3R precedent. -/
theorem fa3_census_refuted :
    ¬ (∀ (c : Card), (c = faQH ∨ c = faQH.twin) ↔ CanRaiseS fa3L c) := by
  intro hiff
  have hL : faJS = faQH ∨ faJS = faQH.twin :=
    (hiff faJS).mpr fa3_resurrected.1
  rcases hL with h | h
  · exact fa3_resurrected.2.1 h
  · exact fa3_resurrected.2.2 h

#print axioms fa3_wf
#print axioms fa3_faceUp
#print axioms fa3_iff
#print axioms fa3_bothLive
#print axioms fa3_cornerWorld
#print axioms fa3_commit
#print axioms fa3L_wf
#print axioms fa3_membersLive
#print axioms fa3_resurrected
#print axioms fa3_census_refuted
#print axioms ascent_barecover_res_sites
#print axioms ascent_barecover_landing_sat
#print axioms ascent_barecover_corner_of_nores
