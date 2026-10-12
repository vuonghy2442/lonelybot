import Orig.ForkStateSB

/-!
# Orig — the orbit factorization

The orbit factorization card: `sameOrbitSetoid.r` as the
composition of the board component (`NoDrawPlayW`, reversible plays
with no draw legs) and the draw component (`SWRotW`, the banked
witness rotation closure of `Orig/Canonical.lean`), plus the
`SWPhase` quotient plumbing.

Sections:

* §0 the component definitions;
* §1 the disjoint-field commutation lemma — a fired draw at `st`
  and a fired board leg at the drawn landing square: the board leg
  fires at `st` too, and the draw fires at the moved board (the two
  moves read/write disjoint field sets: the draw touches only
  `stock`/`waste`/`drawStep`, each board leg only `piles`/`found`);
* §2 the draw-last bubbling of witness journeys;
* §3 the factorization theorem — landed clean in
  `Orig/OrbitFactorC.lean` as `sameOrbit_factor_full`;
* §4 the quotient plumbing (`swCompSetoid`, never an instance:
  `sameOrbitSetoid` owns `State`'s setoid slot).
-/

/-! ## §0 The component definitions

The phase component is the banked `SWRotW` (`Orig/Canonical.lean`):
draws-only witness rounds both ways (`DrawPlayW`).  The board
component is this chapter's own `NoDrawPlayW`: witness shuffles
with no draw legs, in both directions. -/

/-- The board component: witness shuffles in both directions whose
plays contain NO draw legs — pure board moves, verified per leg by
`reversibleAtW` witnesses (the `ShufflePlayW` structure carries
them).  Two positions are `NoDrawPlayW`-related exactly when the
board can be reshuffled from one to the other and back without ever
touching the draw zone. -/
def NoDrawPlayW (u v : State) : Prop :=
  ∃ play, ShufflePlayW u play v ∧ (∀ m ∈ play, m ≠ Move.draw) ∧
    ∃ back, ShufflePlayW v back u ∧ (∀ m ∈ back, m ≠ Move.draw)

/-! ## §1 The disjoint-field commutation lemma

The heart of the factorization, one adjacent pair at a time: a fired
draw at `st` and a fired board leg at the drawn landing.  The two
moves' guards and effects live in disjoint field sets — the draw
reads and writes only `stock`/`waste`/`drawStep` (`stepDraw_piles` /
`stepDraw_found` keep the board fields; the field-determined draw
`stepDraw_rel` reads only the zone), and each board leg reads and
writes only `piles`/`found` (the guard congruences of `Orig/Twin.lean`
and the zone-keep projection rows of `Orig/Irreversible.lean`) — so
the board leg fires at `st` as well, and the draw fires at the moved
board with the drawn landing's exact successor.  The waste movers
need no case: a witness journey's leg is never one (the cycle-count
census, `journey_never_wasteToFound`/`journey_never_wasteToTab`).

The small congruence rows below are deduped where they were pure
duplicates of the edge-label chapter's public `EdgeKit` kit (the
draw's draw-step keep, the `putCard`/`putRun` piles congruences,
the waste discriminator, the run `cons` row — cited as `EdgeKit.*`,
not copied).  The three §1 squares stay local BY SHAPE: unlike
their edge-kit namesakes they DERIVE the origin board leg's firing
from the drawn-landing pair instead of assuming both origin
firings. -/

/-- **The §1 square, `tabToFound` leg.**  A fired draw at `st` and a
fired raise at the drawn landing: the raise fires at `st` (its guards
read only the board fields, untouched by the draw), and the draw fires
at the raise's `st`-landing with the drawn landing's exact successor
(the zone is untouched by the raise, so the two draws see one zone). -/
private theorem square_tabToFound {st s₁ s₂ : State} {c : Card}
    (hd : st.stepDraw = some s₁) (hm : s₁.step (Move.tabToFound c) = some s₂) :
    ∃ t, st.step (Move.tabToFound c) = some t ∧ t.stepDraw = some s₂ := by
  obtain ⟨hnext₁, a, hpo₁, hs₂⟩ := step_tabToFound_inv hm
  have hpil : st.piles = s₁.piles := (stepDraw_piles hd).symm
  have hfnd : st.found = s₁.found := (stepDraw_found hd).symm
  have hnext : st.nextUp c = true := by rw [nextUp_congr c hfnd]; exact hnext₁
  have hpo : st.pileOfTop c = some a := by rw [pileOfTop_congr c hpil]; exact hpo₁
  refine ⟨_, step_tabToFound_splice hnext hpo, ?_⟩
  obtain ⟨hz1, hz2, hz3⟩ :
    (({ st.setFound c.suit (st.found c.suit ++ [c]) with
        piles := fun a' =>
          if a' = a then Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
          else st.piles a' } : State).stock = st.stock) ∧
    (({ st.setFound c.suit (st.found c.suit ++ [c]) with
        piles := fun a' =>
          if a' = a then Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
          else st.piles a' } : State).waste = st.waste) ∧
    (({ st.setFound c.suit (st.found c.suit ++ [c]) with
        piles := fun a' =>
          if a' = a then Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
          else st.piles a' } : State).drawStep = st.drawStep) :=
    ⟨rfl, rfl, rfl⟩
  obtain ⟨w, hwfire, hwp, -, hwf, -, hwd, -, hws, hww⟩ :=
    stepDraw_rel hz1 hz2 hz3 hd
  have hpw : ({ st.setFound c.suit (st.found c.suit ++ [c]) with
      piles := fun a' =>
        if a' = a then Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
        else st.piles a' } : State).piles = s₂.piles := by
    rw [hs₂]
    show (fun a' =>
        if a' = a then Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
        else st.piles a')
      = (fun a' =>
        if a' = a then Pile.afterRunRemoved (s₁.piles a) (chop (s₁.piles a).faceUp)
        else s₁.piles a')
    simp only [hpil]
  have hfw : ({ st.setFound c.suit (st.found c.suit ++ [c]) with
      piles := fun a' =>
        if a' = a then Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
        else st.piles a' } : State).found = s₂.found := by
    rw [hs₂]
    show (fun s' => if s' = c.suit then st.found c.suit ++ [c] else st.found s')
      = (fun s' => if s' = c.suit then s₁.found c.suit ++ [c] else s₁.found s')
    simp only [hfnd]
  have hzs2 : s₂.stock = s₁.stock := by rw [hs₂]; rfl
  have hzw2 : s₂.waste = s₁.waste := by rw [hs₂]; rfl
  have hzds2 : s₂.drawStep = s₁.drawStep := by rw [hs₂]; rfl
  have heq : w = s₂ := by
    apply State.ext
    · rw [hwf, hfw]
    · rw [hwp, hpw]
    · rw [hws, hzs2]
    · rw [hww, hzw2]
    · rw [hwd, hz3, hzds2]
      exact (EdgeKit.stepDraw_drawStep hd).symm
  exact hwfire.trans (congrArg Option.some heq)

/-- **The §1 square, `foundToTab` leg.** -/
private theorem square_foundToTab {st s₁ s₂ : State} {c : Card} {b : Base}
    (hd : st.stepDraw = some s₁) (hm : s₁.step (Move.foundToTab c b) = some s₂) :
    ∃ t, st.step (Move.foundToTab c b) = some t ∧ t.stepDraw = some s₂ := by
  obtain ⟨c', htop₁, hceq, hcp₁, hs₂⟩ := step_foundToTab_inv hm
  have hpil : st.piles = s₁.piles := (stepDraw_piles hd).symm
  have hfnd : st.found = s₁.found := (stepDraw_found hd).symm
  have htop : st.foundTop c.suit = some c := by
    rw [foundTop_congr c.suit hfnd, htop₁, hceq]
  have hcp : st.canPlace c b = true := by rw [canPlace_congr c b hpil]; exact hcp₁
  refine ⟨_, step_foundToTab_splice htop hcp, ?_⟩
  have hz1 : ((st.setFound c.suit (chop (st.found c.suit))).putCard c b).stock
      = st.stock := by rw [putCard_stock, setFound_stock]
  have hz2 : ((st.setFound c.suit (chop (st.found c.suit))).putCard c b).waste
      = st.waste := by rw [putCard_waste, setFound_waste]
  have hz3 : ((st.setFound c.suit (chop (st.found c.suit))).putCard c b).drawStep
      = st.drawStep := by rw [putCard_drawStep, setFound_drawStep]
  obtain ⟨w, hwfire, hwp, -, hwf, -, hwd, -, hws, hww⟩ :=
    stepDraw_rel hz1 hz2 hz3 hd
  have hsf : (st.setFound c.suit (chop (st.found c.suit))).piles
      = (s₁.setFound c.suit (chop (s₁.found c.suit))).piles := by
    show st.piles = s₁.piles
    exact hpil
  have hpw : ((st.setFound c.suit (chop (st.found c.suit))).putCard c b).piles
      = s₂.piles := by
    rw [hs₂]
    exact EdgeKit.putCard_piles_congr c b hsf
  have hfw : ((st.setFound c.suit (chop (st.found c.suit))).putCard c b).found
      = s₂.found := by
    rw [hs₂, putCard_found, putCard_found]
    show (fun s' => if s' = c.suit then chop (st.found c.suit) else st.found s')
      = (fun s' => if s' = c.suit then chop (s₁.found c.suit) else s₁.found s')
    simp only [hfnd]
  have hzs2 : s₂.stock = s₁.stock := by rw [hs₂, putCard_stock, setFound_stock]
  have hzw2 : s₂.waste = s₁.waste := by rw [hs₂, putCard_waste, setFound_waste]
  have hzds2 : s₂.drawStep = s₁.drawStep := by
    rw [hs₂, putCard_drawStep, setFound_drawStep]
  have heq : w = s₂ := by
    apply State.ext
    · rw [hwf, hfw]
    · rw [hwp, hpw]
    · rw [hws, hzs2]
    · rw [hww, hzw2]
    · rw [hwd, hz3, hzds2]
      exact (EdgeKit.stepDraw_drawStep hd).symm
  exact hwfire.trans (congrArg Option.some heq)

/-- **The §1 square, `tabToTab` leg.** -/
private theorem square_tabToTab {st s₁ s₂ : State} {c : Card} {b : Base}
    (hd : st.stepDraw = some s₁) (hm : s₁.step (Move.tabToTab c b) = some s₂) :
    ∃ t, st.step (Move.tabToTab c b) = some t ∧ t.stepDraw = some s₂ := by
  obtain ⟨a, hh₁, hcp₁, hfr₁, hs₂⟩ := step_tabToTab_inv hm
  have hpil : st.piles = s₁.piles := (stepDraw_piles hd).symm
  have hfnd : st.found = s₁.found := (stepDraw_found hd).symm
  have gh : st.pileHolding c = some a := by
    rw [← pileHolding_congr hpil.symm]
    exact hh₁
  have gc : st.canPlace c b = true := by rw [canPlace_congr c b hpil]; exact hcp₁
  have hfrun : fromCard c (st.piles a).faceUp = fromCard c (s₁.piles a).faceUp :=
    congrArg (fromCard c) (congrArg Pile.faceUp (congrFun hpil a))
  have hstep : st.step (Move.tabToTab c b) = some
      ((st.setPile a
        (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).putRun
        (fromCard c (st.piles a).faceUp) b) := by
    simp only [State.step, gh, gc]
    cases hwfr : fromCard c (st.piles a).faceUp with
    | nil =>
        rw [hfrun] at hwfr
        exact absurd hwfr hfr₁
    | cons x xs => rfl
  refine ⟨_, hstep, ?_⟩
  have hz1 : ((st.setPile a
      (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).putRun
      (fromCard c (st.piles a).faceUp) b).stock = st.stock := by
    rw [putRun_stock, setPile_stock]
  have hz2 : ((st.setPile a
      (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).putRun
      (fromCard c (st.piles a).faceUp) b).waste = st.waste := by
    rw [putRun_waste, setPile_waste]
  have hz3 : ((st.setPile a
      (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).putRun
      (fromCard c (st.piles a).faceUp) b).drawStep = st.drawStep := by
    rw [putRun_drawStep, setPile_drawStep]
  obtain ⟨w, hwfire, hwp, -, hwf, -, hwd, -, hws, hww⟩ :=
    stepDraw_rel hz1 hz2 hz3 hd
  have hsp : (st.setPile a
      (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles
      = (s₁.setPile a
      (Pile.afterRunRemoved (s₁.piles a) (below c (s₁.piles a).faceUp))).piles := by
    show (fun a' =>
        if a' = a then
            Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp)
          else st.piles a')
      = (fun a' =>
        if a' = a then
            Pile.afterRunRemoved (s₁.piles a) (below c (s₁.piles a).faceUp)
          else s₁.piles a')
    simp only [hpil]
  have hpw : ((st.setPile a
      (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).putRun
      (fromCard c (st.piles a).faceUp) b).piles = s₂.piles := by
    rw [hs₂, hfrun]
    exact EdgeKit.putRun_piles_congr _ _ hsp
  have hfw : ((st.setPile a
      (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).putRun
      (fromCard c (st.piles a).faceUp) b).found = s₂.found := by
    rw [hs₂, putRun_found, putRun_found, setPile_found, setPile_found]
    exact hfnd
  have hzs2 : s₂.stock = s₁.stock := by rw [hs₂, putRun_stock, setPile_stock]
  have hzw2 : s₂.waste = s₁.waste := by rw [hs₂, putRun_waste, setPile_waste]
  have hzds2 : s₂.drawStep = s₁.drawStep := by
    rw [hs₂, putRun_drawStep, setPile_drawStep]
  have heq : w = s₂ := by
    apply State.ext
    · rw [hwf, hfw]
    · rw [hwp, hpw]
    · rw [hws, hzs2]
    · rw [hww, hzw2]
    · rw [hwd, hz3, hzds2]
      exact (EdgeKit.stepDraw_drawStep hd).symm
  exact hwfire.trans (congrArg Option.some heq)

/-- **§1: the disjoint-field commutation lemma** (dispatched).  Any
witness leg at a drawn landing commutes with the drawing step: the
leg fires at the origin too, and the draw fires at the leg's
origin-landing with the drawn landing's own successor.  A draw leg
coincides with the pushed draw (the identical move); the waste
movers cannot be witness legs (the banked census
`journey_never_wasteToFound`/`journey_never_wasteToTab`); the three
board movers run the three squares above. -/
theorem board_draw_commute {st s₁ s₂ : State} {m : Move}
    (hd : st.stepDraw = some s₁)
    (hm : s₁.step m = some s₂) (hw : reversibleAtW s₁ m) :
    ∃ t, st.step m = some t ∧ t.stepDraw = some s₂ := by
  cases m with
  | draw => exact ⟨s₁, hd, hm⟩
  | wasteToFound c => exact absurd hw (journey_never_wasteToFound hm)
  | wasteToTab c b => exact absurd hw (journey_never_wasteToTab hm)
  | tabToFound c => exact square_tabToFound hd hm
  | foundToTab c b => exact square_foundToTab hd hm
  | tabToTab c b => exact square_tabToTab hd hm

/-! ## §2 The bubbling — every play permutes draws-last

Two grades land:

* the RUN grade proves fully: a successful waste-free play at the
  drawn landing re-runs wholesale at the drawing origin (the
  invariant walk: each board leg crosses its §1 square, a draw leg
  lands the frame-pair itself, the two dealers share one cycle
  count so both frames always fire), and the draw-last normal form
  follows by one induction;
* the WITNESS grade (the `ShufflePlayW`-preserving regroup) landed
  clean in `Orig/OrbitFactorC.lean` as `shuffle_drawsLast` (the
  erstwhile named residue `shuffle_split_drawsLastW` is retired
  from this chapter). -/

/-- **The run-level dual push** (the ⊥ of the edge-label chapter's
private `run_drawPush`): a successful waste-free play at the DRAWN
landing re-runs at the drawing origin, and the origin's landing
draws to the play's own landing — the frame invariant
`c.stepDraw = some c⁺` walks through every leg (board legs cross
the §1 squares, a draw leg lands the invariant's own pair), firing
included since both frames share one cycle count. -/
private theorem run_drawPull : ∀ (play : List Move) (s₁ x y : State),
    x.stepDraw = some s₁ → s₁.run play = some y →
    (∀ m ∈ play, EdgeKit.isWasteMove m = false) →
    ∃ y', x.run play = some y' ∧ y'.stepDraw = some y := by
  intro play
  induction play with
  | nil =>
      intro s₁ x y hd hrun _
      injection hrun with hy
      exact ⟨x, rfl, by rw [← hy]; exact hd⟩
  | cons m tail ih =>
      intro s₁ x y hd hrun hfree
      obtain ⟨t, hleg, hrest⟩ := State.run_cons hrun
      have hfreer : ∀ m' ∈ tail, EdgeKit.isWasteMove m' = false := by
        intro m' hm'
        exact hfree m' (List.mem_cons_of_mem _ hm')
      cases m with
      | draw =>
          have hedge : s₁.stepDraw = some t := hleg
          obtain ⟨y', hrun', hfire'⟩ :=
            ih t s₁ y hedge hrest hfreer
          refine ⟨y', ?_, hfire'⟩
          rw [EdgeKit.run_step_cons' (show State.step x Move.draw = some s₁ from hd)]
          exact hrun'
      | wasteToFound c =>
          have h0 : EdgeKit.isWasteMove (Move.wasteToFound c) = false :=
            hfree (Move.wasteToFound c) (by simp)
          exact absurd h0 (by simp [EdgeKit.isWasteMove])
      | wasteToTab c b =>
          have h0 : EdgeKit.isWasteMove (Move.wasteToTab c b) = false :=
            hfree (Move.wasteToTab c b) (by simp)
          exact absurd h0 (by simp [EdgeKit.isWasteMove])
      | tabToFound c =>
          obtain ⟨r', hpull, hedge⟩ := square_tabToFound hd hleg
          obtain ⟨y', hrun', hfire'⟩ := ih t r' y hedge hrest hfreer
          refine ⟨y', ?_, hfire'⟩
          rw [show x.run (Move.tabToFound c :: tail) = r'.run tail from
            EdgeKit.run_step_cons' hpull]
          exact hrun'
      | foundToTab c b =>
          obtain ⟨r', hpull, hedge⟩ := square_foundToTab hd hleg
          obtain ⟨y', hrun', hfire'⟩ := ih t r' y hedge hrest hfreer
          refine ⟨y', ?_, hfire'⟩
          rw [show x.run (Move.foundToTab c b :: tail) = r'.run tail from
            EdgeKit.run_step_cons' hpull]
          exact hrun'
      | tabToTab c b =>
          obtain ⟨r', hpull, hedge⟩ := square_tabToTab hd hleg
          obtain ⟨y', hrun', hfire'⟩ := ih t r' y hedge hrest hfreer
          refine ⟨y', ?_, hfire'⟩
          rw [show x.run (Move.tabToTab c b :: tail) = r'.run tail from
            EdgeKit.run_step_cons' hpull]
          exact hrun'

/-- **The run-grade draw-last regroup**: every successful waste-free
play factors as a draw-free front segment to a mid-state, then an
all-draw tail segment landing the original end. -/
private theorem run_split_drawsLast : ∀ (play : List Move) (x y : State),
    x.run play = some y → (∀ m ∈ play, EdgeKit.isWasteMove m = false) →
    ∃ B D z, (∀ m ∈ B, m ≠ Move.draw) ∧ (∀ m ∈ D, m = Move.draw) ∧
      x.run B = some z ∧ z.run D = some y := by
  intro play
  induction play with
  | nil =>
      intro x y hrun _
      injection hrun with hy
      subst hy
      exact ⟨[], [], x, by simp, by simp, rfl, rfl⟩
  | cons m tail ih =>
      intro x y hrun hfree
      obtain ⟨t, hleg, hrest⟩ := State.run_cons hrun
      have hfreer : ∀ m' ∈ tail, EdgeKit.isWasteMove m' = false := by
        intro m' hm'
        exact hfree m' (List.mem_cons_of_mem _ hm')
      cases m with
      | draw =>
          have hedge : x.stepDraw = some t := hleg
          obtain ⟨y', hpull, hfired⟩ :=
            run_drawPull tail t x y hedge hrest hfreer
          obtain ⟨B, D, z, hBnd, hDdr, hBz, hDz⟩ :=
            ih x y' hpull hfreer
          refine ⟨B, D ++ [Move.draw], z, hBnd, ?_, hBz, ?_⟩
          · intro m' hm'
            rcases List.mem_append.mp hm' with h1 | h2
            · exact hDdr m' h1
            · have : m' = Move.draw := (List.mem_singleton.mp h2)
              exact this
          · exact run_split D z y' [Move.draw] y hDz
              (run_one (show State.step y' Move.draw = some y from hfired))
      | wasteToFound c =>
          have h0 : EdgeKit.isWasteMove (Move.wasteToFound c) = false :=
            hfree (Move.wasteToFound c) (by simp)
          exact absurd h0 (by simp [EdgeKit.isWasteMove])
      | wasteToTab c b =>
          have h0 : EdgeKit.isWasteMove (Move.wasteToTab c b) = false :=
            hfree (Move.wasteToTab c b) (by simp)
          exact absurd h0 (by simp [EdgeKit.isWasteMove])
      | tabToFound c =>
          obtain ⟨B, D, z, hBnd, hDdr, hBz, hDz⟩ :=
            ih t y hrest hfreer
          refine ⟨Move.tabToFound c :: B, D, z, ?_, hDdr, ?_, hDz⟩
          · intro m' hm'
            cases List.mem_cons.mp hm' with
            | inl heq => intro hcon; rw [heq] at hcon; exact nomatch hcon
            | inr htl => exact hBnd m' htl
          · rw [show x.run (Move.tabToFound c :: B) = t.run B from
              EdgeKit.run_step_cons' hleg]
            exact hBz
      | foundToTab c b =>
          obtain ⟨B, D, z, hBnd, hDdr, hBz, hDz⟩ :=
            ih t y hrest hfreer
          refine ⟨Move.foundToTab c b :: B, D, z, ?_, hDdr, ?_, hDz⟩
          · intro m' hm'
            cases List.mem_cons.mp hm' with
            | inl heq => intro hcon; rw [heq] at hcon; exact nomatch hcon
            | inr htl => exact hBnd m' htl
          · rw [show x.run (Move.foundToTab c b :: B) = t.run B from
              EdgeKit.run_step_cons' hleg]
            exact hBz
      | tabToTab c b =>
          obtain ⟨B, D, z, hBnd, hDdr, hBz, hDz⟩ :=
            ih t y hrest hfreer
          refine ⟨Move.tabToTab c b :: B, D, z, ?_, hDdr, ?_, hDz⟩
          · intro m' hm'
            cases List.mem_cons.mp hm' with
            | inl heq => intro hcon; rw [heq] at hcon; exact nomatch hcon
            | inr htl => exact hBnd m' htl
          · rw [show x.run (Move.tabToTab c b :: B) = t.run B from
              EdgeKit.run_step_cons' hleg]
            exact hBz

/-- No reversible witness leg is a waste mover (the two universal
commitment rows, at the leg). -/
private theorem reversibleAtW_wasteFalse {st : State} {mm : Move}
    (hw : reversibleAtW st mm) : EdgeKit.isWasteMove mm = false := by
  obtain ⟨s₁, play, hstep, hrun⟩ := hw
  cases mm with
  | draw => rfl
  | wasteToFound c => exact absurd ⟨s₁, play, hstep, hrun⟩ (journey_never_wasteToFound hstep)
  | wasteToTab c b => exact absurd ⟨s₁, play, hstep, hrun⟩ (journey_never_wasteToTab hstep)
  | tabToFound c => rfl
  | foundToTab c b => rfl
  | tabToTab c b => rfl

/-- A witness journey's legs are never waste movers (each leg is
`reversibleAtW`, and the banked census rows kill the two waste
shapes). -/
private theorem shuffleW_wasteFree {x y : State} {play : List Move} :
    ShufflePlayW x play y → ∀ m ∈ play, EdgeKit.isWasteMove m = false := by
  intro h
  induction h with
  | nil s => intro m hm; cases hm
  | cons hw hstep hrest ih =>
      intro m' hm'
      rcases List.mem_cons.mp hm' with heq | htl
      · rw [heq]
        exact reversibleAtW_wasteFalse hw
      · exact ih m' htl

/-- **The run-grade regroup, read on a witness journey**: the
draw-last segments exist as legal runs.  (The witness-grade
leg-by-leg reconstruction is the named residue below.) -/
theorem shuffle_drawsLast_run {x y : State} {play : List Move}
    (h : ShufflePlayW x play y) :
    ∃ B D z, (∀ m ∈ B, m ≠ Move.draw) ∧ (∀ m ∈ D, m = Move.draw) ∧
      x.run B = some z ∧ z.run D = some y :=
  run_split_drawsLast play x y (ShufflePlayW_run h) (shuffleW_wasteFree h)

/-- **The draw-reversibility census is zone-determined**: a
reversible draw stays reversible at any state sharing its draw zone
(positive draw step, same stock/waste/draw step) — the alignment
facts the banked reversible rows read (in-phase with cards in
stock, `draw_reversible_inphaseW`; the pass base,
`draw_passBase_reversibleW`) mention the zone only, and the
off-phase shapes (`draw_irreversible_pristine`/`_offset`) are
excluded by the given witness.  This is the re-run machine for the
phase component of the factorization. -/
theorem draw_revW_congr {x x' : State} (hpos : 0 < x.drawStep)
    (hs : x.stock = x'.stock) (hw : x.waste = x'.waste)
    (hd : x.drawStep = x'.drawStep)
    (h : reversibleAtW x Move.draw) : reversibleAtW x' Move.draw := by
  obtain ⟨s₁, play, hstep, hrun⟩ := h
  cases hst : x.stock with
  | nil =>
      cases hws : x.waste with
      | nil =>
          exfalso
          have hdead : x.stepDraw = none := by
            rw [show x.stepDraw = State.dealStock (State.recycle x) from rfl,
              recycle_allEmpty x hst hws, dealStock_nil x hst]
          rw [show State.step x Move.draw = x.stepDraw from rfl, hdead] at hstep
          exact absurd hstep (by simp)
      | cons w ws =>
          have hxw' : x'.waste = w :: ws := by rw [← hw, hws]
          have hxs' : x'.stock = [] := by rw [← hs]; exact hst
          exact draw_passBase_reversibleW hxs'
            (by rw [hxw']; simp)
            (by rw [← hd]; exact hpos)
  | cons c cs =>
      have hst' : x'.stock ≠ [] := by
        intro hc
        rw [← hs] at hc
        rw [hst] at hc
        exact nomatch hc
      have hpos' : 0 < x'.drawStep := by rw [← hd]; exact hpos
      by_cases hpr : x.waste = []
      · rw [hpr] at hw
        exact absurd (draw_irreversible_pristine hpos
            (by intro hc; rw [hst] at hc; exact nomatch hc) hpr)
          (reversibleAt_of_W ⟨s₁, play, hstep, hrun⟩)
      · by_cases hres : x.waste.length % x.drawStep = 0
        · have hph : inPhase x = true := by
            rw [inPhase_eq_decide_of_cons hst, decide_eq_true hres]
          have hxw' : x'.waste ≠ [] := by
            intro hc
            exact hpr (by rw [hw]; exact hc)
          exact draw_reversible_inphaseW hpos' hst' hxw'
            (by rw [inPhase_congr hs.symm hw.symm hd.symm]; exact hph)
        · exact absurd (draw_irreversible_offset hpos
              (by intro hc; rw [hst] at hc; exact nomatch hc) hres)
            (reversibleAt_of_W ⟨s₁, play, hstep, hrun⟩)

/-- The frame-threading core of the transplant: proved by list
induction with BOTH frames generalized, so the successor pair of a
draw leg (`stepDraw_rel`) chains. -/
private theorem draw_play_transplant_aux : ∀ (x x' : State) (play : List Move)
    (y : State), ShufflePlayW x play y → (∀ m ∈ play, m = Move.draw) →
    0 < x.drawStep → x.stock = x'.stock → x.waste = x'.waste →
    x.drawStep = x'.drawStep →
    ∃ y', ShufflePlayW x' play y' ∧
      y'.stock = y.stock ∧ y'.waste = y.waste ∧ y'.drawStep = y.drawStep := by
  intro x x' play
  induction play generalizing x x' with
  | nil =>
      intro y hx hdraw hpos hst1 hst2 hst3
      cases hx
      exact ⟨x', ShufflePlayW.nil x', hst1.symm, hst2.symm, hst3.symm⟩
  | cons m rest ih =>
      intro y hx hdraw hpos hst1 hst2 hst3
      have hdrawer : ∀ m' ∈ rest, m' = Move.draw := fun m' hm' =>
        hdraw m' (List.mem_cons_of_mem _ hm')
      have hmd : m = Move.draw := hdraw m (by simp)
      subst hmd
      cases hx with
      | @cons _ _ mid _ _ hw hstep hrest =>
          have hb : x.stepDraw = some mid := hstep
          obtain ⟨mid', hfire', -, -, -, -, -, -, hz1, hz2⟩ :=
            stepDraw_rel hst1.symm hst2.symm hst3.symm hb
          have hleg : reversibleAtW x' Move.draw :=
            draw_revW_congr hpos hst1 hst2 hst3 hw
          have hdss : mid.drawStep = mid'.drawStep :=
            (EdgeKit.stepDraw_drawStep hb).trans (hst3.trans (EdgeKit.stepDraw_drawStep hfire').symm)
          obtain ⟨y'', hjrest, hz1', hz2', hdss'⟩ :=
            ih mid mid' y hrest hdrawer (by rw [EdgeKit.stepDraw_drawStep hb]; exact hpos)
              hz1.symm hz2.symm hdss
          exact ⟨y'', ShufflePlayW.cons hleg hfire' hjrest, hz1', hz2', hdss'⟩

/-- **Draws-only witness journeys transplant across board frames**:
a draws-only witness journey re-runs, legs still witnessed, at any
state sharing the draw zone.  Each leg fires by the field-determined
draw (`stepDraw_rel`), each leg's `reversibleAtW` re-instantiates
by the zone census (`draw_revW_congr`), and the landing shares the
original's zone while keeping the new frame's board (the pile-shift
machine the SWRotW reconciliation consumes: the phase component
runs equally at every board that shares its zone). -/
theorem draw_play_transplant {x y x' : State} {play : List Move}
    (h : ShufflePlayW x play y) (hdraw : ∀ m ∈ play, m = Move.draw)
    (hpos : 0 < x.drawStep)
    (hs : x.stock = x'.stock) (hw : x.waste = x'.waste) (hd : x.drawStep = x'.drawStep) :
    ∃ y', ShufflePlayW x' play y' ∧
      y'.stock = y.stock ∧ y'.waste = y.waste ∧ y'.drawStep = y.drawStep :=
  draw_play_transplant_aux x x' play y h hdraw hpos hs hw hd

/-! ## §3 The factorization theorem

Landed clean in `Orig/OrbitFactorC.lean` — `sameOrbit_factor_fwd`
(the → direction) and `sameOrbit_factor_full` (the biconditional,
built with `shuffle_drawsLast`; the ← glue, the four-witness
composition, is copied there so the canonical row carries no
`sorryAx` lineage).  The same-named skeleton rows formerly here
(the witness-grade bubbling `shuffle_split_drawsLastW`; the
factorization card `sameOrbit_factor`) are retired — superseded by
those proofs, unconsumed in the tree. -/

/-! ## §4 The quotient plumbing

`sameOrbitSetoid` owns `State`'s instance slot; the SW-phase setoid
below is a PLAIN `def`, never an instance. -/

/-- **The SW-phase setoid** — `SWComp` as a setoid, for the fiber
plumbing only.  NEVER an instance: `sameOrbitSetoid` owns `State`'s
setoid slot. -/
def swCompSetoid : Setoid State where
  r a b := SWComp a b
  iseqv := ⟨fun a => ⟨rfl, rfl⟩,
    fun h => ⟨h.1.symm, h.2.symm⟩,
    fun h1 h2 => ⟨h2.1.trans h1.1, h1.2.trans h2.2⟩⟩

/-- The SW phase quotient (scalar `def`; consumed through `mkSW`). -/
def SWPhase : Type := Quotient swCompSetoid

/-- The SW-phase projection. -/
def mkSW (s : State) : SWPhase := Quotient.mk swCompSetoid s

/-- A draw-free witness leg keeps the zone verbatim (waste legs are
never witness legs by the banked census; the draw leg is excluded
by hypothesis; each board leg's successor record leaves the zone
untouched). -/
private theorem leg_keep_zone {x y : State} {m : Move}
    (hw : reversibleAtW x m) (hstep : State.step x m = some y)
    (hnd : m ≠ Move.draw) :
    y.stock = x.stock ∧ y.waste = x.waste ∧ y.drawStep = x.drawStep := by
  cases m with
  | draw => exact absurd rfl hnd
  | wasteToFound c =>
      obtain ⟨s₁, play, hs₀, hr₀⟩ := hw
      exact absurd ⟨s₁, play, hs₀, hr₀⟩ (journey_never_wasteToFound hstep)
  | wasteToTab c b =>
      obtain ⟨s₁, play, hs₀, hr₀⟩ := hw
      exact absurd ⟨s₁, play, hs₀, hr₀⟩ (journey_never_wasteToTab hstep)
  | tabToFound c =>
      obtain ⟨hnex, a, hpo, hs₁⟩ := step_tabToFound_inv hstep
      rw [hs₁]
      exact ⟨rfl, rfl, rfl⟩
  | foundToTab c b =>
      obtain ⟨c₀, ht₀, hce, hcp, hs₁⟩ := step_foundToTab_inv hstep
      rw [hs₁]
      exact ⟨by rw [putCard_stock, setFound_stock],
        by rw [putCard_waste, setFound_waste],
        by rw [putCard_drawStep, setFound_drawStep]⟩
  | tabToTab c b =>
      obtain ⟨aa, hh, hcp, hfr, hs₁⟩ := step_tabToTab_inv hstep
      rw [hs₁]
      exact ⟨by rw [putRun_stock, setPile_stock],
        by rw [putRun_waste, setPile_waste],
        by rw [putRun_drawStep, setPile_drawStep]⟩

/-- A draw-free witness journey keeps the whole draw zone verbatim,
so both `SWComp` components are literally constant along it. -/
private theorem zone_keep_journey :
    ∀ {x : State} {play : List Move} {y : State},
    ShufflePlayW x play y → (∀ m ∈ play, m ≠ Move.draw) →
    y.stock = x.stock ∧ y.waste = x.waste ∧ y.drawStep = x.drawStep := by
  intro x play y h
  induction h with
  | nil s => intro _; exact ⟨rfl, rfl, rfl⟩
  | @cons st m s1 rest st' hw hstep hrest ih =>
      intro hnd
      obtain ⟨h1, h2, h3⟩ := leg_keep_zone hw hstep (hnd m (by simp))
      obtain ⟨h4, h5, h6⟩ := ih
        (fun m' hm' => hnd m' (List.mem_cons_of_mem _ hm'))
      exact ⟨h4.trans h1, h5.trans h2, h6.trans h3⟩

/-- **NoDraw journeys preserve the SW phase class**: every leg
keeps the zone verbatim, so the pool and phase line — the `SWComp`
pair — are constant and `mkSW` sees nothing. -/
theorem mkSW_invariant_board {x y : State} {play : List Move}
    (h : ShufflePlayW x play y) (hnd : ∀ m ∈ play, m ≠ Move.draw) :
    mkSW x = mkSW y := by
  obtain ⟨h1, h2, h3⟩ := zone_keep_journey h hnd
  have hz1 : drawPool y = drawPool x := by
    show y.stock.reverse ++ y.waste = x.stock.reverse ++ x.waste
    rw [h1, h2]
  apply Quotient.sound
  exact ⟨hz1, inPhase_congr h1.symm h2.symm h3.symm⟩

/-- **The same-orbit fiber claim**: same-orbit members share one SW
phase class — the banked SWComp residue (`swComp_of_orbit`) is
exactly the setoid relation, so `mkSW` factors through the macro
state.  The `u.WF` gate is `swComp_of_orbit`'s. -/
theorem orbit_in_SWPhase_fiber {u v : State} (hwf : u.WF)
    (h : sameOrbitSetoid.r u v) : mkSW u = mkSW v :=
  Quotient.sound (swComp_of_orbit hwf h)

#print axioms board_draw_commute
#print axioms run_drawPull
#print axioms run_split_drawsLast
#print axioms shuffle_drawsLast_run
#print axioms draw_revW_congr
#print axioms draw_play_transplant
#print axioms mkSW_invariant_board
#print axioms orbit_in_SWPhase_fiber
