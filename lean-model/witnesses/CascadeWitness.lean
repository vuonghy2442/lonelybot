import Klondike.Dominance
import Klondike.Initial

/-!
# The cascade witness (2026-09-13)

`cascade_sound` as staged — the escape clause is `dominantAt st₁ m`
alone — is FALSE.  `State.applyDraw` is unconditionally `some`, and on
an exhausted stock `Cycle.dealOnce` is the identity (`cursor ≥ length`
wraps to `0`, and `0 ≥ 0`), so `draw` is *trivially dominant* at every
state: the successor is the state itself, and a state reaches itself.
The hypothesis therefore holds for the draw-only filter at EVERY
reachable solvable state, while no all-draw play can ever win (draws
never touch `heights`, and `isWin` is `heights` alone).

State `stW`: standard deal, ♦K alone on pile 0's anchor (kings sit free
on anchors — a `board_edges`-clean edge), ♠/♥/♣ foundations complete
and ♦ at 12, stock exhausted at cursor 0.  It is WF (all eleven
conjuncts, `stW_wf` below — so adding a bare `hwf` does not repair),
solvable (one `pileStack ♦K` from the win), and *frozen* under `Pdraw`
(every P-play is the identity run to `stW`, which is not a win).

The same hole yawns for any reversible non-commit: `pilePile` (kings
between free anchors) and worry-back `stackPile` (with
`stackPile_pileStack_cancel`) are dominant by invertibility and make
no progress.  `dominantAt` carries no termination content — the
progress measure must be hypothesized (the repair: the escape must
strictly decrease `cascadeMeasure`).

HISTORICAL after the repair (2026-09-13, same session): the
`cascade_refuted` corollary cites the pre-repair statement; the core
facts (`stW_wf`, `stW_solvable`, `h_W`, `stW_notSolvableWith`) cite no
sorry'd constant and stay green.
-/

/-- The king of diamonds — the one card still out. -/
def dK : Card := ⟨Suit.diamond, Rank.king⟩

/-- One edge: ♦K seated on pile 0's anchor. -/
def bdW : Board := (Board.empty.attach (Sum.inl Anchor.p0) dK).getD Board.empty

theorem bdW_attach : Board.empty.attach (Sum.inl Anchor.p0) dK = some bdW := by
  have hne : Board.empty.attach (Sum.inl Anchor.p0) dK ≠ none :=
    (Board.attach_eq_some_iff _ _ _).mpr ⟨Board.empty_topOf _, Board.empty_bottomOf _⟩
  cases hh : Board.empty.attach (Sum.inl Anchor.p0) dK with
  | none => rw [hh] at hne; exact absurd hne (by simp)
  | some bd =>
      have hbd : bdW = bd := by
        show (Board.empty.attach (Sum.inl Anchor.p0) dK).getD Board.empty = bd
        rw [hh]
        rfl
      rw [hbd]

theorem bdW_topOf_p0 : bdW.topOf (Sum.inl Anchor.p0) = some dK :=
  Board.attach_topOf _ _ _ bdW_attach

theorem bdW_topOf_ne (b : Base) (h : b ≠ Sum.inl Anchor.p0) : bdW.topOf b = none :=
  (Board.attach_topOf_ne _ _ _ bdW_attach h).trans (Board.empty_topOf b)

theorem bdW_bottomOf_dK : bdW.bottomOf dK = some (Sum.inl Anchor.p0) :=
  (Board.bottomOf_eq _ _ _).mpr bdW_topOf_p0

/-- The board's only edge: every top sits at pile 0 and is ♦K. -/
theorem bdW_topOf_cases (b : Base) (c : Card) (hb : bdW.topOf b = some c) :
    b = Sum.inl Anchor.p0 ∧ c = dK := by
  by_cases hbp : b = Sum.inl Anchor.p0
  · subst hbp
    rw [bdW_topOf_p0] at hb
    exact ⟨rfl, (Option.some.inj hb).symm⟩
  · rw [bdW_topOf_ne b hbp] at hb; simp at hb

/-- The trap state: standard deal, ♦K alone on pile 0, ♠/♥/♣ complete
and ♦ at 12, stock exhausted at cursor 0, draw step 1. -/
def stW : State where
  deal := Deal.standard
  board := bdW
  heights := fun s => if s = Suit.diamond then 12 else 13
  depths := fun _ => 0
  stock := ⟨[], 0⟩
  drawStep := 1

/-- The draw-only filter: the generator keeps only `.draw`. -/
def Pdraw : Move → Bool
  | .draw => true
  | _ => false

-- Refute-first probes: the trap is real.
#eval stW.isWin                                -- false
#eval (stW.apply (Move.pileStack dK)).isSome   -- true (the only way out)
#eval (stW.apply Move.draw).isSome             -- true (the identity)

/-- The winning successor: ♦K stacked, ♦ at 13 — all four complete. -/
def stWin : State := { stW with
  board := bdW.detach (Sum.inl Anchor.p0),
  heights := fun s => if s = dK.suit then stW.heights s + 1 else stW.heights s }

theorem stW_pileStack : stW.apply (Move.pileStack dK) = some stWin := by
  rw [apply_pileStack_iff]
  exact ⟨bdW_topOf_ne _ (by simp), Sum.inl Anchor.p0, bdW_bottomOf_dK, rfl, rfl⟩

theorem stWin_isWin : stWin.isWin = true := by decide

theorem stW_solvable : stW.solvableFrom := by
  refine ⟨[Move.pileStack dK], stWin, ?_, stWin_isWin⟩
  show (match stW.apply (Move.pileStack dK) with
      | some s => s.run [] | none => none) = some stWin
  rw [stW_pileStack]
  rfl

/-! ## The stock invariant: from `stW` the cycle stays empty -/

/-- On an empty cycle at cursor 0, `draw` is the identity. -/
theorem draw_id (s : State) (hst : s.stock = ⟨[], 0⟩) : s.apply Move.draw = some s := by
  have hdd : s.stock.dealOnce s.drawStep = ⟨[], 0⟩ := by rw [hst]; rfl
  show some {s with stock := s.stock.dealOnce s.drawStep} = some s
  rw [hdd, ← hst]

/-- Any successful move from an empty-cycle state leaves the cycle
empty (the deck moves die on `prev = none`; everything else keeps the
stock field verbatim). -/
theorem stock_inv_step (m : Move) (s s' : State) (hst : s.stock = ⟨[], 0⟩)
    (hap : s.apply m = some s') : s'.stock = ⟨[], 0⟩ := by
  have hprev : s.stock.prev = none := by rw [hst]; rfl
  cases m with
  | draw =>
      rw [draw_id s hst] at hap
      rw [← Option.some.inj hap]
      exact hst
  | reveal c =>
      obtain ⟨-, r, a, bd, -, -, -, hs⟩ := (apply_reveal_iff (st := s) (st' := s')).mp hap
      rw [hs]
      exact hst
  | deckPile c b =>
      obtain ⟨hp, -, -, -, -⟩ := (apply_deckPile_iff (st := s) (st' := s')).mp hap
      rw [hprev] at hp; simp at hp
  | deckStack c =>
      obtain ⟨hp, -, -⟩ := (apply_deckStack_iff (st := s) (st' := s')).mp hap
      rw [hprev] at hp; simp at hp
  | pileStack c =>
      obtain ⟨-, b, -, -, hs⟩ := (apply_pileStack_iff (st := s) (st' := s')).mp hap
      rw [hs]
      exact hst
  | stackPile c b =>
      obtain ⟨-, -, bd, -, hs⟩ := (apply_stackPile_iff (st := s) (st' := s')).mp hap
      rw [hs]
      exact hst
  | pilePile c b =>
      obtain ⟨b₀, -, -, -, bd, -, hs⟩ := (apply_pilePile_iff (st := s) (st' := s')).mp hap
      rw [hs]
      exact hst

theorem stock_inv (play : List Move) : ∀ (s₀ s : State), s₀.stock = ⟨[], 0⟩ →
    s₀.run play = some s → s.stock = ⟨[], 0⟩ := by
  induction play with
  | nil =>
      intro s₀ s hst h
      simp only [State.run] at h
      rw [← Option.some.inj h]
      exact hst
  | cons m rest ih =>
      intro s₀ s hst h
      obtain ⟨s', hap, hrest, -⟩ := run_cons_inv h
      exact ih s' s (stock_inv_step m s₀ s' hst hap) hrest

theorem stW_reach_stock (play : List Move) (s : State) (h : stW.run play = some s) :
    s.stock = ⟨[], 0⟩ := stock_inv play stW s rfl h

/-! ## The staged hypothesis holds — vacuously, via the identity draw -/

theorem h_W : ∀ (s : State) (play : List Move), stW.run play = some s → s.solvableFrom →
    s.isWin = true ∨ ∃ m, Pdraw m = true ∧ s.legal m = true ∧ dominantAt s m := by
  intro s play hrun hsolv
  refine Or.inr ⟨Move.draw, rfl, ?_, ?_⟩
  · show (s.apply Move.draw).isSome = true
    rw [draw_id s (stW_reach_stock play s hrun)]
    rfl
  · intro hsolv'
    exact ⟨s, draw_id s (stW_reach_stock play s hrun), hsolv'⟩

/-! ## But no P-play wins -/

theorem stW_notWin : stW.isWin = false := by decide

theorem Pdraw_draw : ∀ {m : Move}, Pdraw m = true → m = Move.draw := by
  intro m
  cases m with
  | draw => intro _; rfl
  | reveal c => intro h; simp [Pdraw] at h
  | deckPile c b => intro h; simp [Pdraw] at h
  | deckStack c => intro h; simp [Pdraw] at h
  | pileStack c => intro h; simp [Pdraw] at h
  | stackPile c b => intro h; simp [Pdraw] at h
  | pilePile c b => intro h; simp [Pdraw] at h

/-- Every P-play is the identity run: `stW`, forever. -/
theorem draw_run : ∀ (play : List Move), (∀ m ∈ play, Pdraw m = true) →
    stW.run play = some stW := by
  intro play
  induction play with
  | nil => intro _; rfl
  | cons m rest ih =>
      intro hall
      have hm : m = Move.draw := Pdraw_draw (hall m (by simp))
      rw [hm]
      show (match stW.apply Move.draw with
        | some s => s.run rest | none => none) = some stW
      rw [draw_id stW rfl]
      exact ih (fun m' hm' => hall m' (List.mem_cons.mpr (Or.inr hm')))

theorem stW_notSolvableWith : ¬ stW.solvableWith Pdraw := by
  intro hsw
  obtain ⟨play, hall, st', hrun, hwin⟩ := hsw
  rw [draw_run play hall] at hrun
  rw [← Option.some.inj hrun] at hwin
  rw [stW_notWin] at hwin
  exact Bool.noConfusion hwin

/-! ## The staged statement refuted (pre-repair) -/

theorem cascade_refuted : False :=
  stW_notSolvableWith (cascade_sound (P := Pdraw) stW h_W stW_solvable)

/-! ## The trap survives WF — a bare `hwf` is not a repair -/

theorem stW_wf : stW.WF := by
  refine ⟨Deal.ofList_wf Card.universe_length universe_noDup, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro a
    exact Nat.zero_le _
  · intro b c hb
    refine ⟨(Board.bottomOf_eq _ _ _).mpr hb, ?_⟩
    obtain ⟨hbp, hcd⟩ := bdW_topOf_cases b c hb
    subst hbp
    subst hcd
    exact Or.inl rfl
  · intro c _
    exact rfl
  · intro c _
    exact rfl
  · intro c hc
    have hne : c ≠ dK := by
      intro hcon
      rw [hcon] at hc
      exact absurd hc (Nat.lt_irrefl 12)
    refine ⟨?_, rfl, ?_⟩
    · have hbn : bdW.bottomOf c = none :=
        (Board.bottomOf_eq_none _ c).mpr (fun b hb => by
          obtain ⟨-, hcd⟩ := bdW_topOf_cases b c hb
          exact hne hcd)
      show (bdW.bottomOf c).isSome = false
      rw [hbn]
      rfl
    · intro a hcm
      have h' : c ∈ ([] : List Card) := hcm
      exact nomatch h'
  · intro c _ a hcm
    have h' : c ∈ ([] : List Card) := hcm
    exact nomatch h'
  · intro s
    show (if s = Suit.diamond then 12 else 13) ≤ 13
    by_cases hsd : s = Suit.diamond
    · rw [if_pos hsd]; omega
    · rw [if_neg hsd]; omega
  · exact Nat.zero_le _
  · exact Nat.zero_lt_one
  · refine ⟨?_, ?_⟩
    · intro i j hi _ _
      have h0 : stW.stock.cards.length = 0 := rfl
      omega
    · intro c hc
      have h' : c ∈ ([] : List Card) := hc
      exact nomatch h'