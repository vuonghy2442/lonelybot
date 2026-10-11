import Orig.EdgeLabel
import Orig.TwinExchangeQuotient
import Orig.Dominance

/-!
# Orig.MacroInternal — the structured macro class (STATEMENT SKELETON)

The investigation skeleton for the 2026-10-11 program: the macro class
as a structured space.  Banked carriers are used by their real names;
every theorem is `sorry`-stated so each row can be opened and attacked
independently; docstrings name each row's payers.

The layer map (the four-coordinate decomposition):

* arm     — which fork wing saturates (read off the founded content);
            joined across the class by the NECK (pull · slide · re-raise)
* wiggle  — where parked never-stackable content sits; joined by SLIDES
* torsor  — identity bits on seated twin pairs; joined by EXCHANGES
* depth   — de-saturation distance and pull seatings; joined by the CONE

The selector reads the coordinates (`canonKey` over `canusOf`); the main
goal is `canonV3_iff`.  The heavy payers: the envelope row (`mem_macro_iff`,
decompression card) and `saturated_classification` (the exotic census).
-/

open Classical

/-! ## Sanity battery: the banked names this skeleton stands on. -/

#check @CanRaise            -- the licensed-raise predicate
#check @Final               -- ∀ c, ¬ CanRaise st c
#check @StackRun            -- the saturating-run relation
#check @canon
#check @canon_unique
#check @canon_in_class
#check @reversibleAtW
#check @sameOrbitSetoid
#check @SameOrbit
#check @ExchStep
#check @ExchChain
#check @Move.foundToTab
#check @Move.tabToTab
#check @Card.twin

/-! ## §1. Membership and the ceiling vocabulary
(The definitional face sits on membership alone; the cone is only the engine.) -/

/-- Membership in a macro class. -/
def classOf (C : SameOrbit) (w : State) : Prop :=
  Quotient.mk sameOrbitSetoid w = C

/-- The current founded count of a suit — the rung. -/
def rungAt (w : State) (s : Suit) : Nat := (w.found s).length

/-- Suits of one color ('twin' suits). -/
def twinSuit (s₁ s₂ : Suit) : Prop := s₁ = s₂ ∨ s₁ = s₂.twin



/-- **The direct class-grade**: some member has `c` AT-RUNG
(next-in-line).  One existential — no folds, no lifts, no carrier at
the definitional level. -/
def atRungInClass (C : SameOrbit) (c : Card) : Prop :=
  ∃ st, classOf C st ∧ rungAt st c.suit = c.rank.toIdx

/-- **SatStackable — the eventual-stackability grade, direct by ∃**:
some state in the macro state has the card STACKED (founded on its
suit's foundation).  One existential — no ceiling arithmetic, no
folds, no lifts. -/
def satStackable (C : SameOrbit) (c : Card) : Prop :=
  ∃ st, classOf C st ∧ c ∈ st.found c.suit

/-- Stranded: never even ready (below every ceiling the class reaches). -/
def strandedInClass (C : SameOrbit) (c : Card) : Prop := ¬ atRungInClass C c

/-- **The ceiling population** — ready-forever, never founded: covered
twins at Finals, buried stranded kings; the obstruction inventory's
positional blockage, now a first-class grade. -/
def pendingForever (C : SameOrbit) (c : Card) : Prop :=
  atRungInClass C c ∧ ¬ satStackable C c

/-- **SurelyStackable** (the universal grade): at EVERY Final member of
the macro state the card is already stacked — stackedness holds at
every saturation arm.  The sat/surely GAP is arm-contingency, and
localizes the fork exactly. -/
def surelyStackable (C : SameOrbit) (c : Card) : Prop :=
  ∀ st, classOf C st → Final st → c ∈ st.found c.suit

/-! ## §1.5 The floor rows' engine battery
(Private, self-contained on the banked carrier: the witness-loop
bridge — one reversible leg lands inside the macro class — and the
per-move rung locality: which suit's foundation a move writes.) -/

/-- The loop-closure engine: a play from `x` landing at `w`, spliced
with ANY play back from `w` to `x`, is a witness shuffle `x → w` —
for every interior leg, the loop remainder (suffix, anchor-back,
front) is an explicit returning play, so each leg carries its own
`reversibleAtW`.  Pure run-splice arithmetic; no state physics. -/
private theorem shuffleW_of_round : ∀ (σ : List Move) (x w : State),
    x.run σ = some w → ∀ ρ : List Move, w.run ρ = some x →
      ShufflePlayW x σ w := by
  intro σ
  induction σ with
  | nil =>
      intro x w hσ ρ hρ
      have hxw : some x = some w := hσ
      injection hxw with hx
      rw [hx]
      exact .nil w
  | cons p rest ih =>
      intro x w hσ ρ hρ
      obtain ⟨y, hp, hrest⟩ := State.run_cons hσ
      refine .cons ⟨y, rest ++ ρ, hp, run_split rest y w ρ x hrest hρ⟩ hp ?_
      exact ih y w hrest (ρ ++ [p]) (run_split ρ w x [p] y hρ (run_one hp))

/-- One reversible leg stays inside the macro class: the firing's own
witness gives the both-directions shuffle pair — the σ side is the
single move itself, the τ side is the loop-closure of the return
play, and the setoid's `r` IS that pair (the reversed-argument
orientation).  This is the per-leg heart of `cone_inClass` and
`dance_inClass` below. -/
private theorem class_leg {st s₁ : State} {m : Move}
    (hrev : reversibleAtW st m) (hstep : State.step st m = some s₁) :
    sameOrbitSetoid.r st s₁ := by
  obtain ⟨s₁', play, hstep', hrun⟩ := hrev
  have hs : s₁' = s₁ := Option.some.inj (hstep'.symm.trans hstep)
  rw [hs] at hrun
  show RevEqW s₁ st
  exact ⟨play, shuffleW_of_round play s₁ st hrun [m] (run_one hstep),
    [m], .cons ⟨s₁, play, hstep, hrun⟩ hstep (.nil s₁)⟩

/-- Class-membership transitivity, through the rev-closure's own
transitivity (the setoid's reversed-argument orientation, one
argument-swap). -/
private theorem class_trans {a b c : State}
    (h₁ : sameOrbitSetoid.r a b) (h₂ : sameOrbitSetoid.r b c) :
    sameOrbitSetoid.r a c :=
  RevEqW_trans h₂ h₁

/-- A run relocation never writes the foundations: all rungs level
(the stock/waste legs of the same story are `step_draw_rungs`; the
giveback and the raise are the two one-rung writers). -/
private theorem step_tabToTab_rungs {st st' : State} {c : Card} {b : Base}
    (hstep : State.step st (Move.tabToTab c b) = some st') :
    ∀ s, rungAt st' s = rungAt st s := by
  obtain ⟨a, -, -, -, hs⟩ := step_tabToTab_inv hstep
  intro s
  show (st'.found s).length = (st.found s).length
  rw [hs, putRun_found (st.setPile a
    (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp)))
    (fromCard c (st.piles a).faceUp) b]
  rfl

/-- A draw never writes the foundations: all rungs level (the canlaw
satStep locality row territory, here as the direct step-level fact of
the banked draw readers). -/
private theorem step_draw_rungs {st st' : State}
    (hstep : st.step .draw = some st') :
    ∀ s, rungAt st' s = rungAt st s := by
  intro s
  have hd : st.stepDraw = some st' := hstep
  show (st'.found s).length = (st.found s).length
  rw [stepDraw_found hd]

/-- A licensed raise writes exactly one rung: its suit up one, all
other rungs level (rides the banked `tabToFound_found_trio`). -/
private theorem step_tabToFound_rungs {st st' : State} {c : Card}
    (hstep : State.step st (Move.tabToFound c) = some st') :
    rungAt st' c.suit = rungAt st c.suit + 1 ∧
      ∀ s, s ≠ c.suit → rungAt st' s = rungAt st s := by
  obtain ⟨-, a, -, hs⟩ := step_tabToFound_inv hstep
  obtain ⟨hself, hothers, -⟩ := tabToFound_found_trio (a := a) hs
  refine ⟨?_, ?_⟩
  · show (st'.found c.suit).length = (st.found c.suit).length + 1
    rw [hself, List.length_append]
    have h1 : ([c] : List Card).length = 1 := rfl
    omega
  · intro s hs2
    show (st'.found s).length = (st.found s).length
    rw [hothers s hs2]

/-- A foundation giveback writes exactly one rung: its suit down one,
all other rungs level. -/
private theorem step_foundToTab_rungs {st st' : State} {c : Card} {b : Base}
    (hstep : State.step st (Move.foundToTab c b) = some st') :
    rungAt st' c.suit + 1 = rungAt st c.suit ∧
      ∀ s, s ≠ c.suit → rungAt st' s = rungAt st s := by
  obtain ⟨c', htop, hceq, hcp, hs⟩ := step_foundToTab_inv hstep
  rw [hceq] at htop
  have hlast : lastOf (st.found c.suit) = some c := htop
  have hsnoc : st.found c.suit = chop (st.found c.suit) ++ [c] :=
    lastOf_chop hlast
  have hlen : (st.found c.suit).length = (chop (st.found c.suit)).length + 1 := by
    have h : (chop (st.found c.suit) ++ [c] : List Card).length =
        (chop (st.found c.suit)).length + ([c] : List Card).length := List.length_append
    rw [← hsnoc] at h
    have h1 : ([c] : List Card).length = 1 := rfl
    omega
  refine ⟨?_, ?_⟩
  · show (st'.found c.suit).length + 1 = (st.found c.suit).length
    rw [hs]
    have hself' : (((st.setFound c.suit (chop (st.found c.suit))).putCard c b).found)
        c.suit = chop (st.found c.suit) := by
      rw [putCard_found, setFound_found_self]
    rw [hself']
    omega
  · intro s hs2
    show (st'.found s).length = (st.found s).length
    rw [hs]
    have hothers' : (((st.setFound c.suit (chop (st.found c.suit))).putCard c b).found)
        s = st.found s := by
      rw [putCard_found, setFound_found_ne hs2]
    rw [hothers']

/-! ## §2. Calibration rows -/

/-- **Stackable-now implies rung-exact** — the rank-encoding
calibration (CALIBRATION NOTE, the adjustment the card authorizes for
this row): the 0-based `toIdx` encoding matches `foundHeight`
EXACTLY — no offset adjustment is needed, because `nextUp` is
literally `decide (rank.toIdx = foundHeight)` (Orig/State.lean:379)
and the license opens with it.  The skeleton's iff-face is
unprovable in the reverse direction and was calibrated to the
one-directional read: a card AT the rung may sit buried, stocked, or
wasted, so the license's seat legs (`pileOfTop`, the refillable
base) are not implied by rung-exactness alone.  Every consumer pins
the rung FROM the license (the fork dossier's bare-pin walks exactly
this way), and the `WF` premise was dropped: the license's nextUp
leg is rank-exact at every state, well-formed or not. -/
theorem stackable_now_rungexact (st : State) (c : Card) :
    CanRaise st c → rungAt st c.suit = c.rank.toIdx := by
  intro h
  obtain ⟨hn, -, -⟩ := h
  have h2 : c.rank.toIdx = st.foundHeight c.suit := of_decide_eq_true hn
  show (st.found c.suit).length = c.rank.toIdx
  exact h2.symm

/-- The saturation step never lowers a rung: it either holds or raises
exactly one suit by one (`raise_foundHeight`). -/
private theorem satStep_rung_mono (st : State) (s : Suit) :
    rungAt st s ≤ rungAt (satStep st) s := by
  cases hp : pick st with
  | none =>
      have h : satStep st = st := satStep_none hp
      rw [h]
      exact Nat.le_refl _
  | some c =>
      obtain ⟨s', hr⟩ := raise_eq_some_of_canRaise st (pick_some_canRaise hp)
      have hsat : satStep st = s' := satStep_some hp hr
      have hstep : State.step st (Move.tabToFound c) = some s' := hr
      obtain ⟨-, hF⟩ := raise_foundTransport hstep
      obtain ⟨hself, hothers⟩ := raise_foundHeight hF
      rw [hsat]
      by_cases hsc : s = c.suit
      · subst hsc
        have h1 : rungAt st c.suit = st.foundHeight c.suit := rfl
        have h2 : rungAt s' c.suit = s'.foundHeight c.suit := rfl
        omega
      · have h1 := hothers s hsc
        have h2 : rungAt s' s = s'.foundHeight s := rfl
        have h3 : rungAt st s = st.foundHeight s := rfl
        omega

/-- The saturator at any budget never lowers a rung (induction along
the `canonAux` recursion, `satStep_rung_mono` composed). -/
private theorem canonAux_rung_mono (n : Nat) (st : State) (s : Suit) :
    rungAt st s ≤ rungAt (canonAux n st) s := by
  induction n generalizing st with
  | zero => exact Nat.le_refl _
  | succ m ih =>
      rw [canonAux_succ]
      exact Nat.le_trans (satStep_rung_mono st s) (ih (satStep st))

/-- Saturation only raises: the canonical form dominates the rungs. -/
theorem canon_rung_mono (st : State) (s : Suit) (hwf : st.WF) :
    rungAt st s ≤ rungAt (canon st) s :=
  canonAux_rung_mono 53 st s

/-- The three grades partition every card — sorry-free: a case split.
stranded (never even ready) / pending-forever (ready, never founded) /
founded. -/
theorem grade_partition (C : SameOrbit) (c : Card) :
    strandedInClass C c ∨ pendingForever C c ∨ satStackable C c := by
  by_cases hf : satStackable C c
  · exact Or.inr (Or.inr hf)
  · by_cases ha : atRungInClass C c
    · exact Or.inr (Or.inl ⟨ha, hf⟩)
    · exact Or.inl ha

/-- Founding implies at-rung somewhere: pull the founded cards back
down (cone legs stay in class) and the pulled state sits at the rung —
the walk property, ∃-grade.

BLOCKED (this row, floor-card escape hatch): the pops-backward walk
needs more than this file's battery carries.  What is missing is the
LANDING-EXISTENCE leg of the walk: to pop a foundation top at an
intermediate state, the popped card must land legally somewhere
(a rank-adjacent opposite-color pile top, or an empty seat for a
king), and a WF member may offer NEITHER — the landing host cards can
sit buried in hidden lists or in the stock, and the walk must first
shuffle them free, which is precisely the neck/envelope content owned
by the decompression card (`mem_macro_iff`, every member a
conj-of-a-cone-element of the canon).  The founding read-backward is
envelope-grade; per the card ("route via canon or via the pull letter;
if it needs the envelope, leave BLOCKED-noted") this row stays sorry'd
here rather than forced.  The honest partial content this side DOES
own (and the walk will consume): every reversible pop of a foundation
top at a WF state is a cone pull whose round trip is one move
(foundToTab then tabToFound back onto the historic seat — both
under-seat and bare-king shapes, the Classify witness constructors),
and the rung arithmetic of that pop is `step_foundToTab_rungs` in the
battery. -/
theorem founded_implies_atRung (C : SameOrbit) (c : Card) :
    satStackable C c → atRungInClass C c := by
  sorry

/-! ## §3. The cone: the three reversible padding letters -/

/-- One reversible cone leg: a pull, a noreveal slide, or a pure draw —
each carrying its witnessed reversibility.  The letters cannot stand
in for one another (pulls besides their pop never touch `found`-content
seating, slides never relocate identities, draws never touch the board). -/
inductive ConeStep : State → State → Prop
  | pull {st st' : State} (c : Card) (b : Base)
      (hstep : st.step (.foundToTab c b) = some st')
      (hrev : reversibleAtW st (.foundToTab c b)) : ConeStep st st'
  | slide {st st' : State} (c : Card) (b : Base)
      (hstep : st.step (.tabToTab c b) = some st')
      (hrev : reversibleAtW st (.tabToTab c b)) : ConeStep st st'
  | draw {st st' : State}
      (hstep : st.step .draw = some st')
      (hrev : reversibleAtW st .draw) : ConeStep st st'

/-- The cone from an anchor: reflexive-transitive closure of the legs. -/
inductive ConePath : State → State → Prop
  | refl (w : State) : ConePath w w
  | cons {w u u' : State} (h : ConeStep w u) (t : ConePath u u') : ConePath w u'

/-- Every cone leg is a reversible leg: the constructor's own
`reversibleAtW` witnesses feed `class_leg`. -/
private theorem ConeStep_class {w u : State} (h : ConeStep w u) :
    sameOrbitSetoid.r w u := by
  cases h with
  | pull c b hstep hrev => exact class_leg hrev hstep
  | slide c b hstep hrev => exact class_leg hrev hstep
  | draw hstep hrev => exact class_leg hrev hstep

/-- Cone legs stay in class: each carries its witness round trip, and
the loop-closure engine turns it into the both-directions shuffle
pair (the leg-level home is `class_leg`; the path composes by the
rev-closure's own transitivity). -/
theorem cone_inClass (w u : State) (hwf : w.WF) (h : ConePath w u) :
    sameOrbitSetoid.r w u := by
  clear hwf
  induction h with
  | refl x => exact RevEqW_refl x
  | cons hleg _t ih => exact class_trans (ConeStep_class hleg) ih

/-! ### The inter-fiber moves -/

/-- **The per-move rung semantics of the cone letters** (row named by
the floor card; `cone_step_fiber` and `dance_step_grading` both ride
it): a cone leg is FLAT — slide or draw, all rungs level (the
foundations are never touched) — or DOWN exactly one rung of exactly
one suit: a pull pops exactly one founded top (its suit −1, all else
verbatim).  Case analysis on the constructors; the reader homes are
the battery's `step_tabToTab_rungs`, `step_draw_rungs` and
`step_foundToTab_rungs`. -/
theorem cone_step_heights {st st' : State} (h : ConeStep st st') :
    (∀ s : Suit, rungAt st' s = rungAt st s) ∨
    (∃ s₀ : Suit, rungAt st' s₀ + 1 = rungAt st s₀ ∧
      ∀ s : Suit, s ≠ s₀ → rungAt st' s = rungAt st s) := by
  cases h with
  | pull c b hstep _hrev =>
      obtain ⟨h1, h2⟩ := step_foundToTab_rungs hstep
      exact Or.inr ⟨c.suit, h1, h2⟩
  | slide c b hstep _hrev => exact Or.inl (step_tabToTab_rungs hstep)
  | draw hstep _hrev => exact Or.inl (step_draw_rungs hstep)

/-- One dance leg: any reversible single move.  Adds the raising
direction (licensed `tabToFound`, carrying its V2 undo) to the cone
letters.  Waste moves and reveals were never here by construction. -/
inductive DanceStep : State → State → Prop
  | cone {w u : State} (h : ConeStep w u) : DanceStep w u
  | raise {w u : State} (c : Card)
      (hstep : w.step (.tabToFound c) = some u)
      (hrev : reversibleAtW w (.tabToFound c)) : DanceStep w u

inductive DancePath : State → State → Prop
  | refl (w : State) : DancePath w w
  | cons {w z u : State} (h : DanceStep w z) (t : DancePath z u) : DancePath w u

/- The exchange's playability is now DEFINITIONAL: every licensed
ExchStep is a single cargo move (`exch_is_cargo` below), so the
dance-realization needs no separate row. -/

/-- **THE GRADING TRICHOTOMY** (the user's characterization): every
class-internal transition is FLAT (slide/draw — same fiber), UP one
suit-rung (`tabToFound` — the fiber one level above), or DOWN one
suit-rung (`foundToTab` — the adjacent fiber below).  The neck's
"super move" is a composite: slide flat, then raise up — crossing
fibers through the fork corridor leg-by-leg within this law. -/
theorem dance_step_grading {w u : State} (h : DanceStep w u) :
    (∀ s : Suit, rungAt u s = rungAt w s) ∨
    (∃ s₀ : Suit, rungAt u s₀ = rungAt w s₀ + 1 ∧
      ∀ s : Suit, s ≠ s₀ → rungAt u s = rungAt w s) ∨
    (∃ s₀ : Suit, rungAt u s₀ + 1 = rungAt w s₀ ∧
      ∀ s : Suit, s ≠ s₀ → rungAt u s = rungAt w s) := by
  cases h with
  | cone hc =>
      rcases cone_step_heights hc with hflat | ⟨s₀, hs₀, hothers⟩
      · exact Or.inl hflat
      · exact Or.inr (Or.inr ⟨s₀, hs₀, hothers⟩)
  | raise c hstep hrev =>
      obtain ⟨h1, h2⟩ := step_tabToFound_rungs hstep
      exact Or.inr (Or.inl ⟨c.suit, h1, h2⟩)

/-- Every dance stays in class (the reversible legs were always the
journey side of the setoid). -/
theorem dance_inClass {w u : State} (h : DanceStep w u) :
    sameOrbitSetoid.r w u := by
  cases h with
  | cone hc => exact ConeStep_class hc
  | raise _ hstep hrev => exact class_leg hrev hstep

/-! ### The flat (horizontal) world: cargo, exchanges, phase

THE FIBER ALGEBRA (the user's characterization): a same-height fiber's
members are the ORBIT OF THE LAWFULLY GENERATED ARRANGEMENT GROUP —
generated by CARGO steps (every suffix relocation between fitting
hosts: this includes all slides, all king reseatings, AND every
licensed twin exchange — per TwinExchange.lean's own semantics the
exchange keeps the twin hosts seated and only swaps their above-
suffixes, and the twin-blind right-fit makes each licensed exchange a
SINGLE tabToTab move; `exchangeTwin_eq_self_of_both_bare` prices the
degenerate bit at zero) and DRAW LOOPS (the phase rotations) — with
LEGALITY AS THE MEMBERSHIP FILTER: unlawful arrangements are precisely
the shadow the fiber correctly refuses to connect. -/

/-- The class conjugation map: swaps the twin pairs of card identities
(the carrier def lands with the card; the laws pin it). -/
noncomputable def conjl (w : State) : State := sorry

theorem conjl_involutive (w : State) : conjl (conjl w) = w := by sorry

theorem conjl_inClass (w : State) : sameOrbitSetoid.r w (conjl w) := by sorry

/-- One flat step — TWO letters only: a CARGO step (any `tabToTab`
run relocation between fitting hosts: slides, reseatings, AND licensed
twin exchanges alike — the exchange is a single cargo move at every
licensed shape, per the banked suffix-swap semantics), or a pure draw
(phase). -/
inductive FlatStep : State → State → Prop
  | cargo {w u : State} (c : Card) (b : Base)
      (hstep : w.step (.tabToTab c b) = some u)
      (hrev : reversibleAtW w (.tabToTab c b)) : FlatStep w u
  | draw {w u : State}
      (hstep : w.step .draw = some u)
      (hrev : reversibleAtW w .draw) : FlatStep w u

/-- The banked exchange IS a cargo move: at any `TwinExchOK`-licensed
pair the suffix-swap realizes as ONE `tabToTab` (the hosts keep their
piles — `exchangeTwin_eq_of_located`; the empty suffix rides across;
joints legal by the twin-blind right fit `canSitOn_twin_right`), and
the degenerate both-bare bit prices at ZERO as the identity
(`exchangeTwin_eq_self_of_both_bare`) — CALIBRATION NOTE: the bare
both-empty step is `ExchStep a a`, and no successful `tabToTab` is
ever a fixed point (the moving run always relocates), so the honest
row carries the identity as its own disjunct: the licensed exchange
is one cargo move, or the identity in the degenerate case; the
routing between the cons-cases is the public one-move realizer
`step_realize_fwd` (TwinExchange, promoted at this wave), applied
directly on the cargo side and mirrored through the pair involution
`exchangeTwin_pair` when the cargo sits above the other twin.  The
ExchangeTwin vocabulary stays as the RELATION-level name (the
quotient, freeness, abelian fate rows); it is no longer a separate
path letter. -/
theorem exch_is_cargo {a b : State} (h : ExchStep a b) :
    (∃ c b', a.step (.tabToTab c b') = some b) ∨ a = b := by
  obtain ⟨t, hok, rfl⟩ := h
  obtain ⟨hwf, k, k', h₁, h₂, hne, hbare⟩ := hok
  cases hS : aboveIn t ((a.piles k).faceUp) with
  | nil =>
      cases hS' : aboveIn t.twin ((a.piles k').faceUp) with
      | nil =>
          exact Or.inr (State.exchangeTwin_eq_self_of_both_bare h₁ h₂ hne hS hS').symm
      | cons z rest =>
          have hroot := step_realize_fwd (st := a) (t := t.twin) (a := k') (a' := k)
            hwf h₂
            (show a.pileHolding t.twin.twin = some k by rw [Card.twin_twin]; exact h₁)
            (Ne.symm hne) hS'
            (show aboveIn t.twin.twin ((a.piles k).faceUp) = [] by
              rw [Card.twin_twin]; exact hS)
          exact Or.inl ⟨z, Sum.inr t.twin.twin, by rw [hroot, State.exchangeTwin_pair]⟩
  | cons z rest =>
      have hS' : aboveIn t.twin ((a.piles k').faceUp) = [] := by
        rcases hbare with hbr | hbr
        · rw [hbr] at hS
          exact absurd hS (by simp)
        · exact hbr
      have hroot := step_realize_fwd (st := a) (t := t) (a := k) (a' := k')
        hwf h₁ h₂ hne hS hS'
      exact Or.inl ⟨z, Sum.inr t.twin, hroot⟩

inductive FlatPath : State → State → Prop
  | refl (w : State) : FlatPath w w
  | cons {w z u : State} (h : FlatStep w z) (t : FlatPath z u) : FlatPath w u

/-- Both flat letters never touch the foundations: cargo relocations
and draws level every rung (the engine battery's two non-writers). -/
private theorem FlatStep_rungs {w z : State} (h : FlatStep w z) :
    ∀ s, rungAt z s = rungAt w s := by
  cases h with
  | cargo _ _ hstep _hrev => exact step_tabToTab_rungs hstep
  | draw hstep _hrev => exact step_draw_rungs hstep

/-- Flats preserve all four heights (the cheap direction: pile and
zone writes never touch the foundations). -/
theorem flat_heights {w u : State} (h : FlatPath w u) :
    ∀ s : Suit, rungAt u s = rungAt w s := by
  induction h with
  | refl x => intro s; rfl
  | cons hleg _t ih =>
      intro s
      exact (ih s).trans (FlatStep_rungs hleg s)

/-- **THE FIBER-FLAT COINCIDENCE** — the user's closing principle, with the
conjugate slack the statement needs: within one macro class, two
members share a height tuple IFF some flat path joins them — POSSIBLY
ACROSS THE CONJUGATE ARM (the identity-relabeled variant: unlicensed
twin bits are travelled by the deco, not by play; licensed pairs ride
`ExchStep`; king reseatings are plain slides; both-covered immovable
pairs correctly stay unconnected).  Vertical = rung steps, horizontal
= cargo exchange, identity slack = the conjugate. -/
theorem fiber_iff_flat (C : SameOrbit) (u v : State)
    (hu : u.WF) (hv : v.WF)
    (hcu : classOf C u) (hcv : classOf C v) :
    (∀ s : Suit, rungAt u s = rungAt v s) ↔
      (FlatPath u v ∨ FlatPath u (conjl v) ∨ FlatPath (conjl u) v) := by
  sorry

/-- Founding is a rank-ordered stack: a suit's founded content is the
initial segment of its rung length — so at a FIXED TUPLE, the founded
content of every fiber member is IDENTICAL.  This is why the
horizontal world never needs mixed-residence swaps: the only
Z-slot-dip-requiring exchanges (foundation-resident twins) live
between fibers — neck business, not fiber business. -/
theorem rung_found_prefix (w : State) (s : Suit) :
    ∃ cs : List Card, (w.found s) = cs.take (rungAt w s) ∧
      True := by
  sorry

/-- Relation to the dance world: every FlatPath embeds as a NET-FLAT
DancePath (the cargo and draw letters are dance legs; licensed
exchanges are single cargo moves by `exch_is_cargo`).  The converse
is the per-leg-honest rerouting content — genuinely stronger, kept
sharp by NOT replacing FlatPath. -/
theorem flat_into_dance {w u : State} (h : FlatPath w u) :
    ∃ p : DancePath w u, ∀ s : Suit, rungAt u s = rungAt w s := by
  sorry

/-- **The height fiber**: the members of one class at an exact height
tuple — the micro-state grouping by the 4-suit foundation profile. -/
def rungFiber (C : SameOrbit) (t : Suit → Nat) (st : State) : Prop :=
  classOf C st ∧ ∀ s, rungAt st s = t s

/-- **Fiber behavior of the letters**: slides and draws stay WITHIN the
fiber; a pull steps to the ADJACENT fiber, exactly one suit one rung
down.  The class is thus a graded DAG of fibers with the pull-letters
as grading edges. -/
theorem cone_step_fiber {st st' : State} (h : ConeStep st st') (t : Suit → Nat)
    (hit : ∀ s, rungAt st s = t s) :
    (∀ s, rungAt st' s = t s) ∨
    (∃ s₀ : Suit, rungAt st' s₀ + 1 = t s₀ ∧
      ∀ s : Suit, s ≠ s₀ → rungAt st' s = t s) := by
  rcases cone_step_heights h with hflat | ⟨s₀, hs₀, hothers⟩
  · exact Or.inl fun s => (hflat s).trans (hit s)
  · refine Or.inr ⟨s₀, ?_, ?_⟩
    · exact hs₀.trans (hit s₀)
    · intro s hs
      exact (hothers s hs).trans (hit s)

/-- **The top fibers are the Finals**: every member is dominated by a
Final's tuple (its own saturation), and the Finals occupy at most TWO
tuples — the arm profiles (the orbit row).  The fiber-grading thus
refines the four-layer decomposition: ARM = which top fiber, WIGGLE and
TORSOR = within-fiber content, DEPTH = how far below the top. -/
theorem finals_topFibers (C : SameOrbit) (u : State) (hu : u.WF)
    (hmem : classOf C u) :
    (∃ w, classOf C w ∧ Final w ∧ ∀ s, rungAt u s ≤ rungAt w s) ∧
    (∀ w w', classOf C w → Final w → classOf C w' → Final w' →
      (∀ s, rungAt w s = rungAt w' s) ∨
      (∃ x : Card,
        rungAt w x.suit = rungAt w' x.twin.suit ∧
        rungAt w x.twin.suit = rungAt w' x.suit ∧
        ∀ s : Suit, s ≠ x.suit → s ≠ x.twin.suit →
          rungAt w s = rungAt w' s)) := by
  sorry

/-! ## §4. canus and the selector -/

/-- **canus**: saturated members reachable from `u`'s canonical form by
the cone, up to conjugation (abstract form; the computation is canon +
neck-neighbors, not class enumeration). -/
def canusOf (u w' : State) : Prop :=
  Final w' ∧ ∃ w₁, ConePath (canon u) w₁ ∧ (w' = w₁ ∨ w' = conjl w₁)

theorem canusOf_nonempty (u : State) (hwf : u.WF) :
    ∃ w, canusOf u w := by
  obtain ⟨-, -, hfin⟩ := canon_run u
  exact ⟨canon u, hfin, canon u, ConePath.refl (canon u), Or.inl rfl⟩

/-- canus is constant on classes — `mem_macro_iff` restated: THE
load-bearing dependency (the decompression card's engine). -/
theorem canusOf_class_inv (u v : State) (hu : u.WF) (hv : v.WF)
    (h : sameOrbitSetoid.r u v) : ∀ w, canusOf u w ↔ canusOf v w := by
  sorry

/-- The position key layer: parked-never-stackable seating data.
(Carrier def lands with the case table; laws pin it below.) -/
noncomputable def posKey (w : State) : Nat := sorry

/-- The total serial order on keys: lexicographic on lists. -/
def lexLE : List Nat → List Nat → Prop
  | _, [] => True
  | [], _ :: _ => False
  | a :: as, b :: bs => a < b ∨ (a = b ∧ lexLE as bs)

/-- The canonical index, HEIGHT-FIRST: founded content leads, positions
break the wiggle ties, the serial order breaks conjugate-arm ties. -/
noncomputable def canonKey (w : State) : List Nat :=
  [(w.found .spade).length, (w.found .heart).length,
   (w.found .diamond).length, (w.found .club).length, posKey w]

/-- The class's canonical member exists: the lexLE-minimum of canus. -/
theorem canonV3_witness (u : State) (hwf : u.WF) :
    ∃ w', canusOf u w' ∧ ∀ z, canusOf u z → lexLE (canonKey w') (canonKey z) := by
  sorry

noncomputable def canonV3 (u : State) : State :=
  if h : u.WF then Classical.choose (canonV3_witness u h) else u

/-! ## §5. THE MAIN GOAL: the iff, and the section property -/

/-- The class-constant direction (the ⇐ engine is `canusOf_class_inv`). -/
theorem canonV3_eq_of_sameClass (u v : State) (hu : u.WF) (hv : v.WF)
    (h : sameOrbitSetoid.r u v) : canonV3 u = canonV3 v := by
  sorry

/-- The class-injective direction (the in-class witness legs). -/
theorem sameClass_of_canonV3_eq (u v : State) (hu : u.WF) (hv : v.WF)
    (h : canonV3 u = canonV3 v) : sameOrbitSetoid.r u v := by
  sorry

/-- **THE MAIN GOAL**: the canonical form characterizes the macro state. -/
theorem canonV3_iff (u v : State) (hu : u.WF) (hv : v.WF) :
    sameOrbitSetoid.r u v ↔ canonV3 u = canonV3 v :=
  ⟨canonV3_eq_of_sameClass u v hu hv, sameClass_of_canonV3_eq u v hu hv⟩

/-- The section property: constant on classes, distinct across them,
in-class by construction — the quotient bijects with canonical states. -/
theorem canonV3_section (u : State) (hwf : u.WF) :
    Quotient.mk sameOrbitSetoid (canonV3 u) = Quotient.mk sameOrbitSetoid u := by
  sorry

/-! ## §6. The fork dossier (the arm layer's topology) -/

/-- The fork state, intrinsically: a state whose canonical form is
SLIDE-SENSITIVE — a one-slide neighbor saturates to the other wing. -/
def forkState (st : State) : Prop :=
  ∃ c b st', st.step (.tabToTab c b) = some st' ∧ canon st ≠ canon st'

/-- Covered: the card sits beneath other face-up content. -/
def coveredIn (st : State) (c : Card) : Prop :=
  ∃ a, st.pileHolding c = some a ∧ aboveIn c (st.piles a).faceUp ≠ []

/-- **The swap-aware license** (the user's cargo-accounting CanRaise):
raisable now (vanilla), or raisable after finitely many licensed cargo
slides — the {slide · raise} closure, the cascade license.  The fork is
contention at THIS grade (the census's TwinContended-emptiness is the
VANILLA grade; two predicates, no contradiction). -/
inductive CanRaiseS : State → Card → Prop
  | now {st : State} (c : Card) (h : CanRaise st c) : CanRaiseS st c
  | via {st st' : State} (c : Card)
      (hl : ∃ d b, st.step (.tabToTab d b) = some st' ∧
        reversibleAtW st (.tabToTab d b))
      (h : CanRaiseS st' c) : CanRaiseS st c

/-- Saturating completion: `s` is a maximal licensed run from `u`. -/
def saturatesTo (u s : State) : Prop := ∃ l, StackRun u l s ∧ Final s

/-- The cargo reading: `d` TOPS the twin's pile — the twin sits beneath
it, covered by construction. -/
def cargoTop (st : State) (d c : Card) : Prop :=
  ∃ a, st.pileOfTop d = some a ∧ st.pileHolding c = some a

/-- **The fork point with its cargo as first-class witness** — the
constructive form. -/
def forkPointC (st : State) (x d : Card) : Prop :=
  CanRaiseS st x ∧ cargoTop st d x.twin ∧
    d.rank.toIdx + 1 = x.rank.toIdx ∧ ¬ twinSuit d.suit x.suit ∧
    ¬ satStackable (Quotient.mk sameOrbitSetoid st) d

/-- **The fork point** (the live signature, existentially packaged): one
twin stackable in the cargo-exchange sense, the other twin topped by a
cargo card non-stackable in the macro state. -/
def forkPoint (st : State) (x : Card) : Prop := ∃ d, forkPointC st x d

/-- **The fork, macro-grade**: some card's stackedness is ARM-CONTINGENT
— stacked somewhere, but not at every Final.  The witnesses are exactly
the fork pair's twins at the fork rank. -/
def forkedCard (C : SameOrbit) (c : Card) : Prop :=
  satStackable C c ∧ ¬ surelyStackable C c

/-- Surely implies sat, under a WF member of the class: the canonical
form is a Final class-member (canon_run + canon_in_class), and
surely-at-every-Final reads the foundedness right there.  Added as the
named row the floor card lists beside benign; the member premise is
the CALIBRATION the ⇐ direction genuinely needs (a bare quotient with
no WF member can lack Final members entirely, making surelyStackable
vacuous — every consumer of the grades holds a WF member). -/
theorem surely_imp_sat (C : SameOrbit) (c : Card)
    (hmem : ∃ u, classOf C u ∧ u.WF)
    (h : surelyStackable C c) :
    satStackable C c := by
  obtain ⟨u, hcu, hwf⟩ := hmem
  have hclass : classOf C (canon u) := (canon_in_class hwf).trans hcu
  obtain ⟨-, -, hfin⟩ := canon_run u
  have hfound := h (canon u) hclass hfin
  exact ⟨canon u, hclass, hfound⟩

/-- Benign collapse: with no arm-contingent card, the grades coincide.
(The member premise calibrated in as for `surely_imp_sat`; the
fork-free direction is pure logic on the forkedCard definition — a
Final member where the card missed its foundation would itself
witness the fork — decidable branch, no classicals.) -/
theorem benign_sat_iff_surely (C : SameOrbit) (c : Card)
    (hmem : ∃ u, classOf C u ∧ u.WF)
    (hforkfree : ¬ forkedCard C c) :
    satStackable C c ↔ surelyStackable C c := by
  constructor
  · intro hsat w hw hfin
    by_cases hmem_s : c ∈ w.found c.suit
    · exact hmem_s
    · exact absurd ⟨hsat, fun hS => absurd (hS w hw hfin) hmem_s⟩ hforkfree
  · intro hsure
    exact surely_imp_sat C c hmem hsure

/-- **The two faces agree**: a class has an arm-contingent card iff some
member shows the live fork-point signature. -/
theorem forkedCard_iff_forkPoint (C : SameOrbit) (u : State)
    (hu : u.WF) (hmem : classOf C u) :
    (∃ c, forkedCard C c) ↔ (∃ x, forkPoint u x) := by
  sorry

/-- **After the fork** (class-level): the decision has been taken —
some satStackable card is NO LONGER surelyStackable; the pair's
stackedness became arm-contingent. -/
def afterFork (C : SameOrbit) : Prop := ∃ c, forkedCard C c

/-- **The pair configuration** — the three cases: at any member, the
fork pair {x, x.twin} and its cargo d stand in exactly one of:
PRE (undecided: neither twin stacked, the cargo parked on one twin),
ARM A (this twin stacked, the cargo on the other),
ARM B (the mirror). -/
inductive PairCfg (st : State) (x d : Card) : Prop
  | pre (h₀ : ¬ (x ∈ st.found x.suit))
      (h₁ : ¬ (x.twin ∈ st.found x.twin.suit))
      (h₂ : cargoTop st d x ∨ cargoTop st d x.twin) : PairCfg st x d
  | armA (h₀ : x ∈ st.found x.suit)
      (h₁ : cargoTop st d x.twin) : PairCfg st x d
  | armB (h₀ : x.twin ∈ st.found x.twin.suit)
      (h₁ : cargoTop st d x) : PairCfg st x d

/-- **GIVEN the saturation fork point, its witnessed pair and cargo
characterize every member into the three cases** — the classification
is READ OFF from the known point, not posited over the class.  And the
cases are state-level decidable: given (x, d), each member's
configuration is a computable check of its founds and seatings. -/
theorem forkPoint_classifies (C : SameOrbit) (st₀ : State)
    (hwf : st₀.WF) (hmem₀ : classOf C st₀)
    (x d : Card) (hfp : forkPointC st₀ x d)
    (w : State) (hmem : classOf C w) :
    PairCfg w x d := by
  sorry

/-- **THE THREE-CASES THEOREM**: after the fork, ONE pair and ONE cargo
classify every member of the class — each member's fork geometry is
PRE, ARM A, or ARM B.  Stronger than the card-roster count: this pins
the geometry, and it is exactly why at most three cards are ever
contingent. -/
theorem fork_threeCases (C : SameOrbit) (u : State) (hu : u.WF)
    (hmem : classOf C u) (haf : afterFork C) :
    ∃ x d : Card, ∀ st', classOf C st' → PairCfg st' x d := by
  sorry

/-- **The three-cards corollary**: the arm-contingent population is
exactly the twin pair {x, x.twin}, and the steering cargo is the one
card d — outside these three, every card is either surelyStackable or
stranded-inert.  (Cargo uniqueness: a second would-be cargo sits
stock/waste — it can never surface in-class; and if it were founded,
the fork would have dissolved.) -/
theorem fork_threeCards (C : SameOrbit) (u : State) (hu : u.WF)
    (hmem : classOf C u) (haf : afterFork C) :
    ∃ x d : Card,
      (∀ c, forkedCard C c ↔ (c = x ∨ c = x.twin)) := by
  sorry

/-- **Fewness, tuple form**: after the fork, every Final member's rung
tuple is EITHER the shared profile OR its one-pair flip at the fork
pair — the orbit theorem's fork branch, consumed at the new notion:
only a few possible Finals. -/
theorem afterFork_fewFinals (C : SameOrbit) (u : State) (hu : u.WF)
    (hmem : classOf C u) (haf : afterFork C)
    (w' : State) (hw' : classOf C w') (hf : Final w') :
    (∀ s : Suit, rungAt w' s = rungAt (canon u) s) ∨
    (∃ x : Card,
      rungAt w' x.suit = rungAt (canon u) x.twin.suit ∧
      rungAt w' x.twin.suit = rungAt (canon u) x.suit ∧
      ∀ s : Suit, s ≠ x.suit → s ≠ x.twin.suit →
        rungAt w' s = rungAt (canon u) s) := by
  sorry

/-- **Fewness, state form**: after the fork, every Final member sits
within ONE NECK of `canon u` — cone-reachable to a midpoint, then a
saturation completes.  The midpoints are bounded by the case table's
rank arithmetic (the classification closure's remaining work). -/
theorem afterFork_neckReachable (C : SameOrbit) (u : State) (hu : u.WF)
    (hmem : classOf C u) (w' : State) (hw' : classOf C w')
    (hf : Final w') :
    ∃ m, ConePath (canon u) m ∧ saturatesTo m w' := by
  sorry

/-! ### The fork dossier's derivable halves
(Private engine rows landed as the evidence base for the BLOCKED notes
below: the piled-rung arithmetic and the two pin-halves the
skeleton's forkPointC DOES carry.  The covered-twin's exact pin is
deliberately NOT here — that leg is the gap-form content the
skeleton's signature under-carries, see the notes.) -/

/-- A face-up card's own suit rung sits weakly below its rank index —
the piled leg of the fork arithmetic (canon-v3's `v3PiledRung`
re-striped on the banked carrier: `WF.found_prefix`, the banked
`mem_upCards_take`, and the face-up census inversion
`mem_faceUp_only`; conservation forbids a card in two zones). -/
private theorem piled_rung {st : State} {q : Card} {k : Anchor}
    (hwf : st.WF) (hmem : q ∈ (st.piles k).faceUp) :
    rungAt st q.suit ≤ q.rank.toIdx := by
  obtain ⟨n, hn⟩ := hwf.found_prefix q.suit
  have hlen : rungAt st q.suit ≤ n := by
    show (st.found q.suit).length ≤ n
    rw [hn, List.length_take, Suit.upCards_length]
    omega
  rcases Nat.lt_trichotomy (rungAt st q.suit) q.rank.toIdx with hlt | heq | hgt
  · exact Nat.le_of_lt hlt
  · exact Nat.le_of_eq heq
  · exfalso
    have hqf : q ∈ st.found q.suit := by
      rw [hn, show q = Card.mk q.suit q.rank from rfl]
      exact mem_upCards_take q.suit n q.rank (by omega)
    exact (mem_faceUp_only hwf hmem).2.2.2.2 q.suit hqf

/-- The bare twin's exact pin, along the swap-grade cascade: the
vanilla license at the cascade's far end is rung-exact
(`stackable_now_rungexact`, the calibrated row), and the cascade's
cargo slides never write foundations (the battery's tabToTab
non-write) — so the rung already sits at the pair rank at the point
itself.  This is the pins' derivable half; the forkPoint BLOCKED note
below records the other half. -/
private theorem canRaiseS_rung_pin {st : State} {x : Card} (h : CanRaiseS st x) :
    rungAt st x.suit = x.rank.toIdx := by
  induction h with
  | now c hcan => exact stackable_now_rungexact _ c hcan
  | via c hl _h2 ih =>
      obtain ⟨d, b, hstep, -⟩ := hl
      have hr := (step_tabToTab_rungs hstep) c.suit
      omega

/-- The cargo's strict strand: at a fork point the cargo — topping the
covered twin's pile, never founded anywhere in the class — has its own
suit's rung STRICTLY below its rank.  Reductio: were the cargo
next-up, its license would fire (it tops the covering pile, and the
seat is refillable — the twin sits face-up below it, so the chop is
nonempty), the licensed raise is reversible at WF (the under-seat
witness constructor), the raised mate sits in-class with the cargo
founded (`class_leg` + `tabToFound_found_trio`), contradicting the
macro-grade ¬satStackable leg.  The weak half is `piled_rung`
(conservation); strictness is the negated nextUp. -/
private theorem forkPoint_cargo_strand {st : State} {x d : Card}
    (hwf : st.WF) (hfp : forkPointC st x d) :
    rungAt st d.suit < d.rank.toIdx := by
  obtain ⟨-, hcargo, -, hcol, hnsat⟩ := hfp
  obtain ⟨k, htopd, hholdt⟩ := hcargo
  have hdmem : d ∈ (st.piles k).faceUp := lastOf_mem (pileOfTop_top htopd).2
  have hxtm0 : x.twin ∈ (st.piles k).faceUp := pileHolding_mem hholdt
  have hsnoc : (st.piles k).faceUp = chop (st.piles k).faceUp ++ [d] :=
    lastOf_chop (pileOfTop_top htopd).2
  have hdne : d ≠ x.twin := by
    intro hcon
    exact hcol (by rw [hcon]; exact Or.inr rfl)
  rw [hsnoc] at hxtm0
  have hchop : chop (st.piles k).faceUp ≠ [] := by
    intro hnil
    rw [hnil] at hxtm0
    have hxt : x.twin = d := List.mem_singleton.1 (by simpa using hxtm0)
    exact absurd hxt.symm hdne
  by_cases hnu : st.nextUp d = true
  · exfalso
    obtain ⟨z', preT, hch⟩ := list_cons_of_ne_nil hchop
    have hrev := tabToFound_reversibleAtW_under_wf hwf hnu htopd hch
    obtain ⟨s₁, play, hstep, hrun⟩ := hrev
    have hclass := class_leg ⟨s₁, play, hstep, hrun⟩ hstep
    obtain ⟨-, ka, -, hs⟩ := step_tabToFound_inv hstep
    have hfound : d ∈ s₁.found d.suit := by
      have htrio := (tabToFound_found_trio (a := ka) hs).1
      rw [htrio]
      exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
    exact hnsat ⟨s₁, (Quotient.sound hclass).symm, hfound⟩
  · have hle := piled_rung hwf hdmem
    have hne : st.foundHeight d.suit ≠ d.rank.toIdx := by
      intro hcon
      have hexp : st.nextUp d = true := by
        show decide (d.rank.toIdx = st.foundHeight d.suit) = true
        rw [show d.rank.toIdx = st.foundHeight d.suit from hcon.symm]
        exact decide_eq_true rfl
      exact absurd hexp hnu
    have hr : rungAt st d.suit = st.foundHeight d.suit := rfl
    omega

/-- The operational trial, derived: the twin's swap-raise realizes
through the cargo slide onto the bare twin's host, and there the twin
lights vanilla.

BLOCKED (this row, fork-card escape hatch): the skeleton's
`forkPointC` under-carries the live fork signature.  The trial needs
(i) `x` topping a pile AT the point — but `CanRaiseS st x` only says
x is raisable after cargo slides, and x may sit buried behind a
slidable run at the point itself, so the base `Sum.inr x` may have no
top to land on; and (ii) the covered twin's rung already AT the pair
rank so it lights vanilla once uncovered — but the signature carries
no twin-side raisability, and a WF craft satisfies every conjunct
with the twin's rung one below the pair (the twin strands behind its
ladder).  Both legs live in the corrected forkEvidence GAP FORM
decided at the canon-v3 battery: `CanRaiseS x.twin ∧ ¬CanRaiseVanilla
x.twin ∧ coveredIn x.twin ∧ cargo-shape` (FUTURES-ORIG.md §11-L4.2,
probes/CanonV3Probe.lean — the l4RowGapForm rows; the derived trial
decide-verified at both standing-fork stalls), and that session's
ledger already records this sorry as its own next closure.  This
file banks the trial's two engines: the bare pin (`canRaiseS_rung_pin`)
and the cargo strand (`forkPoint_cargo_strand`). -/
theorem forkPoint_trial {st : State} {x : Card} (h : forkPoint st x) :
    ∃ d st', st.step (.tabToTab d (Sum.inr x)) = some st' ∧
      CanRaise st' x.twin ∧ d.rank.toIdx + 1 = x.rank.toIdx := by
  sorry

/-- The pin lemma: at the fork point, BOTH same-color rungs sit at the
pair rank — the bare twin's pin by `stackable_now_rungexact`, the
covered twin's pin by the cargo/cascade arithmetic.

BLOCKED (this row, fork-card escape hatch): the BARE half is banked
and proven above (`canRaiseS_rung_pin` — the cascade's rung-exact
license plus the slides' found non-write).  The COVERED half is what
the skeleton's `forkPointC` under-carries: `cargoTop` only says the
twin sits at-or-below the cargo in its pile, and nothing forbids the
twin's own suit rung sitting BELOW the pair rank at the point (a WF
craft with the twin stranded one rung short passes every conjunct of
the signature while failing the pin), so the exact covered pin is
unreachable from these hypotheses alone.  It becomes derivable from
the gap form's `CanRaiseS x.twin` leg — the same canon-v3 §11-L4.2
correction the trial's note records — where the covered pin rides
the SAME cascade induction as the bare half. -/
theorem forkPoint_pins (st : State) (x : Card) (hwf : st.WF)
    (h : forkPoint st x) :
    rungAt st x.suit = x.rank.toIdx ∧ rungAt st x.twin.suit = x.rank.toIdx := by
  sorry

/-- **The exclusivity sandwich** (the user's rank-arithmetic proof):
fork points in BOTH color pairs at one state are impossible — each
fork strands a card the other needs seated.

BLOCKED (this row, fork-card escape hatch): the user's sandwich
consumes BOTH pins of BOTH forks — each fork pins its own color pair
at its pair rank (forkPoint_pins) and strands a suit of the OPPOSITE
color strictly below its own rank (the cargo strand
`forkPoint_cargo_strand`, whose suit is opposite-colored by the
signature's ¬twinSuit leg, so it sits inside the other fork's pair)
— the two strict inequalities then cross-pinch into `x < y ∧ y < x`,
the v3ForkExclusivity arithmetic (canon-v3 battery, Orig/CanV3 on
that branch).  Both inputs are behind the pins' BLOCKED notes above
(the covered pins under-carry in the skeleton's signature: without
them the cross-cases of the sandwich hit the covered twins' suits,
whose rungs the bare pins leave free), so this row waits with them.
The half that IS banked here: the bare pins (via `canRaiseS_rung_pin`)
and the cargo strands of both forks. -/
theorem forkPoint_exclusive (st : State) (x y : Card) (hwf : st.WF)
    (hcol : ¬ twinSuit x.suit y.suit)
    (hx : forkPoint st x) (hy : forkPoint st y) : False := by
  sorry

/-- **Unionability**: two states share a common saturating descendant —
their founded accomplishments coexist in one future. -/
def unionable (u v : State) : Prop :=
  ∃ s, saturatesTo u s ∧ saturatesTo v s

/-- The union profile: per-suit max of the two canonical rungs. -/
def unionRung (u v : State) (s : Suit) : Nat :=
  Nat.max (rungAt (canon u) s) (rungAt (canon v) s)

/-- Unionable ⟺ the union profile is jointly realizable at one
saturated member. -/
theorem unionable_iff_unionTuple (u v : State) (hu : u.WF) (hv : v.WF) :
    unionable u v ↔ ∃ s, Final s ∧ ∀ cl : Suit, rungAt s cl = unionRung u v cl := by
  sorry

/-- The fork is non-unionability: the wings' union profile unrealizable
(seating the never-stackable cargo fails — the homeless-cargo row). -/
theorem fork_iff_nonUnionable (u v : State) (hu : u.WF) (hv : v.WF)
    (hf : Final u) (hg : Final v)
    (hwings : ∃ st, forkState st ∧
      Quotient.mk sameOrbitSetoid st = Quotient.mk sameOrbitSetoid u) :
    ¬ unionable u v := by
  sorry

/-- A legal journey: any play of legal moves. -/
inductive Journey : State → State → Prop
  | refl (w : State) : Journey w w
  | cons {w u u' : State} (h : ∃ m, w.step m = some u) (t : Journey u u') :
      Journey w u'

/-- **The bottleneck**: any legal journey from one wing's saturated
member to the other's passes through a fork state — the forced dip
(the slide's host must first be freed by a pull). -/
theorem wing_crossing_bottleneck (u v st : State)
    (hu : Final u) (hv : Final v) (hjourney : Journey u v)
    (hwings : Quotient.mk sameOrbitSetoid u = Quotient.mk sameOrbitSetoid v) :
    ∃ st₁, Journey u st₁ ∧ forkState st₁ ∧ Journey st₁ v := by
  sorry

/-! ## §7. The one-class structure theorem (the classification) -/

/-- **The orbit theorem** (corrected group): saturated class-mates'
rung tuples are equal, or differ by exactly ONE twin pair flipped
(per the fork exclusivity, at most one pair can fork). -/
theorem saturated_tuple_orbit (u v : State) (hu : u.WF) (hv : v.WF)
    (h : sameOrbitSetoid.r u v) (hf : Final u) (hg : Final v) :
    (∀ s : Suit, rungAt u s = rungAt v s) ∨
    ∃ x : Card,
      rungAt u x.suit = rungAt v x.twin.suit ∧
      rungAt u x.twin.suit = rungAt v x.suit ∧
      (∀ s : Suit, s ≠ x.suit → s ≠ x.twin.suit → rungAt u s = rungAt v s) := by
  sorry

/-- **The classification closure** (the one genuinely open row): at a
fixed arm profile, saturated class-mates differ only by slides —
exotic-census evidence, proof by falsifier hunt. -/
theorem saturated_classification (u v : State) (hu : u.WF) (hv : v.WF)
    (h : sameOrbitSetoid.r u v) (hf : Final u) (hg : Final v)
    (hesion : ∀ s : Suit, rungAt u s = rungAt v s) :
    ConePath u v := by
  sorry

/-- **The envelope** (mem_macro_iff's skeleton form): every class member
is a conjugation of a cone element of any member's canonical form. -/
theorem envelope (u v : State) (hu : u.WF) (hv : v.WF)
    (h : sameOrbitSetoid.r u v) (hf : Final v) :
    ConePath (canon u) v ∨ ConePath u (conjl v) := by
  sorry

/-! ## §8. Canonical-index echo (for the selector's proofs) -/

/-- canonKey's first four components are the rungs — definitional echo. -/
theorem canonKey_rungs (w : State) :
    canonKey w = [rungAt w .spade, rungAt w .heart, rungAt w .diamond,
      rungAt w .club, posKey w] := rfl

/-! ## The floor-row audit
(#print axioms on each newly proved floor head — expected
[propext, Quot.sound]; anything else flagged.)

FLAGGED: `canusOf_nonempty` reports [propext, sorryAx, Quot.sound].
The sorryAx enters at the STATEMENT level only, through the
skeleton's designated carrier bit `conjl` (`noncomputable def conjl
:= sorry`, the conjugation carrier whose laws are canon-v3's ledgered
next def-landing): the `canusOf` definition's second disjunct
mentions `conjl w₁`, so any constant whose type expands it carries
the occurrence.  The proof itself never forces the carrier — the
witness rides `Or.inl` (w = w₁ = canon u), so the row is proved at
canon + ConePath.refl; the flag clears the moment the conjl carrier
lands.  Every other floor head audits within [propext, Quot.sound]. -/

#print axioms stackable_now_rungexact
#print axioms canon_rung_mono
#print axioms cone_step_heights
#print axioms cone_inClass
#print axioms dance_step_grading
#print axioms dance_inClass
#print axioms flat_heights
#print axioms cone_step_fiber
#print axioms exch_is_cargo
#print axioms surely_imp_sat
#print axioms benign_sat_iff_surely
#print axioms canusOf_nonempty
#print axioms piled_rung
#print axioms canRaiseS_rung_pin
#print axioms forkPoint_cargo_strand

