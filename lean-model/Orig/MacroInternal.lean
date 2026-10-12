import Orig.EdgeLabel
import Orig.TwinExchangeQuotient
import Orig.Dominance
/- import Orig.CanV3 lands with the v3 harvest merge (the selector
   chapter: canonIdxLt, canonFormalKey) — re-added post-merge. -/

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
theorem canon_rung_mono (st : State) (s : Suit):
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
theorem cone_inClass (w u : State) (h : ConePath w u) :
    sameOrbitSetoid.r w u := by
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

/- THE CONJUGATION CARRIER IS GONE (the 2026-11-11 cleanup): no state-map
`conjl` — conjugation enters through the LANDED setoid (the four-disjunct
`sameOrbitSetoid.r` folds the relabeling in-class) and through
CanV3's KEY-INVARIANCE rows (`canonHtup_twinMap`): the selector does not
feed conjugate variants through a function — its keys are blind to the
relabel by construction.  Every former `conjl`-bearing statement below
now reads through `sameOrbitSetoid.r` directly. -/

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
      (FlatPath u v ∨ ∃ z, FlatPath u z ∧ sameOrbitSetoid.r z v) := by
  sorry

/-! ### The per-letter found writers (the descent microscope)

Private copy-kit for this module's rows, dedup-marked against the
reader banks: the raw step unfoldings are the public homes
(`step_foundToTab_eq` / `step_tabToTab_eq` in `Orig/Play.lean`,
`draw_unfold` there too), and the take/chop identities below are
verbatim-shaped copies of `Orig/Reach.lean`'s PRIVATE kit
(`chop_eq_take`, `chop_take_succ`, `take_len_pin` — banked there
behind `private`, invisible across modules, so this base re-proves
them; the harvest-time dedup sweep should absorb them). -/

/-- A taken build-order prefix records its length (the copy of
`Orig/Reach.lean`'s private `take_len_pin`). -/
private theorem take_len_pin (σ : Suit) (n : Nat) :
    (σ.upCards.take n).length = min n 13 := by
  rw [List.length_take, Suit.upCards_length]

/-- A list is its own take down to the taken length (the general
`take`-min identity the rung reading rides). -/
private theorem take_min_len (l : List Card) (n : Nat) :
    l.take n = l.take (min n l.length) := by
  have h6 : l.take n = (l.take l.length).take n := by rw [List.take_length]
  rw [h6, List.take_take]

/-- The chop-take identity: chopping a build-order prefix of length
`m+1` leaves the `m`-prefix (the copy of `Orig/Reach.lean`'s private
`chop_take_succ`, reached through `chop_eq_take`). -/
private theorem chop_eq_take : ∀ (l : List Card), chop l = l.take (l.length - 1)
  | [] => rfl
  | [x] => rfl
  | x :: y :: t => by
      have ih := chop_eq_take (y :: t)
      have hA : (y :: t).length = t.length + 1 := List.length_cons
      have hlen : (x :: y :: t).length - 1 = (y :: t).length - 1 + 1 := by
        rw [List.length_cons]
        omega
      rw [hlen]
      show x :: chop (y :: t) = x :: (y :: t).take ((y :: t).length - 1)
      rw [ih]

private theorem chop_take_succ (L : List Card) (m : Nat) (h : m + 1 ≤ L.length) :
    chop (L.take (m + 1)) = L.take m := by
  rw [chop_eq_take, List.length_take, Nat.min_eq_left h, List.take_take,
    Nat.min_eq_left (by omega : m + 1 - 1 ≤ m + 1)]
  exact congrArg L.take (by omega)

/-- A snoc'd list is one longer than its chop. -/
private theorem chop_len_of_last {l : List Card} {c : Card}
    (h : lastOf l = some c) : l.length = (chop l).length + 1 := by
  have hsnoc : l = chop l ++ [c] := lastOf_chop h
  have h1 : l.length = (chop l ++ [c]).length := congrArg List.length hsnoc
  rw [h1, List.length_append]
  simp

/-- Chopping exactly `r` cards of the build order pops the `r-1`
prefix back — the pull leg's chop restated on `upCards`. -/
private theorem chop_take_upCards {s : Suit} {c : Card} {r : Nat}
    (htop : lastOf (s.upCards.take r) = some c) (hr13 : r ≤ 13) :
    chop (s.upCards.take r) = s.upCards.take (r - 1) := by
  have hlen : 1 ≤ (s.upCards.take r).length :=
    List.length_pos_of_mem (lastOf_mem htop)
  have hdet := take_len_pin s r
  have hr1 : 1 ≤ r := by omega
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (show r ≠ 0 by omega)
  subst hm
  rw [chop_take_succ s.upCards m (by rw [Suit.upCards_length]; omega)]
  exact congrArg s.upCards.take (by omega)

/-- The raw pull write: a firing `foundToTab` names the current
founded TOP (the guard `foundTop = some c`), chops it off its suit,
and leaves every other foundation verbatim.  (The guard analysis is
the banked idiom — `Orig/Dominance.lean`'s private
`g_step_foundToTab_inv` owns the shape; this copy keeps the found
side only.) -/
private theorem pull_write {st st' : State} {c : Card} {b : Base}
    (h : st.step (Move.foundToTab c b) = some st') :
    lastOf (st.found c.suit) = some c ∧
    st'.found c.suit = chop (st.found c.suit) ∧
    ∀ σ, σ ≠ c.suit → st'.found σ = st.found σ := by
  simp only [State.step] at h
  split at h
  · split at h
    · rename_i _ c' ht hg
      rw [Bool.and_eq_true] at hg
      injection h with hEq
      have hcc : c' = c := of_decide_eq_true hg.1
      obtain ⟨hfld, _, _, _⟩ :=
        putCard_keep (st := st.setFound c.suit (chop (st.found c.suit))) (c := c) (b := b)
      refine ⟨?_, ?_, ?_⟩
      · exact (show st.foundTop c.suit = some c from by rw [ht, hcc])
      · rw [← hEq, hfld, setFound_found_self]
      · intro σ hneσ
        rw [← hEq, hfld, setFound_found_ne hneσ]
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The raw slide write: a firing `tabToTab` never touches any
foundation.  (The branch analysis is the banked idiom —
`Orig/Dominance.lean`'s private `g_step_tabToTab_inv` owns the
shape.) -/
private theorem slide_write {st st' : State} {c : Card} {b : Base}
    (h : st.step (Move.tabToTab c b) = some st') :
    ∀ σ, st'.found σ = st.found σ := by
  simp only [State.step] at h
  split at h
  · exact absurd h (by simp)
  · rename_i _ a hh
    split at h
    · rename_i hcp
      split at h
      · exact absurd h (by simp)
      · rename_i _ hne
        injection h with hEq
        intro σ
        rw [← hEq]
        obtain ⟨hfld, _, _, _⟩ :=
          putRun_keep (st := st.setPile a
            (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp)))
            (run := fromCard c (st.piles a).faceUp) (b := b)
        rw [hfld, congrFun (setPile_found st a
          (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))) σ]
    · exact absurd h (by simp)

/-- The raw draw write: a firing draw never touches any foundation. -/
private theorem draw_write {st st' : State}
    (h : st.step Move.draw = some st') :
    ∀ σ, st'.found σ = st.found σ := by
  intro σ
  have hsd : st.stepDraw = some st' := h
  obtain ⟨r, hr, _, hshape⟩ := draw_unfold hsd
  have hr2 : r = State.recycle st := hr.symm
  subst hr2
  rw [hshape]
  show (State.recycle st).found σ = st.found σ
  simp only [State.recycle]
  split
  · split
    · rfl
    · rfl
  · rfl

/-- The prefix discipline (the canonical `rung_found_prefix` form)
caps every rung at thirteen. -/
private theorem rung_le_of_discipline {st : State}
    (h : ∀ σ, st.found σ = σ.upCards.take (rungAt st σ)) (σ : Suit) :
    rungAt st σ ≤ 13 := by
  show (st.found σ).length ≤ 13
  rw [h σ, take_len_pin σ (rungAt st σ)]
  omega

/-- The pull leg preserves the rank-order discipline: chopping a
build-order prefix leaves the shorter build-order prefix. -/
private theorem pull_discipline {st st' : State} {c : Card} {b : Base}
    (hstep : st.step (Move.foundToTab c b) = some st')
    (h : ∀ σ, st.found σ = σ.upCards.take (rungAt st σ)) :
    ∀ σ, st'.found σ = σ.upCards.take (rungAt st' σ) := by
  obtain ⟨hlast, hchop, hne⟩ := pull_write hstep
  have hr13 : rungAt st c.suit ≤ 13 := rung_le_of_discipline h c.suit
  intro σ
  rcases Decidable.em (σ = c.suit) with rfl | hneσ
  · have hl : lastOf (c.suit.upCards.take (rungAt st c.suit)) = some c := by
      rw [h c.suit] at hlast
      exact hlast
    have hchop2 : chop (st.found c.suit) = c.suit.upCards.take (rungAt st c.suit - 1) := by
      rw [h c.suit]
      exact chop_take_upCards hl hr13
    have hzrung : rungAt st' c.suit = rungAt st c.suit - 1 := by
      have hL1 : (st.found c.suit).length = rungAt st c.suit := rfl
      show (st'.found c.suit).length = (st.found c.suit).length - 1
      rw [hchop, hchop2, take_len_pin]
      omega
    rw [hchop, hchop2, hzrung]
  · rw [hne σ hneσ, h σ]
    have hr : rungAt st' σ = rungAt st σ := by
      show (st'.found σ).length = (st.found σ).length
      rw [hne σ hneσ]
    rw [hr]

/-- The rung-congr of a pointwise found equality. -/
private theorem rung_congr_found {st st' : State} (s : Suit)
    (h : st'.found s = st.found s) : rungAt st' s = rungAt st s := by
  show (st'.found s).length = (st.found s).length
  rw [h]

/-- Founding is a rank-ordered stack — THE BANKED INVARIANT, restated
at the rung: a `WF` state's suit foundation is its build order
truncated AT THE RUNG (`WF.found_prefix` carries `∃ n, found =
upCards.take n` — `Orig/Integrity.lean`; the conservation conjunct —
`Orig/State.lean`); the length of the take pins `n` to the rung
itself.  So THE RUNG ALONE READS THE FOUNDATION: at a FIXED TUPLE,
the founded content of every fiber member is IDENTICAL.

(The skeleton's placeholder form — `∃ cs, found = cs.take rung` with
a vacuous conjunct — was trivially true and content-free; this is
the honest per-the-bank restatement the row was shaped for.) -/
theorem rung_found_prefix (w : State) (hwf : w.WF) (s : Suit) :
    w.found s = s.upCards.take (rungAt w s) := by
  obtain ⟨n, hn⟩ := hwf.found_prefix s
  have hr : rungAt w s = min n 13 := by
    show (w.found s).length = min n 13
    rw [hn]
    exact take_len_pin s n
  have htake : s.upCards.take n = s.upCards.take (min n 13) := by
    have hmin := take_min_len s.upCards n
    rwa [Suit.upCards_length] at hmin
  rw [hn, htake, hr]

/-- THE KEY CONSEQUENCE: same rung count, same founded content —
at a fixed height-tuple every fiber member's foundations agree card
for card.  This is why the horizontal world never needs
mixed-residence swaps: foundation-resident content never wiggles
inside a fiber (the only Z-slot-dip-requiring exchanges live between
fibers — neck business, not fiber business). -/
theorem rung_found_congr (w w' : State) (hw : w.WF) (hw' : w'.WF) (s : Suit)
    (h : rungAt w s = rungAt w' s) : w.found s = w'.found s := by
  rw [rung_found_prefix w hw s, rung_found_prefix w' hw' s, h]

/-- Relation to the dance world: every FlatPath embeds as a NET-FLAT
DancePath (the cargo and draw letters are dance legs; licensed
exchanges are single cargo moves by `exch_is_cargo`).  The converse
is the per-leg-honest rerouting content — genuinely stronger, kept
sharp by NOT replacing FlatPath.

The proof is the straight structural mirror: post-merge FlatStep
carries no exchange letter — `cargo` (a `tabToTab`) IS a
`ConeStep.slide` constructor shape and `draw` likewise, so each flat
leg embeds as a cone dance leg, and the net-flat reading follows from
the writers above (a slide/draw writes no foundation, so every leg of
the walk preserves the whole rung tuple). -/
theorem flat_into_dance {w u : State} (h : FlatPath w u) :
    ∃ p : DancePath w u, ∀ s : Suit, rungAt u s = rungAt w s := by
  induction h with
  | refl A => exact ⟨DancePath.refl A, fun _ => rfl⟩
  | @cons A z u2 hs t ih =>
      obtain ⟨dp, hflat⟩ := ih
      cases hs with
      | cargo c b hstep hrev =>
          refine ⟨DancePath.cons (DanceStep.cone (ConeStep.slide c b hstep hrev)) dp, ?_⟩
          intro s
          exact (hflat s).trans (rung_congr_found s (slide_write hstep s))
      | draw hstep hrev =>
          refine ⟨DancePath.cons (DanceStep.cone (ConeStep.draw hstep hrev)) dp, ?_⟩
          intro s
          exact (hflat s).trans (rung_congr_found s (draw_write hstep s))

/-! ### The pull-multiset determinism family

THE NEW THEOREM (nobody has it): the descent-determinism of the
-_pull letter.  The cone's pops are FORCED top-down — a `foundToTab`
leg fires only on the CURRENT FOUNDED TOP (the guard `foundTop =
some c` makes the popped card the rank-next card exactly), and along
a cone descent the rungs only ever fall (pulls chop one suit rung,
slides and draws write no foundation).  So the per-suit pop ledger
of ANY descent from a rank-disciplined anchor is a function of the
PROGRAM'S OWN DATA — the anchor's founded prefix chopped down to the
member's rung — never of the path taken.  Two same-tuple
cone-descendants of one anchor therefore pulled exact card-for-card
equal multisets: the deterministic spine the capstone's horizontal
world runs on (mixed-residence pop histories never arise in-fiber). -/

/-- The forced per-suit pop window: the cards a rank-ordered descent
from founded list `l` down to rung `j` pops, in pop order (top
first — the reverse of the founded prefix's drop). -/
def popWindow (l : List Card) (j : Nat) : List Card := (l.drop j).reverse

/-- A window at or past the end of the list is empty. -/
private theorem window_nil {l : List Card} {j : Nat} (hj : l.length ≤ j) :
    popWindow l j = [] := by
  have hd : (l.drop j).length = 0 := by
    rw [List.length_drop]
    omega
  have hnil : l.drop j = [] := List.eq_nil_of_length_eq_zero hd
  unfold popWindow
  rw [hnil]
  rfl

/-- A window over a snoc pops the snocced card first. -/
private theorem window_snoc {front : List Card} {c : Card} {j : Nat}
    (hj : j < (front ++ [c]).length) :
    popWindow (front ++ [c]) j = c :: popWindow front j := by
  have hl2 : (front ++ [c]).length = front.length + 1 := List.length_append
  have h0 : j - front.length = 0 := by omega
  show (List.drop j (front ++ [c])).reverse = c :: (List.drop j front).reverse
  rw [List.drop_append, h0, List.drop_zero, List.reverse_append,
    List.reverse_singleton, List.cons_append, List.nil_append]

/-- The descent's pop ledger: `ConeLedger p L` says the cone path `p`
pops exactly the cards `L`, pull leg by pull leg (slide and draw legs
append nothing).  The path carrier lives in `Prop`, so the multiset
is carried as a List-indexed inductive RELATION — the collection is
purely structural, and every cone path has one (below). -/
inductive ConeLedger : {A u : State} → ConePath A u → List Card → Prop
  | refl (A : State) : ConeLedger (ConePath.refl A) []
  | pull {A z u : State} (c : Card) (b : Base)
      (hstep : A.step (Move.foundToTab c b) = some z)
      (hrev : reversibleAtW A (Move.foundToTab c b))
      {p : ConePath z u} {L : List Card}
      (hl : ConeLedger p L) :
      ConeLedger (ConePath.cons (ConeStep.pull c b hstep hrev) p) (c :: L)
  | slide {A z u : State} (c : Card) (b : Base)
      (hstep : A.step (Move.tabToTab c b) = some z)
      (hrev : reversibleAtW A (Move.tabToTab c b))
      {p : ConePath z u} {L : List Card}
      (hl : ConeLedger p L) :
      ConeLedger (ConePath.cons (ConeStep.slide c b hstep hrev) p) L
  | draw {A z u : State}
      (hstep : A.step Move.draw = some z)
      (hrev : reversibleAtW A Move.draw)
      {p : ConePath z u} {L : List Card}
      (hl : ConeLedger p L) :
      ConeLedger (ConePath.cons (ConeStep.draw hstep hrev) p) L

/-- Every cone path carries its pop ledger. -/
theorem cone_ledger_of_path {A u : State} (p : ConePath A u) :
    ∃ L, ConeLedger p L := by
  induction p with
  | refl A₀ => exact ⟨[], ConeLedger.refl A₀⟩
  | @cons A₀ z u2 h t ih =>
      obtain ⟨L, hL⟩ := ih
      cases h with
      | pull c b hstep hrev => exact ⟨c :: L, ConeLedger.pull c b hstep hrev hL⟩
      | slide c b hstep hrev => exact ⟨L, ConeLedger.slide c b hstep hrev hL⟩
      | draw hstep hrev => exact ⟨L, ConeLedger.draw hstep hrev hL⟩

/-- The cone runs rung-monotonely downward: per suit, the rung along
a cone descent never rises (a pull chops one suit rung, slides and
draws write no foundation). -/
theorem cone_rung_mono {A u : State} (p : ConePath A u) (s : Suit) :
    rungAt u s ≤ rungAt A s := by
  induction p with
  | refl A₀ => exact Nat.le_refl _
  | @cons A₀ z u2 h t ih =>
      cases h with
      | pull c b hstep hrev =>
          obtain ⟨hlast, hchop, hneW⟩ := pull_write hstep
          have hSu : rungAt z c.suit + 1 = rungAt A₀ c.suit := by
            show (z.found c.suit).length + 1 = (A₀.found c.suit).length
            rw [hchop, chop_len_of_last hlast]
          rcases Decidable.em (s = c.suit) with rfl | hne
          · exact Nat.le_trans ih (by omega)
          · exact Nat.le_trans ih (Nat.le_of_eq (rung_congr_found s (hneW s hne)))
      | slide c b hstep hrev =>
          exact Nat.le_trans ih (Nat.le_of_eq (rung_congr_found s (slide_write hstep s)))
      | draw hstep hrev =>
          exact Nat.le_trans ih (Nat.le_of_eq (rung_congr_found s (draw_write hstep s)))

/-- **THE DESCENT-DETERMINISM MASTER**: along any cone descent from a
prefix-disciplined anchor, the per-suit pop ledger is exactly the
FORCED WINDOW — the anchor's founded prefix chopped down to the
member's rung, top-first.  The popped cards of suit `s`, in pop
order, are `popWindow (A.found s) (rungAt u s)` — a function of the
anchor's founded content and the height-tuple alone, never of the
path taken, its slides, its draws, or its interleavings. -/
theorem cone_pop_window : ∀ {A u : State} (p : ConePath A u) (L : List Card),
    ConeLedger p L → (∀ σ, A.found σ = σ.upCards.take (rungAt A σ)) →
    ∀ s : Suit, (L.filter fun x => decide (x.suit = s)) =
      popWindow (A.found s) (rungAt u s) := by
  intro A u p L hl
  induction hl with
  | refl A₀ =>
      intro hA s
      rw [show popWindow (A₀.found s) (rungAt A₀ s) = []
        from window_nil (Nat.le_refl (A₀.found s).length)]
      rfl
  | @pull A₀ z u2 c b hstep hrev pp L' hl' ih =>
      intro hA s
      obtain ⟨hlast, hchop, hneW⟩ := pull_write hstep
      have hIH := ih (pull_discipline hstep hA)
      rcases Decidable.em (c.suit = s) with rfl | hneq
      · -- the popped suit: the window pops the top card first
        have hsnoc : A₀.found c.suit = chop (A₀.found c.suit) ++ [c] :=
          lastOf_chop hlast
        have hmono := cone_rung_mono pp c.suit
        have hzrung : rungAt z c.suit = rungAt A₀ c.suit - 1 := by
          show (z.found c.suit).length = (A₀.found c.suit).length - 1
          rw [hchop, chop_len_of_last hlast]
          omega
        have hLe : (chop (A₀.found c.suit) ++ [c]).length = rungAt A₀ c.suit :=
          (congrArg List.length hsnoc).symm
        have hlen : (A₀.found c.suit).length = rungAt A₀ c.suit := rfl
        have hpos : 1 ≤ rungAt A₀ c.suit :=
          List.length_pos_of_mem (lastOf_mem hlast)
        have hjlt : rungAt u2 c.suit < (chop (A₀.found c.suit) ++ [c]).length := by
          rw [hLe]
          exact Nat.lt_of_le_of_lt hmono (by rw [hzrung]; omega)
        have hfil : (c :: L').filter (fun x => decide (x.suit = c.suit)) =
            c :: L'.filter (fun x => decide (x.suit = c.suit)) := by
          rw [List.filter_cons]
          simp
        rw [hfil]
        rw [hsnoc]
        rw [window_snoc hjlt]
        rw [← hchop]
        exact congrArg (c :: ·) (hIH c.suit)
      · -- another suit: the head filters out, the window is unchanged
        have hfil : (c :: L').filter (fun x => decide (x.suit = s)) =
            L'.filter (fun x => decide (x.suit = s)) := by
          rw [List.filter_cons]
          simp [hneq]
        rw [hfil, ← hneW s (Ne.symm hneq)]
        exact hIH s
  | @slide A₀ z u2 c b hstep hrev pp L' hl' ih =>
      intro hA s
      have hAz : ∀ σ, z.found σ = σ.upCards.take (rungAt z σ) := by
        intro σ
        rw [slide_write hstep, hA σ]
        rw [rung_congr_found σ (slide_write hstep σ)]
      rw [← slide_write hstep s]
      exact ih hAz s
  | @draw A₀ z u2 hstep hrev pp L' hl' ih =>
      intro hA s
      have hAz : ∀ σ, z.found σ = σ.upCards.take (rungAt z σ) := by
        intro σ
        rw [draw_write hstep, hA σ]
        rw [rung_congr_found σ (draw_write hstep σ)]
      rw [← draw_write hstep s]
      exact ih hAz s

/-- The multiset reading of the master: a card is pulled along the
descent exactly as often as it sits in the forced window (a
multiset-graded equality of pop ledgers — both sides count the same
card populations). -/
theorem cone_pop_countP {A u : State} (p : ConePath A u) {L : List Card}
    (hl : ConeLedger p L)
    (hA : ∀ σ, A.found σ = σ.upCards.take (rungAt A σ)) (c : Card) :
    L.countP (fun x => decide (x = c)) =
      (popWindow (A.found c.suit) (rungAt u c.suit)).countP (fun x => decide (x = c)) := by
  have hwin := cone_pop_window p L hl hA c.suit
  rw [← hwin, List.countP_filter]
  refine List.countP_congr ?_
  intro x _
  by_cases hxc : x = c
  · subst hxc
    simp
  · simp [hxc]

/-- **THE INTRA-ARM FORM**: two cone-descendants of the SAME
prefix-disciplined anchor at the SAME height tuple pulled equal
multisets (the count-function equality — multiset equality for lists
of cards).  The pull history is a function of the descent ANCESTRY
(the shared arm) and the tuple: never of the route.  (Saturation of
the anchor is not load-bearing — any `WF` anchor's pops are forced
by rank order; the saturated-arm reading is the deployed use.) -/
theorem cone_pulls_congr_tuple {A w w' : State} (hwfA : A.WF)
    (p : ConePath A w) (L : List Card) (hp : ConeLedger p L)
    (p' : ConePath A w') (L' : List Card) (hp' : ConeLedger p' L')
    (htup : ∀ s : Suit, rungAt w s = rungAt w' s) (c : Card) :
    L.countP (fun x => decide (x = c)) =
      L'.countP (fun x => decide (x = c)) := by
  have hA : ∀ σ, A.found σ = σ.upCards.take (rungAt A σ) :=
    fun σ => rung_found_prefix A hwfA σ
  have h1 := cone_pop_countP p hp hA c
  have h2 := cone_pop_countP p' hp' hA c
  rw [h1, h2, htup c.suit]

/-- **THE CROSS-ARM RESIDUAL, stated conditionally on the envelope**:
two same-class members at the same height tuple hanging off TWO
saturated anchors pull equal multisets, GIVEN the corridor the
envelope supplies between the arm anchors — the second up to the
conjugate, the envelope's own disjunct shape.

**BLOCKED — gated, kept sorry.**  The corridor hypothesis is the
bridge the envelope exists to provide (`envelope` further down this
file — the decompression card's `mem_macro_iff` output), and its
honest statement runs through the CONJUGATION content — now carried
by the LANDED setoid itself (the relabeled variants are class-mates
by the four-disjunct `r`; the corridor `∃ z, ConePath A₁ z ∧ r z A₂`
names an intermediate flat-reach plus the class identification): between genuinely distinct arms the Final
tuples are fork-flipped (`saturated_tuple_orbit`'s flip branch), and
cone legs are rung-monotone (`cone_rung_mono`), so a literal
cone bridge between the arm anchors cannot exist — the conjugate
corridor is the only route, and pricing it is the envelope card's
business.  Given the corridor plus the conjugate transport, the
comparison closes at the shared arm anchor through
`cone_pop_window` mechanically.  Not provable today; recorded as
this family's residual. -/
theorem cone_pulls_congr_crossarm {A₁ A₂ w w' : State}
    (hwf₁ : A₁.WF) (hwf₂ : A₂.WF)
    (hsat₁ : Final A₁) (hsat₂ : Final A₂)
    (p₁ : ConePath A₁ w) (L₁ : List Card) (hl₁ : ConeLedger p₁ L₁)
    (p₂ : ConePath A₂ w') (L₂ : List Card) (hl₂ : ConeLedger p₂ L₂)
    (htup : ∀ s : Suit, rungAt w s = rungAt w' s)
    (hcorr : ∃ z, ConePath A₁ z ∧ sameOrbitSetoid.r z A₂) :
    ∀ c : Card,
      L₁.countP (fun x => decide (x = c)) =
        L₂.countP (fun x => decide (x = c)) := by
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

/-! ## §4. The canonical face — spec at the fork (the machinery gone)
THE canusList/argmax/choose selector machinery is DELETED
(the 2026-11-11 shape-first redesign: no enumeration, no sort,
no pick).  The face spec now lives in §5 below the fork dossier
it reads: CanonFace — the class stops at its fork, maximally
stacked except the twin pair; both slide-mates qualify; the canon
IS the shape, unique up to the bare cargo exchange — the rigidity
is canonFace_sameShape, a THEOREM (canonFace_sameShape).  -/

/-! ## §6. The fork dossier (the arm layer's topology) -/

/-- **THE FINAL FORK STATE** — the user's iff form: both twins
next-up on their foundations, and the only raising card is x (the
↔ gives maximality → and existence ← in one clause: instantiating
at c = x derives CanRaise st x; Final states have no witness since
the ← direction would force a raise where none exists). -/
def weakForkState (st : State) : Prop :=
  ∃ x, rungAt st x.suit = x.rank.toIdx ∧
    rungAt st x.twin.suit = x.rank.toIdx ∧
    (∀ c, CanRaise st c ↔ c = x)

/-- **THE PAIR UNIQUENESS** — PROVED FROM THE DETECTION ALONE: the
witness of a weakForkState is unique up to the twin flip.  x raises
(the iff's ←-direction); every raiser equals both x and y (the two
iff →-directions); the twin involution closes. -/
theorem finalFork_pairUnique (st : State)
    (h₁ : weakForkState st) (h₂ : weakForkState st) :
    ∃ x y, (rungAt st x.suit = x.rank.toIdx ∧
            rungAt st x.twin.suit = x.rank.toIdx ∧
            (∀ c, CanRaise st c ↔ c = x) ∧
            (y = x ∨ y = x.twin)) := by
  obtain ⟨x, hx₁, hx₂, hiff⟩ := h₁
  obtain ⟨y, _, _, hiffy⟩ := h₂
  have hcx : CanRaise st x := (hiff x).2 rfl
  refine ⟨x, y, ⟨hx₁, hx₂, hiff, ?_⟩⟩
  have hxy : x = y := (hiffy x).1 hcx
  exact Or.inl hxy.symm

/- **THE weakForkState UNIQUENESS** (class-level): within one class,
any two forkStates connect through the CARGO CLOSURE.  Stated in
the FaceShape section below (follows its def). -/

/- **THE CONJUGATE FORK STATE** — the other face of the fork pair, by
the user's PHYSICAL SWAP construction (raise · segment-slide · pull-back):

Before:  pile A: [any (x+1), x]                          ← x bare, raises
         pile B: [other (x+1), x.twin, something]         ← x.twin covered

After:   pile A: [any (x+1), x.twin, something]          ← x.twin at A, still covered
         pile B: [other (x+1), x]                        ← x at x.twin's old seat, bare

THE THREE STEPS:
1. tabToFound x — x goes to its foundation (pile A's seat opens);
2. tabToTab x.twin (with the whole above-segment [x.twin, something])
   from pile B onto pile A's (x+1) under-seat — the ENTIRE SEGMENT
   rides as one tabToTab (the block above x.twin moves together);
3. foundToTab x onto pile B's now-bare (x+1) under-seat — x takes
   x.twin's old seat.

The twins physically TRADE POSITIONS — each taking the other's
under-seat content, maintaining the covering relationship.  The
composite is NET-FLAT (up one rung on x's suit, down one — net-zero)
but PER-LEG DIPPING through the foundation: NOT a pure cargo-composite
(step 1 and 3 change rungs; only step 2 is flat).  This state is
DIFFERENT from the slide-mate (which only moves the cargo without
moving the twins): the physical swap relocates both twin cards.
-/
def conjugateForkState (st w : State) : Prop :=
  ∃ x ba bb st₁ st₂,
    weakForkState st ∧
    st.step (Move.tabToFound x) = some st₁ ∧
    st₁.step (Move.tabToTab x.twin ba) = some st₂ ∧
    st₂.step (Move.foundToTab x bb) = some w

/-- The conjugate is a weakForkState itself (the mate arm live, the
pair-swapped seating preserving the iff).  GATE: the composite's
anatomy derivation — must show the position swap preserves the
three-clause detection (rungs unchanged net, maximality at the
swapped-set state). -/
theorem conjugate_forkState {st w : State}
    (hconj : conjugateForkState st w)
    (hwf : st.WF)
    (hw : sameOrbitSetoid.r st w) :
    weakForkState w := by
  sorry

/- THE CONJUGATE EXISTENCE IFF (the user's necessary-and-sufficient
condition): the physical swap composite fires iff BOTH twins' seats
are valid — either they are KINGS (bare-king vacate: any empty
anchor receives), or BOTH have nonempty under-seat content (the
(x+1) base material beneath them).  If one twin is bare-non-king
(no chop, no king), that twin's seat FAILS the bar: the (Q,J)
finding.  Stated as the seat-package gate, consumed by the
conjugation-weakForkState rows and the conjugation existence theorem
(the anatomy card). -/

/- THE RETIRED CANON-SENSITIVE detector: weakForkState was formerly
"some tabToTab neighbor canon-diverges" — the slide-sensitivity
read.  The new rung reads make the detection local and decidable;
the canon-divergence content lives on as forkedCard (class grade)
and the anatomy rows below consume it.  Consumer updates:
fork_iff_nonUnionable's hwings and wing_crossing_bottleneck cite
the new weakForkState — their premises re-fence at the new read (both
rows sorry'd; the reinterpretation is the honest one: the wings
join through states where the pair runs live). -/

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

/-- **THE DETECTION — the maneuver-stable `forkState`** (the S-grade): the
pair-saturation iff at the {slide · raise} grade, plus the orientation
pin.  The two conjuncts replace the old three (the rung pins travel free
as theorems — `canRaiseS_rung` through the iff, so the old clauses 1–2
are derivable, not premises); the vanilla iff's unique raiser is
derivable from these two as well, making the S-grade strictly stronger
than the retired `weakForkState` (the G2 craft's endpoints are weakForkState
but not forkState — the falsifier family that killed the vanilla
uniqueness rows). See `Orig.ForkStateS` for the flat characterization,
the mate orbit, and the pins-free rows. -/
def forkState (st : State) : Prop :=
  ∃ x, (∀ c, (c = x ∨ c = x.twin) ↔ CanRaiseS st c) ∧
       ¬ CanRaise st x.twin

/-- Saturating completion: `s` is a maximal licensed run from `u`. -/
def saturatesTo (u s : State) : Prop := ∃ l, StackRun u l s ∧ Final s

/-- The cargo reading: `d` TOPS the twin's pile — the twin sits beneath
it, covered by construction. -/
def cargoTop (st : State) (d c : Card) : Prop :=
  ∃ a, st.pileOfTop d = some a ∧ st.pileHolding c = some a

/-- **The fork point with its cargo as first-class witness** — the
V3-CALIBRATED form.  V2 (the floor card's batch-F diagnosis) fixed
the bare twin (vanilla at the point) and the covered pin (premise);
the canon-v3 wake's (Q, J) falsifier analysis found the remaining
under-carried leg — the SEAT: a covered twin sitting BARE-BOTTOM
under its cargo (empty under-seat, non-king) satisfies every V2
conjunct yet cannot lift vanilla once exposed.  V3 adds the seat
premise the trial's own rank arithmetic already wanted: the cargo
sits DIRECTLY on the twin (the run discipline is rank-consecutive
upward — consecutive ranks admit no intermediates, so the
witness-pair shape is honest) and the twin carries the license's
seat package (under-seat content, or a bare king):
`faceUp = bs ++ [x.twin, d]` with `bs ≠ [] ∨ (hidden = [] ∧
king)`.  NO global king restriction — the sandwich's color-family
placement never needs it, and generic-rank forking is honest at
any rank with the seat clause. -/
def forkPointC (st : State) (x d : Card) : Prop :=
  CanRaise st x ∧
  rungAt st x.twin.suit = x.rank.toIdx ∧
  cargoTop st d x.twin ∧
    d.rank.toIdx + 1 = x.rank.toIdx ∧ ¬ twinSuit d.suit x.suit ∧
    ¬ satStackable (Quotient.mk sameOrbitSetoid st) d ∧
    ∃ a bs, st.pileOfTop d = some a ∧
      (st.piles a).faceUp = bs ++ [x.twin, d] ∧
      (bs ≠ [] ∨ ((st.piles a).hidden = [] ∧ x.twin.rank = Rank.king))

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
  obtain ⟨-, -, hcargo, -, hcol, hnsat, -⟩ := hfp
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

/-- A snoc-nodup membership bar: if appending `[d]` keeps the list
duplicate-free, `d` was not in the prefix. -/
private theorem nodup_snoc_notmem : ∀ (bs : List Card) (d : Card) (hnd : (bs ++ [d]).Nodup), d ∉ bs
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

/-- Suit families are colors: a suit outside another's family carries
the OTHER color. -/
private theorem not_twinSuit_colors {s t : Suit}
    (h : ¬ twinSuit s t) : s.color ≠ t.color := by
  rcases s with _ | _ | _ | _ <;>
    rcases t with _ | _ | _ | _ <;>
    simp_all [twinSuit, Suit.twin, Suit.color]

/-- The operational trial, derived: the twin's swap-raise realizes

CLOSED AT THE V3 BASE (the canon-v3 wake directive, amr_12aaf07c1):
the (Q, J) falsifier analysis found the V2 under-carried leg — the
exposed twin's SEAT (a bare-bottom non-king twin lifts nothing) —
and V3 carries it as the premise it always was: the cargo sits
DIRECTLY on the twin (the run discipline is rank-consecutive
upward, so the consecutivity the trial's own arithmetic proves is
now the witness shape) and the twin carries the seat package
(under-seat content or a bare king).  The proof is the mechanical
decomposition this file's engines always wanted: the fire
(pile-holding by membership uniqueness, place by rank and color),
the successor read (the moved run is exactly the singleton [d],
the source pile keeps [bs, x.twin] so the twin EXPOSES as the new
top), and the license (rungs never written by the cargo slide, the
twin pin is the premise, the seat bar is the premise).  -/
theorem forkPoint_trial {st : State} {x : Card} (hwf : st.WF) (h : forkPoint st x) :
    ∃ d st', st.step (.tabToTab d (Sum.inr x)) = some st' ∧
      CanRaise st' x.twin ∧ d.rank.toIdx + 1 = x.rank.toIdx := by
  obtain ⟨d, hCan, htwinpin, hcargo, hrank, hcol, hnsat, hseat⟩ := h
  obtain ⟨hn, a₀, hpj, hs₀⟩ := hCan
  obtain ⟨a, bs, htopd, hfaceup, hseatbar⟩ := hseat
  -- the pile pieces
  have hpa : (st.piles a).top = some d := (pileOfTop_top htopd).2
  have hmem : d ∈ (st.piles a).faceUp := by
    rw [hfaceup]
    exact List.mem_append.mpr (Or.inr
      (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl))))
  have hdnet : d ≠ x.twin := by
    intro hcon
    exact hcol (by rw [hcon]; exact Or.inr rfl)
  have hxnet : x.twin ≠ x := by
    intro hcon
    have hs : x.suit.twin = x.suit := congrArg Card.suit hcon
    exact Suit.twin_ne x.suit hs
  have hdne : d ≠ x := by
    intro hcon
    rw [hcon] at hrank
    omega
  -- the duplicate-free walk bar (the run discipline keeps the pile
  -- duplicate-free, and the cargo sits at its end)
  have hnd0 : ((bs ++ [x.twin]) ++ [d]).Nodup := by
    have h := runOK_nodup (hwf.2.1 a)
    rw [hfaceup,
      show bs ++ [x.twin, d] = (bs ++ [x.twin]) ++ [d] from
        (congrArg (bs ++ ·)
          (show [x.twin, d] = [x.twin] ++ [d] from rfl)).trans
        (List.append_assoc bs [x.twin] [d]).symm] at h
    exact h
  have hdnotmem : d ∉ bs ++ [x.twin] := by
    intro hcon
    rcases List.mem_append.mp hcon with hbs | hlast
    · exact nodup_snoc_notmem (bs ++ [x.twin]) d hnd0
        (List.mem_append.mpr (Or.inl hbs))
    · exact hdnet (List.mem_singleton.mp hlast)
  -- the walk: the source pile keeps [bs, x.twin]; the moved run is [d]
  have hpre : below d ((bs ++ [x.twin]) ++ [d]) = bs ++ [x.twin] :=
    below_append_stop hdnotmem
  have hfrom : fromCard d ((bs ++ [x.twin]) ++ [d]) = [d] :=
    fromCard_append_stop hdnotmem
  -- THE FIRE (the guards all pass)
  have hhold : st.pileHolding d = some a := (pileHolding_eq_some_iff hwf).2 hmem
  have hcol1 : d.suit ≠ x.suit := fun hcon => hcol (Or.inl hcon)
  have hcol2 : d.suit ≠ x.suit.twin := fun hcon => hcol (Or.inr hcon)
  have hcolne : d.suit.color ≠ x.suit.color := not_twinSuit_colors hcol
  have hplace : st.canPlace d (Sum.inr x) = true := by
    show (match st.pileOfTop x with
      | some _ => canSitOn d x
      | none => false) = true
    rw [hpj]
    exact (canSitOn_eq d x).2 ⟨hrank, hcolne⟩
  have hfire : ∃ s', State.step st (Move.tabToTab d (Sum.inr x)) = some s' := by
    have hne : fromCard d (st.piles a).faceUp ≠ [] := by
      rw [hfaceup,
        show bs ++ [x.twin, d] = (bs ++ [x.twin]) ++ [d] from
          (congrArg (bs ++ ·)
            (show [x.twin, d] = [x.twin] ++ [d] from rfl)).trans
          (List.append_assoc bs [x.twin] [d]).symm,
        hfrom]
      simp
    refine ⟨(st.setPile a
        (Pile.afterRunRemoved (st.piles a) (below d (st.piles a).faceUp))).putRun
      (fromCard d (st.piles a).faceUp) (Sum.inr x), ?_⟩
    simp only [State.step, hhold, hplace]
    cases hList : fromCard d (st.piles a).faceUp with
    | nil => exact absurd hList hne
    | cons w r => rfl
  obtain ⟨s', hstep'⟩ := hfire
  refine ⟨d, s', hstep', ?_, hrank⟩
  -- THE SHAPE: read the successor through the inverse row
  obtain ⟨a₁, hh₁, hcp₁, hfr₁, hseq⟩ := step_tabToTab_inv hstep'
  rw [show a₁ = a from Option.some.inj (hhold.symm.trans hh₁).symm] at hseq
  sorry -- THE EXPOSURE AND LICENSE REMAIN, staged next pass

/-- The pin lemma: at the fork point, BOTH same-color rungs sit at the
pair rank — the bare twin's pin by `stackable_now_rungexact`, the
covered twin's pin by the cargo/cascade arithmetic.

CLOSED AT THE V2 BASE (the batch-F calibration): the covered twin's
pin enters as the signature's own premise, and the bare twin's pin
is the banked one-directional calibration row.  The earlier BLOCKED
note (the covered pin "unreachable from these hypotheses alone")
described the PRE-v2 signature — before the twin-rung premise
landed — and is retired. -/
theorem forkPoint_pins (st : State) (x : Card)
    (h : forkPoint st x) :
    rungAt st x.suit = x.rank.toIdx ∧ rungAt st x.twin.suit = x.rank.toIdx := by
  -- CLOSED at the v2 base (the batch-F calibration): the covered
  -- twin's pin enters as the signature's own premise; the bare
  -- twin's pin is the banked one-directional calibration row
  -- (the license's nextUp leg is rank-exact).  The earlier
  -- BLOCKED note (the covered pin "unreachable from these
  -- hypotheses alone") described the PRE-v2 signature and is
  -- retired by the premise's own landing.
  obtain ⟨d, hC⟩ := h
  obtain ⟨hCan, htwin, hcargo, hrank, hcol, hstrand, hseat⟩ := hC
  exact ⟨stackable_now_rungexact st x hCan, htwin⟩

/-- `twinSuit` is symmetric (same-color family membership). -/
private theorem twinSuit_symm {a b : Suit} (h : twinSuit a b) : twinSuit b a := by
  rcases h with h' | h'
  · exact Or.inl h'.symm
  · refine Or.inr ?_
    rw [h', Suit.twin_twin]

/-- Four suits, two color families: a suit outside `b`'s family and
outside... — precisely: if `a` shares no family with `b`, and `b`
shares no family with `c`, then `a` is IN `c`'s family. -/
private theorem suitfamily_antipodal {a b c : Suit}
    (hab : ¬ twinSuit a b) (hbc : ¬ twinSuit b c) : twinSuit a c := by
  rcases a with _ | _ | _ | _ <;>
    rcases b with _ | _ | _ | _ <;>
    rcases c with _ | _ | _ | _ <;>
    simp_all [twinSuit, Suit.twin]

/-- The cross-pinch arithmetic of the sandwich: a cargo `d` inside
`w`'s color family (same family as the OTHER fork's pair), one rank
below `z`'s pair rank, stranded strictly below its own rank, against
`w`'s pins at its own pair rank: Rw + 2 ≤ Rz. -/
private theorem cross_pin {st : State} {d z w : Card}
    (hfam : twinSuit d.suit w.suit) (hrank : d.rank.toIdx + 1 = z.rank.toIdx)
    (hp1 : rungAt st w.suit = w.rank.toIdx)
    (hp2 : rungAt st w.twin.suit = w.rank.toIdx)
    (hstrand : rungAt st d.suit < d.rank.toIdx) :
    w.rank.toIdx + 2 ≤ z.rank.toIdx := by
  rcases hfam with h | h
  · rw [h] at hstrand
    have hA : rungAt st w.suit = w.rank.toIdx := hp1
    omega
  · rw [h] at hstrand
    have hA : rungAt st (w.suit.twin) = w.rank.toIdx := hp2
    omega

/-- **The exclusivity sandwich** (the user's rank-arithmetic proof):
CLOSED at the canon-v3 wake (amr_12a492e2) — the v2 base made the
covered pins PREMISES (retiring the original BLOCKED note, which
described the pre-v2 signature) and the cargo strands are in-file
engines, so the sandwich consumes exactly: the pins of both forks
(each pair's suits at its pair rank — the bare pin by the banked
one-directional calibration, the covered pin by the premise), the
strands of both cargos (strictly below their own ranks,
`forkPoint_cargo_strand`), the color-family placement (each cargo,
opposite-colored to its OWN pair by the ¬twinSuit leg, is
same-colored as the OTHER fork's pair — four suits, two families),
and `omega`.  The cross-pinch: Ry + 2 ≤ Rx ∧ Rx + 2 ≤ Ry. -/
theorem forkPoint_exclusive (st : State) (x y : Card) (hwf : st.WF)
    (hcol : ¬ twinSuit x.suit y.suit)
    (hx : forkPoint st x) (hy : forkPoint st y) : False := by
  -- CLOSED (the canon-v3 wake, amr_12a492e2): the v2 base makes
  -- the covered pins premises and the strands in-file engines —
  -- the user's rank sandwich consumes exactly those.  Each
  -- fork's cargo is opposite-colored to its OWN pair (the
  -- ¬twinSuit leg), hence same-colored as the OTHER fork's pair
  -- (four suits, two color families); so the x-fork's cargo
  -- sits inside y's pair suits, where y's pins hold the rung AT
  -- the pair rank, while the x-strand demands it strictly BELOW
  -- x's pair rank — and symmetrically.  The two strict
  -- inequalities cross-pinch: Ry + 2 ≤ Rx ∧ Rx + 2 ≤ Ry.
  obtain ⟨dx, hCanx, htpinx, hcargox, hrankx, hcolx, hstrandx, hseatx⟩ := hx
  obtain ⟨dy, hCany, htpiny, hcargoy, hranky, hcoly, hstrandy, hseaty⟩ := hy
  have hCx : forkPointC st x dx :=
    ⟨hCanx, htpinx, hcargox, hrankx, hcolx, hstrandx, hseatx⟩
  have hCy : forkPointC st y dy :=
    ⟨hCany, htpiny, hcargoy, hranky, hcoly, hstrandy, hseaty⟩
  have hsx := forkPoint_cargo_strand hwf hCx
  have hsy := forkPoint_cargo_strand hwf hCy
  have hpx := stackable_now_rungexact st x hCanx
  have hpy := stackable_now_rungexact st y hCany
  have hfamx : twinSuit dx.suit y.suit := suitfamily_antipodal hcolx hcol
  have hfamy : twinSuit dy.suit x.suit :=
    suitfamily_antipodal hcoly (fun h => hcol (twinSuit_symm h))
  have kx := cross_pin hfamx hrankx hpy htpiny hsx
  have ky := cross_pin hfamy hranky hpx htpinx hsy
  omega

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
    (hwings : ∃ st, weakForkState st ∧
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
    ∃ st₁, Journey u st₁ ∧ weakForkState st₁ ∧ Journey st₁ v := by
  sorry


/-! ## §5. THE CANONICAL FACE — the class's shape, spec-first

(The user's 2026-11-11 design, FINAL FORM: the canonical state STOPS AT
THE FORK — maximally stacked except the twin pair.  The face is
FLEXIBLE: both slide-mates qualify; the class's canon is the SHAPE,
and shape-rigidity is a THEOREM below (canonFace_sameShape), not a
hidden definitional pick.  No enumeration, no sort, no argmax fold,
no arm choice — the two fork wings stay legible and unbiased.) -/

/-- Maximally stacked except the twin pair: every licensed raise at
w is a pair member.  The benign pattern is the ∅ case: a Final state
has NO licensed raises — maximal except nothing. -/
def OnlyPairLicensed (w : State) (x : Card) : Prop :=
  ∀ c, CanRaise w c → c = x ∨ c = x.twin

/-- THE CARGO CLOSURE — the flat world's cargo letter alone (no
draws: phase stays pinned).  By `exch_is_cargo` every licensed
twin swap realizes as ONE cargo move, so slides and free twin
swaps are the SAME letter here.  THE TWO-TIER GUARANTEE (the
user's refinement, explicit): (i) exposed free pairs swap in
one reversible leg; (ii) BURIED twins swap COMPOSITELY when
their covers relocate freely (slide-cover-aside, swap, slide-
back — each leg separately reversible, so the whole route is
in the closure without the banked exchange machinery, and the
both-occupied TwinExchOK gap is irrelevant here); (iii) the
reveal bar is enforced by reversibleAtW ITSELF — a leg whose
departure fires the hidden flip is a commit (reveals never
re-arm, canlaw's boundary), refuses, and the shape correctly
excludes it: free swaps in, reveal-causing out. -/
inductive CargoPath : State → State → Prop
  | refl (w : State) : CargoPath w w
  | cons {w z w' : State} (h : FlatStep w z)
      (hkind : ∃ c b hstep hrev, h = FlatStep.cargo c b hstep hrev)
      (t : CargoPath z w') : CargoPath w w'

/-- **THE FACE SHAPE** (the user's final corrected composition): the
cargo closure ALONE (same face), OR the conjugate composite
CROSSED-BRIDGE plus cargo within the dual face:
   same-face:   CargoPath w w'
   cross-face:  conjugateForkState w z (the physical swap) then
               CargoPath z w' (within the dual face's orbit).
The conjugate is the ONE step that crosses between the two face
orbits; all other state-difference is cargo within each orbit. -/
def FaceShape (w w' : State) : Prop :=
  CargoPath w w' ∨ ∃ z, conjugateForkState w z ∧ CargoPath z w'

/-! ## §7. THE FORK-STATE SPECTRUM (the user's simplified characterization)

THE THREE GENERATORS: the game's OWN rules are the only constraint
—the foundation-stack discipline already prevents worrying back.
The spectrum of all forkStates of a class is the closure under
three named structural generators:

1. TWIN SWAP: conjugateForkState (the pair swap, always when
   the seat precondition holds)
2. PARENT SWAP: the (x+1) under-seat cards trade between twins
   — sometimes, when the alternating-color condition is right
3. CARGO SWAP: CargoPath (the reversible-cargo closure, always)

THE COMPLETENESS theorem: every weakForkState of the class is in
this three-generator closure (see ForkSpectrum.lean for the
proof — the raise-pull pair cancellation + the game's own
stack discipline). -/

/-- The fork spectrum: the closure of a starting weakForkState under
the three generators — the twin swap bridge + the parent swap
and the cargo closure within and across the bridge.  Read at the
states where the weakForkState detection fires. -/
inductive ForkSpectrum : State → State → Prop
  | base (st : State) : ForkSpectrum st st
  | twinSwap {st w w' : State}
      (hc : conjugateForkState st w)
      (t : ForkSpectrum w w') : ForkSpectrum st w'
  | parentSwap {st w w' : State}
      (hp : st = w ∧ True) -- the conditional (x+1) parent trade: to be instantiated
      (t : ForkSpectrum w w') : ForkSpectrum st w'
  | cargo {st w w' : State}
      (h : CargoPath st w)
      (t : ForkSpectrum w w') : ForkSpectrum st w'

/-- **THE SPECTRUM COMPLETENESS** — every weakForkState of the class
is in the three-generator closure from any starting forkState. -/
theorem forkSpectrum_complete (st : State) (hwf : st.WF)
    (hfs : weakForkState st) (w : State)
    (hcls : sameOrbitSetoid.r st w) (hwfs : weakForkState w) :
    ForkSpectrum st w := by
  sorry

/-! ## §7. THE FORK-STATE SPECTRUM (the user's simplified characterization)

THE THREE GENERATORS: the game's OWN rules are the only constraint
(the foundation-stack discipline already prevents worrying back —
foundToTab only pops the current top).  The spectrum of all
forkStates of a class is the closure under three named structural
generators — no artificial move-language restriction:

1. TWIN SWAP: conjugateForkState (the pair trade positions,
   taking each other's under-seat, the covering following)
2. PARENT SWAP: the (x+1) under-seat cards trade between the
   twins' two piles — sometimes available (the positive color
   check: both (x+1)s must fit the alternating-color discipline
   at the traded positions — one from each opposing color)
3. CARGO SWAP: CargoPath (the full reversible-cargo closure)

The COMPLETENESS theorem: every weakForkState of the class is in this
three-generator closure from any starting forkState.  The proof:
raise-pull pair cancellation + the game's stack discipline
(buried non-pair cards can't come back — the rank-ordered stack
is the autonomous restriction). -/

/-- The parent swap: the (x+1) under-seat cards of the twins'
piles trade positions.  Occurs when the color discipline permits
it (the two (x+1) cards are from opposite-color families and
neither violates the stacking fit at the swapped position). -/
/- The parentSwap concept is carried by the ForkSpectrum.parentSwap
constructor: the (x+1) trade between the twins' piles when the
alternating-color discipline permits. Its full formalization (the
fit-side conditions, the tabToTab composite semantics) is the
spectrum card's territory. -/

inductive CanonFace (u w : State) : Prop
  | benign (hwf : u.WF) (hfin : Final w) (hw : w = canon u)
      (hnofork : ∀ st, sameOrbitSetoid.r (canon u) st →
                   ∀ x, ¬ (rungAt st x.suit = x.rank.toIdx ∧
                           rungAt st x.twin.suit = x.rank.toIdx ∧
                           (CanRaise st x ∨ CanRaise st x.twin)))
  | forked (hwf : u.WF)
      (hclass : sameOrbitSetoid.r (canon u) w)
      (hfins : weakForkState w)

/-- Faces exist: the benign case is canon u itself; the forked case
is the saturation-until-pair-only stop (the realization: canon,
then undo the founding pair-lift when the fork read is live). -/
theorem canonFace_exists (u : State) (hwf : u.WF) :
    ∃ w, CanonFace u w := by
  sorry

/-- Faces are class members (benign: canon_in_class; forked: the
class-link conjunct + transitivity). -/
theorem canonFace_mem (u w : State) (hwf : u.WF)
    (h : CanonFace u w) : sameOrbitSetoid.r u w := by
  sorry

/-- Shape-mates are class-mates (the slide is a reversible dance
leg; identical is reflexive). -/
theorem faceShape_rel (w w' : State)
    (h : FaceShape w w') : sameOrbitSetoid.r w w' := by
  sorry

/-- **THE SHAPE THEOREM** — THE canon IS the shape: any two faces of
one class share ONE shape (identical or slide-mates).  The rigidity
that other designs baked into definitions lives HERE as a theorem —
the benign half rides canon_unique; the forked half is the ≤2
sandwich content, the pins and exclusivity doing their work. -/
theorem canonFace_sameShape (u w w' : State) (hwf : u.WF)
    (h : CanonFace u w) (h' : CanonFace u w') : FaceShape w w' := by
  sorry

/-- The face is class-invariant: class-mates see the same faces
(the benign constancy is canon_unique; the forked pair is the
class's own fork). -/
theorem canonFace_class_inv (u v : State) (hu : u.WF) (hv : v.WF)
    (h : sameOrbitSetoid.r u v) (w : State) :
    CanonFace u w → CanonFace v w := by
  sorry

/-- **THE MAIN GOAL, SHAPE-FORM**: two states are the same macro
class IFF their faces coincide as shapes — every u-face
share-shapes with every v-face.  (⇐: a shared shape is r-related
(faceShape_rel) and faces are class members (canonFace_mem); the
class composition closes.  ⇒: canonFace_class_inv + the benign/
forked cases.) -/
theorem canonFace_iff (u v : State) (hu : u.WF) (hv : v.WF) :
    sameOrbitSetoid.r u v ↔
      ∀ w w', CanonFace u w → CanonFace v w' → FaceShape w w' := by
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
    ∃ z, ConePath (canon u) z ∧ sameOrbitSetoid.r z v := by
  sorry

/-! ## §8. Canonical-index echo (for the selector's proofs) -/

/- The canonKey echo retired (the 2026-11-11 cleanup): canonKey IS
`canonFormalKey` definitionally — the old `[rungs…, posKey w]` echo
died with the posKey stub; CanV3's own key rows are the public home. -/

/-! ## The floor-row audit
(#print axioms on each newly proved floor head — expected
[propext, Quot.sound]; anything else flagged.)

FLAGGED rows (post-cleanup): the sorry surface rides the ONE carrier
– `canusList` (the enumeration BFS, the deep row's def-stub) – and the
gated theorems consuming it: `canusList_sound`, `canusList_complete`,
`canusOf_class_inv`, `canonV3_mem/_final/_max`, and the §5 main-goal
block.  `canusOf_nonempty` now consumes the contract stub (the old
statement-level conjl flag ended with the carrier's deletion; the
statement type is now conjl-free; the sorry rides the proof's cite of
the complete contract).  Everything else audits within
[propext, Quot.sound]. -/

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
/- canusOf_nonempty retired with the canusList deletion — the face
design's existence row is canonFace_exists (its audit lands with its
proof). -/
#print axioms piled_rung
#print axioms canRaiseS_rung_pin
#print axioms forkPoint_cargo_strand
/-! ## The determinism battery rows — leaf audits

`#print axioms` for this branch's fresh rows, per the house rule
(battery at the leaf: `lake env lean Orig/MacroInternal.lean` —
this module is deliberately NOT wired into `lake build Orig`, whose
root `Orig.lean` imports none of it).  The cross-arm residual is
audited too, and shows its `sorryAx` — that row is gated on the
envelope (its docstring records the owner); every other fresh row
must come out clean. -/

#print axioms rung_found_prefix
#print axioms rung_found_congr
#print axioms flat_into_dance
#print axioms cone_ledger_of_path
#print axioms cone_rung_mono
#print axioms cone_pop_window
#print axioms cone_pop_countP
#print axioms cone_pulls_congr_tuple
#print axioms cone_pulls_congr_crossarm
