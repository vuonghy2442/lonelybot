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
`dance_inClass` below.  (Public since the 2026-10-17 dossier
archive: the relocated strand row consumes it from
`Orig.ForkDossier.lean`.) -/
theorem class_leg {st s₁ : State} {m : Move}
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
    (h : rungAt w s = rungAt w' s) : w.found s = w'.found s :=
  FoundKit.found_congr w w' hw hw' s h

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

/-! THE CROSS-ARM CARGO-COUNT CONGRUENCE now lives in
`Orig.ConeCrossarm` (the same-package leaf): the mechanical half
landed sorry-free (`cone_pulls_congr_crossarm_of_anchorRungs`), and the
one named gate (`crossarm_anchor_agree` — the de-flip classification
tier rests on the corridor evidence) carries the residual the docstring
below priced for years. -/

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

/-- **THE RETIRED VANILLA-GRADE DETECTION** (`weakForkState`, the
pre-migration `forkState`): both twins next-up on their foundations,
and the only VANILLA-raising card is x (the ↔ gives maximality → and
existence ← in one clause).  RETIRED as the detection by the S-grade
migration: the canonical `def forkState` (beside `CanRaiseS` above)
subsumes this form — every clause here is a theorem of the strong def
(`Orig.ForkWeaker.forkState_to_weak`, same witness) while the
converse fails (the G2 craft's endpoints satisfy this form but are
not forkStates — the falsifier family that killed the vanilla
uniqueness rows).  This def stays as the weak consumer interface for
the pre-migration rows. -/
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

/- **THE RETIRED weakForkState-UNIQUENESS FORMULATION** (truespeaked
2026-10-17, the old ad-hoc conjugate-case card): the claim —
within one class, any two forkStates connect through the CARGO
CLOSURE — is REFUTED at theorem grade (the G2 craft,
`Orig/ForkStateUniqGate`; the negation row retired at the
2026-10-17 stale-grade strike, the verdict on ledger record —
CHALLENGES.md REFUTED tier).  `FaceShape` below stays as the
canonFace-chain interface; `conjugateForkState` stays as the
conjugate-composite record the S-grade siblings consume. -/

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
swapped-set state).

2026-10-17 VERDICT TRUING (the surgical session): this SEAT-LESS shape
is refuted at the probe grade — `Orig/ConjugateProof.lean` §6's probe-B
records (the (Q,J) corner: the composite fires, the endpoint carries
TWO raisers, not a weakForkState; the theorem-grade
`conjugate_corner_notForkState` there remains staged future work).
The honest seat-carrying closure is banked DOWNSTREAM as
`conjugate_forkState_corrected` (`Orig/ConjugateProof.lean:532`, the
`TwinSeat` seat premise, audited), reachable only through
`Orig.ForkStateUniq`, which imports THIS file — import-invisible here.
The MI-grade honest content is landed as the composite rows of §9
below: the per-leg-reversibility class row and the composite's
net-flat rung arithmetic.  This row keeps its sorry as the residue of
the seat-less statement, per the house REFUTED discipline. -/
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

/- THE FORK-POINT PROGRAM — RELOCATED (the 2026-10-17 owner archive
decision): `cargoTop`, `forkPointC` (the V3-calibrated form),
`forkPoint`, `afterFork`, `PairCfg`, the seven frozen dossier
targets (`forkedCard_iff_forkPoint`, `forkPoint_classifies`,
`fork_threeCases`, `fork_threeCards`, `afterFork_fewFinals`,
`afterFork_neckReachable`, `forkPoint_trial`), and the proved
satellites (`forkPoint_pins`, `forkPoint_exclusive`, with the
private kit) moved VERBATIM to `Orig/ForkDossier.lean` —
statements byte-identical, the frozen sorries riding along.  The
arm language `forkedCard` STAYS HERE (the cross-arm rows at
`Orig/ConeCrossarm.lean` state themselves in it;
`benign_sat_iff_surely`'s premise reads it), as does
`canRaiseS_rung_pin` (the S-tier evidence row; public replica
`Orig.ForkStateS.canRaiseS_rung`). -/

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

/-! ### The S-tier private engine row
(The one private engine row that stayed when the fork dossier
relocated to `Orig/ForkDossier.lean` at the 2026-10-17 archive: the
license rung pin, whose public replica is
`Orig.ForkStateS.canRaiseS_rung`.) -/

/-- The bare twin's exact pin, along the swap-grade cascade: the
vanilla license at the cascade's far end is rung-exact
(`stackable_now_rungexact`, the calibrated row), and the cascade's
cargo slides never write foundations (the battery's tabToTab
non-write) — so the rung already sits at the pair rank at the point
itself.  (The forkPoint dossier's frozen records relocated to
`Orig.ForkDossier`; this S-tier row stays as the pins' derivable
half.) -/
private theorem canRaiseS_rung_pin {st : State} {x : Card} (h : CanRaiseS st x) :
    rungAt st x.suit = x.rank.toIdx := by
  induction h with
  | now c hcan => exact stackable_now_rungexact _ c hcan
  | via c hl _h2 ih =>
      obtain ⟨d, b, hstep, -⟩ := hl
      have hr := (step_tabToTab_rungs hstep) c.suit
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

/- THE FORK-STATE SPECTRUM — RETIRED (the 2026-10-17 cleanup): the
`ForkSpectrum` inductive and the `forkSpectrum_complete` stub are
DELETED — the completeness row was refuted and sealed at both grades
(2026-10-11, the third landing (rung) and the fourth (phase) of the
falsifier family), and the unconsumed proof leaf
`Orig/ForkSpectrumProof.lean` was deleted with them.  The never-retry
fence stays at CHALLENGES.md (the statement-family lesson: a
foundation-flat generator language cannot reach different-rung
forkStates; add a raise letter); the session record at
FARM_MEMORY.md.  The generators stay in-tree under their own names:
`conjugateForkState` (the twin swap), `CargoPath` (the cargo
closure), and the §9 composites (`conjugateCompositeRev`) the
living rows read. -/

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

FLAGGED rows (2026-10-17 sorry-map truing: the pre-redesign `canusList`
carrier and its consumer rows were DELETED with the shape-first
redesign and no longer exist; the 2026-10-17 spectrum cleanup
likewise deleted the `forkSpectrum_complete` stub — the retirement
note sits at the former §7; and the 2026-10-17 dossier archive
RELOCATED the fork-point program — `forkPointC`, `forkPoint`,
`PairCfg`, `afterFork`, the seven frozen dossier targets, and the
sandwich/pins satellites — VERBATIM to `Orig/ForkDossier.lean`,
their seven sorries riding along there): the current sorry surface
is 16 tactic-level sorries in five tiers — the blocked floor row
(`founded_implies_atRung`, envelope-gated); the fiber/orbit tier
(`fiber_iff_flat`, `finals_topFibers`); the conjugate row
(`conjugate_forkState` — the seat-less shape refuted at the probe
grade, see its docstring); the fork-journey tier
(`unionable_iff_unionTuple`, `fork_iff_nonUnionable`,
`wing_crossing_bottleneck`); and the canonical-face/classification
block (`canonFace_exists`, `canonFace_mem`, `faceShape_rel`,
`canonFace_sameShape`, `canonFace_class_inv`, `canonFace_iff`,
`saturated_tuple_orbit`, `saturated_classification`, `envelope`).
The battery audits the PROVED heads only — every other row lands
within [propext, Quot.sound], and the fresh §9 heads are audited in
their own inline battery below. -/

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
#print axioms canRaiseS_rung_pin
/- piled_rung and forkPoint_cargo_strand audited at the archive leaf
(`Orig/ForkDossier.lean`) after the 2026-10-17 relocation. -/
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
-- (the cross-arm row now lives in Orig.ConeCrossarm; its audit lives there)

/-! ## §9. The surgical rows (2026-10-17 session, the recon-surgical landings)

Two fronts landed at MI grade, both shaped by the import graph: the
CONJUGATE anatomy's derivable legs and FACE-SHAPE's mechanical
strands.  The seat-carrying corrected closure itself is
import-invisible (its home consumes this file through
`Orig.ForkStateUniq`), so what lands HERE is the honest in-file
residue of that grade: the composite's class and rung content at the
per-leg-reversibility premise shape, the cargo closure's class row
(the in-tree mechanical mirror of the strand `Orig.ForkStateUniq`
banks as `cargoPath_class`), their faceShape cross-face combination,
and the canonical-face kernel — the FULL `canonFace_mem` content, the
BENIGN/FORKED NO-MIX census (`canonFace_sameKind`, which collapses
`canonFace_sameShape`'s case split to the within-kind cases), and
the shape reflexivity.  The frozen statements above keep their
sorries; every head here is additive, zero `Classical.choice`, and
consumes no sorried row.  Wave-3 adds the forked-cell completion
below (§9.6) — the degenerate-support converter
(`conjugateCompositeRev_forkState`), the composite's class+rungs
midpoint row (`conjugateCompositeRev_midpoint`), and the FORKED-CELL
r-transport and share-shape twins (`canonFace_class_inv_forked`,
`canonFace_sameShape_forked`) finishing the wave-2 benign
pair-lift's census. -/

/-- **THE SEAT-CARRYING COMPOSITE AT MI GRADE** — the corrected
conjugation's firing shape, restated minimally: the three physical
steps of `conjugateForkState`, each with its witnessed REVERSIBILITY
(the premise the seat packages of the downstream corrected theorem
carry operationally — the undos that make every leg a class leg). -/
def conjugateCompositeRev (st w : State) : Prop :=
  ∃ (x : Card) (ba bb : Base) (st₁ st₂ : State),
    st.step (Move.tabToFound x) = some st₁ ∧
    st₁.step (Move.tabToTab x.twin ba) = some st₂ ∧
    st₂.step (Move.foundToTab x bb) = some w ∧
    reversibleAtW st (Move.tabToFound x) ∧
    reversibleAtW st₁ (Move.tabToTab x.twin ba) ∧
    reversibleAtW st₂ (Move.foundToTab x bb)

/-- **THE COMPOSITE'S NET-FLAT RUNG CONTENT** (the anatomy's rung leg,
unconditional on seats — the steps alone price it): up one on `x`'s
suit at the raise, flat across the segment slide, down one at the
giveback — every suit's rung lands where it started. -/
theorem conjugateComposite_rungs {st w : State} {x : Card} {ba bb : Base}
    {st₁ st₂ : State}
    (hstep₁ : State.step st (Move.tabToFound x) = some st₁)
    (hstep₂ : State.step st₁ (Move.tabToTab x.twin ba) = some st₂)
    (hstep₃ : State.step st₂ (Move.foundToTab x bb) = some w) :
    ∀ s : Suit, rungAt w s = rungAt st s := by
  obtain ⟨hup, hothers₁⟩ := step_tabToFound_rungs hstep₁
  have hflat₂ := step_tabToTab_rungs hstep₂
  obtain ⟨hdown, hothers₃⟩ := step_foundToTab_rungs hstep₃
  intro s
  by_cases hs : s = x.suit
  · rw [hs]
    have h₂ := hflat₂ x.suit
    omega
  · have h₁ := hothers₁ s hs
    have h₂ := hflat₂ s
    have h₃ := hothers₃ s hs
    omega

/-- **THE COMPOSITE'S CLASS LEG** (the anatomy's membership leg at the
seat-carrying grade): a composite whose every leg is reversible stays
in one macro class — the premise content the downstream
`conjugate_forkState_corrected` derives from its `TwinSeat` package. -/
theorem conjugateComposite_class {st w : State}
    (h : conjugateCompositeRev st w) :
    sameOrbitSetoid.r st w := by
  obtain ⟨x, ba, bb, st₁, st₂, h₁, h₂, h₃, hr₁, hr₂, hr₃⟩ := h
  exact class_trans (class_leg hr₁ h₁)
    (class_trans (class_leg hr₂ h₂) (class_leg hr₃ h₃))

/-- **THE CARGO CLOSURE'S CLASS ROW** — the mechanical strand of the
in-tree `faceShape_rel`, mirrored here from `Orig.ForkStateUniq`'s
`cargoPath_class` (banked there downstream, import-invisible): every
cargo leg carries its own `reversibleAtW`, so the closure composes
through the loop-closure engine. -/
theorem cargoPath_inClass {w u : State} (h : CargoPath w u) :
    sameOrbitSetoid.r w u := by
  induction h with
  | refl s => exact RevEqW_refl s
  | @cons st₀ z u₂ hstep hkind _t ih =>
      obtain ⟨c, b, hfire, hrev, -⟩ := hkind
      exact class_trans (class_leg hrev hfire) ih

/-- **THE CROSS-FACE STRAND, GATE EXPLICIT** — `faceShape_rel`'s
cross-face arm at the narrowest true form: a reversible composite
into the conjugate, then cargo inside the dual face — the two
mechanical legs of the shape relation, with the seat gate carried as
the premise it is. -/
theorem faceShape_cross_inClass {w z w' : State}
    (hc : conjugateCompositeRev w z) (hp : CargoPath z w') :
    sameOrbitSetoid.r w w' :=
  class_trans (conjugateComposite_class hc) (cargoPath_inClass hp)

/-- The shape relation's reflexivity (the identical-face case of every
intended consumer — the benign-pair cell of the shape theorem). -/
theorem faceShape_refl (w : State) : FaceShape w w :=
  Or.inl (CargoPath.refl w)

/-- **THE FACE-MEMBERSHIP CONTENT, LANDED AS A TWIN** (the additive
closure of `canonFace_mem`, whose frozen statement keeps its sorry;
promotion is the owner's one-line swap): every face is a class
member — the benign arm by the canonical bridge (`canon_in_class`
through `Quotient.exact`), the forked arm by class transitivity
through the canon link. -/
theorem canonFace_inClass (u w : State) (hwf : u.WF)
    (h : CanonFace u w) : sameOrbitSetoid.r u w := by
  have hc : sameOrbitSetoid.r u (canon u) :=
    Quotient.exact (canon_in_class hwf).symm
  cases h with
  | benign _ _ heq _ => rw [heq]; exact hc
  | forked _ hclass _ => exact class_trans hc hclass

/-- **THE NO-MIX KERNEL** (the `canonFace_sameShape` staging's keel):
a class's faces are ALL-benign or ALL-forked — benign's no-fork
clause and forked's live `weakForkState` are contradictory at any
shared class member, so the mixed case is impossible and the shape
theorem's case split collapses to the within-kind cases (benign
pairs by `faceShape_refl` on the canon; forked pairs by the sandwich
cell, which remains the named residual). -/
theorem canonFace_sameKind (u w w' : State)
    (h : CanonFace u w) (h' : CanonFace u w') :
    (w = canon u ∧ w' = canon u) ∨
      (weakForkState w ∧ weakForkState w') := by
  cases h with
  | benign _ _ heq₁ hnofork₁ =>
      cases h' with
      | benign _ _ heq₂ _ => exact Or.inl ⟨heq₁, heq₂⟩
      | forked _ hclass₂ hfins₂ =>
          obtain ⟨y, hy₁, hy₂, hy₃⟩ := hfins₂
          exact absurd ⟨hy₁, hy₂, Or.inl ((hy₃ y).2 rfl)⟩
            (hnofork₁ w' hclass₂ y)
  | forked _ hclass₁ hfins₁ =>
      cases h' with
      | benign _ _ _ hnofork₂ =>
          obtain ⟨y, hy₁, hy₂, hy₃⟩ := hfins₁
          exact absurd ⟨hy₁, hy₂, Or.inl ((hy₃ y).2 rfl)⟩
            (hnofork₂ w hclass₁ y)
      | forked _ _ hfins₂ => exact Or.inr ⟨hfins₁, hfins₂⟩

/-! ### The surgical battery

Fresh heads audited; the frozen sorried rows above keep their own
sorryAx surface, and nothing here consumes a sorried row: -/

#print axioms conjugateComposite_rungs
#print axioms conjugateComposite_class
#print axioms cargoPath_inClass
#print axioms faceShape_cross_inClass
#print axioms faceShape_refl
#print axioms canonFace_inClass
#print axioms canonFace_sameKind

/-! ## §9.5 The benign-carrier completion (wave-2, one row)

The `canonFace_class_inv` (⇐)-half's benign-carrier composition, landed
as the census-restricted r-transport: the NO-MIX cell
(`canonFace_sameKind`'s left disjunct — both faces ARE the canon) is the
shared-shape datum `faceShape_refl` packages (`Or.inl (CargoPath.refl
·)`), and that sole carrier transports through the cargo closure's class
row (`cargoPath_inClass`, the same-face arm of `faceShape_rel`'s
mechanical strand).  Resisted, the full benign composition: the
cross-face arm — a `conjugateForkState` carrier has no in-file class row
even at gate grade (`faceShape_cross_inClass` reads the seat-carrying
`conjugateCompositeRev` only) — so the frozen statements above keep
their sorries and this head stays census-restricted; zero
`Classical.choice`, nothing sorried consumed. -/

/-- **THE BENIGN-CELL r-TRANSPORT** (the `canonFace_sameKind`-restricted
r-transport, one twin head; the frozen `canonFace_class_inv` above keeps
its sorry): two benign faces — the census cell pins both as THE canon —
are class-mates, the shared shape running at `faceShape_refl`'s own
carrier over the canon link, through the cargo class row. -/
theorem canonFace_class_inv_benign (u w w' : State)
    (h : CanonFace u w) (h' : CanonFace u w')
    (hben : w = canon u ∧ w' = canon u) :
    sameOrbitSetoid.r w w' := by
  rw [hben.1, hben.2]
  exact cargoPath_inClass (CargoPath.refl (canon u))

#print axioms canonFace_class_inv_benign

/-! ## §9.6 The forked-cell twins (wave-3, four rows)

The §9.5 record resisted the full `canonFace_class_inv`
(⇐)-composition at the cite level: a `conjugateForkState` carrier has
no in-file class row.  Wave-3 supplies the FORKED cell with
DEGENERATE support instead — the seat-carrying composite package
carried as a premise, not the derived closure.  The converter reduces
`conjugateCompositeRev` to the seat-less carrier `FaceShape`'s cross
arm reads (the census pin `weakForkState` carrying the seat content
the downstream corrected closure derives); the composite's class and
rungs content is packaged once at the midpoint grade; the
class-transport twin rides the canon link alone (`canonFace_inClass`
at the forked arm) through the in-file class engine; the share-shape
twin is gated at the cross face exactly as its class sibling
`faceShape_cross_inClass` prices it.  The wave-2 resist record
stands: nothing here mints a class row for the carrier itself.  The
frozen statements above keep their sorries; every head here is
additive, nothing sorried consumed. -/

/-- **THE DEGENERATE-SUPPORT CONVERTER** (the wave-2 cite-level gap,
bridged the import-visible way: down-cast, not up-derivation): the
seat-carrying composite package reduces to the seat-less
`conjugateForkState` carrier when the census pin `weakForkState st`
supplies the seat content — the per-leg reversibility witnesses
degenerate away, the three physical steps and the twin structure
surviving intact. -/
theorem conjugateCompositeRev_forkState {st w : State}
    (hwfs : weakForkState st)
    (h : conjugateCompositeRev st w) : conjugateForkState st w := by
  obtain ⟨x, ba, bb, st₁, st₂, h₁, h₂, h₃, -, -, -⟩ := h
  exact ⟨x, ba, bb, st₁, st₂, hwfs, h₁, h₂, h₃⟩

/-- **THE CROSS-FACE MIDPOINT ROW** (the composite's class + rung
content packaged at the `conjugateCompositeRev` grade): the
conjugation's endpoint stays in the starting face's class (the
per-leg reversibility composition) and keeps its rung read (the
net-flat anatomy). -/
theorem conjugateCompositeRev_midpoint {st w : State}
    (h : conjugateCompositeRev st w) :
    sameOrbitSetoid.r st w ∧ ∀ s : Suit, rungAt w s = rungAt st s := by
  have hcp := h
  obtain ⟨x, ba, bb, st₁, st₂, h₁, h₂, h₃, -, -, -⟩ := h
  exact ⟨conjugateComposite_class hcp, conjugateComposite_rungs h₁ h₂ h₃⟩

/-- **THE FORKED-CELL r-TRANSPORT** (the `canonFace_sameKind`-
restricted r-transport, the forked twin of the §9.5 benign cell; the
frozen `canonFace_class_inv` above keeps its sorry): two forked
faces — the no-mix census pins both `weakForkState` — are
class-mates, each face a class member through the canon link
(`canonFace_inClass`, the forked arm's constructor conjunct at MI
grade), the shared anchor's class closing the sandwich (`iseqv.symm`
plus the in-file `class_trans`). -/
theorem canonFace_class_inv_forked (u w w' : State)
    (hwf : u.WF)
    (h : CanonFace u w) (h' : CanonFace u w')
    (hfork : weakForkState w ∧ weakForkState w') :
    sameOrbitSetoid.r w w' := by
  have hmemw : sameOrbitSetoid.r u w := canonFace_inClass u w hwf h
  have hmemw' : sameOrbitSetoid.r u w' := canonFace_inClass u w' hwf h'
  exact class_trans (sameOrbitSetoid.iseqv.symm hmemw) hmemw'

/-- **THE FORKED-CELL share-shape TWIN** (the sibling of the §9.5
benign pair-lift, gated at the cross face exactly as its class
sibling `faceShape_cross_inClass` prices it): two forked faces
supplied with the cross-face composite + cargo share the cross face
shape — the converter degenerates the package to the
`conjugateForkState` carrier the cross arm reads, the census pin
carrying the seat content. -/
theorem canonFace_sameShape_forked (u w w' z : State)
    (h : CanonFace u w) (h' : CanonFace u w')
    (hfork : weakForkState w ∧ weakForkState w')
    (hc : conjugateCompositeRev w z)
    (hp : CargoPath z w') :
    FaceShape w w' :=
  Or.inr ⟨z, conjugateCompositeRev_forkState hfork.1 hc, hp⟩

/-! The wave-3 battery (fresh heads audited; the frozen rows above
keep their own surfaces): -/

#print axioms conjugateCompositeRev_forkState
#print axioms conjugateCompositeRev_midpoint
#print axioms canonFace_class_inv_forked
#print axioms canonFace_sameShape_forked
