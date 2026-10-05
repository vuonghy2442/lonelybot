import Klondike.Macro
import Klondike.TwinSwapCompletion

/-!
# C2, streamlined — closures as coordinates, commitments as pinnings

`docs/macro_formalization.md` §7 (the campaign's central theorem: the
two-option commitment bound), model side.  The reframe: a commitment
with target `X` is the irreversible assignment of one coordinate
("where `X` resides"), what makes it executable is the state of a tiny
local coordinate set, and what a macro successor *remembers* is which
coordinates the commitment pinned irreversibly.  The successors are
therefore labeled by the *minimal enabling pinnings* — elements of a
five-line resource poset — and the theorem is one counting fact about
that poset.

**Engine anchor** (definition alignment only; `src/macro_game.rs`):
the channels are `core_run`'s ("stack-direct", "tableau-direct",
"tableau-dig" = `PileStack(twin X)` + commit, "tableau-borrow" =
`StackPile(p)` + commit, the king gate of `free_slot` = the hole,
"stack-prefix-raise" = the raise chains), the classes were measured by
`closure_classes`/`closure_contains`, and the fold by `collapse_pick`.
The measurement (§6.3/§6.7): 16,791 enumerated commitments over 200
greedy games — closure-class histogram `[_, 16777, 14, 0, 0]`, i.e.
max 2 classes per commitment, 1,102 of the singles mixed-kind.

**What is proven here** (the small fully-proven core):

- the two-type ball (§6.2's "never a third suit" as
  `receivers_twin_pair`, `receivers_king_nil`);
- **P1 in full** (`founded_not_covered`, `founded_unseated`,
  `p1_bothBorrows_noDig`) — a foundation top cannot be covered — from
  the card arithmetic plus `board_edges`/`founds_gone`;
- §6.2's fitted-coverer forcing for stocked targets
  (`coverer_is_twin_of_stocked`);
- the one-step channel semantics (`digOpens`, `borrowOpens`) and
  **P2's one-step cores** (`p2_core_dig`, `p2_core_borrow`) — the
  direct landing provably never disturbs the dig's or the borrow's own
  enabling facts;
- the **poset register** (`register_le_two`) — §7's finite lemma made
  formal: three live ball pinnings always contain two equal ones (P1
  closing precisely the `{dig, borrow, borrow̄}` corner);
- the worry-ray confinement (§7's stretch core: `InRay` + the rank,
  alternation and twin-pair theorems);
- the **main theorem's assembly** (`c2_two_option`): the two-option
  bound, CONDITIONAL on five precisely-stated play-level premises
  (the wave-18 restructure: the five wave-17 pillars were
  refute-probed, FOUR FALSE as stated —
  `witnesses/C2KingAnchorWitness.lean`; the plans of the
  formerly-pinned rows live in §11, and the surviving proven half of
  the destination collapse is `commitTableau_class`, the
  stackable-rung regime);

and **the wave-19 rung re-scope** (§12.5 and §14):

- the zero-spend channels' premise content **derived from the rung
  premise** — `pin_join_zeroSpend_rung` for `hpin` and
  `p2_join_zeroSpend_rung` for `hp2` (the stack arm of the root
  commit joins by a two-move worried-back roundtrip, §6.7's
  late-`PileStack X` merge as a proof) — with the derived-scope bound
  itself: `c2_two_option_zeroSpend_rung`, no play-level premises;
- `hball`'s proven core (§14): the pacing guard's accommodation
  invariance (`reachablePos_of_accommodation(_run)`), the per-move
  heights step law (`heights_step_accommodation`), **F2's
  deterministic raise** (`raise_crossing_mem` — any upward crossing
  of a suit's standing level fires the same-suit rank-index-pinned
  `pileStack`), the corner's derived world (`stack_channel_world`),
  and the stack-channel witness's forced final raise
  (`stack_raise_deterministic`, `stack_channel_raise_mem`) with the
  ball-avoidance hygiene (`raise_card_off_ball`).

The convolution with `macro_direct_matches_oracle` (5129 evaluations,
0 fabricated / 0 missed, the BFS fallback at 27/5129) is the empirical
companion for the premises.

**Scope note (model reality).**  The model's macro game
(`Klondike/Macro.lean`) has the `Draw` commitment with its two outcome
arms (`commitApplies`' disjunction) and the anchor-indexed `Reveal`
commitment whose application is a *function* — a single successor per
state, so the Reveal case of the two-option bound is trivial at the
state level and its accommodation-scar content is the same P0/P3
machinery guided here for the Draw arm (reveal-by-stacking is the C12
design decision still pending in FARM.md; this file does not extend
`commitApplies`).  The theorem below is stated for the `Draw`
commitment, the model's two-outcome kind.
-/

namespace Klondike.C2

/-! ## §0. The two colors -/

/-- Two colors both distinct from a third coincide — the helper that
keeps the ray color algebra `cases`-free at call sites. -/
theorem color_pair_of_both_ne {x c₁ c₂ : Color}
    (h₁ : x ≠ c₁) (h₂ : x ≠ c₂) : c₁ = c₂ := by
  cases x <;> cases c₁ <;> cases c₂ <;> simp_all

/-- Constructor disjointness for bases, named once with concrete
argument shapes (the `Sum.noConfusion` idiom stabilized per the
ledger's enumeration guidance). -/
theorem sumInl_ne_sumInr {α β : Type} {a : α} {b : β} :
    Sum.inl a ≠ Sum.inr b := fun h => nomatch h

theorem sumInr_ne_sumInl {α β : Type} {a : α} {b : β} :
    Sum.inr a ≠ Sum.inl b := fun h => nomatch h

/-! ## §1. The two-type ball (§6.2's singleton-blocker fact)

The destination twins: `X`'s tableau landings are exactly its
*receivers* — the cards one rank up, opposite color — and they form a
single twin pair.  This is F1 ("two twins only") and the exact form of
§6.2's "never a third suit": a commitment's interference zone is one
type.  The coverer-side fact `Card.only_blocker_is_twin` already lives
in Basic.lean. -/

/-- §6.2's fitted-coverer classification: every coverer fit to sit on
`X`'s receiver is `X` or its twin (`only_blocker_is_twin` with the
argument order fixed once — its coverer `c` is the *first* argument). -/
theorem coverer_fitted_twin {X Y z : Card}
    (hY : canSitOn X Y = true) (hfit : canSitOn z Y = true) :
    z = X ∨ z = X.flipSuit :=
  Card.only_blocker_is_twin hY hfit

/-- F1/§6.2: any receiver of `X` lies in the twin pair spanned by two
distinct receivers `z₁`, `z₂` — the ball over `X` is one two-element
color-rank class. -/
theorem receivers_twin_pair {X z₁ z₂ z : Card}
    (h₁ : canSitOn X z₁ = true) (h₂ : canSitOn X z₂ = true)
    (hne : z₁ ≠ z₂) (hz : canSitOn X z = true) :
    z = z₁ ∨ z = z₂ := by
  obtain ⟨hr₁, hc₁⟩ := (canSitOn_eq X z₁).mp h₁
  obtain ⟨hr₂, hc₂⟩ := (canSitOn_eq X z₂).mp h₂
  obtain ⟨hr, hc⟩ := (canSitOn_eq X z).mp hz
  -- all three receivers share the rank (one above X) and sit in the
  -- opposite color class; a second distinct receiver is the first's twin
  have hcol12 : z₁.suit.color = z₂.suit.color := color_pair_of_both_ne hc₁ hc₂
  have hcol1z : z₁.suit.color = z.suit.color := color_pair_of_both_ne hc₁ hc
  have hrank12 : z₁.rank = z₂.rank := Rank.toIdx_inj (by omega)
  have hrank1z : z₁.rank = z.rank := Rank.toIdx_inj (by omega)
  have hpair : z₂ = z₁.flipSuit :=
    Card.flipSuit_eq_of_color_rank hcol12 hrank12 hne
  by_cases hzz : z = z₁
  · exact Or.inl hzz
  · exact Or.inr ((Card.flipSuit_eq_of_color_rank hcol1z hrank1z
      (fun hh => hzz hh.symm)).trans hpair.symm)

/-- §6.2, king boundary: a king has no receivers — its tableau outcome
is the king-hole alone (§6.4's dig/borrow gate `!is_king`). -/
theorem receivers_king_nil {X z : Card} (hK : X.rank = Rank.king)
    (h : canSitOn X z = true) : False := by
  obtain ⟨hr, _⟩ := (canSitOn_eq X z).mp h
  rw [hK] at hr
  have h12 : (Rank.king).toIdx = 12 := rfl
  rw [h12] at hr
  have hz := Rank.toIdx_lt z.rank
  omega

/-! ## §2. The resource poset (§7's definition)

The atoms a commitment with target `X` may need to consume; the
pinnings are subsets of that poset, ordered by inclusion, `direct`
being the empty subset (hence least). -/

/-- The resource atoms of the commitment with target `X` (§7's poset
lines `dig(twin X)`, `borrow(Y)`, `borrow(Ȳ)`, plus the king-hole):
the irreversible *seats* an enabling accommodation may have to spend.
`direct` is not an atom — it is the empty pinning. -/
inductive Res (X : Card) : Type where
  /-- The dig: `twin X` occupies its foundation seat — the only
  possible coverer of a destination twin vacates (§6.2's forcing). -/
  | digTwin : Res X
  /-- The borrow: the receiver `p` leaves its foundation seat (a
  worry-back) — `p` ranges over `X`'s two destination twins (the
  liveness predicates carry the `canSitOn` evidence). -/
  | borrow (p : Card) : Res X
  /-- The king-hole: the vacant anchor a king lands on (§6.5's
  refinement (ii): the one non-type-localized read). -/
  | hole : Res X

/-- Pinnings: subsets of the resource poset. -/
def Pinning (X : Card) : Type := List (Res X)

/-- The order on pinnings: inclusion of resource sets (`List.Subset`
on the atom lists). -/
instance pinningLE (X : Card) : LE (Pinning X) := ⟨List.Subset⟩

/-- `direct` is the empty pinning — §7's `direct(=∅)`. -/
def direct (X : Card) : Pinning X := []

/-- §7's `direct(=∅)  <  …`: the empty pinning is least. -/
theorem direct_le (X : Card) (π : Pinning X) : direct X ≤ π :=
  fun _ h => nomatch h

theorem pin_le_refl (X : Card) (π : Pinning X) : π ≤ π :=
  fun _ h => h

theorem pin_le_trans {X : Card} {π₁ π₂ π₃ : Pinning X}
    (h₁ : π₁ ≤ π₂) (h₂ : π₂ ≤ π₃) : π₁ ≤ π₃ :=
  fun _ hm => h₂ (h₁ hm)

/-- The canonical atom pinnings — the poset's non-`direct` minimal
elements. -/
def pinDig (X : Card) : Pinning X := [Res.digTwin]
def pinBorrow (X : Card) (p : Card) : Pinning X := [Res.borrow p]
def pinHole (X : Card) : Pinning X := [Res.hole]

/-- The successor labels — §7's "labeled by the minimal pinnings", in
a flat counting form: the minimal pinnings plus the stack residence.
The `borrow` label carries the parent card freely (the liveness
predicates carry the `canSitOn` evidence), so equality of labels is
pure constructor equality. -/
inductive Label (X : Card) : Type where
  /-- The tableau landing on a free receiver top — the empty pinning. -/
  | direct : Label X
  /-- The tableau landing freed by `PileStack(twin X)` — `pinDig`. -/
  | dig : Label X
  /-- The tableau landing on a parent worried back off its foundation
  top — `pinBorrow p`. -/
  | borrow (p : Card) : Label X
  /-- The king's vacant-anchor tableau landing — `pinHole`. -/
  | hole : Label X
  /-- The stack residence: `Draw(X)`'s foundation arm (the residence
  coordinate itself; not a resource spend). -/
  | toStack : Label X
  deriving DecidableEq

/-- The label of a successor is one of the minimal pinnings; the
`toStack` label names the coordinate flip itself (the stack arm spends
no tableau resource; its raise-chain residue is the `toStack`
liveness below plus the crease). -/
def labelPin {X : Card} : Label X → Pinning X
  | .direct => direct X
  | .dig => pinDig X
  | .borrow p => pinBorrow X p
  | .hole => pinHole X
  | .toStack => direct X

/-! ## §3. The closure quotient (§6.3's classes) -/

/-- Mutual reversible reachability — §6.3's `closure_classes`
equivalence (`closure_contains` is this relation's directed probe;
the Rust side leans on reversibility's symmetry, the model states
both directions because `accommodates` is not known to be symmetric at
all states). -/
def closureEq (s s' : State) : Prop :=
  accommodates s s' ∧ accommodates s' s

theorem accommodates_trans {st st' st'' : State}
    (h₁ : accommodates st st') (h₂ : accommodates st' st'') :
    accommodates st st'' := by
  obtain ⟨π₁, hr₁, ha₁⟩ := h₁
  obtain ⟨π₂, hr₂, ha₂⟩ := h₂
  refine ⟨π₁ ++ π₂, ?_, ?_⟩
  · rw [State.run_append, hr₁]
    exact hr₂
  · intro m hm
    rcases List.mem_append.mp hm with h | h
    · exact ha₁ m h
    · exact ha₂ m h

theorem closureEq_refl (s : State) : closureEq s s :=
  ⟨⟨[], rfl, fun _ hm => by simp at hm⟩, ⟨[], rfl, fun _ hm => by simp at hm⟩⟩

theorem closureEq_symm {s s' : State} (h : closureEq s s') : closureEq s' s :=
  ⟨h.2, h.1⟩

theorem closureEq_trans {a b c : State}
    (h₁ : closureEq a b) (h₂ : closureEq b c) : closureEq a c :=
  ⟨accommodates_trans h₁.1 h₂.1, accommodates_trans h₂.2 h₁.2⟩

/-! ## §4. The channel liveness (the poset's data at a state)

Mirrors `core_run`'s probes: each channel is a guard set read at the
commitment's root state, not an accommodation search. -/

/-- §6.4 case 1 (`tableau-direct`): a receiver `Y` is already a free
tableau top — `X` lands with zero spend. -/
structure DirectLive (st : State) (X Y : Card) : Prop where
  /-- the destination is a receiver (one rank up, opposite color). -/
  hY : canSitOn X Y = true
  /-- `Y`'s top is free — nothing sits on it. -/
  hopen : st.board.topOf (Sum.inr Y) = none
  /-- the card is visible (it carries the stack `X` would inherit). -/
  hvis : st.isVis Y = true

theorem DirectLive.canPlace {st : State} {X Y : Card}
    (h : DirectLive st X Y) : st.canPlace X (Sum.inr Y) = true :=
  canPlace_inr_iff.mpr ⟨h.hopen, h.hvis, h.hY⟩

/-- §6.4 case 2 (`tableau-dig`): the receiver `Y` is covered — by
`twin X`, §6.2's forced coverer (see `coverer_is_twin_of_stocked`) —
and stacking the twin (legal: stackable at its suit height, top free)
frees `Y` for `X`'s landing (`digOpens`). -/
structure DigLive (st : State) (X Y : Card) : Prop where
  /-- the destination is a receiver. -/
  hY : canSitOn X Y = true
  /-- the covered card is visible. -/
  hvis : st.isVis Y = true
  /-- §6.2: the coverer is exactly the twin (the only card of the
  covering type; `X` itself is in flight during its own commitment). -/
  hcover : st.board.topOf (Sum.inr Y) = some X.flipSuit
  /-- `twin X` is stackable at its suit's height. -/
  hstack : X.flipSuit.rank.toIdx = st.heights X.flipSuit.suit
  /-- `twin X` is a run top (nothing sits on it). -/
  htop : st.board.topOf (Sum.inr X.flipSuit) = none

/-- §6.4 case 3 (`tableau-borrow`): the receiver `p` sits at its
suit's foundation *top* — exactly one above its height, which is
`stackPile p`'s un-stack guard — so worrying it back seats it as `X`'s
landing target (`borrowOpens`); the landing ray continues one rank up
(`InRay`). -/
structure BorrowLive (st : State) (X p : Card) : Prop where
  /-- the destination is a receiver. -/
  hp : canSitOn X p = true
  /-- `p` is exactly the top of its suit's foundation. -/
  htop : p.rank.toIdx + 1 = st.heights p.suit

/-- §6.4's king gate (`free_slot`): `X` is a king and the anchor `a`
is free. -/
structure HoleLive (st : State) (X : Card) (a : Anchor) : Prop where
  hK : X.rank = Rank.king
  hfree : st.board.topOf (Sum.inl a) = none

/-- The channel liveness — which minimal pinnings the raw state
presents.  The `toStack` liveness is the stack arm's: some
accommodation makes the draw-stack commit fire (the raise chains when
`X` is not stackable at `st` — §6.4's stack machinery, "the very same
one-card dig, descending"). -/
def LabelLive (st : State) (X : Card) : Label X → Prop
  | .direct => ∃ Y, DirectLive st X Y
  | .dig => ∃ Y, DigLive st X Y
  | .borrow p => ∃ _hp : canSitOn X p = true, BorrowLive st X p
  | .hole => ∃ a, HoleLive st X a
  | .toStack => ∃ st' s', accommodates st st' ∧ st'.applyDrawStackTo X = some s'

/-- P2's coverage: every channel except the stack-residence-through-a
raise (`X` not stackable at `st` itself) joins the direct successor's
class.  The exception is §6.7's mixed-kind second class; when `X` *is*
stackable at `st`, the stack successor merges by the late
`PileStack X` (the 1,102 mixed-kind single-class commitments). -/
def P2Safe (st : State) (X : Card) : Label X → Prop
  | .toStack => X.rank.toIdx = st.heights X.suit
  | _ => True

/-! ## §5. The commitment's two arms -/

/-- The `Draw(X)` commitment's tableau arm at `st` (the first
disjunct of `commitApplies`). -/
def CommitTableau (st : State) (X : Card) (s : State) : Prop :=
  ∃ b : Base, st.canPlace X b = true ∧ st.applyDrawTo X b = some s

/-- The `Draw(X)` commitment's stack arm at `st` (the second
disjunct). -/
def CommitStack (st : State) (X : Card) (s : State) : Prop :=
  st.applyDrawStackTo X = some s

theorem commitApplies_draw_cases (st : State) (X : Card) (s : State) :
    commitApplies st (MacroMove.drawCommit X) s ↔
      CommitTableau st X s ∨ CommitStack st X s := by
  constructor
  · intro h
    have h2 : (∃ b : Base, (st.canPlace X b = true ∧
        st.applyDrawTo X b = some s) ∨
      st.applyDrawStackTo X = some s) := h
    obtain ⟨b, hb⟩ := h2
    rcases hb with hb | hb
    · exact Or.inl ⟨b, hb⟩
    · exact Or.inr hb
  · intro h
    rcases h with h | h
    · obtain ⟨b, hb⟩ := h
      exact ⟨b, Or.inl hb⟩
    · exact ⟨Sum.inl Anchor.p0, Or.inr h⟩

/-- Which arm the label serves at the accommodated state. -/
def commitArmOf (u : State) (X : Card) : Label X → State → Prop
  | .toStack, s => CommitStack u X s
  | _, s => CommitTableau u X s

/-- The channel's signature demand on an enabling accommodation (the
extrinsic witness of the spend): `direct`/`hole` demand the empty
spend (those channels are commits-at-the-root); `dig` demands the
twin's `pileStack`; `borrow p` demands the parent's `stackPile`;
`toStack` demands nothing (its shape is the arm, not the play).  The
play may spend more than the signature — that a *minimal enabling*
pinning labels the successor is `succ_labeled`'s content, with the
chains resolved by `crease_chain_absorbed`. -/
def LabelSig (X : Card) : Label X → List Move → Prop
  | .direct => fun α => α = []
  | .hole => fun α => α = []
  | .dig => fun α => Move.pileStack X.flipSuit ∈ α
  | .borrow p => fun α => ∃ b : Base, Move.stackPile p b ∈ α
  | .toStack => fun _ => True

/-- `s` succeeds through atom `r`: some accommodation `α` (a reversible
play — A2's `pileStack`/`stackPile` fragment) whose shape carries
`r`'s signature delivers a state where the `Draw(X)` commitment fires
onto `s` through `r`'s arm. -/
def SuccThrough (st : State) (X : Card) (r : Label X) (s : State) : Prop :=
  ∃ u α, st.run α = some u ∧ (∀ m ∈ α, m.isAccommodation = true) ∧
    commitArmOf u X r s ∧ LabelSig X r α

/-! ## §6. P1 — both borrows live ⟹ no dig (PROVEN)

The register's closing exclusion, in full, from the card arithmetic. -/

/-- A foundation-passed card sits under no tableau card at a WF state:
`founds_gone` says it is neither visible nor hidden, while every
covered base, by `board_edges`, is either deal-adjacent (with the base
card a hidden boundary or placed) or placed — both shapes put the
base card in exactly one of those two zones. -/
theorem founded_not_covered {st : State} (hwf : st.WF) {d z : Card}
    (hf : d.rank.toIdx < st.heights d.suit)
    (hcover : st.board.topOf (Sum.inr d) = some z) : False := by
  obtain ⟨hvis, _, hhid⟩ := hwf.founds_gone d hf
  have hedge := hwf.board_edges (Sum.inr d) z hcover
  have hbase : (∃ a t rest, st.deal.piles a = t ++ d :: z :: rest ∧
        ((∃ a', st.topHidden a' = some d) ∨
          (st.board.bottomOf d).isSome = true)) ∨
      ((st.board.bottomOf d).isSome = true ∧ canSitOn z d = true) :=
    hedge.2
  rcases hbase with ⟨a, t, rest, hsplit, hsub⟩ | ⟨hbot, _⟩
  · rcases hsub with ⟨a', hth⟩ | hbot
    · exact absurd (mem_of_getLast hth) (hhid a')
    · have hcast : st.isVis d = true := hbot
      rw [hvis] at hcast
      exact Bool.noConfusion hcast
  · have hcast : st.isVis d = true := hbot
    rw [hvis] at hcast
    exact Bool.noConfusion hcast

/-- At a WF state a founded card is unseated: `bottomOf` is `none`. -/
theorem founded_unseated {st : State} (hwf : st.WF) {d : Card}
    (hf : d.rank.toIdx < st.heights d.suit) :
    st.board.bottomOf d = none := by
  have h1 : st.isVis d = false := (hwf.founds_gone d hf).1
  cases hbot : st.board.bottomOf d with
  | none => rfl
  | some b' =>
      have hcast : st.isVis d = true := by
        show (st.board.bottomOf d).isSome = true
        rw [hbot]
        rfl
      rw [h1] at hcast
      exact Bool.noConfusion hcast

/-- **P1** (§7's poset axiom): both borrows live ⟹ no dig — a
foundation top cannot be covered.  The two parents `Y`, `Z` are the
two receivers (one twin pair, `receivers_twin_pair`), each a
foundation top — hence founded — while the dig's covered parent is one
of them, and `founded_not_covered` forbids the cover.  This closes the
`{dig, borrow(Y), borrow(Z)}` corner of the register (§6.7's measured
exclusion `borrowable: 2 ⟹ dig: false`). -/
theorem p1_bothBorrows_noDig {st : State} (hwf : st.WF) {X Y Z Y₀ : Card}
    (hbY : BorrowLive st X Y) (hbZ : BorrowLive st X Z) (hne : Y ≠ Z)
    (hd : DigLive st X Y₀) : False := by
  rcases receivers_twin_pair hbY.hp hbZ.hp hne hd.hY with h | h
  · subst h
    exact founded_not_covered hwf (by
      have := hbY.htop
      omega) hd.hcover
  · subst h
    exact founded_not_covered hwf (by
      have := hbZ.htop
      omega) hd.hcover

/-! ## §7. §6.2's forcing, the in-flight half -/

/-- For a *stocked* target — the `Draw` commitment's in-flight premise
("`X` is in flight during its own commitment") — the fitted coverer of
`X`'s receiver is exactly `twin X`: `only_blocker_is_twin` classifies
the coverer into `{X, twin X}`, and `X` itself cannot be seated (a
stocked card is not visible by `vis_off_cycle`, while `board_edges`
gives every seated card its seat).  Boundary note: `board_edges`'
deal-adjacency disjunct also admits non-fitting coverers of *hidden*
bases — the WF-overapproximation the engine's per-card masks do not
have (§6.5's parity reading) — so the fitted-coverer premise is the
honest model-side half; every coverer formed by a real seating move
satisfies it (`canPlace`'s `canSitOn` half is pure). -/
theorem coverer_is_twin_of_stocked {st : State} (hwf : st.WF) {X Y z : Card}
    {i : Nat} (hstock : st.stock.posOf X = some i)
    (hY : canSitOn X Y = true) (hfit : canSitOn z Y = true)
    (hcover : st.board.topOf (Sum.inr Y) = some z) :
    z = X.flipSuit := by
  rcases coverer_fitted_twin hY hfit with h | h
  · -- the coverer being X itself contradicts the flight (X is stocked)
    have hcover' : st.board.topOf (Sum.inr Y) = some X :=
      hcover.trans (congrArg some h)
    have hbot := (hwf.board_edges (Sum.inr Y) X hcover').1
    have hvisX : st.isVis X = true := by
      show (st.board.bottomOf X).isSome = true
      rw [hbot]
      rfl
    have hn := hwf.vis_off_cycle _ hvisX
    rw [hn] at hstock
    exact absurd hstock (by simp)
  · exact h

/-! ## §8. The channels open the landing (one-step semantics) -/

/-- The dig's enabling consequence (`dig(twin X)` really enables the
direct pinning's landing): the one-move accommodation
`pileStack (twin X)` leaves a state where `X`'s direct landing on the
freed parent is `canPlace`-legal — the freed top, the preserved
visibility, the pure fit. -/
theorem digOpens {st : State} {X Y : Card} (h : DigLive st X Y) :
    ∃ s₁, st.apply (Move.pileStack X.flipSuit) = some s₁ ∧
      s₁.canPlace X (Sum.inr Y) = true := by
  have hbot : st.board.bottomOf X.flipSuit = some (Sum.inr Y) :=
    (Board.bottomOf_eq _ _ _).mpr h.hcover
  refine ⟨{ st with
    board := st.board.detach (Sum.inr Y),
    heights := fun s => if s = X.flipSuit.suit then st.heights s + 1
      else st.heights s }, ?_, ?_⟩
  · rw [apply_pileStack_iff]
    exact ⟨h.htop, Sum.inr Y, hbot, h.hstack, rfl⟩
  · have hne : Y ≠ X.flipSuit := by
      intro hhe
      subst hhe
      obtain ⟨hr', _⟩ := (canSitOn_eq X X.flipSuit).mp h.hY
      simp only [Card.flipSuit_rank] at hr'
      omega
    have hvis' : ((st.board.detach (Sum.inr Y)).bottomOf Y).isSome = true := by
      rw [bottomOf_detach_ne h.hcover hne]
      exact h.hvis
    show (decide ((st.board.detach (Sum.inr Y)).topOf (Sum.inr Y) = none)
        && (((st.board.detach (Sum.inr Y)).bottomOf Y).isSome &&
          canSitOn X Y)) = true
    rw [Board.detach_topOf, hvis', h.hY]
    rfl

/-- The borrow's enabling consequence: given a landing `β` for the
worried parent (the same question one rank up — `InRay`'s next level),
the one-move accommodation `stackPile p β` seats `p`, and `X`'s
landing on it is `canPlace`-legal: `p` is freshly seated (its
visibility *is* the seating), `p`'s top is free (it was founded, hence
uncovered), and the fit is pure. -/
theorem borrowOpens {st : State} (hwf : st.WF) {X p : Card} {β : Base}
    (hb : BorrowLive st X p) (hland : st.canPlace p β = true) :
    ∃ s₁, st.apply (Move.stackPile p β) = some s₁ ∧
      s₁.canPlace X (Sum.inr p) = true := by
  have hfounded : p.rank.toIdx < st.heights p.suit := by
    have := hb.htop
    omega
  have hpbot : st.board.bottomOf p = none := founded_unseated hwf hfounded
  -- nothing covers the foundation top
  have hnoc : st.board.topOf (Sum.inr p) = none := by
    by_cases htop : st.board.topOf (Sum.inr p) = none
    · exact htop
    · exfalso
      cases htop' : st.board.topOf (Sum.inr p) with
      | none => rw [htop'] at htop; exact htop rfl
      | some w => exact founded_not_covered hwf hfounded (by rw [htop'])
  -- the landing base is free (the placement guard) — so the attach fires
  have hβfree : st.board.topOf β = none := topOf_of_canPlace hland
  have hsome := (Board.attach_eq_some_iff _ _ _).mpr ⟨hβfree, hpbot⟩
  cases hatt : st.board.attach β p with
  | none =>
      rw [hatt] at hsome
      exact absurd rfl hsome
  | some bd'' =>
      -- X's landing on the freshly-seated parent: p is now a visible
      -- top (its visibility is the seating; nothing covers it in the
      -- old board, and the new edge sits below no one)
      refine ⟨{ st with
        board := bd'',
        heights := fun s => if s = p.suit then st.heights s - 1
          else st.heights s }, ?_, ?_⟩
      · rw [apply_stackPile_iff]
        exact ⟨hb.htop, hland, bd'', hatt, rfl⟩
      · have hver : bd''.bottomOf p = some β :=
          (Board.bottomOf_eq _ _ _).mpr (Board.attach_topOf _ _ _ hatt)
        have hne : Sum.inr p ≠ β := by
          cases β with
          | inl a => exact sumInr_ne_sumInl
          | inr z =>
              intro hh
              have hzp : z = p := Sum.inr.inj hh.symm
              have hfit := canSitOn_of_canPlace_inr hland
              rw [hzp] at hfit
              obtain ⟨hrz, _⟩ := (canSitOn_eq p p).mp hfit
              omega
        have htop : bd''.topOf (Sum.inr p) = none := by
          rw [Board.attach_topOf_ne _ _ _ hatt hne]
          exact hnoc
        have hvis : (bd''.bottomOf p).isSome = true := by
          rw [hver]
          rfl
        show (decide (bd''.topOf (Sum.inr p) = none)
            && ((bd''.bottomOf p).isSome && canSitOn X p)) = true
        rw [htop, hvis, hb.hp]
        rfl

/-! ## §9. P2's one-step cores (the scar is reproducible after the
direct commit) -/

/-- The zero-spend channels commit at the root: a `.direct`- or
`.hole`-through successor is witnessed by `commitApplies` at `st`
itself (the accommodation is empty). -/
theorem through_direct_hole_commits {st : State} {X : Card} {s : State}
    {r : Label X}
    (h : SuccThrough st X r s) (he : r = Label.direct ∨ r = Label.hole) :
    ∃ sd, commitApplies st (MacroMove.drawCommit X) sd := by
  obtain ⟨u, α, hrun, _, harm, hsig⟩ := h
  rcases he with he | he <;> rw [he] at harm hsig
  · have hα : α = [] := hsig
    rw [hα] at hrun
    have hu : u = st := by
      have hnul : st.run [] = some st := rfl
      rw [hnul] at hrun
      exact (Option.some.inj hrun).symm
    rw [hu] at harm
    exact ⟨s, (commitApplies_draw_cases st X s).mpr (Or.inl harm)⟩
  · have hα : α = [] := hsig
    rw [hα] at hrun
    have hu : u = st := by
      have hnul : st.run [] = some st := rfl
      rw [hnul] at hrun
      exact (Option.some.inj hrun).symm
    rw [hu] at harm
    exact ⟨s, (commitApplies_draw_cases st X s).mpr (Or.inl harm)⟩

/-- Only the stack residence can fall outside P2's coverage. -/
theorem unsafe_is_toStack {st : State} {X : Card} {r : Label X}
    (h : ¬ P2Safe st X r) : r = Label.toStack := by
  cases r with
  | direct => exact absurd trivial h
  | dig => exact absurd trivial h
  | borrow p => exact absurd trivial h
  | hole => exact absurd trivial h
  | toStack => rfl

/-- **P2's one-step core, dig side** (the dominance whose class-level
form is `p2_direct_class`): committing `X` directly — the tableau
commit move `deckPile X b` — leaves the dig's accommodation step still
legal: `pileStack (twin X)` fires at the committed state.  The
landing's base is never the twin's seat (rank arithmetic: receivers
sit one above `X`, the twin shares `X`'s rank) and the landing writes
no heights, so all three of the dig's facts survive the attach. -/
theorem p2_core_dig {st : State} {X Y : Card} {b : Base} {s₂ : State}
    (hcom : st.apply (Move.deckPile X b) = some s₂)
    (hd : DigLive st X Y) :
    ∃ s₃, s₂.apply (Move.pileStack X.flipSuit) = some s₃ := by
  rw [apply_deckPile_iff] at hcom
  obtain ⟨_, hcp, bd', hatt, hs₂⟩ := hcom
  rw [hs₂]
  -- the twin's seat is never the landing's base
  have hne' : Sum.inr X.flipSuit ≠ b := by
    cases b with
    | inl a => exact sumInr_ne_sumInl
    | inr z =>
        intro hh
        have hz : X.flipSuit = z := Sum.inr.inj hh
        have hcp' := canSitOn_of_canPlace_inr hcp
        obtain ⟨hrz, _⟩ := (canSitOn_eq X z).mp hcp'
        rw [← hz] at hrz
        simp only [Card.flipSuit_rank] at hrz
        omega
  refine ⟨{ st with
    board := bd'.detach (Sum.inr Y),
    heights := fun s => if s = X.flipSuit.suit then st.heights s + 1
      else st.heights s,
    stock := st.stock.removeAt (st.stock.cursor - 1) }, ?_⟩
  rw [apply_pileStack_iff]
  refine ⟨?_, Sum.inr Y, ?_, ?_, rfl⟩
  · show ({ st with
        board := bd',
        stock := st.stock.removeAt (st.stock.cursor - 1)  } : State).board.topOf
        (Sum.inr X.flipSuit) = none
    rw [Board.attach_topOf_ne _ _ _ hatt hne']
    exact hd.htop
  · show ({ st with
        board := bd',
        stock := st.stock.removeAt (st.stock.cursor - 1)  } : State).board.bottomOf
        X.flipSuit = some (Sum.inr Y)
    rw [bottomOf_attach_of_ne hatt (Card.flipSuit_ne X)]
    exact (Board.bottomOf_eq _ _ _).mpr hd.hcover
  · show X.flipSuit.rank.toIdx =
      ({ st with
        board := bd',
        stock := st.stock.removeAt (st.stock.cursor - 1)  } : State).heights
        X.flipSuit.suit
    exact hd.hstack

/-- **P2's one-step core, borrow side**: committing `X` directly
leaves the borrow's accommodation step still legal: `stackPile p β`
fires at the committed state.  The bases never collide by rank
arithmetic (the direct landing sits on an `X`-receiver, rank `r+1`;
the borrow's landing sits on a `p`-receiver, rank `r+2`; and a
king-anchor direct landing makes `X` a king, hence receiver-less), the
founding facts of the parent survive the landing (heights untouched),
and the borrow's own base's freeness and visibility survive by the
attach-off-a-disjoint-base analysis. -/
theorem p2_core_borrow {st : State} (hwf : st.WF) {X p : Card}
    {β b : Base} {s₂ : State}
    (hb : BorrowLive st X p)
    (hcom : st.apply (Move.deckPile X b) = some s₂)
    (hland : st.canPlace p β = true) :
    ∃ s₃, s₂.apply (Move.stackPile p β) = some s₃ := by
  rw [apply_deckPile_iff] at hcom
  obtain ⟨_, hcp, bd', hatt, hs₂⟩ := hcom
  rw [hs₂]
  -- the borrow's base is disjoint from the direct landing's base
  have hneb : β ≠ b := by
    cases b with
    | inl a =>
        exfalso
        exact receivers_king_nil (king_of_canPlace_inl hcp) hb.hp
    | inr z =>
        cases β with
        | inl a' => exact sumInl_ne_sumInr
        | inr w =>
            intro hh
            have hwz : w = z := Sum.inr.inj hh
            have hfit1 := canSitOn_of_canPlace_inr hcp
            have hfit2 := canSitOn_of_canPlace_inr hland
            obtain ⟨hr1, _⟩ := (canSitOn_eq X z).mp hfit1
            obtain ⟨hr2, _⟩ := (canSitOn_eq p w).mp hfit2
            obtain ⟨hr3, _⟩ := (canSitOn_eq X p).mp hb.hp
            rw [hwz] at hr2
            omega
  -- the founding facts that survive the landing
  have hfounded : p.rank.toIdx < st.heights p.suit := by
    have := hb.htop
    omega
  have hpcX : p ≠ X := by
    intro hh
    obtain ⟨hr3, _⟩ := (canSitOn_eq X p).mp hb.hp
    rw [hh] at hr3
    omega
  -- β's guards transfer across the attach (the disjoint-base pair)
  have hTopC : bd'.topOf β = none := by
    rw [Board.attach_topOf_ne _ _ _ hatt hneb]
    exact topOf_of_canPlace hland
  have hpbot' : bd'.bottomOf p = none := by
    rw [bottomOf_attach_of_ne hatt hpcX]
    exact founded_unseated hwf hfounded
  -- the borrow's landing guard holds at the committed state
  have hcpC : ({ st with
      board := bd',
      stock := st.stock.removeAt (st.stock.cursor - 1) } : State).canPlace p β = true := by
    cases β with
    | inl a' =>
        exact canPlace_inl_iff.mpr ⟨hTopC, king_of_canPlace_inl hland⟩
    | inr w =>
        refine canPlace_inr_iff.mpr ⟨hTopC, ?_, canSitOn_of_canPlace_inr hland⟩
        show (bd'.bottomOf w).isSome = true
        have hwc : w ≠ X := by
          intro hh
          have hfit2 := canSitOn_of_canPlace_inr hland
          rw [hh] at hfit2
          obtain ⟨hr2, _⟩ := (canSitOn_eq p X).mp hfit2
          obtain ⟨hr3, _⟩ := (canSitOn_eq X p).mp hb.hp
          omega
        rw [bottomOf_attach_of_ne hatt hwc]
        exact isVis_of_canPlace_inr hland
  -- the attach at the committed board fires
  have hsome := (Board.attach_eq_some_iff _ _ _).mpr ⟨hTopC, hpbot'⟩
  cases hatt2 : bd'.attach β p with
  | none =>
      rw [hatt2] at hsome
      exact absurd rfl hsome
  | some bd'' =>
      refine ⟨{ st with
        board := bd'',
        heights := fun s => if s = p.suit then st.heights s - 1
          else st.heights s,
        stock := st.stock.removeAt (st.stock.cursor - 1) }, ?_⟩
      rw [apply_stackPile_iff]
      exact ⟨hb.htop, hcpC, bd'', hatt2, rfl⟩

/-! ## §9.5. The destination collapse at the commitment level (PROVEN)

T's destination collapse (TwinSwapCompletion's O1), lifted to the
commitment level and the `closureEq` relation: the *same drawn card's*
two tableau landings — on either destination twin, or (for a king) on
either free anchor — are ONE closure class whenever the card is
stackable at its suit's rung.  The reversible shuttle is the two-move
foundation round trip `[pileStack X; stackPile X b₂]`, and it lands on
EXACTLY the second commit's successor (the board is the same attach
away from the same source board — `attach_detach_cancel` — the
heights bump-and-drop cancels at `X`'s suit, and the stock is the same
splice because the guard's reachable position is the state's own).

This is the workhorse of §6.3's free-float collapse at equal
commitment states, and the honest within-channel twin choice: what
the class computation may quotient without a cross-pile swap.  The
BOUNDARY is equally explicit: without the rung, the landed card can
never leave its seat by accommodation moves (only `pileStack` unseats
a card — `unseats_imp_pileStack`'s taxonomy), and the two landings are
genuinely closure-separated; `witnesses/C2KingAnchorWitness.lean` pins
that corner (a climb-blocked stocked king whose anchor landings are
pairwise closure-separated), so the rung premise below is load-bearing
on both sides of the collapse. -/

/-- A stocked card is never a pile's hidden boundary — the membership
form of the `stock_prev_not_mem_hidden` fact (the deal's piles and
stock are disjoint, so no pile slice contains a cycle card). -/
theorem stocked_not_mem_hidden {st : State} (hwf : st.WF) {c : Card}
    (hmem : c ∈ st.stock.cards) {a : Anchor} : c ∉ st.hidden a := by
  intro hc
  have hndeal : c ∈ st.deal.stock := hwf.stock_wf.2 c hmem
  have hpile : c ∈ st.deal.piles a :=
    List.take_subset _ _ (show c ∈ (st.deal.piles a).take (st.depths a) from hc)
  exact noDupCards_append_disj ((hwf.deal_wf).2.2)
    (List.mem_flatMap.mpr ⟨a, Anchor.mem_all a, hpile⟩) hndeal

/-- The tableau arm's commit unpacks into the reachable position, the
attach, and the successor literal (the `applyDrawTo_eq` shape, with
`CommitTableau`'s own canPlace witness). -/
theorem commitTableau_shape {u : State} {X : Card} {s : State}
    (h : CommitTableau u X s) :
    ∃ b i bd, u.canPlace X b = true ∧ u.reachablePos X = some i ∧
      u.board.attach b X = some bd ∧
      s = { u with board := bd, stock := ⟨Cycle.removeIdx u.stock.cards i, i⟩ } := by
  obtain ⟨b, hcp, hto⟩ := h
  obtain ⟨i, bd, hpos, hatt, hs⟩ := applyDrawTo_eq hto
  exact ⟨b, i, bd, hcp, hpos, hatt, hs⟩

/-- The one-way shuttle: from one committed landing of a stackable
drawn card, the accommodation play `[pileStack X; stackPile X b₂]`
reaches the OTHER commit's successor exactly. -/
theorem commitTableau_shuttle {u : State} (hwf : u.WF) {X : Card}
    (hrk : X.rank.toIdx = u.heights X.suit)
    {s s' : State} (hs : CommitTableau u X s) (hs' : CommitTableau u X s') :
    ∃ play : List Move, (∀ m ∈ play, m.isAccommodation = true) ∧
      s.run play = some s' := by
  obtain ⟨b₁, hcp₁, hto₁⟩ := hs
  obtain ⟨i, bd₁, hpos₁, hatt₁, hshape₁⟩ := applyDrawTo_eq hto₁
  obtain ⟨b₂, hcp₂, hto₂⟩ := hs'
  obtain ⟨i', bd₂, hpos₂, hatt₂, hshape₂⟩ := applyDrawTo_eq hto₂
  have hii : i = i' := Option.some.inj (hpos₁.symm.trans hpos₂)
  rw [← hii] at hshape₂
  -- X rides no stack at the commit state: unplaced (the attach guard),
  -- off every hidden slice (stocked), so nothing sits on it
  have hbox : u.board.bottomOf X = none :=
    ((Board.attach_eq_some_iff _ _ _).mp (by rw [hatt₁]; simp)).2
  have hhid : ∀ a, X ∉ u.hidden a :=
    fun a => stocked_not_mem_hidden hwf
      (Pace.mem_of_posOf u.stock.cards u.stock.cursor X i (reachablePos_posOf hpos₁))
  have hXtop : u.board.topOf (Sum.inr X) = none :=
    State.topOf_inr_eq_none hwf hbox hhid
  -- the first landing's base is never X's own seat
  have hb₁ : b₁ ≠ Sum.inr X := by
    cases b₁ with
    | inl a => exact sumInl_ne_sumInr
    | inr d =>
        intro hcon
        have hd : d = X := Sum.inr.inj hcon
        have hfit := canSitOn_of_canPlace_inr hcp₁
        rw [hd] at hfit
        obtain ⟨hr, -⟩ := (canSitOn_eq X X).mp hfit
        omega
  -- the committed state's shape facts
  have hsb : s.board = bd₁ := by rw [hshape₁]
  have hsh : s.heights X.suit = u.heights X.suit := by rw [hshape₁]
  have hstopX : s.board.topOf (Sum.inr X) = none := by
    rw [hsb, Board.attach_topOf_ne _ _ _ hatt₁ (Ne.symm hb₁)]
    exact hXtop
  have hsbotX : s.board.bottomOf X = some b₁ := by
    rw [hsb]
    exact (Board.bottomOf_eq _ _ _).mpr (Board.attach_topOf _ _ _ hatt₁)
  have hrkXs : X.rank.toIdx = s.heights X.suit := by rw [hsh]; exact hrk
  -- move 1: the landed card worries back onto the foundation
  obtain ⟨t, hmove1⟩ :
      ∃ t, s.apply (Move.pileStack X) = some t := by
    refine ⟨{ s with
      board := s.board.detach b₁,
      heights := fun σ => if σ = X.suit then s.heights σ + 1 else s.heights σ }, ?_⟩
    rw [apply_pileStack_iff]
    exact ⟨hstopX, b₁, hsbotX, hrkXs, rfl⟩
  have htlit : t = { s with
      board := s.board.detach b₁,
      heights := fun σ => if σ = X.suit then s.heights σ + 1 else s.heights σ } := by
    have h := apply_pileStack_iff.mp hmove1
    obtain ⟨b', hb', hrk', hshape⟩ := h.2
    have hb'eq : b' = b₁ := Option.some.inj (hb'.symm.trans hsbotX)
    rw [hb'eq] at hshape
    exact hshape
  have htb : t.board = u.board := by
    rw [htlit]
    show (s.board.detach b₁) = u.board
    rw [hsb]
    exact Board.attach_detach_cancel hatt₁
  have htrk : X.rank.toIdx + 1 = t.heights X.suit := by
    rw [htlit]
    show X.rank.toIdx + 1 =
      (if X.suit = X.suit then s.heights X.suit + 1 else s.heights X.suit)
    rw [ite_eq_left rfl, hsh]
    exact congrArg _ hrk
  -- the other commit's placement guard survives the shuttle's midpoint
  have hcpT : t.canPlace X b₂ = true := by
    cases b₂ with
    | inl a =>
        obtain ⟨h1, h2⟩ := canPlace_inl_iff.mp hcp₂
        exact canPlace_inl_iff.mpr ⟨by rw [htb]; exact h1, h2⟩
    | inr d =>
        obtain ⟨h1, h2, h3⟩ := canPlace_inr_iff.mp hcp₂
        refine canPlace_inr_iff.mpr ⟨by rw [htb]; exact h1, ?_, h3⟩
        show (t.board.bottomOf d).isSome = true
        rw [htb]
        exact h2
  -- move 2: back onto the other commit's base
  obtain ⟨w, hmove2⟩ :
      ∃ w, t.apply (Move.stackPile X b₂) = some w := by
    refine ⟨{ t with
      board := bd₂,
      heights := fun σ => if σ = X.suit then t.heights σ - 1 else t.heights σ }, ?_⟩
    rw [apply_stackPile_iff]
    refine ⟨htrk, hcpT, bd₂, ?_, rfl⟩
    rw [htb]
    exact hatt₂
  have hwlit : w = { t with
      board := bd₂,
      heights := fun σ => if σ = X.suit then t.heights σ - 1 else t.heights σ } := by
    have h := apply_stackPile_iff.mp hmove2
    obtain ⟨bd', hatt', hshape⟩ := h.2.2
    have hbd'eq : bd' = bd₂ := by
      rw [htb] at hatt'
      exact Option.some.inj (hatt'.symm.trans hatt₂)
    rw [hbd'eq] at hshape
    exact hshape
  -- the shuttle's end state IS the other commit's successor
  have hw_eq : w = s' := by
    apply state_ext
    · -- deal
        have h1 : w.deal = t.deal := by rw [hwlit]
        have h2 : t.deal = s.deal := by rw [htlit]
        have h3 : s.deal = u.deal := by rw [hshape₁]
        have h4 : s'.deal = u.deal := by rw [hshape₂]
        rw [h1, h2, h3, ← h4]
    · -- board
        have h1 : w.board = bd₂ := by rw [hwlit]
        have h2 : s'.board = bd₂ := by rw [hshape₂]
        rw [h1, h2]
    · -- heights: the bump and the drop cancel at X's suit
        funext σ
        have hw : w.heights σ =
            (if σ = X.suit then t.heights σ - 1 else t.heights σ) := by
          rw [hwlit]
        have ht : t.heights σ =
            (if σ = X.suit then s.heights σ + 1 else s.heights σ) := by
          rw [htlit]
        have hs'lit : s'.heights σ = u.heights σ := by rw [hshape₂]
        have hslit : s.heights σ = u.heights σ := by rw [hshape₁]
        rw [hw, ht, hslit, hs'lit]
        by_cases hσ : σ = X.suit
        · rw [ite_eq_left hσ, ite_eq_left hσ]
          omega
        · rw [ite_eq_right hσ, ite_eq_right hσ]
    · -- depths
        have h1 : w.depths = t.depths := by rw [hwlit]
        have h2 : t.depths = s.depths := by rw [htlit]
        have h3 : s.depths = u.depths := by rw [hshape₁]
        have h4 : s'.depths = u.depths := by rw [hshape₂]
        rw [h1, h2, h3, ← h4]
    · -- stock: both commits splice the same position
        have h1 : w.stock = t.stock := by rw [hwlit]
        have h2 : t.stock = s.stock := by rw [htlit]
        have h3 : s.stock = ⟨Cycle.removeIdx u.stock.cards i, i⟩ := by rw [hshape₁]
        have h4 : s'.stock = ⟨Cycle.removeIdx u.stock.cards i, i⟩ := by rw [hshape₂]
        rw [h1, h2, h3, h4]
    · -- drawStep
        have h1 : w.drawStep = t.drawStep := by rw [hwlit]
        have h2 : t.drawStep = s.drawStep := by rw [htlit]
        have h3 : s.drawStep = u.drawStep := by rw [hshape₁]
        have h4 : s'.drawStep = u.drawStep := by rw [hshape₂]
        rw [h1, h2, h3, ← h4]
  refine ⟨[Move.pileStack X, Move.stackPile X b₂], ?_, ?_⟩
  · intro m hm
    rcases List.mem_cons.mp hm with h | h
    · rw [h]; rfl
    · rw [List.mem_singleton.mp h]; rfl
  · simp only [State.run, hmove1, hmove2]
    exact congrArg some hw_eq

/-- **The destination collapse at the commitment level** (§6.3's
within-channel twin choice, the provable half): the two tableau-arm
successors of the same drawn card at one WF state are `closureEq`
whenever the card is stackable at its suit's rung — the shuttle runs
both ways through the foundation.  This covers both destination twins
and (for kings) the free-anchor pairs; the rung premise is
load-bearing — without it the landings are closure-separated
(`witnesses/C2KingAnchorWitness.lean`). -/
theorem commitTableau_class {u : State} (hwf : u.WF) {X : Card}
    (hrk : X.rank.toIdx = u.heights X.suit)
    {s s' : State} (hs : CommitTableau u X s) (hs' : CommitTableau u X s') :
    closureEq s s' := by
  obtain ⟨p₁, hall₁, hrun₁⟩ := commitTableau_shuttle hwf hrk hs hs'
  obtain ⟨p₂, hall₂, hrun₂⟩ := commitTableau_shuttle hwf hrk hs' hs
  exact ⟨⟨p₁, hrun₁, hall₁⟩, ⟨p₂, hrun₂, hall₂⟩⟩

/-! ## §10. The poset register (§7's finite lemma, PROVEN) -/

/-- §7's finite lemma: among three live ball pinnings some two
coincide — unless one is `direct` (whose dominance is P2's class
half).  Proof: the king gate kills the receiver channels (a live hole
makes `X` a king, `receivers_king_nil`); otherwise the borrows
pigeonhole through the twin pair (`receivers_twin_pair`), a live dig
forbids two distinct live borrows (**P1**), and no third distinct
slot exists.  This is the whole "two mutually exclusive cases × two
options" table of §6.7. -/
theorem register_le_two {st : State} {X : Card} (hwf : st.WF)
    {r₁ r₂ r₃ : Label X}
    (h₁ : LabelLive st X r₁) (h₂ : LabelLive st X r₂) (h₃ : LabelLive st X r₃)
    (hb₁ : r₁ ≠ Label.toStack) (hb₂ : r₂ ≠ Label.toStack)
    (hb₃ : r₃ ≠ Label.toStack) :
    r₁ = r₂ ∨ r₁ = r₃ ∨ r₂ = r₃ ∨
      r₁ = Label.direct ∨ r₂ = Label.direct ∨ r₃ = Label.direct := by
  -- the king gate: a live hole makes every receiver channel dead
  by_cases hh : ∃ a, HoleLive st X a
  · obtain ⟨a, hka⟩ := hh
    have kill : ∀ r : Label X, LabelLive st X r →
        r = Label.hole ∨ r = Label.toStack := by
      intro r hlive
      cases r with
      | direct =>
          have hx : ∃ Y, DirectLive st X Y := hlive
          obtain ⟨Y, hd⟩ := hx
          exact absurd hd.hY (receivers_king_nil hka.hK)
      | dig =>
          have hx : ∃ Y, DigLive st X Y := hlive
          obtain ⟨Y, hd⟩ := hx
          exact absurd hd.hY (receivers_king_nil hka.hK)
      | borrow p =>
          obtain ⟨hp, _⟩ := (hlive : ∃ hp : canSitOn X p = true, BorrowLive st X p)
          exact absurd hp (receivers_king_nil hka.hK)
      | hole => exact Or.inl rfl
      | toStack => exact Or.inr rfl
    rcases kill _ h₁ with e₁ | e₁
    · rcases kill _ h₂ with e₂ | e₂
      · rcases kill _ h₃ with e₃ | e₃
        · exact Or.inl (e₁.trans e₂.symm)
        · exact absurd e₃ hb₃
      · exact absurd e₂ hb₂
    · exact absurd e₁ hb₁
  -- no live hole: `.hole` labels contradict their own liveness
  have killH : ∀ (r : Label X), r = Label.hole → ¬ LabelLive st X r := by
    intro r he hlive
    rw [he] at hlive
    have hx : ∃ a, HoleLive st X a := hlive
    obtain ⟨a, ha⟩ := hx
    exact hh ⟨a, ha⟩
  cases r₁ with
  | direct => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | toStack => exact absurd rfl hb₁
  | hole =>
      have kf := killH _ rfl h₁
      exact kf.elim
  | dig =>
      cases r₂ with
      | direct => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      | toStack => exact absurd rfl hb₂
      | hole =>
          have kf := killH _ rfl h₂
          exact kf.elim
      | dig => exact Or.inl rfl
      | borrow p₂ =>
          cases r₃ with
          | direct => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
          | toStack => exact absurd rfl hb₃
          | hole =>
              have kf := killH _ rfl h₃
              exact kf.elim
          | dig => exact Or.inr (Or.inl rfl)
          | borrow p₃ =>
              by_cases hp : p₂ = p₃
              · exact Or.inr (Or.inr (Or.inl (by rw [hp])))
              · exfalso
                have hx₁ : ∃ Y, DigLive st X Y := h₁
                obtain ⟨Y₀, hd⟩ := hx₁
                obtain ⟨_, hbl₂⟩ := (h₂ : ∃ hp : canSitOn X p₂ = true, BorrowLive st X p₂)
                obtain ⟨_, hbl₃⟩ := (h₃ : ∃ hp : canSitOn X p₃ = true, BorrowLive st X p₃)
                exact p1_bothBorrows_noDig hwf hbl₂ hbl₃ hp hd
  | borrow p₁ =>
      cases r₂ with
      | direct => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      | toStack => exact absurd rfl hb₂
      | hole =>
          have kf := killH _ rfl h₂
          exact kf.elim
      | dig =>
          cases r₃ with
          | direct => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
          | toStack => exact absurd rfl hb₃
          | hole =>
              have kf := killH _ rfl h₃
              exact kf.elim
          | dig => exact Or.inr (Or.inr (Or.inl rfl))
          | borrow p₃ =>
              by_cases hp : p₁ = p₃
              · exact Or.inr (Or.inl (by rw [hp]))
              · exfalso
                have hx₂ : ∃ Y, DigLive st X Y := h₂
                obtain ⟨Y₀, hd⟩ := hx₂
                obtain ⟨_, hbl₁⟩ := (h₁ : ∃ hp : canSitOn X p₁ = true, BorrowLive st X p₁)
                obtain ⟨_, hbl₃⟩ := (h₃ : ∃ hp : canSitOn X p₃ = true, BorrowLive st X p₃)
                exact p1_bothBorrows_noDig hwf hbl₁ hbl₃ hp hd
      | borrow p₂ =>
          cases r₃ with
          | direct => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
          | toStack => exact absurd rfl hb₃
          | hole =>
              have kf := killH _ rfl h₃
              exact kf.elim
          | dig =>
              by_cases hp : p₁ = p₂
              · exact Or.inl (by rw [hp])
              · exfalso
                have hx₃ : ∃ Y, DigLive st X Y := h₃
                obtain ⟨Y₀, hd⟩ := hx₃
                obtain ⟨_, hbl₁⟩ := (h₁ : ∃ hp : canSitOn X p₁ = true, BorrowLive st X p₁)
                obtain ⟨_, hbl₂⟩ := (h₂ : ∃ hp : canSitOn X p₂ = true, BorrowLive st X p₂)
                exact p1_bothBorrows_noDig hwf hbl₁ hbl₂ hp hd
          | borrow p₃ =>
              by_cases hp12 : p₁ = p₂
              · exact Or.inl (by rw [hp12])
              · obtain ⟨_, hbl₁⟩ := (h₁ : ∃ hp : canSitOn X p₁ = true, BorrowLive st X p₁)
                obtain ⟨_, hbl₂⟩ := (h₂ : ∃ hp : canSitOn X p₂ = true, BorrowLive st X p₂)
                obtain ⟨_, hbl₃⟩ := (h₃ : ∃ hp : canSitOn X p₃ = true, BorrowLive st X p₃)
                rcases receivers_twin_pair hbl₁.hp hbl₂.hp hp12 hbl₃.hp with
                  h' | h'
                · exact Or.inr (Or.inl (by rw [h']))
                · exact Or.inr (Or.inr (Or.inl (by rw [h'])))

/-! ## §11. The play-level content — from pinned claims to premises

The wave-17 pillar set pinned five play-level universals here as
open rows with proof plans.  The 2026-10-05 C2-closure session
refute-probed them and found **four of the five FALSE as stated** in
the free model semantics
(`witnesses/C2KingAnchorWitness.lean`: a climb-blocked stocked king
on a pristine WF state — one spade-blocked stock, seven free anchors,
all foundations at zero — whose anchor landings are pairwise
closure-separated because `pileStack` of the landed king is dead
along every accommodation walk; the negated as-stated universals are
`wk_c2_as_stated_false`, `wk_same_pin_as_stated_false`,
`wk_p2_direct_as_stated_false`, `wk_crease_as_stated_false`):

* `succ_labeled` (P0): the channel list is incomplete for the model's
  king-unseat/an.channel taxonomy — a pile head seated on an anchor
  leaves by its rank-dig and the king lands on the vacated anchor,
  which is `hole`-shaped at the end state but dead at the root
  (no free anchor there), so no `LabelLive`-at-`st` channel names it;
* `p2_direct_class` / `same_pin_closureEq` / `crease_chain_absorbed`:
  every tableau-arm successor of the same stocked card is asked to
  join one class, but an **unstackable-at-its-rung** target can never
  leave its landed seat by accommodation moves (only `pileStack`
  ever unseats a card), so two landings are genuinely closure-split;
* the assembled `c2_two_option` inherited the same hole.

The statements left the library per the refutation protocol; the
**proven half of the destination collapse** — the stackable-rung
regime, where the join is the two-move foundation shuttle — is
`commitTableau_class` above (§9.5), which is exactly the engine's
safe-sweep canonicalization regime.

The five requests survive as the EXPLICIT PREMISES of `c2_two_option`
below, whose assembly (the register, the pigeonhole, the
arms-cannot-label step) was and stays PROVEN.  The plans of the
formerly-pinned rows follow, as the open-program record — what a
future C2 pass must prove or re-scope to close each premise.

**P0 — the labeling** (§6.4's channel-list completeness; now the
`hlab` premises): every macro successor of the `Draw(X)` commitment
is reached through some channel whose atom is live at the
commitment's root state.  PLAN: from `hstep`'s accommodation
(`pileStack`/`stackPile` only), classify the commit's landing at the
end state; tableau arm — receiver landings by the §6.4 extraction
(direct/dig/borrow by the coverer's `only_blocker_is_twin` and the
worry-back ray), king landings on free anchors (hole); stack arm —
`toStack`.  The prover-side gap (the king-anchor channel above) must
be added to the channel list or the guard added first.

**P2, class half** (premise `hp2`): a successor through any `P2Safe`
channel is closure-equal to the direct-committed successor.  PLAN:
the `p2_core_dig`/`p2_core_borrow` one-step cores lifted to plays by
the Commutation/Frame reorder kit, with the crease residue for
chains; the late-`PileStack X` merge handles the stack arm under
`P2Safe .toStack` (the tableau landing writes no heights).

**P3, class half** (premise `hpin`): successors through the same
channel pin are closure-equal.  PLAN: the free-float collapse —
equal spend structures differ only in floats outside the
commitment's two-type ball, whose legality masks the commit does not
touch; nested/chained residues by the depth ordering (the crease).
The within-channel twin choice, when the target is stackable at its
rung, is PROVEN — `commitTableau_class`; the unstackable corner is
the witness's split, so a future honest statement must carry the
rung premise.

**The crease** (formerly `crease_chain_absorbed`; folded into `hpin`
and `hp2`'s plans): multi-rank dig/borrow chains attach to a single
parent side and are absorbed by the shallower pinning; the
`InRay`-confinement + `merge_refires_*` walk + the
`stackPile_pileStack_cancel` cancellation, depth-ordered.

**The L1/L2-diligence residue corner** (premise `hball`; the one row
never refuted and believed true): when direct is absent, the stack
arm is reached only through raises, and two distinct ball pins are
simultaneously live — the three-class shape the streamlined argument
must exclude pairwise, by the raise-chain geometry (the prefix raise
is same-suit deterministic, so the raise spends into one of the two
live pins' balls and the stack successor reproduces inside that
pin's class). -/

/-! ## §12. The theorem (the two-option commitment bound) -/

/-- **C2, streamlined, the conditional form** (§7): a commitment has
at most two macro successors — every three successors of the
`Draw(X)` commitment contain a closure-equal pair — CONDITIONAL on
the play-level content, which is stated as explicit premises (the
wave-17 pillars, four of which were refuted as UNIVERal claims by
`witnesses/C2KingAnchorWitness.lean` and left the library; see §11
above for the record and the plans, and `commitTableau_class` for
the proven half of the destination collapse):

* `hlab₁ hlab₂ hlab₃` — the run-P0 content: each successor is
  labeled by a channel live at the commitment's root;
* `hp2` — the P2 class-join: every `P2Safe`-labeled successor joins
  any direct commit's class;
* `hpin` — the P3 same-pin join: two successors through one live
  channel pin are closure-equal (the *proven* regime: when the drawn
  card is stackable at its rung and the accommodations coincide,
  `commitTableau_class` IS this premise, unconditionally);
* `hball` — the L1/L2-diligence corner (believed true, unrefuted):
  with direct absent, the stack arm and two distinct ball pins
  resolve pairwise.

The assembly — the register (`register_le_two`), the pigeonhole,
and `through_direct_hole_commits`' arms-cannot-label step (`harms`,
built from P1's `p1_bothBorrows_noDig` closing the register itself)
— was proven in wave 17 and stays proven here: given the premises,
the case tree below is complete.  Stripping the premises re-offers
exactly the refuted as-stated theorem, so a future C2 pass closes
each premise (or re-scopes it) per §11's plans and deletes the
corresponding hypothesis here. -/
theorem c2_two_option {st : State} (hwf : st.WF) {X : Card}
    {s₁ s₂ s₃ : State}
    (_h₁ : macroStep st (MacroMove.drawCommit X) s₁)
    (_h₂ : macroStep st (MacroMove.drawCommit X) s₂)
    (_h₃ : macroStep st (MacroMove.drawCommit X) s₃)
    (hlab₁ : ∃ r : Label X, LabelLive st X r ∧ SuccThrough st X r s₁)
    (hlab₂ : ∃ r : Label X, LabelLive st X r ∧ SuccThrough st X r s₂)
    (hlab₃ : ∃ r : Label X, LabelLive st X r ∧ SuccThrough st X r s₃)
    (hp2 : ∀ {sd : State}, commitApplies st (MacroMove.drawCommit X) sd →
      ∀ {r : Label X} {s : State}, SuccThrough st X r s →
      P2Safe st X r → closureEq sd s)
    (hpin : ∀ {r : Label X} {s s' : State}, LabelLive st X r →
      SuccThrough st X r s → SuccThrough st X r s' → closureEq s s')
    (hball : (¬∃ sd, commitApplies st (MacroMove.drawCommit X) sd) →
      ∀ {rₐ r_b : Label X} {s₀ sₐ s_b : State},
      LabelLive st X Label.toStack → SuccThrough st X Label.toStack s₀ →
      LabelLive st X rₐ → SuccThrough st X rₐ sₐ →
      LabelLive st X r_b → SuccThrough st X r_b s_b →
      rₐ ≠ r_b →
      closureEq s₀ sₐ ∨ closureEq s₀ s_b ∨ closureEq sₐ s_b) :
    closureEq s₁ s₂ ∨ closureEq s₁ s₃ ∨ closureEq s₂ s₃ := by
  obtain ⟨r₁, hl₁, ht₁⟩ := hlab₁
  obtain ⟨r₂, hl₂, ht₂⟩ := hlab₂
  obtain ⟨r₃, hl₃, ht₃⟩ := hlab₃
  by_cases hd : ∃ sd, commitApplies st (MacroMove.drawCommit X) sd
  · -- P2's world: every safe successor joins the direct class
    obtain ⟨sd, hsd⟩ := hd
    by_cases h1s : P2Safe st X r₁
    · by_cases h2s : P2Safe st X r₂
      · by_cases h3s : P2Safe st X r₃
        · have q₁ := hp2 hsd ht₁ h1s
          have q₂ := hp2 hsd ht₂ h2s
          exact Or.inl ⟨accommodates_trans q₁.2 q₂.1,
            accommodates_trans q₂.2 q₁.1⟩
        · have e₃ : r₃ = Label.toStack := unsafe_is_toStack h3s
          rw [e₃] at hl₃ ht₃
          have q₁ := hp2 hsd ht₁ h1s
          have q₂ := hp2 hsd ht₂ h2s
          exact Or.inl ⟨accommodates_trans q₁.2 q₂.1,
            accommodates_trans q₂.2 q₁.1⟩
      · by_cases h3s : P2Safe st X r₃
        · have q₁ := hp2 hsd ht₁ h1s
          have q₃ := hp2 hsd ht₃ h3s
          exact Or.inr (Or.inl ⟨accommodates_trans q₁.2 q₃.1,
            accommodates_trans q₃.2 q₁.1⟩)
        · have e₂ : r₂ = Label.toStack := unsafe_is_toStack h2s
          have e₃ : r₃ = Label.toStack := unsafe_is_toStack h3s
          rw [e₂] at hl₂ ht₂
          rw [e₃] at hl₃ ht₃
          exact Or.inr (Or.inr (hpin hl₂ ht₂ ht₃))
    · by_cases h2s : P2Safe st X r₂
      · by_cases h3s : P2Safe st X r₃
        · have q₂ := hp2 hsd ht₂ h2s
          have q₃ := hp2 hsd ht₃ h3s
          exact Or.inr (Or.inr ⟨accommodates_trans q₂.2 q₃.1,
            accommodates_trans q₃.2 q₂.1⟩)
        · have e₁ : r₁ = Label.toStack := unsafe_is_toStack h1s
          have e₃ : r₃ = Label.toStack := unsafe_is_toStack h3s
          rw [e₁] at hl₁ ht₁
          rw [e₃] at hl₃ ht₃
          exact Or.inr (Or.inl (hpin hl₁ ht₁ ht₃))
      · by_cases h3s : P2Safe st X r₃
        · have e₁ : r₁ = Label.toStack := unsafe_is_toStack h1s
          have e₂ : r₂ = Label.toStack := unsafe_is_toStack h2s
          rw [e₁] at hl₁ ht₁
          rw [e₂] at hl₂ ht₂
          exact Or.inl (hpin hl₁ ht₁ ht₂)
        · have e₁ : r₁ = Label.toStack := unsafe_is_toStack h1s
          have e₂ : r₂ = Label.toStack := unsafe_is_toStack h2s
          rw [e₁] at hl₁ ht₁
          rw [e₂] at hl₂ ht₂
          exact Or.inl (hpin hl₁ ht₁ ht₂)
  · -- direct absent: the zero-spend arms cannot label
    have harms : ∀ (r : Label X) (s : State),
        r = Label.direct ∨ r = Label.hole → ¬ SuccThrough st X r s := by
      intro r s he hth
      exact hd (through_direct_hole_commits hth he)
    by_cases h12 : r₁ = r₂
    · rw [h12] at ht₁
      exact Or.inl (hpin hl₂ ht₁ ht₂)
    · by_cases h13 : r₁ = r₃
      · rw [h13] at ht₁
        exact Or.inr (Or.inl (hpin hl₃ ht₁ ht₃))
      · by_cases h23 : r₂ = r₃
        · rw [h23] at ht₂
          exact Or.inr (Or.inr (hpin hl₃ ht₂ ht₃))
        · -- pairwise distinct: a toStack must be present, else the
          -- register refutes the shape outright
          have hstack : r₁ = Label.toStack ∨ r₂ = Label.toStack ∨
              r₃ = Label.toStack := by
            by_cases h1t : r₁ = Label.toStack
            · exact Or.inl h1t
            · by_cases h2t : r₂ = Label.toStack
              · exact Or.inr (Or.inl h2t)
              · by_cases h3t : r₃ = Label.toStack
                · exact Or.inr (Or.inr h3t)
                · exfalso
                  rcases register_le_two hwf hl₁ hl₂ hl₃ h1t h2t h3t with
                    heq | heq | heq | hdir | hdir | hdir
                  · exact h12 heq
                  · exact h13 heq
                  · exact h23 heq
                  · exact harms _ s₁ (Or.inl hdir) ht₁
                  · exact harms _ s₂ (Or.inl hdir) ht₂
                  · exact harms _ s₃ (Or.inl hdir) ht₃
          -- the residue corner: the stack label against the two
          -- distinct ball pins
          rcases hstack with e | e | e
          · rw [e] at hl₁ ht₁
            rcases hball hd hl₁ ht₁ hl₂ ht₂ hl₃ ht₃ h23 with
              q | q | q
            · exact Or.inl q
            · exact Or.inr (Or.inl q)
            · exact Or.inr (Or.inr q)
          · rw [e] at hl₂ ht₂
            rcases hball hd hl₂ ht₂ hl₁ ht₁ hl₃ ht₃ h13 with
              q | q | q
            · exact Or.inl (closureEq_symm q)
            · exact Or.inr (Or.inr q)
            · exact Or.inr (Or.inl q)
          · rw [e] at hl₃ ht₃
            rcases hball hd hl₃ ht₃ hl₁ ht₁ hl₂ ht₂ h12 with
              q | q | q
            · exact Or.inr (Or.inl (closureEq_symm q))
            · exact Or.inr (Or.inr (closureEq_symm q))
            · exact Or.inl q

/-! ## §12.5. The rung re-scope (wave-19): the premises' derivable
fragments

The wave-18 restructure left the play-level content of §7's theorem
as the explicit premises of `c2_two_option`, and the king-anchor
witness showed the UNGUARDED forms of `hpin`/`hp2` are false
(the climb-blocked stocked king's anchor landings are
closure-separated — the failure is exactly the rung premise).  This
section makes the re-scope precise for a class of channels wide
enough to contain the witness's own corner: the **zero-spend
channels** (`direct`, `hole`), whose `LabelSig` is `α = []`.

The derivations carry the rung premise AT THE ROOT
(`X.rank.toIdx = st.heights X.suit`) and nothing else play-level:

* `succThrough_zeroSpend` — the empty signature forces the whole
  channel play empty, so both the arm and its commit sit at `st`
  (with `through_direct_hole_commits`, this is also why the
  direct-absent world of §12 cannot present a zero-spend label);
* `pin_join_zeroSpend_rung` — `hpin`'s content for these channels
  IS `commitTableau_class` at the shared root;
* `p2_join_zeroSpend_rung` — `hp2`'s content: the tableau arm of the
  root commit is `commitTableau_class` again, and the STACK arm of
  the root commit joins by the two-move worried-back roundtrip
  (`stackPile X b` rebuilds the tableau successor exactly, `pileStack
  X` returns it) — §6.7's "late `PileStack(X)` merge" (the 1,102
  mixed-kind single-class commitments) as a proof;
* `c2_two_option_zeroSpend_rung` — the derived-scope bound itself:
  three zero-spend-labeled successors contain a closure-equal pair,
  with NO play-level premises left.

What stays out (the honest residue, per §11's plans): the spend
channels (`dig`, `borrow p`) and the stack channel's same-pin cases,
where two witnesses' plays may end at different accommodation states
— the free-float reconciliation (α₁ ≠ α₂) plus the crease chains.
The rung premise at the root does not reach there: a witness's play
can raise and re-drop a suit past the rung.  These remain premises
of `c2_two_option`. -/

/-- The zero-spend channels' witnesses commit at the root: both
`direct` and `hole` demand the EMPTY accommodation (their `LabelSig`
is `α = []`), so the channel play collapses and the tableau arm (the
only arm these channels serve) fires at `st` itself. -/
theorem succThrough_zeroSpend {st : State} {X : Card} {r : Label X}
    {s : State} (h : SuccThrough st X r s)
    (he : r = Label.direct ∨ r = Label.hole) :
    CommitTableau st X s := by
  obtain ⟨u, α, hrun, _, harm, hsig⟩ := h
  rcases he with he | he
  · rw [he] at harm hsig
    have hα : α = [] := hsig
    rw [hα] at hrun
    rw [(run_nil_elim hrun).symm] at harm
    exact harm
  · rw [he] at harm hsig
    have hα : α = [] := hsig
    rw [hα] at hrun
    rw [(run_nil_elim hrun).symm] at harm
    exact harm

/-- **`hpin`'s derivable half** (wave-19): two successors through one
zero-spend channel join, at a WF state where `X` is stackable at its
rung.  The zero-spend signature puts both commits at the ROOT, so
this is `commitTableau_class` applied at `st` — `LabelLive` is not
even consulted.  The unstackable corner (the king-anchor witness's
split) is exactly the rung premise's failure, and no other
play-level premise is needed for these channels. -/
theorem pin_join_zeroSpend_rung {st : State} (hwf : st.WF) {X : Card}
    (hrk : X.rank.toIdx = st.heights X.suit)
    {r : Label X} (he : r = Label.direct ∨ r = Label.hole)
    {s s' : State} (h₁ : SuccThrough st X r s)
    (h₂ : SuccThrough st X r s') : closureEq s s' :=
  commitTableau_class hwf hrk (succThrough_zeroSpend h₁ he)
    (succThrough_zeroSpend h₂ he)

/-- **`hp2`'s derivable half** (wave-19): every zero-spend-labeled
successor joins EVERY root commit's class, at a WF state where `X` is
stackable at its rung — both arms of the root commitment.  The
tableau arm of the root commit is `commitTableau_class` at the shared
root.  The STACK arm of the root commit joins by the worried-back
roundtrip: `stackPile X b` (the un-stack guard holds — the stack
commit itself bumped the rank edge) rebuilds the tableau successor
EXACTLY — same board (the landing's `attach`), same stock splice (both
arms jump the SAME reachable position), bump/drop heights cancelling
at `X`'s suit — and `pileStack X` (legal: `X` freshly topped at its
own rung) returns it.  This is §6.7's "late `PileStack(X)` merge" (the
corpus's 1,102 mixed-kind single-class commitments) as a proof. -/
theorem p2_join_zeroSpend_rung {st : State} (hwf : st.WF) {X : Card}
    (hrk : X.rank.toIdx = st.heights X.suit)
    {r : Label X} (he : r = Label.direct ∨ r = Label.hole)
    {sd s : State} (hsd : commitApplies st (MacroMove.drawCommit X) sd)
    (hth : SuccThrough st X r s) : closureEq sd s := by
  have hs : CommitTableau st X s := succThrough_zeroSpend hth he
  obtain ⟨b, hcp, hto⟩ := hs
  obtain ⟨i, bd, hpos, hatt, hslit⟩ := applyDrawTo_iff.mp hto
  -- the landing base is never X's own seat (a card does not fit itself)
  have hbX : b ≠ Sum.inr X := by
    cases b with
    | inl a => exact sumInl_ne_sumInr
    | inr d =>
        intro hcon
        have hd : d = X := Sum.inr.inj hcon
        have hfit := canSitOn_of_canPlace_inr hcp
        rw [hd] at hfit
        obtain ⟨hr, -⟩ := (canSitOn_eq X X).mp hfit
        omega
  -- X rides no stack at st: unplaced (the attach guard) and out of
  -- every hidden slice (stocked, via the reachable-position guard)
  have hbox : st.board.bottomOf X = none :=
    ((Board.attach_eq_some_iff _ _ _).mp (by rw [hatt]; simp)).2
  have hstockmem : X ∈ st.stock.cards :=
    Pace.mem_of_posOf st.stock.cards st.stock.cursor X i
      (reachablePos_posOf hpos)
  have hhid : ∀ a, X ∉ st.hidden a :=
    fun a => stocked_not_mem_hidden hwf hstockmem
  have hXtop : st.board.topOf (Sum.inr X) = none :=
    State.topOf_inr_eq_none hwf hbox hhid
  rcases (commitApplies_draw_cases st X sd).mp hsd with htab | hstack
  · -- both are root tableau commits: the destination collapse applies
    exact commitTableau_class hwf hrk htab ⟨b, hcp, hto⟩
  · -- the stack commit at the root: the worried-back roundtrip joins
    obtain ⟨i', hrpos', hrk', hsdlit⟩ := applyDrawStackTo_iff.mp hstack
    have hii : i = i' := Option.some.inj (hpos.symm.trans hrpos')
    rw [← hii] at hsdlit
    -- the stack commit's per-suit height read (bumped at X's suit)
    have hsdh : ∀ σ : Suit, sd.heights σ =
        (if σ = X.suit then st.heights σ + 1 else st.heights σ) := by
      intro σ
      rw [hsdlit]
    have hedge : X.rank.toIdx + 1 = sd.heights X.suit := by
      have h1 := hsdh X.suit
      rw [ite_eq_left rfl] at h1
      rw [h1, hrk']
    -- the stack commit wrote neither the board nor the pacing guard
    have hbdSD : sd.board = st.board := by rw [hsdlit]
    have hcpSD : sd.canPlace X b = true := by
      rw [canPlace_board_congr hbdSD]
      exact hcp
    have hattSD : sd.board.attach b X = some bd := by
      rw [hbdSD]
      exact hatt
    -- forward: the stack commit worries X back onto the base
    have hfwd : sd.apply (Move.stackPile X b) = some s := by
      rw [apply_stackPile_iff]
      refine ⟨hedge, hcpSD, bd, hattSD, ?_⟩
      apply state_ext
      · rw [hslit, hsdlit]
      · rw [hslit, hsdlit]
      · -- heights: the bump and the drop cancel at X's suit
        funext σ
        rw [hslit]
        show st.heights σ =
          (if σ = X.suit then sd.heights σ - 1 else sd.heights σ)
        by_cases hσ : σ = X.suit
        · rw [hσ, ite_eq_left rfl]
          have h1 := hsdh X.suit
          rw [ite_eq_left rfl] at h1
          rw [h1]
          omega
        · rw [ite_eq_right hσ, hsdh σ, ite_eq_right hσ]
      · rw [hslit, hsdlit]
      · -- stock: both commitments jump the same reachable position
        rw [hslit, hsdlit]
      · rw [hslit, hsdlit]
    -- reverse: `pileStack X` at the landed successor returns it
    have hsb : s.board = bd := by rw [hslit]
    have hstop : s.board.topOf (Sum.inr X) = none := by
      rw [hsb]
      exact (Board.attach_topOf_ne _ _ _ hatt (Ne.symm hbX)).trans hXtop
    have hsbot : s.board.bottomOf X = some b := by
      rw [hsb]
      exact (Board.bottomOf_eq _ _ _).mpr (Board.attach_topOf _ _ _ hatt)
    have hrung : X.rank.toIdx = s.heights X.suit := by
      rw [hslit]
      exact hrk
    have hrev : s.apply (Move.pileStack X) = some sd := by
      rw [apply_pileStack_iff]
      refine ⟨hstop, b, hsbot, hrung, ?_⟩
      apply state_ext
      · rw [hsdlit, hslit]
      · -- board: the detach cancels the landing's attach
        rw [hsdlit, hslit]
        exact (Board.attach_detach_cancel hatt).symm
      · -- heights: the drop and the bump cancel at X's suit
        rw [hsdlit, hslit]
      · rw [hsdlit, hslit]
      · rw [hsdlit, hslit]
      · rw [hsdlit, hslit]
    refine ⟨⟨[Move.stackPile X b], ?_, ?_⟩,
      ⟨[Move.pileStack X], ?_, ?_⟩⟩
    · rw [run_singleton]
      exact hfwd
    · intro m hm
      rw [List.mem_singleton.mp hm]
      rfl
    · rw [run_singleton]
      exact hrev
    · intro m hm
      rw [List.mem_singleton.mp hm]
      rfl

/-- **The derived-scope two-option bound** (wave-19): at a
stackable-at-rung WF state, three successors of the `Draw(X)`
commitment all zero-spend-labeled contain a closure-equal pair — every
play-level premise of §12's conditional is discharged for this scope
(the register is not even consulted: any one zero-spend labeling
forces a root commit by `through_direct_hole_commits`, and all
zero-spend-labeled successors join EVERY root commit's class). -/
theorem c2_two_option_zeroSpend_rung {st : State} (hwf : st.WF)
    {X : Card} (hrk : X.rank.toIdx = st.heights X.suit)
    {s₁ s₂ s₃ : State}
    (_h₁ : macroStep st (MacroMove.drawCommit X) s₁)
    (_h₂ : macroStep st (MacroMove.drawCommit X) s₂)
    (_h₃ : macroStep st (MacroMove.drawCommit X) s₃)
    (_hl₁ : ∃ r : Label X, (r = Label.direct ∨ r = Label.hole) ∧
      LabelLive st X r ∧ SuccThrough st X r s₁)
    (_hl₂ : ∃ r : Label X, (r = Label.direct ∨ r = Label.hole) ∧
      LabelLive st X r ∧ SuccThrough st X r s₂)
    (_hl₃ : ∃ r : Label X, (r = Label.direct ∨ r = Label.hole) ∧
      LabelLive st X r ∧ SuccThrough st X r s₃) :
    closureEq s₁ s₂ ∨ closureEq s₁ s₃ ∨ closureEq s₂ s₃ := by
  obtain ⟨r₁, he₁, -, hth₁⟩ := _hl₁
  obtain ⟨r₂, he₂, -, hth₂⟩ := _hl₂
  obtain ⟨sd, hsd⟩ := through_direct_hole_commits hth₁ he₁
  have q₁ := p2_join_zeroSpend_rung hwf hrk he₁ hsd hth₁
  have q₂ := p2_join_zeroSpend_rung hwf hrk he₂ hsd hth₂
  exact Or.inl ⟨accommodates_trans q₁.2 q₂.1,
    accommodates_trans q₂.2 q₁.1⟩

/-! ## §13. The stretch corollary — the worry ray's two-suit
confinement (PROVEN) -/

/-- The worry-back ray rooted at `X` (§6.4's ascending borrow ray):
level-`n` cards sit `n` parent steps up, one rank per level; the
colors alternate strictly (the `canSitOn` color law). -/
def InRay (X : Card) : Nat → Card → Prop
  | 0, c => c = X
  | n + 1, c => ∃ d, InRay X n d ∧ canSitOn d c = true

/-- The ray's rank grading: a level-`n` card lives exactly `n` ranks
above the root (the ray ascends toward the kings, one rank per step). -/
theorem inRay_rank (X : Card) : ∀ (n : Nat) (c : Card),
    InRay X n c → c.rank.toIdx = X.rank.toIdx + n := by
  intro n
  induction n with
  | zero =>
      intro c h
      obtain rfl := h
      omega
  | succ n ih =>
      intro c h
      obtain ⟨d, hd, hfit⟩ := h
      have hrd := ih d hd
      have hrr := ((canSitOn_eq d c).mp hfit).1
      omega

/-- The ray's alternation: level parity fixes the color — even levels
share `X`'s color, odd levels carry the opposite.  This is §7's
stretch's "runs may repeat suits; only colors alternate": nothing
pins a suit beyond this, and the same *pair* reappears every second
rank with fresh cards. -/
theorem inRay_color (X : Card) : ∀ (n : Nat) (c : Card), InRay X n c →
    (n % 2 = 0 ∧ c.suit.color = X.suit.color) ∨
    (n % 2 = 1 ∧ c.suit.color ≠ X.suit.color) := by
  intro n
  induction n with
  | zero =>
      intro c h
      obtain rfl := h
      exact Or.inl ⟨by omega, rfl⟩
  | succ n ih =>
      intro c h
      obtain ⟨d, hd, hfit⟩ := h
      have hcc : d.suit.color ≠ c.suit.color := ((canSitOn_eq d c).mp hfit).2
      rcases ih d hd with ⟨h₀, hdX⟩ | ⟨h₁, hdX⟩
      · -- d even-level (shares X's color); c differs from d, hence from X
        refine Or.inr ⟨by omega, ?_⟩
        rw [hdX] at hcc
        exact Ne.symm hcc
      · -- d odd-level (avoids X's color); c differs from d, hence shares X's
        refine Or.inl ⟨by omega, ?_⟩
        exact color_pair_of_both_ne hcc hdX

/-- Same-level ray cards relate to `X`'s color identically: both share
it or both avoid it (level parity fixes the color relation). -/
theorem inRay_color_rel {X : Card} {n : Nat} {a b : Card}
    (ha : InRay X n a) (hb : InRay X n b) :
    (a.suit.color = X.suit.color ∧ b.suit.color = X.suit.color) ∨
    (a.suit.color ≠ X.suit.color ∧ b.suit.color ≠ X.suit.color) := by
  rcases inRay_color X n a ha with ⟨h₀, hc⟩ | ⟨h₁, hc⟩
  · rcases inRay_color X n b hb with ⟨h₀', hc'⟩ | ⟨h₁', hc'⟩
    · exact Or.inl ⟨hc, hc'⟩
    · exact absurd h₁' (by omega)
  · rcases inRay_color X n b hb with ⟨h₀', hc'⟩ | ⟨h₁', hc'⟩
    · exact absurd h₀' (by omega)
    · exact Or.inr ⟨hc, hc'⟩

/-- Same-level ray cards share their color (the relation to `X` is
parity-fixed; two-colors closes the avoid-case). -/
theorem inRay_same_color {X : Card} {n : Nat} {a b : Card}
    (ha : InRay X n a) (hb : InRay X n b) : a.suit.color = b.suit.color := by
  rcases inRay_color_rel ha hb with ⟨hc, hc'⟩ | ⟨hc, hc'⟩
  · exact hc.trans hc'.symm
  · exact color_pair_of_both_ne (Ne.symm hc) (Ne.symm hc')

/-- The ray's confinement: any three ray cards at one level span a
single twin pair — the level's suit choices are twins ("twins of at
most one red and one black channel"). -/
theorem inRay_twin_pair {X : Card} {n : Nat} {z₁ z₂ z : Card}
    (h₁ : InRay X n z₁) (h₂ : InRay X n z₂) (hne : z₁ ≠ z₂)
    (h : InRay X n z) : z = z₁ ∨ z = z₂ := by
  have hcol12 := inRay_same_color h₁ h₂
  have hcol1z := inRay_same_color h₁ h
  have hr1 := inRay_rank X n z₁ h₁
  have hr2 := inRay_rank X n z₂ h₂
  have hrz := inRay_rank X n z h
  have hrank12 : z₁.rank = z₂.rank := Rank.toIdx_inj (by omega)
  have hrank1z : z₁.rank = z.rank := Rank.toIdx_inj (by omega)
  have hpair : z₂ = z₁.flipSuit :=
    Card.flipSuit_eq_of_color_rank hcol12 hrank12 hne
  by_cases hzz : z = z₁
  · exact Or.inl hzz
  · exact Or.inr ((Card.flipSuit_eq_of_color_rank hcol1z hrank1z
      (fun hh => hzz hh.symm)).trans hpair.symm)

/-- The ray terminates at the kings' holes (§6.4: "borrows ascend
toward kings, which terminate at holes"): no ray card lives past rank
13. -/
theorem inRay_bounded {X : Card} {n : Nat} {c : Card}
    (hno : 13 ≤ X.rank.toIdx + n) : ¬ InRay X n c := by
  intro h
  have hr := inRay_rank X n c h
  have hlt := Rank.toIdx_lt c.rank
  omega

/-! ## §14. `stack_ball_corner` (the `hball` premise) — the raise-ray
geometry, the proven core

The one never-refuted pillar (§11's L1/L2-diligence corner): direct
absent, the stack channel live, two distinct ball pins live — the
three-class shape to be excluded pairwise.  The plan's central
mechanism is F2's same-suit determinism of the prefix raise; its core
is now proven:

1. `reachablePos_of_accommodation(_run)` — accommodation moves never
   touch the stock cycle or the draw step, so the commitment pacing
   guard is invariant along every accommodation play;
2. `heights_step_accommodation` — the per-move step law: a suit's
   standing height changes only at a same-suit `pileStack` (+1, with
   the fired card's rank-index pinned by the move's own guard to the
   standing level) or a same-suit `stackPile` (-1);
3. `raise_crossing_mem` — **F2's deterministic raise**: an
   accommodation play that crosses standing level `k` of `X`'s own
   suit upward fires, somewhere in its course, the `pileStack` of the
   UNIQUE `X`-suit card at rank-index `k` (at the first passage the
   standing height IS `k`, and the `pileStack` guard forces both the
   suit and the rank-index).

`stack_channel_world` assembles the corner's own precondition: WF +
the stack channel live + direct absent FORCE `X` reachable in the
stock and the standing height of `X`'s suit strictly below `X`'s
rank (a founded card is never stocked; a rung-matched reachable card
would fire the stack commit) — the raise content is present, not
degenerate.  `stack_raise_deterministic` and `stack_channel_raise_mem`
then deliver the named fact the residue analysis needs: EVERY
stack-channel witness's play fires the `pileStack` of `X`'s same-suit
rank-mate (the `X`-suit card one below `X`'s rank-index) — the final
raise that delivered `X`'s stackability — with
`raise_card_off_ball` the hygiene that this raise spends strictly
inside `X`'s own suit-column, never the twin's seat, never a
receiver, and never a pin's own signature card (the twin's suit is
the pair-flip, a borrow parent's suit the opposite color).

**The honest residue**, made precise: the deterministic raise must,
at its firing moment, find the rank-mate visible and un-covered, and
the moves that FREE it are the corner's actual content — reconciling
those freeing moves (the multi-rank dig/borrow chains of §11's
crease) with the two live pins' own witnessing plays is exactly the
free-float/crease residue of §12.5.  What is proven here bounds every
resolution: the stack channel cannot be witnessed without consuming
the one same-suit raise chain, so the three successors share a common
spine. -/

/-- Accommodation moves never touch the stock cycle or the draw step:
the commitment pacing guard `reachablePos` is invariant along them. -/
theorem reachablePos_of_accommodation {st s₁ : State} {m : Move}
    (h : st.apply m = some s₁) (c : Card)
    (hm : m.isAccommodation = true) :
    s₁.reachablePos c = st.reachablePos c := by
  cases m with
  | draw => simp [Move.isAccommodation] at hm
  | reveal a => simp [Move.isAccommodation] at hm
  | deckPile c b => simp [Move.isAccommodation] at hm
  | deckStack c => simp [Move.isAccommodation] at hm
  | pilePile c b => simp [Move.isAccommodation] at hm
  | pileStack c =>
      rw [apply_pileStack_iff] at h
      obtain ⟨_, b, _, _, hshape⟩ := h
      rw [hshape]
      rfl
  | stackPile c b =>
      rw [apply_stackPile_iff] at h
      obtain ⟨_, _, bd, _, hshape⟩ := h
      rw [hshape]
      rfl

/-- The play form of the pacing-guard invariance. -/
theorem reachablePos_of_accommodation_run (u : State) (c : Card) :
    ∀ (α : List Move) (st : State), st.run α = some u →
    (∀ m ∈ α, m.isAccommodation = true) →
    u.reachablePos c = st.reachablePos c := by
  intro α
  induction α with
  | nil =>
      intro st hrun _
      rw [(run_nil_elim hrun).symm]
  | cons m ms ih =>
      intro st hrun hall
      obtain ⟨v, hmstep, hmsrun⟩ := run_cons_elim hrun
      rw [ih v hmsrun (fun m' hm' => hall m' (List.mem_cons_of_mem _ hm'))]
      rw [reachablePos_of_accommodation hmstep c (hall m List.mem_cons_self)]

/-- The accommodation step law for one suit's standing height: only a
same-suit `pileStack` raises it (by exactly one, the fired card's
rank-index pinned by the move's guard to the standing level), only a
same-suit `stackPile` lowers it. -/
theorem heights_step_accommodation {st s₁ : State} {m : Move}
    (h : st.apply m = some s₁) (X : Card)
    (hm : m.isAccommodation = true) :
    s₁.heights X.suit = st.heights X.suit ∨
    (∃ c, m = Move.pileStack c ∧ c.suit = X.suit ∧
      c.rank.toIdx = st.heights X.suit ∧
      s₁.heights X.suit = st.heights X.suit + 1) ∨
    (∃ c b, m = Move.stackPile c b ∧ c.suit = X.suit ∧
      s₁.heights X.suit + 1 = st.heights X.suit) := by
  cases m with
  | draw => simp [Move.isAccommodation] at hm
  | reveal a => simp [Move.isAccommodation] at hm
  | deckPile c b => simp [Move.isAccommodation] at hm
  | deckStack c => simp [Move.isAccommodation] at hm
  | pilePile c b => simp [Move.isAccommodation] at hm
  | pileStack c =>
      rw [apply_pileStack_iff] at h
      obtain ⟨_, b, _, hrk', hshape⟩ := h
      by_cases hsc : c.suit = X.suit
      · refine Or.inr (Or.inl ⟨c, rfl, hsc, ?_, ?_⟩)
        · rw [hsc] at hrk'
          exact hrk'
        · rw [hshape]
          show (if X.suit = c.suit then st.heights X.suit + 1
              else st.heights X.suit) = st.heights X.suit + 1
          rw [ite_eq_left hsc.symm]
      · refine Or.inl ?_
        rw [hshape]
        show (if X.suit = c.suit then st.heights X.suit + 1
            else st.heights X.suit) = st.heights X.suit
        rw [ite_eq_right (fun hh => hsc hh.symm)]
  | stackPile c b =>
      rw [apply_stackPile_iff] at h
      obtain ⟨hrk'', _, bd, _, hshape⟩ := h
      by_cases hsc : c.suit = X.suit
      · refine Or.inr (Or.inr ⟨c, b, rfl, hsc, ?_⟩)
        rw [hshape]
        show ((if X.suit = c.suit then st.heights X.suit - 1
            else st.heights X.suit) + 1) = st.heights X.suit
        rw [ite_eq_left hsc.symm]
        rw [hsc] at hrk''
        omega
      · refine Or.inl ?_
        rw [hshape]
        show (if X.suit = c.suit then st.heights X.suit - 1
            else st.heights X.suit) = st.heights X.suit
        rw [ite_eq_right (fun hh => hsc hh.symm)]

/-- **F2's deterministic raise** — the same-suit determinism: an
accommodation play that crosses standing level `k` of `X`'s own suit
upward — at or below `k` at the start, strictly above at the end —
fires somewhere in its course the `pileStack` of the (unique) `X`-suit
card at rank-index `k`.  The crossing move is forced: at the first
passage above `k` the standing height IS `k`, and the `pileStack`
guard pins the fired card's suit to `X`'s and its rank-index to
exactly `k`. -/
theorem raise_crossing_mem {X : Card} {k : Nat} :
    ∀ (α : List Move) (st u : State),
    st.heights X.suit ≤ k → st.run α = some u → k < u.heights X.suit →
    (∀ m ∈ α, m.isAccommodation = true) →
    ∃ R : Card, R.suit = X.suit ∧ R.rank.toIdx = k ∧
      Move.pileStack R ∈ α := by
  intro α
  induction α with
  | nil =>
      intro st u h₀ hrun hkEnd _
      rw [(run_nil_elim hrun).symm] at hkEnd
      omega
  | cons m ms ih =>
      intro st u h₀ hrun hkEnd hall
      obtain ⟨v, hmstep, hmsrun⟩ := run_cons_elim hrun
      rcases heights_step_accommodation hmstep X
          (hall m List.mem_cons_self) with
        hsame | ⟨c, hmEq, hcs, hcrk, hbump⟩ | ⟨c, b, hmEq, hcs, hdrop⟩
      · obtain ⟨R, hRs, hRr, hRm⟩ :=
          ih v u (by omega) hmsrun hkEnd
            (fun m' hm' => hall m' (List.mem_cons_of_mem _ hm'))
        exact ⟨R, hRs, hRr, List.mem_cons_of_mem _ hRm⟩
      · by_cases hlt : v.heights X.suit < k + 1
        · obtain ⟨R, hRs, hRr, hRm⟩ :=
            ih v u (by omega) hmsrun hkEnd
              (fun m' hm' => hall m' (List.mem_cons_of_mem _ hm'))
          exact ⟨R, hRs, hRr, List.mem_cons_of_mem _ hRm⟩
        · -- the crossing happens at m itself: pre-height exactly k
          refine ⟨c, hcs, ?_, List.mem_cons.mpr (Or.inl hmEq.symm)⟩
          have hpre : st.heights X.suit = k := by omega
          rw [hpre] at hcrk
          exact hcrk
      · obtain ⟨R, hRs, hRr, hRm⟩ :=
          ih v u (by omega) hmsrun hkEnd
            (fun m' hm' => hall m' (List.mem_cons_of_mem _ hm'))
        exact ⟨R, hRs, hRr, List.mem_cons_of_mem _ hRm⟩

/-- The twin's suit is never `X`'s own suit (the pair-flip moves
within the color; the raise/pin suit analysis needs the separation). -/
theorem flipSuit_suit_ne (X : Card) : X.flipSuit.suit ≠ X.suit := by
  intro h
  rcases X with ⟨⟨c, p⟩, r⟩
  cases p <;> simp_all [Card.flipSuit, Suit.flipPair]

/-- The deterministic raise's card is outside the commitment's
two-type ball, and the pins' own signature cards spend other suits:
the twin's suit is the pair-flip of `X`'s, a receiver parent's suit
is the opposite color's — never `X`'s own suit — so no pin's signature
move can ever double as one of the raise's own-suit spends. -/
theorem raise_card_off_ball {X R p : Card}
    (hRs : R.suit = X.suit) (hRr : R.rank.toIdx + 1 = X.rank.toIdx)
    (hp : canSitOn X p = true) :
    R ≠ X ∧ R ≠ X.flipSuit ∧ R ≠ p ∧ p.suit ≠ X.suit ∧
      R.suit ≠ X.flipSuit.suit := by
  obtain ⟨-, hcol⟩ := (canSitOn_eq X p).mp hp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hcon
    rw [hcon] at hRr
    omega
  · intro hcon
    rw [hcon] at hRr
    simp only [Card.flipSuit_rank] at hRr
    omega
  · intro hcon
    obtain ⟨hzr, -⟩ := (canSitOn_eq X p).mp hp
    rw [← hcon] at hzr
    omega
  · intro hcon
    exact hcol (by rw [hcon])
  · rw [hRs]
    exact (flipSuit_suit_ne X).symm

/-- **The corner's derived world**: at a WF state with the stack
channel live but NO root commit, the drawn card is reachable in the
stock and its suit's standing height is strictly BELOW its rank — a
founded card is never stocked, and a rung-matched reachable card would
fire the stack commit itself.  The raise content of the corner is
genuinely present, never degenerate. -/
theorem stack_channel_world {st : State} (hwf : st.WF) {X : Card}
    (hno : ¬ ∃ sd, commitApplies st (MacroMove.drawCommit X) sd)
    (hlive : LabelLive st X Label.toStack) :
    st.heights X.suit < X.rank.toIdx ∧ ∃ i, st.reachablePos X = some i := by
  have hL : ∃ st' s'', accommodates st st' ∧
      st'.applyDrawStackTo X = some s'' := hlive
  obtain ⟨st', s'', hacc, hstack⟩ := hL
  obtain ⟨α, hαrun, hαall⟩ := hacc
  obtain ⟨i', hpos', _, _⟩ := applyDrawStackTo_iff.mp hstack
  have hpos : st.reachablePos X = some i' :=
    (reachablePos_of_accommodation_run st' X α st hαrun hαall).symm.trans hpos'
  by_cases hgt : X.rank.toIdx < st.heights X.suit
  · exfalso
    have hstockmem : X ∈ st.stock.cards :=
      Pace.mem_of_posOf st.stock.cards st.stock.cursor X i'
        (reachablePos_posOf hpos)
    have hfg := hwf.founds_gone X hgt
    have hp : st.stock.posOf X = some i' := reachablePos_posOf hpos
    rw [hfg.2.1] at hp
    exact absurd hp (by simp)
  · by_cases hlt : st.heights X.suit < X.rank.toIdx
    · exact ⟨hlt, i', hpos⟩
    · exfalso
      have hheq : st.heights X.suit = X.rank.toIdx := by omega
      refine hno ⟨{ st with
        stock := (st.stock.drawTo i').removeAt i',
        heights := fun s => if s = X.suit then st.heights s + 1
          else st.heights s }, ?_⟩
      rw [commitApplies_draw_cases]
      exact Or.inr (applyDrawStackTo_iff.mpr ⟨i', hpos, hheq.symm, rfl⟩)

/-- Every rung-matched accommodation play from a below-rung standing
height fires the same FINAL raise: `X`'s same-suit rank-mate (the
`X`-suit card one below `X`'s rank-index) has its `pileStack` somewhere
in the play — no two witnesses can differ in which card delivered the
final raise. -/
theorem stack_raise_deterministic {st : State} {X : Card}
    (h₀ : st.heights X.suit < X.rank.toIdx)
    (α : List Move) (u : State)
    (hrun : st.run α = some u) (hall : ∀ m ∈ α, m.isAccommodation = true)
    (hrung : X.rank.toIdx = u.heights X.suit) :
    ∃ R : Card, R.suit = X.suit ∧ R.rank.toIdx + 1 = X.rank.toIdx ∧
      Move.pileStack R ∈ α := by
  obtain ⟨R, hRs, hRk, hRm⟩ :=
    raise_crossing_mem (X := X) (k := X.rank.toIdx - 1) α st u (by omega)
      hrun (by omega) hall
  refine ⟨R, hRs, ?_, hRm⟩
  omega

/-- The stack-channel witness's play crosses the raise levels: the
deterministic final raise is IN the successor's own accommodation
play, whose end state is rung-matched and fires the stack commit onto
exactly that successor. -/
theorem stack_channel_raise_mem {st : State} (hwf : st.WF) {X : Card}
    (hno : ¬ ∃ sd, commitApplies st (MacroMove.drawCommit X) sd)
    {s₀ : State} (hth : SuccThrough st X Label.toStack s₀) :
    ∃ (R : Card) (u₀ : State) (α : List Move),
      R.suit = X.suit ∧ R.rank.toIdx + 1 = X.rank.toIdx ∧
      st.run α = some u₀ ∧ (∀ m ∈ α, m.isAccommodation = true) ∧
      Move.pileStack R ∈ α ∧ u₀.applyDrawStackTo X = some s₀ := by
  obtain ⟨u₀, α₀, hrun₀, hall₀, harm₀, _⟩ := hth
  have hstack : u₀.applyDrawStackTo X = some s₀ := harm₀
  have hL : LabelLive st X Label.toStack :=
    ⟨u₀, s₀, ⟨α₀, hrun₀, hall₀⟩, hstack⟩
  obtain ⟨hlt, _⟩ := stack_channel_world hwf hno hL
  obtain ⟨i₀, _, hrk₀, _⟩ := applyDrawStackTo_iff.mp hstack
  obtain ⟨R, hRs, hRr, hRm⟩ :=
    stack_raise_deterministic hlt α₀ u₀ hrun₀ hall₀ hrk₀
  exact ⟨R, u₀, α₀, hRs, hRr, hrun₀, hall₀, hRm, hstack⟩

/-! ## §15. The wave-20 restorations — the reach-gated universals
in their honest regimes

The wave-19B probe (`witnesses/KingAnchorReachProbe.lean`) fenced the
pristine corners off the dealt-reachable fragment, and its FARM row
licensed "restored under hreach" readings of the five refuted
universals.  The wave-20 session then built the reachability corner
witnesses themselves (`Witnesses.SuccLabeledWitness`, the
reachable-corner addendum): the naive gated readings FAIL — the
pristine SHAPES are unreachable, but the reachable fragment presents
the same content at dealt initial states (a frozen-suit stocked king
with two free anchors splits; the anchored-ace unseat route delivers
a macro successor no root-live channel names).  What is therefore
RESTORED is each universal *in its honest regime*, stated here:

* the **weak-corner regime** — `X` a king of a frozen suit (the
  `toStack` channel dead), at most one free anchor (the corpus's
  weak corners: `hone`), any two labeled successors (`hlab`): the
  ONLY surviving live channel is `hole`, whose signature play is
  empty, so both successors commit at the root onto the ONE free
  anchor, and are EQUAL — `c2_two_option_king_frozen` proves the
  two-option bound with NO rung, NO WF, NO play-level premises
  (`succThrough_king_frozen_join` is the join it rides on, and
  `same_pin_hole_oneAnchor` the same-pin one below it; the P2 form
  is `p2_direct_class_king_oneAnchor_reachable`, where the gate
  supplies the WF via `initialReachable_visClean`);
* the **conditional umbrella** — `c2_two_option_reachable`: the gate
  discharges `st.WF` and nothing else; the four play-level premises
  stay (the addendum's witnesses show `hlab` is NOT gate-dischargeable
  — a reachable macro successor can be labeled by nothing in the
  current channel list — so the umbrella is honestly conditional);
* the **crease's equal-window half** — `crease_absorbed_reachable`:
  two same-channel windows that END AT THE SAME accommodation state
  (`hwin : u = u'`, the free-float residue isolated as an explicit
  premise — the refuted original claimed the absorption from a
  Sublist alone, which `u = u'` here honestly replaces) with the rung
  at the shared end: the tableau arms join by `commitTableau_class`,
  the stack arm by determinism (`crease_stack_deterministic`).

The stack arm's rung extraction (the stack commit's own guard, read
out of its successor fact) is `heights_of_applyDrawStackTo` — used
by the P2 weak-corner form where a stack-committed `sd` forces the
rung that `p2_join_zeroSpend_rung` demands. -/

/-- The stack commitment's guard, extracted: if the safe-stack
`Draw(X)` commitment fired at `st`, the card was stackable at its
rung there. -/
theorem heights_of_applyDrawStackTo {st : State} {X : Card} {s : State}
    (h : st.applyDrawStackTo X = some s) :
    X.rank.toIdx = st.heights X.suit := by
  simp only [State.applyDrawStackTo] at h
  cases hp : st.reachablePos X with
  | none => rw [hp] at h; exact absurd h (by simp)
  | some i =>
      rw [hp] at h
      have h' : (if X.rank.toIdx = st.heights X.suit then
          some { st with
            stock := (st.stock.drawTo i).removeAt i,
            heights := fun s => if s = X.suit then st.heights s + 1 else st.heights s }
          else none) = some s := h
      by_cases hrk : X.rank.toIdx = st.heights X.suit
      · exact hrk
      · rw [ite_eq_right hrk] at h'; exact absurd h' (by simp)

/-- A king's tableau placements are exactly the free anchors (kings
have no receivers, and canPlace is free-base + king on anchors). -/
theorem king_tableau_base {st : State} {X : Card} (hK : X.rank = Rank.king)
    {b : Base} (hcp : st.canPlace X b = true) :
    ∃ a : Anchor, b = Sum.inl a ∧ st.board.topOf (Sum.inl a) = none := by
  cases b with
  | inl a => exact ⟨a, rfl, (canPlace_inl_iff.mp hcp).1⟩
  | inr Y => exact absurd (canSitOn_of_canPlace_inr hcp) (receivers_king_nil hK)

/-- **The same-pin universal at the weak corner** — two successors
through the `hole` channel at a state with at most one free anchor
join, with NO rung premise and NO WF: the hole signature play is
empty, both commits sit at the root, and a king's bases are anchors,
so both landings are the landing on THE free anchor — the same
`applyDrawTo`, hence the same successor.  This is the honest
restoration of `same_pin_closureEq` for the channel and shape the
corpus weak corners actually present (a climb-blocked king needs no
rung here — that is the point). -/
theorem same_pin_hole_oneAnchor {st : State} {X : Card} (hK : X.rank = Rank.king)
    (hone : ∀ a a' : Anchor, st.board.topOf (Sum.inl a) = none →
      st.board.topOf (Sum.inl a') = none → a = a')
    {s s' : State} (h₁ : SuccThrough st X Label.hole s)
    (h₂ : SuccThrough st X Label.hole s') : closureEq s s' := by
  obtain ⟨b, hcp, hto⟩ := succThrough_zeroSpend h₁ (Or.inr rfl)
  obtain ⟨b', hcp', hto'⟩ := succThrough_zeroSpend h₂ (Or.inr rfl)
  obtain ⟨a, rfl, hfree⟩ := king_tableau_base hK hcp
  obtain ⟨a', ha'b, hfree'⟩ := king_tableau_base hK hcp'
  rw [ha'b] at hto'
  have haa : a = a' := hone a a' hfree hfree'
  rw [← haa] at hto'
  have hss : s = s' := Option.some.inj (hto.symm.trans hto')
  rw [hss]
  exact closureEq_refl s'

/-- At a frozen-suit king corner, every live channel is the hole: the
receiver channels die on `receivers_king_nil`, the stack channel on
the freeze premise (the honest spelling of "climb-blocked": no
accommodation sequence could raise the suit, so `toStack` is dead
exactly when the climb is frozen — `witnesses/SuccLabeledWitness`'s
freeze argument is its engine-side evidence). -/
theorem labelLive_of_king_frozen {st : State} {X : Card} (hK : X.rank = Rank.king)
    (hfroz : ¬ LabelLive st X Label.toStack) {r : Label X}
    (hlive : LabelLive st X r) : r = Label.hole := by
  cases r with
  | direct =>
      obtain ⟨Y, hd⟩ := hlive
      exact absurd hd.hY (receivers_king_nil hK)
  | dig =>
      obtain ⟨Y, hd⟩ := hlive
      exact absurd hd.hY (receivers_king_nil hK)
  | borrow p =>
      obtain ⟨hp, -⟩ := hlive
      exact absurd hp (receivers_king_nil hK)
  | hole => rfl
  | toStack => exact absurd hlive hfroz

/-- **The frozen-corner join**: at a frozen-suit king corner with at
most one free anchor, ANY two channel-labeled successors join — both
labels are forced to `hole`, and the same-pin one-anchor fact
closes. -/
theorem succThrough_king_frozen_join {st : State} {X : Card}
    (hK : X.rank = Rank.king)
    (hone : ∀ a a' : Anchor, st.board.topOf (Sum.inl a) = none →
      st.board.topOf (Sum.inl a') = none → a = a')
    (hfroz : ¬ LabelLive st X Label.toStack)
    {s s' : State}
    (h₁ : ∃ r : Label X, LabelLive st X r ∧ SuccThrough st X r s)
    (h₂ : ∃ r : Label X, LabelLive st X r ∧ SuccThrough st X r s') :
    closureEq s s' := by
  obtain ⟨r₁, hl₁, ht₁⟩ := h₁
  obtain ⟨r₂, hl₂, ht₂⟩ := h₂
  rw [labelLive_of_king_frozen hK hfroz hl₁] at ht₁
  rw [labelLive_of_king_frozen hK hfroz hl₂] at ht₂
  exact same_pin_hole_oneAnchor hK hone ht₁ ht₂

/-- **The ≤2-count universal at the weak corner, fully proven**:
three channel-labeled successors of the `Draw(X)` commitment at a
frozen-suit king corner with at most one free anchor contain a
closure-equal pair — under the labeled-successor reading (the P0
content stays a premise: the addendum shows it is not
gate-dischargeable).  NO rung, NO WF, NO further play-level
premises.  (The chosen realizing disjunct consumes the first two
labelings; the third successor joins everything by the same
`succThrough_king_frozen_join`.) -/
theorem c2_two_option_king_frozen {st : State} {X : Card}
    (hK : X.rank = Rank.king)
    (hone : ∀ a a' : Anchor, st.board.topOf (Sum.inl a) = none →
      st.board.topOf (Sum.inl a') = none → a = a')
    (hfroz : ¬ LabelLive st X Label.toStack)
    {s₁ s₂ s₃ : State}
    (h₁ : ∃ r : Label X, LabelLive st X r ∧ SuccThrough st X r s₁)
    (h₂ : ∃ r : Label X, LabelLive st X r ∧ SuccThrough st X r s₂)
    (_h₃ : ∃ r : Label X, LabelLive st X r ∧ SuccThrough st X r s₃) :
    closureEq s₁ s₂ ∨ closureEq s₁ s₃ ∨ closureEq s₂ s₃ :=
  Or.inl (succThrough_king_frozen_join hK hone hfroz h₁ h₂)

/-- The stack arm is deterministic per state: two equal-window stack
successors are the same successor — the crease's `toStack` content,
with no rung and no window data at all. -/
theorem crease_stack_deterministic {u : State} {X : Card} {s s' : State}
    (hs : u.applyDrawStackTo X = some s) (hs' : u.applyDrawStackTo X = some s') :
    closureEq s s' := by
  have h : s = s' := Option.some.inj (hs.symm.trans hs')
  rw [h]
  exact closureEq_refl s'

/-- **The crease universal's honest gated form**: two same-channel
windows with their channel's signature moves — under the labeled
shape of the refuted original but with the free-float residue
isolated as the EXPLICIT premise `hwin : u = u'` (the original
claimed absorption from `α.Sublist α'` alone; the pristine refutation
fell there, and here the reconciliation of the windows' ends is
exactly what is assumed) — join whenever the shared end state shows
the rung.  `initialReachable` supplies the end state's WF along the
window (`run_visClean`).  The tableau arms join by
`commitTableau_class` at the shared end; the stack arm by
determinism. -/
theorem crease_absorbed_reachable {st : State} (hreach : initialReachable st)
    {X : Card} {r : Label X} {s s' : State} {α α' : List Move} {u u' : State}
    (hα : st.run α = some u) (_hallα : ∀ m ∈ α, m.isAccommodation = true)
    (harmα : commitArmOf u X r s)
    (hα' : st.run α' = some u') (_hallα' : ∀ m ∈ α', m.isAccommodation = true)
    (harmα' : commitArmOf u' X r s')
    (hwin : u = u')
    (hrk : X.rank.toIdx = u.heights X.suit) :
    closureEq s s' := by
  obtain ⟨hwf, hv⟩ := initialReachable_visClean hreach
  have hwfu : u.WF := (run_visClean α st u hwf hv hα).1
  subst hwin
  cases r with
  | direct | dig | borrow p | hole =>
      exact commitTableau_class hwfu hrk harmα harmα'
  | toStack =>
      exact crease_stack_deterministic harmα harmα'

/-- **The reach-gated conditional umbrella** — the two-option bound on
the dealt-reachable fragment: the gate discharges `st.WF`
(`initialReachable_visClean`) and NOTHING else; the four play-level
premises of §12 stay premises.  The reachable-corner addendum
(`Witnesses.SuccLabeledWitness`) calibrated this honestly: `hlab` is
NOT gate-dischargeable (a reachable macro successor can be labeled by
nothing in the current channel list — the anchored-ace unseat
route), and `hpin`/`hp2` are not either (the frozen-suit king's
landings are closure-split at reachable two-anchor states).  The
proven regimes are this theorem's hypotheses' discharged fragments:
§12.5 (zero-spend, rung) and the weak-corner theorems above. -/
theorem c2_two_option_reachable {st : State} (hreach : initialReachable st)
    {X : Card} {s₁ s₂ s₃ : State}
    (h₁ : macroStep st (MacroMove.drawCommit X) s₁)
    (h₂ : macroStep st (MacroMove.drawCommit X) s₂)
    (h₃ : macroStep st (MacroMove.drawCommit X) s₃)
    (hlab₁ : ∃ r : Label X, LabelLive st X r ∧ SuccThrough st X r s₁)
    (hlab₂ : ∃ r : Label X, LabelLive st X r ∧ SuccThrough st X r s₂)
    (hlab₃ : ∃ r : Label X, LabelLive st X r ∧ SuccThrough st X r s₃)
    (hp2 : ∀ {sd : State}, commitApplies st (MacroMove.drawCommit X) sd →
      ∀ {r : Label X} {s : State}, SuccThrough st X r s →
      P2Safe st X r → closureEq sd s)
    (hpin : ∀ {r : Label X} {s s' : State}, LabelLive st X r →
      SuccThrough st X r s → SuccThrough st X r s' → closureEq s s')
    (hball : (¬∃ sd, commitApplies st (MacroMove.drawCommit X) sd) →
      ∀ {rₐ r_b : Label X} {s₀ sₐ s_b : State},
      LabelLive st X Label.toStack → SuccThrough st X Label.toStack s₀ →
      LabelLive st X rₐ → SuccThrough st X rₐ sₐ →
      LabelLive st X r_b → SuccThrough st X r_b s_b →
      rₐ ≠ r_b →
      closureEq s₀ sₐ ∨ closureEq s₀ s_b ∨ closureEq sₐ s_b) :
    closureEq s₁ s₂ ∨ closureEq s₁ s₃ ∨ closureEq s₂ s₃ :=
  c2_two_option (initialReachable_visClean hreach).1
    h₁ h₂ h₃ hlab₁ hlab₂ hlab₃ hp2 hpin hball

/-- **The P2-direct universal at the weak corner, gated**: a
root-committed successor joins a `hole`-through successor at a
frozen-king one-anchor reachable corner.  The tableau-arm commit
lands on the one free anchor — the same landing as the successor's,
hence equal; the stack-arm commit forces its own rung
(`heights_of_applyDrawStackTo`), so §12.5's roundtrip
(`p2_join_zeroSpend_rung`) applies.  This is the honest gated
restoration of `p2_direct_class` for the weak-corner shape. -/
theorem p2_direct_class_king_oneAnchor_reachable {st : State}
    (hreach : initialReachable st) {X : Card} (hK : X.rank = Rank.king)
    (hone : ∀ a a' : Anchor, st.board.topOf (Sum.inl a) = none →
      st.board.topOf (Sum.inl a') = none → a = a')
    {sd s_p : State} (hsd : commitApplies st (MacroMove.drawCommit X) sd)
    (hth : SuccThrough st X Label.hole s_p) : closureEq sd s_p := by
  have hwf := (initialReachable_visClean hreach).1
  rcases (commitApplies_draw_cases st X sd).mp hsd with ⟨b, hcp, hto⟩ | hstack
  · obtain ⟨a, rfl, hfree⟩ := king_tableau_base hK hcp
    obtain ⟨b', hcp', hto'⟩ := succThrough_zeroSpend hth (Or.inr rfl)
    obtain ⟨a', ha'b, hfree'⟩ := king_tableau_base hK hcp'
    rw [ha'b] at hto'
    have haa : a = a' := hone a a' hfree hfree'
    rw [← haa] at hto'
    have hss : sd = s_p := Option.some.inj (hto.symm.trans hto')
    rw [hss]
    exact closureEq_refl s_p
  · have hrk : X.rank.toIdx = st.heights X.suit :=
      heights_of_applyDrawStackTo hstack
    exact p2_join_zeroSpend_rung hwf hrk (Or.inr rfl) hsd hth

end Klondike.C2
