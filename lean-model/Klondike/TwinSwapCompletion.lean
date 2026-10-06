import Klondike.TwinQuotient
import Klondike.TwinCollapse

/-!
# Theorem T, completed slices — O1 (destination collapse) and O3 (the asymmetric boundary)

The twin-swap family BEFORE this file (all machine-checked in the imports):

* **T, global relabeling form**: `solvable_relabel` + `solvable_flipAll`
  (Relabel.lean) — solvability is invariant under every coherent suit
  relabeling (the whole 8-element group at once).  PROVEN, axiom-clean.
* **T, local pair exchange** (`State.swapTwin t`, the two-card
  transposition): the unconditional seat-swap direction was REFUTED
  (witnesses/TwinSwapWitness.lean — the legality flip at unequal twin
  heights); the PROVEN exchange windows are `solvable_swapTwin_paired`
  / `_back` (TwinAgnostic.lean — the twin foundation moves occur as ONE
  adjacent pair) and `solvable_swapTwin_separated` / `_back`
  (TwinQuotient.lean — the two stackings separated by an ORTHO mid: no
  move whose legality reads the twin suits' heights).
* **T, cargo/exchange forms**: `solvable_cargoTwin` (TwinSwap.lean, one
  bare twin), `solvable_cargoTwin_exchange_bare` (TwinExchange.lean),
  `solvable_cargoTwin_exchange_of_visClean` (TwinQuotient.lean, the
  both-occupied iff at reachable states).  PROVEN.

The OPEN residue, in TwinQuotient's L1/O3 decomposition: the general
window (ii) — twin-suit activity BETWEEN the two stackings (the
catch-up: the low suit's exact-rung `pileStack`s; and the twin-suit
worry-backs).  This file lands the first genuinely ASYMMETRIC slice.

## O1 — the destination collapse (resolved, minimal form)

`State.solvable_twinDestination_collapse`: at a WF state, if the drawn
card `X` can land on either twin top — `deckPile X (inr Y)` or
`deckPile X (inr Y.flipSuit)` — the two post-states are
solvability-equivalent, by an explicit one-`pilePile` transfer each way
whose landing closes exactly (the board cancel `detach ∘ attach = id`
at the vacated seat).  This is the destination-collapse instance the
C2 program consumes (§4's note: "both yield the same `Encode`, so this
may not even need a cross-pile swap" — confirmed: NO cross-pile twin
swap is involved at all; the two landings are mutually reachable and
`solvable_iff_mutuallyReaches` finishes).  O1's locality question is
resolved for the campaign: the cross-pile local pair exchange remains
the licensed family (`paired`/`separated`), and nothing in the
destination collapse needs it.

## O3 — the asymmetric boundary (the pure catch-up window)

`State.solvable_swapTwin_catchup`: the source play stacks the twin `t`
(NOW stackable: its suit at the shared rung) while `t.flipSuit`'s suit
sits BELOW the rung — the O3 boundary exactly: one twin stackable now,
the other not — then raises the low suit by a PURE CATCH-UP (a segment
of exact-rung `pileStack`s of `t.flipSuit`-suit cards below the twin
rank) and stacks `t.flipSuit`.  L1's bridge ("build the low suit's
prefix raise by the same unbury structure the winning play used for
the high suit") becomes the REORDER: the catch-up segment commutes
with the first stacking; the mirror plays
[prefix; catch-up; stack t'; stack t] and lands on `D.swapTwin t` via
the twinSkew/crossTwin spine of the separated proof, under `haccess` —
the PER-CARD ACCESSIBILITY license (the catch-up segment is playable
at the pre-firing state A itself: no catch-up card is buried under a
twin).  The window strictly strengthens `paired` (cu = []) and covers
the other side of `separated` (an ortho mid excludes the catch-up by
definition; here the mid IS the catch-up).

## §6.5 — the ambiguous-twin canonicalization instance

`twin_stack_order_exchange_catchup`: the SAME-STATE order exchange —
if the win stacks the HIGH twin first with a low-suit catch-up mid
(under the accessibility licenses), the state also wins stacking the
LOW twin first: [prefix; catch-up; stack L; stack H; tail] lands on
EXACTLY the original successor, so the sweep's lowest-first canonical
choice never uniquely loses wins at this window.  The unproven
remainder — the covered-twin corner (the L-first firing blocked by the
mate: dealt-adjacent twins), mids with twin-suit worry-backs or
landings onto the vacated seats, and the DERIVATION of `haccess` at
engine corpora — is the next queue, recorded in FARM.md.
-/

/-! ## The board-pointwise helpers

`attach`/`detach` at the same base cancel (the destination transfer's
board bookkeeping) and two detaches commute (the one-step exchange's
board bookkeeping).  Both are pointwise `topOf` analyses. -/

/-- Attaching then detaching the same base returns the board (the
attach's own freeness guard is the vacated seat's `none`). -/
theorem Board.attach_detach_cancel {bd : Board} {b : Base} {c : Card} {bd' : Board}
    (hatt : bd.attach b c = some bd') : bd'.detach b = bd := by
  obtain ⟨htop, -⟩ := (Board.attach_eq_some_iff bd b c).mp (by rw [hatt]; simp)
  refine Board.ext_topOf (funext fun b'' => ?_)
  by_cases hbb : b'' = b
  · rw [hbb, Board.detach_topOf, htop]
  · rw [Board.detach_topOf_ne _ _ _ hbb, Board.attach_topOf_ne _ _ _ hatt hbb]

/-- Two detaches at distinct bases commute (both are pointwise
`topOf`-updates at disjoint cells). -/
theorem Board.detach_detach_comm (bd : Board) (b b' : Base) (h : b ≠ b') :
    (bd.detach b).detach b' = (bd.detach b').detach b := by
  refine Board.ext_topOf (funext fun b'' => ?_)
  by_cases h1 : b'' = b
  · rw [h1, Board.detach_topOf_ne _ _ _ h, Board.detach_topOf, Board.detach_topOf]
  · by_cases h2 : b'' = b'
    · rw [h2, Board.detach_topOf, Board.detach_topOf_ne _ _ _ (Ne.symm h),
        Board.detach_topOf]
    · rw [Board.detach_topOf_ne _ _ _ h2, Board.detach_topOf_ne _ _ _ h1,
        Board.detach_topOf_ne _ _ _ h1, Board.detach_topOf_ne _ _ _ h2]

/-! ## The stock card's two off-board facts

The destination collapse needs the drawn `X` to carry no stack (a WF
board has no edge over a stock card): the phantom-stack killer
`State.topOf_inr_eq_none` wants `bottomOf X = none` (the attach guard)
and `X` in no hidden slice (the deal's piles/stock disjointness). -/

/-- The waste top is in the cycle's remaining cards. -/
theorem Cycle.prev_mem {cy : Cycle Card} {c : Card} (h : cy.prev = some c) :
    c ∈ cy.cards := by
  unfold Cycle.prev at h
  by_cases hz : cy.cursor = 0
  · rw [ite_eq_left hz] at h; simp at h
  · rw [ite_eq_right hz] at h
    exact List.mem_iff_getElem?.mpr ⟨cy.cursor - 1, h⟩

/-- A stock card is never in a pile's hidden slice (the deal's piles
and stock are disjoint by `Deal.WF`). -/
theorem State.stock_prev_not_mem_hidden {st : State} {X : Card} (hwf : st.WF)
    (hprev : st.stock.prev = some X) {a : Anchor} : X ∉ st.hidden a := by
  intro hmem
  have hstock : X ∈ st.stock.cards := Cycle.prev_mem hprev
  have hndeal : X ∈ st.deal.stock := hwf.stock_wf.2 X hstock
  have hpile : X ∈ st.deal.piles a := by
    have : X ∈ (st.deal.piles a).take (st.depths a) := hmem
    exact List.take_subset _ _ this
  exact noDupCards_append_disj ((hwf.deal_wf).2.2)
    (List.mem_flatMap.mpr ⟨a, Anchor.mem_all a, hpile⟩) hndeal

/-! ## O1 — the destination collapse

The two twin-top landings of the same drawn card are mutually
reachable: the transfer moves the (still bare-topped) `X` from one twin
seat to the other and lands on EXACTLY the direct landing's
post-state.  No twin-swap of pile positions is used. -/

private theorem twinDestination_transfer {st A B : State} {X Y₁ Y₂ : Card}
    (hwf : st.WF)
    (h₁ : st.apply (Move.deckPile X (Sum.inr Y₁)) = some A)
    (h₂ : st.apply (Move.deckPile X (Sum.inr Y₂)) = some B)
    (hcard : Y₁ ≠ Y₂) :
    A.apply (Move.pilePile X (Sum.inr Y₂)) = some B := by
  obtain ⟨hprev, hcp₁, bdA, hattA, hAeq⟩ := apply_deckPile_iff.mp h₁
  obtain ⟨-, hcp₂, bdB, hattB, hBeq⟩ := apply_deckPile_iff.mp h₂
  obtain ⟨htopY₁, hvisY₁, hfit₁⟩ := canPlace_inr_iff.mp hcp₁
  obtain ⟨htopY₂, hvisY₂, hfit₂⟩ := canPlace_inr_iff.mp hcp₂
  -- X is a fresh stock card: unseated, in no hidden slice, no stack
  have hXbot : st.board.bottomOf X = none :=
    ((Board.attach_eq_some_iff st.board (Sum.inr Y₁) X).mp (by rw [hattA]; simp)).2
  have hXtop : st.board.topOf (Sum.inr X) = none :=
    State.topOf_inr_eq_none hwf hXbot (fun a => State.stock_prev_not_mem_hidden hwf hprev)
  -- rank arithmetic: X sits strictly below both destinations
  have hXY₁ : X ≠ Y₁ := by
    intro hcon; rw [hcon] at hfit₁
    simp only [canSitOn_eq] at hfit₁
    obtain ⟨hr, -⟩ := hfit₁
    omega
  have hXY₂ : X ≠ Y₂ := by
    intro hcon; rw [hcon] at hfit₂
    simp only [canSitOn_eq] at hfit₂
    obtain ⟨hr, -⟩ := hfit₂
    omega
  -- the transfer's premises at A (whose board is the Y₁-attach)
  have hbA : A.board = bdA := by rw [hAeq]
  have hbot' : A.board.bottomOf X = some (Sum.inr Y₁) := by
    rw [hbA]
    exact (Board.bottomOf_eq _ _ _).mpr (Board.attach_topOf _ _ _ hattA)
  have htopA : A.board.topOf (Sum.inr Y₂) = none := by
    rw [hbA]
    rw [Board.attach_topOf_ne _ _ _ hattA
      (fun hh : (Sum.inr Y₂ : Base) = Sum.inr Y₁ => hcard (Sum.inr.inj hh).symm)]
    exact htopY₂
  have hvisA : A.isVis Y₂ = true := by
    obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.mp hvisY₂
    have hb'ne : b' ≠ Sum.inr Y₁ := by
      intro hcon
      rw [hcon] at hb'
      have hh := (Board.bottomOf_eq st.board Y₂ (Sum.inr Y₁)).mp hb'
      rw [htopY₁] at hh
      exact absurd hh (by simp)
    have hteq : A.board.topOf b' = some Y₂ := by
      rw [hbA]
      rw [Board.attach_topOf_ne _ _ _ hattA (fun hh : b' = Sum.inr Y₁ => hb'ne hh)]
      exact (Board.bottomOf_eq st.board Y₂ b').mp hb'
    exact Option.isSome_iff_exists.mpr ⟨b', (Board.bottomOf_eq A.board Y₂ b').mpr hteq⟩
  have hcpA : A.canPlace X (Sum.inr Y₂) = true :=
    canPlace_inr_iff.mpr ⟨htopA, hvisA, hfit₂⟩
  -- the walk from X is empty at st (fresh stock card) and stays empty at A
  have hXtopA : A.board.topOf (Sum.inr X) = none := by
    rw [hbA]
    rw [Board.attach_topOf_ne _ _ _ hattA
      (fun hh : (Sum.inr X : Base) = Sum.inr Y₁ => hXY₁ (Sum.inr.inj hh))]
    exact hXtop
  have haboveA : A.board.aboveOf X = [] := by
    rw [Board.aboveOf_eq_go 53 (by omega)]
    rw [show (53 : Nat) = 52 + 1 from rfl, Board.aboveOf_go_topOf_none hXtopA]
  have hcmrA : A.canMoveRun X (Sum.inr Y₂) = true :=
    canMoveRun_inr_iff.mpr ⟨hcpA, by rw [haboveA]; rfl⟩
  -- board bookkeeping: detach at the vacated seat, attach at the twin seat
  have hdet : A.board.detach (Sum.inr Y₁) = st.board := by
    rw [hbA]
    exact Board.attach_detach_cancel hattA
  have hattB' : (A.board.detach (Sum.inr Y₁)).attach (Sum.inr Y₂) X = some bdB := by
    rw [hdet]; exact hattB
  refine apply_pilePile_iff.mpr ⟨Sum.inr Y₁, hbot', ?_, hcmrA, bdB, hattB', ?_⟩
  · exact fun h0 => hcard (Sum.inr.inj h0)
  · rw [hBeq, hAeq]

/-- **O1, the destination collapse (the resolved minimal form)**: at a
WF state, the two twin-top landings of the drawn card `X` — on `Y` or
on its twin `Y.flipSuit`, the two tableau destinations F1 allows — are
solvability-equivalent.  Each is one `pilePile` from the other, landing
exactly on the direct landing's post-state (the vacated seat's
attach/detach cancel; the stock splice and heights are untouched by
the transfer), so mutual reachability finishes.

This is the instance the transposition table, the ≤2-outcome bound
(C2) and the accommodation-side twin choice consume: the two landings
produce the same engine state *because* they are one `pilePile` apart
in the model — NO cross-pile twin swap is needed, confirming §4's
observation.  The premise `hwf` is the standard repair shape: it kills
the phantom stack over a stock card (the junk-board leg). -/
theorem State.solvable_twinDestination_collapse {st A B : State} {X Y : Card}
    (hwf : st.WF)
    (hA : st.apply (Move.deckPile X (Sum.inr Y)) = some A)
    (hB : st.apply (Move.deckPile X (Sum.inr Y.flipSuit)) = some B) :
    A.solvableFrom ↔ B.solvableFrom := by
  have hcard : Y ≠ Y.flipSuit := fun h => Card.flipSuit_ne Y h.symm
  have h1 := twinDestination_transfer hwf hA hB hcard
  have h2 := twinDestination_transfer hwf hB hA (fun h => hcard h.symm)
  have hr1 : A.run [Move.pilePile X (Sum.inr Y.flipSuit)] = some B := by
    simp only [State.run, h1]
  have hr2 : B.run [Move.pilePile X (Sum.inr Y)] = some A := by
    simp only [State.run, h2]
  exact solvable_iff_mutuallyReaches ⟨[Move.pilePile X (Sum.inr Y.flipSuit)], hr1⟩
    ⟨[Move.pilePile X (Sum.inr Y)], hr2⟩

/-! ## O3 — the asymmetric boundary: the pure catch-up window

The engine: two `pileStack`s of OFF-SUIT cards exchange (one step), a
whole catch-up segment commutes with the twin's stacking (the reorder),
and the assembled window mirrors through the twinSkew/crossTwin spine
of the separated proof — with the low suit BELOW the rung at the
source's first firing, the genuinely asymmetric case. -/

/-- **The one-step stack exchange**: two `pileStack` firings of
off-suit cards commute as partial functions — if both orders fire,
they land on the same successor.  The guard transfer: the two cards'
bases are distinct (a base's top is one card) and the `c`-detach
touches neither `t`'s seat nor `t`'s base nor `t`'s suit height; the
successor equality: disjoint detaches commute and the two height bumps
sit at different suits. -/
theorem apply_pileStack_pileStack_exchange {S : State} {t c : Card} {B S₁ T₁ : State}
    (hsu : c.suit ≠ t.suit)
    (hB : S.apply (Move.pileStack t) = some B)
    (hS₁ : S.apply (Move.pileStack c) = some S₁)
    (hT₁ : B.apply (Move.pileStack c) = some T₁) :
    S₁.apply (Move.pileStack t) = some T₁ := by
  rw [apply_pileStack_iff] at hB
  obtain ⟨htopT, β, hβ, hrkT, hBshape⟩ := hB
  rw [apply_pileStack_iff] at hS₁
  obtain ⟨-, βc, hβc, -, hS₁shape⟩ := hS₁
  rw [apply_pileStack_iff] at hT₁
  obtain ⟨-, βcB, hβcB, -, hT₁shape⟩ := hT₁
  -- the two bases are distinct (a base's top is one card)
  have hβcβ : βc ≠ β := by
    intro hcon
    have hc : c = t := by
      have h1 : S.board.topOf βc = some c := (Board.bottomOf_eq S.board c βc).mp hβc
      have h2 : S.board.topOf β = some t := (Board.bottomOf_eq S.board t β).mp hβ
      rw [hcon] at h1
      exact Option.some.inj (h1.symm.trans h2)
    exact hsu (by rw [hc])
  -- t's firing guards survive at S1 (the c-detach touches neither
  -- t's seat nor t's base nor t's suit)
  have htopS₁ : S₁.board.topOf (Sum.inr t) = none := by
    rw [hS₁shape]
    show (S.board.detach βc).topOf (Sum.inr t) = none
    by_cases hseat : (Sum.inr t : Base) = βc
    · exfalso
      have hh := (Board.bottomOf_eq S.board c βc).mp hβc
      rw [← hseat] at hh
      rw [htopT] at hh
      exact absurd hh (by simp)
    · rw [Board.detach_topOf_ne _ _ _ hseat]
      exact htopT
  have hbotS₁ : S₁.board.bottomOf t = some β := by
    rw [hS₁shape]
    show (S.board.detach βc).bottomOf t = some β
    refine (Board.bottomOf_eq _ _ _).mpr ?_
    rw [Board.detach_topOf_ne _ _ _ (fun hh => hβcβ hh.symm)]
    exact (Board.bottomOf_eq S.board t β).mp hβ
  have hrkS₁ : t.rank.toIdx = S₁.heights t.suit := by
    rw [hS₁shape]
    show t.rank.toIdx =
      (if t.suit = c.suit then S.heights t.suit + 1 else S.heights t.suit)
    rw [ite_eq_right (Ne.symm hsu)]
    exact hrkT
  have hfire : S₁.apply (Move.pileStack t) = some
      { S₁ with
        board := S₁.board.detach β,
        heights := fun s => if s = t.suit then S₁.heights s + 1 else S₁.heights s } :=
    apply_pileStack_iff.mpr ⟨htopS₁, β, hbotS₁, hrkS₁, rfl⟩
  -- c's base agrees across the two orders (board injectivity at B)
  have hβcB : βcB = βc := by
    have h1 : B.board.topOf βcB = some c := (Board.bottomOf_eq B.board c βcB).mp hβcB
    have h2 : B.board.topOf βc = some c := by
      rw [hBshape]
      show (S.board.detach β).topOf βc = some c
      rw [Board.detach_topOf_ne _ _ _ hβcβ]
      exact (Board.bottomOf_eq S.board c βc).mp hβc
    exact B.board.inj βcB βc c h1 h2
  -- the two orders land equal
  rw [hfire]
  refine congrArg some ?_
  rw [hT₁shape, hS₁shape, hBshape, hβcB]
  apply state_ext
  · rfl
  · show (S.board.detach βc).detach β = (S.board.detach β).detach βc
    exact Board.detach_detach_comm S.board βc β hβcβ
  · funext s
    show (if s = t.suit then
        (if s = c.suit then S.heights s + 1 else S.heights s) + 1
      else if s = c.suit then S.heights s + 1 else S.heights s)
      = (if s = c.suit then
        (if s = t.suit then S.heights s + 1 else S.heights s) + 1
      else if s = t.suit then S.heights s + 1 else S.heights s)
    by_cases h1 : s = t.suit
    · rw [ite_eq_left h1, ite_eq_right (fun hh => hsu (hh.symm.trans h1)),
        ite_eq_right (fun hh => hsu (hh.symm.trans h1)), ite_eq_left h1]
    · by_cases h2 : s = c.suit
      · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_left h2, ite_eq_right h1]
      · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h2, ite_eq_right h1]
  · rfl
  · rfl
  · rfl

/-- **The catch-up segment commutes with the twin's stacking** (L1's
reorder): given the off-pair catch-up segment `cu` (all `pileStack`s of
cards off the pair), the twin's firing at A, and BOTH orders firing
(A-runnable is the accessibility premise; B-runnable is the source
play's own mid), the reordered firing at C₀ lands on EXACTLY the
source's mid successor C.  Step: the one-step exchange iterated through
the segment. -/
theorem pileStack_catchup_reorder {t : Card} :
    ∀ (cu : List Move) (A B C₀ C : State),
    (∀ m ∈ cu, ∃ c, m = Move.pileStack c ∧ c.suit ≠ t.suit ∧
      c ≠ t ∧ c ≠ t.flipSuit) →
    A.apply (Move.pileStack t) = some B →
    A.run cu = some C₀ →
    B.run cu = some C →
    C₀.apply (Move.pileStack t) = some C := by
  intro cu
  induction cu with
  | nil =>
      intro A B C₀ C _ h₁ hA hB
      rw [← run_nil_elim hA, ← run_nil_elim hB]
      exact h₁
  | cons m ms ih =>
      intro A B C₀ C hcu h₁ hA hB
      obtain ⟨c, hmc, hsu, -, -⟩ := hcu m List.mem_cons_self
      subst hmc
      obtain ⟨A₁, hA₁, hArest⟩ := run_cons_elim hA
      obtain ⟨B₁, hB₁, hBrest⟩ := run_cons_elim hB
      have hstep := apply_pileStack_pileStack_exchange hsu h₁ hA₁ hB₁
      exact ih A₁ B₁ C₀ C (fun m' hm' => hcu m' (List.mem_cons_of_mem _ hm'))
        hstep hArest hBrest

/-- Decode the catch-up shape (low-suit `pileStack`s below the twin
rank) into the family the exchange machinery consumes: off `t`'s suit
(the low suit IS the other suit) and off the pair. -/
theorem catchup_mem_offPair {t : Card} {cu : List Move}
    (hcu : ∀ m ∈ cu, ∃ c, m = Move.pileStack c ∧
      c.suit = t.flipSuit.suit ∧ c.rank.toIdx < t.rank.toIdx)
    (m : Move) (hm : m ∈ cu) :
    ∃ c, m = Move.pileStack c ∧ c.suit ≠ t.suit ∧ c ≠ t ∧ c ≠ t.flipSuit := by
  obtain ⟨c, hmc, hsu, hlt⟩ := hcu m hm
  have hne : t.flipSuit.suit ≠ t.suit := fun h => Suit.flipPair_ne t.suit h
  refine ⟨c, hmc, ?_, ?_, ?_⟩
  · rw [hsu]; exact hne
  · intro hcon
    rw [hcon] at hsu
    exact hne hsu.symm
  · intro hcon
    rw [hcon] at hlt
    rw [Card.flipSuit_rank] at hlt
    omega

/-- The catch-up segment's moves are CLEAN for the pair exchange (off
the pair), so the clean mirror carries them verbatim. -/
theorem catchup_mem_cleanTwin {t : Card} {cu : List Move}
    (hcu : ∀ m ∈ cu, ∃ c, m = Move.pileStack c ∧
      c.suit = t.flipSuit.suit ∧ c.rank.toIdx < t.rank.toIdx) :
    ∀ m ∈ cu, Move.cleanTwin t m = true := by
  intro m hm
  obtain ⟨c, hmc, hsu, hlt⟩ := hcu m hm
  rw [hmc]
  show Card.offPair t c = true
  have hne : t.flipSuit.suit ≠ t.suit := fun hh => Suit.flipPair_ne t.suit hh
  refine Card.offPair_true (fun hcon => hne (hsu.symm.trans (congrArg Card.suit hcon)))
    (fun hcon => ?_)
  rw [hcon] at hlt
  rw [Card.flipSuit_rank] at hlt
  omega

/-- **O3, the asymmetric boundary — the pure catch-up window**: if the
source game wins via [prefix; stack t; catch-up; stack t'; tail] —
`t` stackable at the first firing (its suit at the rung) while
`t.flipSuit`'s suit sits BELOW the rung, the low suit raised between
the two stackings by a pure prefix-raise `cu` — and the catch-up is
playable at the pre-firing state A itself (`haccess`: per-card
accessibility — no catch-up card is buried under a twin), then the
EXCHANGED game is solvable: it plays [prefix*; catch-up; stack t';
stack t; tail*] — the catch-up rides the clean mirror, the first
stacking lands the cross-skew at the RE-ALIGNED rung (the catch-up put
the low suit exactly at it), and the second re-syncs onto `D.swapTwin t`. -/
theorem State.solvable_swapTwin_catchup {st : State} {t : Card}
    {p₁ cu p₂ : List Move} {A B C D W : State}
    (hc₁ : ∀ m ∈ p₁, Move.cleanTwin t m = true)
    (hc₂ : ∀ m ∈ p₂, Move.cleanTwin t m = true)
    (hcu : ∀ m ∈ cu, ∃ c, m = Move.pileStack c ∧
      c.suit = t.flipSuit.suit ∧ c.rank.toIdx < t.rank.toIdx)
    (hp₁ : st.run p₁ = some A)
    (hf₁ : A.apply (Move.pileStack t) = some B)
    (hcuB : B.run cu = some C)
    (hf₂ : C.apply (Move.pileStack t.flipSuit) = some D)
    (hp₂ : D.run p₂ = some W)
    (haccess : ∃ C₀, A.run cu = some C₀)
    (hwin : W.isWin = true) :
    (st.swapTwin t).solvableFrom := by
  obtain ⟨C₀, hA_cu⟩ := haccess
  have hcuoff := catchup_mem_offPair hcu
  have hcucl := catchup_mem_cleanTwin hcu
  -- the reorder: the twin's firing at C0 lands on the source's C
  have hreor := pileStack_catchup_reorder cu A B C₀ C hcuoff hf₁ hA_cu hcuB
  rw [apply_pileStack_iff] at hreor
  obtain ⟨htop₀, β₀, hβ₀, hrk₀, hCshape⟩ := hreor
  rw [apply_pileStack_iff] at hf₂
  obtain ⟨htop', β', hβ', hrk', hDshape⟩ := hf₂
  have hsne : t.flipSuit.suit ≠ t.suit := fun h => Suit.flipPair_ne t.suit h
  -- the rung alignments the twinSkew/crossTwin spine needs
  have hC₀low : C₀.heights t.flipSuit.suit = t.rank.toIdx := by
    have h1 : t.flipSuit.rank.toIdx = C.heights t.flipSuit.suit := hrk'
    have h2 : C.heights t.flipSuit.suit = C₀.heights t.flipSuit.suit := by
      rw [hCshape]
      show (if t.flipSuit.suit = t.suit then C₀.heights t.flipSuit.suit + 1
        else C₀.heights t.flipSuit.suit) = _
      rw [ite_eq_right hsne]
    rw [Card.flipSuit_rank] at h1
    omega
  have halign₁ : C₀.heights t.suit = C₀.heights t.flipSuit.suit := by
    rw [hrk₀.symm, hC₀low]
  have halign₂ : C.heights t.suit = C.heights t.flipSuit.suit + 1 := by
    have e1 : C.heights t.suit = C₀.heights t.suit + 1 := by
      rw [hCshape]
      show (if t.suit = t.suit then C₀.heights t.suit + 1 else C₀.heights t.suit) = _
      rw [ite_eq_left rfl]
    have e2 : C.heights t.flipSuit.suit = C₀.heights t.flipSuit.suit := by
      rw [hCshape]
      show (if t.flipSuit.suit = t.suit then C₀.heights t.flipSuit.suit + 1
        else C₀.heights t.flipSuit.suit) = _
      rw [ite_eq_right hsne]
    rw [e2, hC₀low, hrk₀]
    omega
  -- the mirror play, segment by segment
  have hcucl' : ∀ m ∈ p₁ ++ cu, Move.cleanTwin t m = true := by
    intro m hm
    rcases List.mem_append.mp hm with h | h
    · exact hc₁ m h
    · exact hcucl m h
  have hseg : st.run (p₁ ++ cu) = some C₀ := run_append_some hp₁ hA_cu
  have hM₁ : (st.swapTwin t).run ((p₁ ++ cu).map (Move.swapTwin t))
      = some (C₀.swapTwin t) := by
    rw [run_swapTwin_clean t st (p₁ ++ cu) hcucl', hseg]
    rfl
  have hrunskew : (C₀.swapTwin t).run [Move.pileStack t.flipSuit]
      = some (C₀.twinSkew t β₀) := by
    simp only [State.run, State.apply_swapTwin_stack_flip htop₀ hβ₀ hC₀low]
  have hskew : C₀.twinSkew t β₀ = C.crossTwin t :=
    State.twinSkew_eq_crossTwin hCshape halign₁
  have hM₁' : (st.swapTwin t).run
      ((p₁ ++ cu).map (Move.swapTwin t) ++ [Move.pileStack t.flipSuit])
      = some (C.crossTwin t) := by
    rw [run_split_bind, hM₁]
    show (C₀.swapTwin t).run [Move.pileStack t.flipSuit] = some (C.crossTwin t)
    rw [hrunskew, hskew]
  have hM₃ : (C.crossTwin t).run [Move.pileStack t] = some (D.swapTwin t) := by
    simp only [State.run, State.apply_crossTwin_stack htop' hβ' hrk' halign₂ hDshape]
  have hM₄ : (D.swapTwin t).run (p₂.map (Move.swapTwin t))
      = some (W.swapTwin t) := by
    rw [run_swapTwin_clean t D p₂ hc₂, hp₂]
    rfl
  have hwin' : (W.swapTwin t).isWin = true := by
    simp only [State.isWin, swapTwin_heights]
    exact hwin
  refine ⟨((p₁ ++ cu).map (Move.swapTwin t) ++ [Move.pileStack t.flipSuit])
      ++ ([Move.pileStack t] ++ p₂.map (Move.swapTwin t)), W.swapTwin t, ?_, hwin'⟩
  exact run_append_some hM₁' (run_append_some hM₃ hM₄)

/-- The packaged form of the catch-up window: the source play as one
run. -/
theorem State.solvable_swapTwin_catchup_run {st : State} {t : Card}
    {p₁ cu p₂ : List Move} {W : State}
    (hc₁ : ∀ m ∈ p₁, Move.cleanTwin t m = true)
    (hc₂ : ∀ m ∈ p₂, Move.cleanTwin t m = true)
    (hcu : ∀ m ∈ cu, ∃ c, m = Move.pileStack c ∧
      c.suit = t.flipSuit.suit ∧ c.rank.toIdx < t.rank.toIdx)
    (haccess : ∀ A, st.run p₁ = some A → ∃ C₀, A.run cu = some C₀)
    (hrun : st.run (p₁ ++ [Move.pileStack t] ++ cu
      ++ [Move.pileStack t.flipSuit] ++ p₂) = some W)
    (hwin : W.isWin = true) :
    (st.swapTwin t).solvableFrom := by
  simp only [List.append_assoc] at hrun
  rw [run_split_bind st p₁
    ([Move.pileStack t] ++ (cu ++ ([Move.pileStack t.flipSuit] ++ p₂)))] at hrun
  cases hA : st.run p₁ with
  | none => rw [hA] at hrun; simp at hrun
  | some A =>
    rw [hA] at hrun
    have hrun1 : A.run ([Move.pileStack t] ++ (cu ++ ([Move.pileStack t.flipSuit] ++ p₂)))
        = some W := hrun
    rw [run_split_bind A [Move.pileStack t]
      (cu ++ ([Move.pileStack t.flipSuit] ++ p₂))] at hrun1
    simp only [State.run] at hrun1
    cases hB₀ : A.apply (Move.pileStack t) with
    | none => rw [hB₀] at hrun1; simp at hrun1
    | some B =>
      rw [hB₀] at hrun1
      have hrun2 : B.run (cu ++ ([Move.pileStack t.flipSuit] ++ p₂)) = some W := hrun1
      rw [run_split_bind B cu
        ([Move.pileStack t.flipSuit] ++ p₂)] at hrun2
      cases hC : B.run cu with
      | none => rw [hC] at hrun2; simp at hrun2
      | some C =>
        rw [hC] at hrun2
        have hrun3 : C.run ([Move.pileStack t.flipSuit] ++ p₂) = some W := hrun2
        rw [run_split_bind C [Move.pileStack t.flipSuit] p₂] at hrun3
        simp only [State.run] at hrun3
        cases hD₀ : C.apply (Move.pileStack t.flipSuit) with
        | none => rw [hD₀] at hrun3; simp at hrun3
        | some D =>
          rw [hD₀] at hrun3
          have hWD : D.run p₂ = some W := hrun3
          obtain ⟨C₀, hA_cu⟩ := haccess A hA
          exact State.solvable_swapTwin_catchup hc₁ hc₂ hcu hA hB₀ hC hD₀ hWD
            ⟨C₀, hA_cu⟩ hwin

/-! ## §6.5 — the ambiguous-twin canonicalization instance

The same-state stack-order exchange: the win that stacks the HIGH twin
first (with the low suit's catch-up between the two) reshapes into a
win that stacks the LOW twin first, landing on EXACTLY the original
successor — the sweep's lowest-first choice is safe at this window. -/

/-- **The canonicalization safety, the closed instance (§6.5)**: if the
game wins by stacking the HIGH twin `H` first — with the low twin `L`
unstackable at that moment (`L = H.flipSuit`, its suit below the rung),
raised in between by a pure `L`-suit catch-up, and stacked second —
then the SAME game wins by stacking `L` first: the run
[prefix; catch-up; stack L; stack H; tail] lands on the original
successor W, under the two accessibility licenses (`hacc`: the
catch-up runs at the pre-firing state, and `L` fires right after it).
The L-first reading never uniquely loses wins at the catch-up window.
Residue (the honest boundary, next queue): the covered-twin corner
(the `L`-firing at C₀ blocked by a dealt-adjacent mate), mids carrying
twin-suit worry-backs or landings onto the vacated seats, and the
derivation of the accessibility licenses at engine states. -/
theorem twin_stack_order_exchange_catchup {st : State} {L H : Card}
    {p₁ cu p₂ : List Move} {A B C D W : State}
    (htwin : L = H.flipSuit)
    (hcu : ∀ m ∈ cu, ∃ c, m = Move.pileStack c ∧
      c.suit = L.suit ∧ c.rank.toIdx < H.rank.toIdx)
    (hp₁ : st.run p₁ = some A)
    (hfH : A.apply (Move.pileStack H) = some B)
    (hcuB : B.run cu = some C)
    (hfL : C.apply (Move.pileStack L) = some D)
    (hp₂ : D.run p₂ = some W)
    (hacc : ∃ C₀ D₀, A.run cu = some C₀ ∧ C₀.apply (Move.pileStack L) = some D₀) :
    st.run (p₁ ++ cu ++ [Move.pileStack L, Move.pileStack H] ++ p₂) = some W := by
  obtain ⟨C₀, D₀, hA_cu, hD₀⟩ := hacc
  have hsu : L.suit ≠ H.suit := by
    rw [htwin]; exact fun h => Suit.flipPair_ne H.suit h
  -- translate cu's shape to the pair-family form (L off H's suit/pair)
  have hcuoff : ∀ m ∈ cu, ∃ c, m = Move.pileStack c ∧ c.suit ≠ H.suit ∧
      c ≠ H ∧ c ≠ H.flipSuit := by
    intro m hm
    obtain ⟨c, hmc, hsu', hlt'⟩ := hcu m hm
    refine ⟨c, hmc, ?_, ?_, ?_⟩
    · rw [hsu']; exact hsu
    · intro hcon
      rw [hcon] at hsu'
      exact hsu hsu'.symm
    · intro hcon
      rw [hcon] at hlt'
      rw [Card.flipSuit_rank] at hlt'
      omega
  -- the reorder puts H's firing after the catch-up, on the source's C
  have hreor := pileStack_catchup_reorder cu A B C₀ C hcuoff hfH hA_cu hcuB
  -- the exchange puts L's firing before H's, landing on the source's D0
  have hexchange := apply_pileStack_pileStack_exchange (t := H) (c := L) hsu
    hreor hD₀ hfL
  -- assemble the reshaped run
  simp only [List.append_assoc]
  rw [run_split_bind st p₁
    (cu ++ ([Move.pileStack L, Move.pileStack H] ++ p₂)), hp₁]
  show A.run (cu ++ ([Move.pileStack L, Move.pileStack H] ++ p₂)) = some W
  rw [run_split_bind A cu ([Move.pileStack L, Move.pileStack H] ++ p₂), hA_cu]
  show C₀.run ([Move.pileStack L, Move.pileStack H] ++ p₂) = some W
  show C₀.run ([Move.pileStack L] ++ ([Move.pileStack H] ++ p₂)) = some W
  rw [run_split_bind C₀ [Move.pileStack L] ([Move.pileStack H] ++ p₂)]
  have hr1 : C₀.run [Move.pileStack L] = some D₀ := by
    simp only [State.run, hD₀]
  rw [hr1]
  exact run_append_some (by simp only [State.run, hexchange]) hp₂

/-! ## L1/O3(ii) — the general window: catch-up MIXED with ortho moves

The pure catch-up window above reorders a mid made only of the low
suit's exact-rung `pileStack`s.  The general window (L1/O3 part (ii))
allows the mid to MIX those catch-up cards with ortho twin moves —
draws, reveals, `deckPile`/`pilePile`/`stackPile` landings, and
foundation moves of cards off the twin's own suit — as long as every
mid move stays off the twin pair and (for the three height-reading
kinds) off the twin's suit.  The obstruction the FARM queue records is
genuine: an ortho move landing onto the twin's vacated base seat fires
only on the source side (the twin still occupies the seat before the
reorder), and the `haccess` premise is exactly what such landings
break (witness A's shape); a landing onto the twin itself is the
covered-twin corner (witness B's shape), and it dies on the source
side already — a fired twin is unseated, hence invisible as a
`canPlace` base.  So `haccess` — the mid is replayable at the
pre-firing state — is the no-landing premise in its executable form,
and the whole window rides the EXCHANGE-shaped reorder below instead
of the pure one.

The engine is a per-kind one-step exchange: given the twin's guarded
firing at `S` and a mid move `m` firing on BOTH sides, the twin fires
at the moved state landing exactly on the moved successor.  The
`pileStack` case is the existing `apply_pileStack_pileStack_exchange`
(one lemma serves the catch-up cards and every off-suit `pileStack`);
the six other kinds get one lemma each.  The covered-twin and
vacated-seat divergences are DERIVED from the two firings, never
premised: a landing base occupied by `t` cannot fire at `S` (the cell
reads `none`), and a landing on `t`'s own seat cannot fire at `B` (no
visible base card).  The lone exception is `reveal`: its attach base
is the pile's hidden second-from-top card — deal data, not board
occupancy — so a junk state could hide the twin itself in a hidden
slice and seat the boundary card on top of it on BOTH sides.  WF's
`vis_not_hidden` kills exactly that (the fired twin is seated, hence
visible, hence in no hidden slice), so the reveal step is the one
place the general window carries `hwf`. -/

/-- The mixed-mid predicate: `true` iff the move can ride the general
window's mid.  The three height-reading kinds demand the moved card be
off the twin's suit (its guard reads `heights`, which the twin's firing
bumps — the exchange needs the guard to read the same height on both
sides) and off the twin pair (the mirror leg needs `cleanTwin`; an
on-pair foundation move in the mid is the shuttle corner recorded as
the residue).  Everything else — `draw`, `reveal`, `deckPile`,
`pilePile` — is unconditionally mid-safe. -/
def Move.twinMid (t : Card) : Move → Bool
  | .pileStack c | .deckStack c | .stackPile c _ =>
      decide (c.suit ≠ t.suit ∧ c ≠ t.flipSuit)
  | _ => true

theorem Move.twinMid_pileStack (t c : Card) :
    Move.twinMid t (Move.pileStack c) = true ↔
      c.suit ≠ t.suit ∧ c ≠ t.flipSuit := by
  simp [Move.twinMid]

theorem Move.twinMid_deckStack (t c : Card) :
    Move.twinMid t (Move.deckStack c) = true ↔
      c.suit ≠ t.suit ∧ c ≠ t.flipSuit := by
  simp [Move.twinMid]

theorem Move.twinMid_stackPile (t c : Card) (b : Base) :
    Move.twinMid t (Move.stackPile c b) = true ↔
      c.suit ≠ t.suit ∧ c ≠ t.flipSuit := by
  simp [Move.twinMid]

@[simp] theorem Move.twinMid_draw (t : Card) :
    Move.twinMid t Move.draw = true := rfl

@[simp] theorem Move.twinMid_reveal (t : Card) (a : Anchor) :
    Move.twinMid t (Move.reveal a) = true := rfl

@[simp] theorem Move.twinMid_deckPile (t : Card) (c : Card) (b : Base) :
    Move.twinMid t (Move.deckPile c b) = true := rfl

@[simp] theorem Move.twinMid_pilePile (t : Card) (c : Card) (b : Base) :
    Move.twinMid t (Move.pilePile c b) = true := rfl

/-- Every mixed-mid move is CLEAN for the pair exchange (the mirror
leg of the window needs it). -/
theorem Move.twinMid_clean {t : Card} {m : Move} (hm : Move.twinMid t m = true) :
    Move.cleanTwin t m = true := by
  cases m with
  | draw | reveal _ | deckPile _ _ | pilePile _ _ => rfl
  | deckStack c =>
      obtain ⟨hsu, h₂⟩ := (Move.twinMid_deckStack t c).mp hm
      show Card.offPair t c = true
      exact Card.offPair_true (fun h => hsu (by rw [h])) (fun h => h₂ (by rw [h]))
  | pileStack c =>
      obtain ⟨hsu, h₂⟩ := (Move.twinMid_pileStack t c).mp hm
      show Card.offPair t c = true
      exact Card.offPair_true (fun h => hsu (by rw [h])) (fun h => h₂ (by rw [h]))
  | stackPile c b =>
      obtain ⟨hsu, h₂⟩ := (Move.twinMid_stackPile t c b).mp hm
      show Card.offPair t c = true
      exact Card.offPair_true (fun h => hsu (by rw [h])) (fun h => h₂ (by rw [h]))

/-- The pure catch-up family rides the mixed mid (below-rank cards are
off the pair; the low suit is off the twin's suit). -/
theorem catchup_mem_twinMid {t : Card} {cu : List Move}
    (hcu : ∀ m ∈ cu, ∃ c, m = Move.pileStack c ∧
      c.suit = t.flipSuit.suit ∧ c.rank.toIdx < t.rank.toIdx) :
    ∀ m ∈ cu, Move.twinMid t m = true := by
  intro m hm
  obtain ⟨c, hmc, hsu, hlt⟩ := hcu m hm
  have hsne : t.flipSuit.suit ≠ t.suit := fun h => Suit.flipPair_ne t.suit h
  rw [hmc]
  refine (Move.twinMid_pileStack t c).mpr ⟨fun hcon => hsne (hsu.symm.trans hcon), ?_⟩
  intro hcon
  rw [hcon] at hlt
  rw [Card.flipSuit_rank] at hlt
  omega

/-! ### The per-kind exchange steps

Each lemma takes the twin's guarded firing at `S` (landing `B`) and the
mid move's firing on BOTH sides, and concludes the twin fires at the
moved state with landing EXACTLY the moved successor — the reorder's
induction step. -/

/-- The `draw` exchange: draws touch only the stock cursor, which the
twin's firing does not read. -/
theorem twin_fire_exchange_draw {S B S₁ T₁ : State} {t : Card}
    (hB : S.apply (Move.pileStack t) = some B)
    (hS : S.apply Move.draw = some S₁)
    (hT : B.apply Move.draw = some T₁) :
    S₁.apply (Move.pileStack t) = some T₁ := by
  rw [apply_draw_iff] at hS hT
  obtain rfl := hS
  obtain rfl := hT
  rw [apply_pileStack_iff] at hB
  obtain ⟨htop, β, hβ, hrk, hBshape⟩ := hB
  refine apply_pileStack_iff.mpr ⟨htop, β, hβ, hrk, ?_⟩
  rw [hBshape]

/-- The `deckStack` exchange: the moved card's suit is off the twin's
suit, so its rung guard reads the same height on both sides and the
two height bumps commute. -/
theorem twin_fire_exchange_deckStack {S B S₁ T₁ : State} {t c : Card}
    (hsu : c.suit ≠ t.suit)
    (hB : S.apply (Move.pileStack t) = some B)
    (hS : S.apply (Move.deckStack c) = some S₁)
    (hT : B.apply (Move.deckStack c) = some T₁) :
    S₁.apply (Move.pileStack t) = some T₁ := by
  rw [apply_deckStack_iff] at hS hT
  obtain ⟨-, -, hS₁⟩ := hS
  obtain ⟨-, -, hT₁⟩ := hT
  rw [hS₁, hT₁]
  rw [apply_pileStack_iff] at hB
  obtain ⟨htop, β, hβ, hrk, hBshape⟩ := hB
  refine apply_pileStack_iff.mpr ⟨htop, β, hβ, ?_, ?_⟩
  · show t.rank.toIdx =
      (if t.suit = c.suit then S.heights t.suit + 1 else S.heights t.suit)
    rw [ite_eq_right (fun h => hsu h.symm)]
    exact hrk
  · rw [hBshape]
    apply state_ext
    · rfl
    · rfl
    · funext s
      show (if s = c.suit then
          (if s = t.suit then S.heights s + 1 else S.heights s) + 1
        else if s = t.suit then S.heights s + 1 else S.heights s)
        = (if s = t.suit then
          (if s = c.suit then S.heights s + 1 else S.heights s) + 1
        else if s = c.suit then S.heights s + 1 else S.heights s)
      by_cases h1 : s = t.suit
      · rw [ite_eq_right (fun hh => hsu (hh.symm.trans h1)),
          ite_eq_left h1, ite_eq_left h1,
          ite_eq_right (fun hh => hsu (hh.symm.trans h1))]
      · rw [ite_eq_right h1, ite_eq_right h1]
    · rfl
    · rfl
    · rfl

/-- The `deckPile` exchange: the drawn card's landing cell is neither
the twin's base (occupied at `S`) nor the twin's own seat (the fired
twin is unseated, hence invisible as a base at `B`) — both excluded by
the firings themselves — so the attach commutes with the twin's
detach, and the stock splice is untouched by the firing. -/
theorem twin_fire_exchange_deckPile {S B S₁ T₁ : State} {t X : Card} {b : Base}
    (hB : S.apply (Move.pileStack t) = some B)
    (hS : S.apply (Move.deckPile X b) = some S₁)
    (hT : B.apply (Move.deckPile X b) = some T₁) :
    S₁.apply (Move.pileStack t) = some T₁ := by
  rw [apply_pileStack_iff] at hB
  obtain ⟨htop, β, hβ, hrk, hBshape⟩ := hB
  rw [apply_deckPile_iff] at hS
  obtain ⟨-, hcp, bdS, hattS, hS₁⟩ := hS
  rw [apply_deckPile_iff] at hT
  obtain ⟨-, hcpB, bdT, hattT, hT₁⟩ := hT
  rw [hS₁, hT₁]
  have hβtop : S.board.topOf β = some t := (Board.bottomOf_eq S.board t β).mp hβ
  have hBbot : B.board.bottomOf t = none := by
    rw [hBshape]; exact Board.bottomOf_detach_self hβtop
  have hbfree : S.board.topOf b = none := topOf_of_canPlace hcp
  have hbβ : b ≠ β := fun hcon => by
    rw [hcon] at hbfree; rw [hβtop] at hbfree; exact absurd hbfree (by simp)
  have hbt : b ≠ Sum.inr t := by
    intro hcon
    rw [hcon] at hcpB
    obtain ⟨-, hvis, -⟩ := canPlace_inr_iff.mp hcpB
    rw [show B.isVis t = (B.board.bottomOf t).isSome from rfl, hBbot] at hvis
    simp at hvis
  rw [hBshape] at hattT
  have hattT' : (S.board.detach β).attach b X = some bdT := hattT
  have hbord : bdT = bdS.detach β :=
    (attach_detach_comm hbβ hattS hattT').symm
  refine apply_pileStack_iff.mpr ⟨?_, β, ?_, hrk, ?_⟩
  · show bdS.topOf (Sum.inr t) = none
    rw [Board.attach_topOf_ne _ _ _ hattS (Ne.symm hbt)]
    exact htop
  · show bdS.bottomOf t = some β
    refine (Board.bottomOf_eq _ _ _).mpr ?_
    rw [Board.attach_topOf_ne _ _ _ hattS (Ne.symm hbβ)]
    exact hβtop
  · rw [hBshape]
    apply state_ext
    · rfl
    · exact hbord
    · funext s
      rfl
    · rfl
    · rfl
    · rfl

/-- The `stackPile` exchange: the worry-back of an off-suit card.  Its
rung guard reads the moved card's suit (off the twin's suit, so the
same height on both sides), and the landing exclusions are derived
exactly as in the `deckPile` exchange. -/
theorem twin_fire_exchange_stackPile {S B S₁ T₁ : State} {t c : Card} {b : Base}
    (hsu : c.suit ≠ t.suit)
    (hB : S.apply (Move.pileStack t) = some B)
    (hS : S.apply (Move.stackPile c b) = some S₁)
    (hT : B.apply (Move.stackPile c b) = some T₁) :
    S₁.apply (Move.pileStack t) = some T₁ := by
  rw [apply_pileStack_iff] at hB
  obtain ⟨htop, β, hβ, hrk, hBshape⟩ := hB
  rw [apply_stackPile_iff] at hS
  obtain ⟨-, hcp, bdS, hattS, hS₁⟩ := hS
  rw [apply_stackPile_iff] at hT
  obtain ⟨-, hcpB, bdT, hattT, hT₁⟩ := hT
  rw [hS₁, hT₁]
  have hβtop : S.board.topOf β = some t := (Board.bottomOf_eq S.board t β).mp hβ
  have hBbot : B.board.bottomOf t = none := by
    rw [hBshape]; exact Board.bottomOf_detach_self hβtop
  have hbfree : S.board.topOf b = none := topOf_of_canPlace hcp
  have hbβ : b ≠ β := fun hcon => by
    rw [hcon] at hbfree; rw [hβtop] at hbfree; exact absurd hbfree (by simp)
  have hbt : b ≠ Sum.inr t := by
    intro hcon
    rw [hcon] at hcpB
    obtain ⟨-, hvis, -⟩ := canPlace_inr_iff.mp hcpB
    rw [show B.isVis t = (B.board.bottomOf t).isSome from rfl, hBbot] at hvis
    simp at hvis
  rw [hBshape] at hattT
  have hattT' : (S.board.detach β).attach b c = some bdT := hattT
  have hbord : bdT = bdS.detach β :=
    (attach_detach_comm hbβ hattS hattT').symm
  refine apply_pileStack_iff.mpr ⟨?_, β, ?_, ?_, ?_⟩
  · show bdS.topOf (Sum.inr t) = none
    rw [Board.attach_topOf_ne _ _ _ hattS (Ne.symm hbt)]
    exact htop
  · show bdS.bottomOf t = some β
    refine (Board.bottomOf_eq _ _ _).mpr ?_
    rw [Board.attach_topOf_ne _ _ _ hattS (Ne.symm hbβ)]
    exact hβtop
  · show t.rank.toIdx =
      (if t.suit = c.suit then S.heights t.suit - 1 else S.heights t.suit)
    rw [ite_eq_right (fun h => hsu h.symm)]
    exact hrk
  · rw [hBshape]
    apply state_ext
    · rfl
    · exact hbord
    · funext s
      show (if s = c.suit then
          (if s = t.suit then S.heights s + 1 else S.heights s) - 1
        else if s = t.suit then S.heights s + 1 else S.heights s)
        = (if s = t.suit then
          (if s = c.suit then S.heights s - 1 else S.heights s) + 1
        else if s = c.suit then S.heights s - 1 else S.heights s)
      by_cases h1 : s = t.suit
      · rw [ite_eq_right (fun hh => hsu (hh.symm.trans h1)),
          ite_eq_left h1, ite_eq_left h1,
          ite_eq_right (fun hh => hsu (hh.symm.trans h1))]
      · rw [ite_eq_right h1, ite_eq_right h1]
    · rfl
    · rfl
    · rfl

/-- The `pilePile` exchange: the run move.  The run head is not the
twin (a run head must be seated, and the twin is unseated at `B`); the
detach cell (the head's own base) is not the twin's base (their tops
differ); the landing cell is neither the twin's base (occupied at
`S`) nor the twin's own seat (no visible base at `B`) — every
exclusion derives from the two firings, including when the twin rides
inside the moved run at `S` (the internal edges ride the move
unchanged, and the twin's base cell is never written). -/
theorem twin_fire_exchange_pilePile {S B S₁ T₁ : State} {t z : Card} {b : Base}
    (hB : S.apply (Move.pileStack t) = some B)
    (hS : S.apply (Move.pilePile z b) = some S₁)
    (hT : B.apply (Move.pilePile z b) = some T₁) :
    S₁.apply (Move.pileStack t) = some T₁ := by
  rw [apply_pileStack_iff] at hB
  obtain ⟨htop, β, hβ, hrk, hBshape⟩ := hB
  rw [apply_pilePile_iff] at hS
  obtain ⟨b₀, hbot, hne, hcmr, bdS, hattS, hS₁⟩ := hS
  rw [apply_pilePile_iff] at hT
  obtain ⟨b₀', hbot', hne', hcmr', bdT, hattT, hT₁⟩ := hT
  rw [hS₁, hT₁]
  rw [hBshape] at hbot' hattT
  have hβtop : S.board.topOf β = some t := (Board.bottomOf_eq S.board t β).mp hβ
  have hzT : (S.board.detach β).bottomOf t = none := Board.bottomOf_detach_self hβtop
  have hBbot : B.board.bottomOf t = none := by
    rw [hBshape]; exact Board.bottomOf_detach_self hβtop
  have hzne : z ≠ t := by
    intro hcon
    rw [hcon] at hbot'
    have hc : (S.board.detach β).bottomOf t = some b₀' := hbot'
    rw [hzT] at hc
    exact absurd hc (by simp)
  have hb₀' : b₀' = b₀ := by
    have hzB' : (S.board.detach β).topOf b₀' = some z :=
      (Board.bottomOf_eq _ z b₀').mp hbot'
    by_cases hβb₀ : b₀' = β
    · rw [hβb₀, Board.detach_topOf] at hzB'
      exact absurd hzB' (by simp)
    · have hzS : S.board.topOf b₀' = some z := by
        rw [← Board.detach_topOf_ne S.board β b₀' hβb₀]
        exact hzB'
      exact S.board.inj b₀' b₀ z hzS ((Board.bottomOf_eq S.board z b₀).mp hbot)
  rw [hb₀'] at hattT
  have hb₀β : b₀ ≠ β := by
    intro hcon
    have hh := (Board.bottomOf_eq S.board z b₀).mp hbot
    rw [hcon] at hh
    exact hzne (Option.some.inj (hh.symm.trans hβtop))
  have hcpS : S.canPlace z b = true := by
    cases b with
    | inl a => exact canMoveRun_inl_iff.mp hcmr
    | inr d => exact (canMoveRun_inr_iff.mp hcmr).1
  have hcpB : B.canPlace z b = true := by
    cases b with
    | inl a => exact canMoveRun_inl_iff.mp hcmr'
    | inr d => exact (canMoveRun_inr_iff.mp hcmr').1
  have hbfree : S.board.topOf b = none := topOf_of_canPlace hcpS
  have hbβ : b ≠ β := fun hcon => by
    rw [hcon] at hbfree; rw [hβtop] at hbfree; exact absurd hbfree (by simp)
  have hbt : b ≠ Sum.inr t := by
    intro hcon
    rw [hcon] at hcpB
    obtain ⟨-, hvis, -⟩ := canPlace_inr_iff.mp hcpB
    rw [show B.isVis t = (B.board.bottomOf t).isSome from rfl, hBbot] at hvis
    simp at hvis
  have hb₀t : b₀ ≠ Sum.inr t := by
    intro hcon
    have hh := (Board.bottomOf_eq S.board z b₀).mp hbot
    rw [hcon, htop] at hh
    exact absurd hh (by simp)
  have hattT' : ((S.board.detach β).detach b₀).attach b z = some bdT := hattT
  have hdet : (S.board.detach β).detach b₀ = (S.board.detach b₀).detach β :=
    Board.detach_detach_comm S.board β b₀ (Ne.symm hb₀β)
  rw [hdet] at hattT'
  have hbord : bdT = bdS.detach β :=
    (attach_detach_comm hbβ hattS hattT').symm
  refine apply_pileStack_iff.mpr ⟨?_, β, ?_, hrk, ?_⟩
  · show bdS.topOf (Sum.inr t) = none
    rw [Board.attach_topOf_ne _ _ _ hattS (Ne.symm hbt),
      Board.detach_topOf_ne _ _ _ (Ne.symm hb₀t)]
    exact htop
  · show bdS.bottomOf t = some β
    refine (Board.bottomOf_eq _ _ _).mpr ?_
    rw [Board.attach_topOf_ne _ _ _ hattS (Ne.symm hbβ),
      Board.detach_topOf_ne _ _ _ (Ne.symm hb₀β)]
    exact hβtop
  · rw [hBshape]
    apply state_ext
    · rfl
    · exact hbord
    · funext s
      rfl
    · rfl
    · rfl
    · rfl

/-- The `reveal` exchange — the one step that needs WF.  The reveal's
attach base is the pile's hidden second-from-top card, which is deal
data rather than board occupancy; without WF a junk state could hide
the twin itself in a pile's hidden slice and seat the boundary card on
top of it on BOTH sides (the covered-twin corner as a mid move).  WF's
`vis_not_hidden` pins the seated twin outside every hidden slice, and
the remaining exclusions (the base cells) derive from the firings. -/
theorem twin_fire_exchange_reveal {S B S₁ T₁ : State} {t : Card} {a : Anchor}
    (hwf : S.WF)
    (hB : S.apply (Move.pileStack t) = some B)
    (hS : S.apply (Move.reveal a) = some S₁)
    (hT : B.apply (Move.reveal a) = some T₁) :
    S₁.apply (Move.pileStack t) = some T₁ := by
  rw [apply_pileStack_iff] at hB
  obtain ⟨htop, β, hβ, hrk, hBshape⟩ := hB
  rw [apply_reveal_iff] at hS
  obtain ⟨r, bdS, htopH, hbare, hattS, hS₁⟩ := hS
  rw [apply_reveal_iff] at hT
  obtain ⟨r', bdT, htopH', hbare', hattT, hT₁⟩ := hT
  rw [hS₁, hT₁]
  have hth' : S.topHidden a = B.topHidden a := by rw [hBshape]; rfl
  rw [← hth'] at htopH'
  have hr'r : r' = r := Option.some.inj (htopH'.symm.trans htopH)
  rw [hr'r] at hattT
  rw [hBshape] at hattT
  have htvis : S.isVis t = true := by
    show (S.board.bottomOf t).isSome = true
    rw [hβ]
    rfl
  have hthid : ∀ a', t ∉ S.hidden a' := hwf.vis_not_hidden t htvis
  have hbb : S.hiddenBase a ≠ Sum.inr t :=
    fun hcon => hthid a (State.mem_hidden_of_hiddenBase hcon)
  have hβtop : S.board.topOf β = some t := (Board.bottomOf_eq S.board t β).mp hβ
  have hbbβ : S.hiddenBase a ≠ β := by
    intro hcon
    obtain ⟨hfree, -⟩ := (Board.attach_eq_some_iff S.board (S.hiddenBase a) r).mp
      (by rw [hattS]; simp)
    rw [hcon] at hfree
    rw [hβtop] at hfree
    exact absurd hfree (by simp)
  have hattT' : (S.board.detach β).attach (S.hiddenBase a) r = some bdT := hattT
  have hbord : bdT = bdS.detach β :=
    (attach_detach_comm hbbβ hattS hattT').symm
  refine apply_pileStack_iff.mpr ⟨?_, β, ?_, hrk, ?_⟩
  · show bdS.topOf (Sum.inr t) = none
    rw [Board.attach_topOf_ne _ _ _ hattS (Ne.symm hbb)]
    exact htop
  · show bdS.bottomOf t = some β
    refine (Board.bottomOf_eq _ _ _).mpr ?_
    rw [Board.attach_topOf_ne _ _ _ hattS (Ne.symm hbbβ)]
    exact hβtop
  · rw [hBshape]
    apply state_ext
    · rfl
    · exact hbord
    · funext s
      rfl
    · funext a'
      rfl
    · rfl
    · rfl
/-- **The general reorder (L1/O3(ii) cornerstone)**: the MIXED mid
commutes with the twin's stacking — given the twin's guarded firing at
`A`, the mid's run at the pre-firing state (the accessibility
license, `haccess` in the window) and the source's own mid (the
second license), the twin fires AFTER the replayed mid landing
EXACTLY on the source's mid successor.  Induction over the mid, one
exchange step per move kind; the `pileStack` case is the existing
one-step exchange (which already serves the catch-up cards and every
off-suit `pileStack`).  `hwf` is carried along the prefixes: the
reveal step is its only consumer (`vis_not_hidden` at each prefix). -/
theorem pileStack_mid_reorder {t : Card} :
    ∀ (mid : List Move) (A B M₀ C : State),
    (∀ m ∈ mid, Move.twinMid t m = true) →
    A.WF →
    A.apply (Move.pileStack t) = some B →
    A.run mid = some M₀ →
    B.run mid = some C →
    M₀.apply (Move.pileStack t) = some C := by
  intro mid
  induction mid with
  | nil =>
      intro A B M₀ C _ _ h₁ hA hB
      rw [← run_nil_elim hA, ← run_nil_elim hB]
      exact h₁
  | cons m ms ih =>
      intro A B M₀ C hmid hwf h₁ hA hB
      obtain ⟨A₁, hmA, hrest⟩ := run_cons_elim hA
      obtain ⟨B₁, hmB, hrest'⟩ := run_cons_elim hB
      have hwfA₁ : A₁.WF := apply_wf hwf m A₁ hmA
      have hmtop : Move.twinMid t m = true := hmid m List.mem_cons_self
      have hstep : A₁.apply (Move.pileStack t) = some B₁ := by
        cases m with
        | draw => exact twin_fire_exchange_draw h₁ hmA hmB
        | reveal a' => exact twin_fire_exchange_reveal hwf h₁ hmA hmB
        | deckPile x b' => exact twin_fire_exchange_deckPile h₁ hmA hmB
        | deckStack x =>
            obtain ⟨hsu, -⟩ := (Move.twinMid_deckStack t x).mp hmtop
            exact twin_fire_exchange_deckStack hsu h₁ hmA hmB
        | pileStack x =>
            obtain ⟨hsu, -⟩ := (Move.twinMid_pileStack t x).mp hmtop
            exact apply_pileStack_pileStack_exchange hsu h₁ hmA hmB
        | stackPile x b' =>
            obtain ⟨hsu, -⟩ := (Move.twinMid_stackPile t x b').mp hmtop
            exact twin_fire_exchange_stackPile hsu h₁ hmA hmB
        | pilePile x b' => exact twin_fire_exchange_pilePile h₁ hmA hmB
      exact ih A₁ B₁ M₀ C (fun m' hm' => hmid m' (List.mem_cons_of_mem _ hm'))
        hwfA₁ hstep hrest hrest'

/-! ### The general window (L1/O3(ii)), its packaging, and its mirror -/

/-- **L1/O3(ii), the general window**: if the source game wins via
[prefix; stack t; MIXED-MID; stack t'; tail] — the mid mixing the low
suit's catch-up `pileStack`s with ortho twin moves (every move
`twinMid`: no foundation move of a `t`-suit card, nothing on the pair) —
and the mid is replayable at the pre-firing state (`haccess`, the
no-landing premise in executable form: witness A is exactly a catch-up
card buried under the twin, and an ortho landing onto the twin's
vacated base breaks the same premise), then the EXCHANGED game is
solvable: it plays [prefix*; mid*; stack t'; stack t; tail*] — the
mid rides the clean mirror, the first stacking lands the cross-skew at
the RE-ALIGNED rung, and the second re-syncs onto `D.swapTwin t` (the
same twinSkew/crossTwin spine as the pure window, fed by the general
reorder).

The `hwf` premise is the reveal-corner repair: `vis_not_hidden` keeps
the seated twin out of every hidden slice, so a mid `reveal` cannot
seat the boundary card onto it.  Note the honest boundary: the mid
predicate is ONE-SIDED in the suit condition (the LOW suit's
foundation moves are allowed — its catch-up `deckStack`s and
worry-backs read the low height, which the twin's firing does not
touch), so the predicate is NOT flip-dual; the `_back` below states
its premises at the flipped roles directly. -/
theorem State.solvable_swapTwin_mixed {st : State} {t : Card}
    {p₁ mid p₂ : List Move} {A B C D W : State}
    (hwf : st.WF)
    (hc₁ : ∀ m ∈ p₁, Move.cleanTwin t m = true)
    (hc₂ : ∀ m ∈ p₂, Move.cleanTwin t m = true)
    (hmid : ∀ m ∈ mid, Move.twinMid t m = true)
    (hp₁ : st.run p₁ = some A)
    (hf₁ : A.apply (Move.pileStack t) = some B)
    (hmidB : B.run mid = some C)
    (hf₂ : C.apply (Move.pileStack t.flipSuit) = some D)
    (hp₂ : D.run p₂ = some W)
    (haccess : ∃ M₀, A.run mid = some M₀)
    (hwin : W.isWin = true) :
    (st.swapTwin t).solvableFrom := by
  obtain ⟨M₀, hA_mid⟩ := haccess
  have hwfA : A.WF := run_wf p₁ st A hp₁ hwf
  -- the reorder: the twin fires after the replayed mid, landing on C
  have hreor := pileStack_mid_reorder mid A B M₀ C hmid hwfA hf₁ hA_mid hmidB
  rw [apply_pileStack_iff] at hreor
  obtain ⟨htop₀, β₀, hβ₀, hrk₀, hCshape⟩ := hreor
  rw [apply_pileStack_iff] at hf₂
  obtain ⟨htop', β', hβ', hrk', hDshape⟩ := hf₂
  have hsne : t.flipSuit.suit ≠ t.suit := fun h => Suit.flipPair_ne t.suit h
  -- the rung alignments the twinSkew/crossTwin spine needs
  have hC₀low : M₀.heights t.flipSuit.suit = t.rank.toIdx := by
    have h1 : t.flipSuit.rank.toIdx = C.heights t.flipSuit.suit := hrk'
    have h2 : C.heights t.flipSuit.suit = M₀.heights t.flipSuit.suit := by
      rw [hCshape]
      show (if t.flipSuit.suit = t.suit then M₀.heights t.flipSuit.suit + 1
        else M₀.heights t.flipSuit.suit) = _
      rw [ite_eq_right hsne]
    rw [Card.flipSuit_rank] at h1
    omega
  have halign₁ : M₀.heights t.suit = M₀.heights t.flipSuit.suit := by
    rw [hrk₀.symm, hC₀low]
  have halign₂ : C.heights t.suit = C.heights t.flipSuit.suit + 1 := by
    have e1 : C.heights t.suit = M₀.heights t.suit + 1 := by
      rw [hCshape]
      show (if t.suit = t.suit then M₀.heights t.suit + 1 else M₀.heights t.suit) = _
      rw [ite_eq_left rfl]
    have e2 : C.heights t.flipSuit.suit = M₀.heights t.flipSuit.suit := by
      rw [hCshape]
      show (if t.flipSuit.suit = t.suit then M₀.heights t.flipSuit.suit + 1
        else M₀.heights t.flipSuit.suit) = _
      rw [ite_eq_right hsne]
    rw [e2, hC₀low, hrk₀]
    omega
  -- the mirror play, segment by segment
  have hmidcl : ∀ m ∈ p₁ ++ mid, Move.cleanTwin t m = true := by
    intro m hm
    rcases List.mem_append.mp hm with h | h
    · exact hc₁ m h
    · exact Move.twinMid_clean (hmid m h)
  have hseg : st.run (p₁ ++ mid) = some M₀ := run_append_some hp₁ hA_mid
  have hM₁ : (st.swapTwin t).run ((p₁ ++ mid).map (Move.swapTwin t))
      = some (M₀.swapTwin t) := by
    rw [run_swapTwin_clean t st (p₁ ++ mid) hmidcl, hseg]
    rfl
  have hrunskew : (M₀.swapTwin t).run [Move.pileStack t.flipSuit]
      = some (M₀.twinSkew t β₀) := by
    simp only [State.run, State.apply_swapTwin_stack_flip htop₀ hβ₀ hC₀low]
  have hskew : M₀.twinSkew t β₀ = C.crossTwin t :=
    State.twinSkew_eq_crossTwin hCshape halign₁
  have hM₁' : (st.swapTwin t).run
      ((p₁ ++ mid).map (Move.swapTwin t) ++ [Move.pileStack t.flipSuit])
      = some (C.crossTwin t) := by
    rw [run_split_bind, hM₁]
    show (M₀.swapTwin t).run [Move.pileStack t.flipSuit] = some (C.crossTwin t)
    rw [hrunskew, hskew]
  have hM₃ : (C.crossTwin t).run [Move.pileStack t] = some (D.swapTwin t) := by
    simp only [State.run, State.apply_crossTwin_stack htop' hβ' hrk' halign₂ hDshape]
  have hM₄ : (D.swapTwin t).run (p₂.map (Move.swapTwin t))
      = some (W.swapTwin t) := by
    rw [run_swapTwin_clean t D p₂ hc₂, hp₂]
    rfl
  have hwin' : (W.swapTwin t).isWin = true := by
    simp only [State.isWin, swapTwin_heights]
    exact hwin
  refine ⟨((p₁ ++ mid).map (Move.swapTwin t) ++ [Move.pileStack t.flipSuit])
      ++ ([Move.pileStack t] ++ p₂.map (Move.swapTwin t)), W.swapTwin t, ?_, hwin'⟩
  exact run_append_some hM₁' (run_append_some hM₃ hM₄)

/-- The packaged form of the general window: the source play as one
run. -/
theorem State.solvable_swapTwin_mixed_run {st : State} {t : Card}
    {p₁ mid p₂ : List Move} {W : State}
    (hwf : st.WF)
    (hc₁ : ∀ m ∈ p₁, Move.cleanTwin t m = true)
    (hc₂ : ∀ m ∈ p₂, Move.cleanTwin t m = true)
    (hmid : ∀ m ∈ mid, Move.twinMid t m = true)
    (haccess : ∀ A, st.run p₁ = some A → ∃ M₀, A.run mid = some M₀)
    (hrun : st.run (p₁ ++ [Move.pileStack t] ++ mid
      ++ [Move.pileStack t.flipSuit] ++ p₂) = some W)
    (hwin : W.isWin = true) :
    (st.swapTwin t).solvableFrom := by
  simp only [List.append_assoc] at hrun
  rw [run_split_bind st p₁
    ([Move.pileStack t] ++ (mid ++ ([Move.pileStack t.flipSuit] ++ p₂)))] at hrun
  cases hA : st.run p₁ with
  | none => rw [hA] at hrun; simp at hrun
  | some A =>
    rw [hA] at hrun
    have hrun1 : A.run ([Move.pileStack t] ++ (mid ++ ([Move.pileStack t.flipSuit] ++ p₂)))
        = some W := hrun
    rw [run_split_bind A [Move.pileStack t]
      (mid ++ ([Move.pileStack t.flipSuit] ++ p₂))] at hrun1
    simp only [State.run] at hrun1
    cases hB₀ : A.apply (Move.pileStack t) with
    | none => rw [hB₀] at hrun1; simp at hrun1
    | some B =>
      rw [hB₀] at hrun1
      have hrun2 : B.run (mid ++ ([Move.pileStack t.flipSuit] ++ p₂)) = some W := hrun1
      rw [run_split_bind B mid
        ([Move.pileStack t.flipSuit] ++ p₂)] at hrun2
      cases hC : B.run mid with
      | none => rw [hC] at hrun2; simp at hrun2
      | some C =>
        rw [hC] at hrun2
        have hrun3 : C.run ([Move.pileStack t.flipSuit] ++ p₂) = some W := hrun2
        rw [run_split_bind C [Move.pileStack t.flipSuit] p₂] at hrun3
        simp only [State.run] at hrun3
        cases hD₀ : C.apply (Move.pileStack t.flipSuit) with
        | none => rw [hD₀] at hrun3; simp at hrun3
        | some D =>
          rw [hD₀] at hrun3
          have hWD : D.run p₂ = some W := hrun3
          obtain ⟨M₀, hA_mid⟩ := haccess A hA
          exact State.solvable_swapTwin_mixed hwf hc₁ hc₂ hmid hA hB₀ hC hD₀ hWD
            ⟨M₀, hA_mid⟩ hwin

/-- **The catch-up iff, backward half (L1/O3(ii) mirrored)**: the
general window at the flipped twin, composed with the involution —
the hypotheses are stated directly at the flipped roles the mirror
game actually has (the state `(st.swapTwin t)` whose first stackable
twin is `t.flipSuit`), because the one-sided suit condition of
`twinMid` is NOT flip-dual: a `t`-suit foundation move is legal in
the MIRROR's mid (it reads the mirror's low suit, which the mirror's
twin firing does not bump).

The between-shaped hypothesis this carries is the honest half of the
iff.  Wave 18 recorded the catch-up-FIRST mirror plays — the shape the
forward window CONSTRUCTS — as needing a CATCH-UP-FIRST-TO-BETWEEN
DEFERRAL under two licenses (pre-catch-up fireability + the
post-stacking tail's access).  Wave 19 resolved it honestly: the
LICENSED literal split (the mid itself re-seated between the stackings)
is REFUTED at the asymmetric window — the rung pin (the catch-up is
what raises the first-stacked twin's suit to its rung) and the flipped
witness-A seat corner (a catch-up card sitting ON that twin, uncovered
only mid-catch-up — witness C,
witnesses/TwinCompletionWitness.lean) kill the pre-catch-up
fireability — but NO license is needed after all: `q₁` never forbade
the catch-up (only ON-PAIR foundation moves are unclean), so the
catch-up-first play re-brackets verbatim as the between window with
the EMPTY mid.  That re-bracketing is
`State.solvable_swapTwin_mixed_back_catchupfirst` below. -/
theorem State.solvable_swapTwin_mixed_back {st : State} {t : Card}
    {q₁ mid q₂ : List Move} {W : State}
    (hwf : (st.swapTwin t).WF)
    (hc₁ : ∀ m ∈ q₁, Move.cleanTwin t.flipSuit m = true)
    (hc₂ : ∀ m ∈ q₂, Move.cleanTwin t.flipSuit m = true)
    (hmid : ∀ m ∈ mid, Move.twinMid t.flipSuit m = true)
    (hrun : (st.swapTwin t).run (q₁ ++ [Move.pileStack t.flipSuit] ++ mid
      ++ [Move.pileStack t] ++ q₂) = some W)
    (haccess : ∀ A', (st.swapTwin t).run q₁ = some A' → ∃ M₀, A'.run mid = some M₀)
    (hwin : W.isWin = true) :
    st.solvableFrom := by
  have hrun' : (st.swapTwin t).run (q₁ ++ [Move.pileStack t.flipSuit] ++ mid
      ++ [Move.pileStack t.flipSuit.flipSuit] ++ q₂) = some W := by
    rw [Card.flipSuit_flipSuit]
    exact hrun
  have h := State.solvable_swapTwin_mixed_run (st := st.swapTwin t) (t := t.flipSuit)
    hwf hc₁ hc₂ hmid haccess hrun' hwin
  rw [State.swapTwin_flipSuit, State.swapTwin_swapTwin] at h
  exact h

/-! ### The catch-up-first→between deferral — resolved (wave 19)

Wave 18's successor ticket asked for the deferral with two licenses.
The honest resolution cuts both ways:

* The LICENSED half — the literal between split, `[q₁; stack t'; MID;
  stack t; q₂]` with the mirror's ACTUAL mid re-seated between the two
  stackings — needs `stack t'` to fire BEFORE the mid, and at the
  asymmetric window that fails STRUCTURALLY: the mid's catch-up raises
  are exactly what lifts `t'`'s suit to its rung, so pre-mid the rung
  guard fails; and even when the heights align, the mate can be
  covered (witness C: a catch-up card dealt onto the twin, uncovered
  only by its own raise mid-catch-up — the flipped witness-A corner).
  The pre-catch-up fireability license is REFUTABLE as stated; no
  license carries the literal split, and none is needed.
* The FREE half — the only one the iff ever wanted: `solvable_swapTwin_mixed_back`
  restricts the BETWEEN-MID (`twinMid t'`) but never restricts `q₁`
  (only `cleanTwin t'`, which forbids ON-PAIR FOUNDATION moves only —
  `t'`-suit raises are `t`-off-pair by rank).  So a catch-up-first
  mirror play `q₁ ++ [stack t', stack t] ++ q₂` — with the whole
  catch-up-containing prefix swallowed into `q₁` and the two stackings
  ADJACENT — IS the between window with the EMPTY mid, and `_back`
  applies verbatim.  Composed with the forward window (whose constructed
  mirror play has exactly this shape), wave 18's iff closes at the
  clean class with no deferral license consumed. -/

/-- **The catch-up-first→between deferral, the free half (L1(ii)'s
mirror completion — wave 19)**: a MIRROR play of the catch-up-first
shape — `q₁` arbitrary clean (it may — and at the asymmetric window
it must — carry the whole catch-up: `t'`-suit raises are off-pair by
rank), the two twin stackings ADJACENT, then the clean tail — makes
`st` solvable: the play re-brackets as `solvable_swapTwin_mixed_back`'s
between window with the EMPTY mid, and `_back` applies verbatim.
No deferral license is consumed; see the section note above for why
the licensed literal split is unavailable at the asymmetric window
(witness C) and unnecessary for the iff. -/
theorem State.solvable_swapTwin_mixed_back_catchupfirst {st : State} {t : Card}
    {q₁ q₂ : List Move} {W : State}
    (hwf : (st.swapTwin t).WF)
    (hc₁ : ∀ m ∈ q₁, Move.cleanTwin t.flipSuit m = true)
    (hc₂ : ∀ m ∈ q₂, Move.cleanTwin t.flipSuit m = true)
    (hrun : (st.swapTwin t).run (q₁ ++ [Move.pileStack t.flipSuit,
      Move.pileStack t] ++ q₂) = some W)
    (hwin : W.isWin = true) :
    st.solvableFrom := by
  refine State.solvable_swapTwin_mixed_back (mid := []) hwf hc₁ hc₂
    (by simp) ?_ (fun A' _ => ⟨A', rfl⟩) hwin
  have hrun' : (st.swapTwin t).run (q₁ ++ [Move.pileStack t.flipSuit]
      ++ ([] : List Move) ++ [Move.pileStack t] ++ q₂) = some W := by
    simpa using hrun
  exact hrun'

/-! ## Item 3 — twin-suit worry-backs in the window

Two facts discipline the window's mid.  First, the EXCLUDED family is
excluded CONTENTFULLY: a foundation move READING the twin's own suit
cannot fire on both sides of the exchange at all — the height the
twin's firing creates is a one-rung offset, and the ±1 is not
satisfiable both ways (the low suit's worry-backs and raises, by
contrast, RIDE the window: `twinMid` admits them, and the exchange
steps transfer their guards verbatim since the twin's firing does not
touch the low suit's height).  Second, the worry-backs that occur in
real winning plays are EXCURSION-SHAPED — [stackPile c b, pileStack c]
is an unconditional identity pair — so they lift out of the mid whole,
on either side of the window. -/

/-- **A `t`-suit worry-back cannot fire on both sides of the
exchange**: the twin's firing pins the `t`-suit height to its own
rung at `S` and one above at `B`, and the worry-back's un-stack guard
(`toIdx c + 1 = heights`) is a fixed point between the two — no card
of the twin's own rank-neighborhood satisfies both readings. -/
theorem twin_fire_tSuit_stackPile_impossible {S B S₁ T₁ : State} {t c : Card} {b : Base}
    (hB : S.apply (Move.pileStack t) = some B)
    (hS : S.apply (Move.stackPile c b) = some S₁)
    (hT : B.apply (Move.stackPile c b) = some T₁)
    (hsu : c.suit = t.suit) : False := by
  rw [apply_pileStack_iff] at hB
  obtain ⟨-, htβ, -, -, hBshape⟩ := hB
  rw [apply_stackPile_iff] at hS hT
  obtain ⟨hg, -, -, -, -⟩ := hS
  obtain ⟨hg', -, -, -, -⟩ := hT
  have hbc : B.heights c.suit = S.heights c.suit + 1 := by
    rw [hBshape]
    show (if c.suit = t.suit then S.heights c.suit + 1 else S.heights c.suit) = _
    rw [ite_eq_left hsu]
  omega

/-- The same one-rung contradiction for the `t`-suit raise kind
(`pileStack` of a card of the twin's own suit): the raise's rung guard
pins the card to the twin's height at `S`, which the twin's own
firing has already left behind at `B`. -/
theorem twin_fire_tSuit_pileStack_impossible {S B S₁ T₁ : State} {t c : Card}
    (hB : S.apply (Move.pileStack t) = some B)
    (hS : S.apply (Move.pileStack c) = some S₁)
    (hT : B.apply (Move.pileStack c) = some T₁)
    (hsu : c.suit = t.suit) : False := by
  rw [apply_pileStack_iff] at hB
  obtain ⟨-, htβ, -, -, hBshape⟩ := hB
  rw [apply_pileStack_iff] at hS hT
  obtain ⟨-, hcβ, -, hg, -⟩ := hS
  obtain ⟨-, hdβ, -, hg', -⟩ := hT
  have hbc : B.heights c.suit = S.heights c.suit + 1 := by
    rw [hBshape]
    show (if c.suit = t.suit then S.heights c.suit + 1 else S.heights c.suit) = _
    rw [ite_eq_left hsu]
  omega

/-- The identity-excursion lift: an adjacent
[worry-back, re-stack] pair nets to the identity on states
(`stackPile_pileStack_return`), so it can be excised from any winning
run without changing the outcome — the worry-backs that DO occur in
winning plays (inside or besides the window) ride this. -/
theorem run_worryback_pair_excise (c : Card) (b : Base) (m₀ m₁ : List Move)
    {st W : State} (hwf : st.WF)
    (hrun : st.run (m₀ ++ [Move.stackPile c b, Move.pileStack c] ++ m₁) = some W) :
    st.run (m₀ ++ m₁) = some W := by
  simp only [List.append_assoc] at hrun
  rw [run_split_bind st m₀
    ([Move.stackPile c b, Move.pileStack c] ++ m₁)] at hrun
  cases hS : st.run m₀ with
  | none => rw [hS] at hrun; simp at hrun
  | some S =>
    rw [hS] at hrun
    have hrest : S.run ([Move.stackPile c b, Move.pileStack c] ++ m₁) = some W := hrun
    rw [show [Move.stackPile c b, Move.pileStack c] ++ m₁
          = [Move.stackPile c b] ++ ([Move.pileStack c] ++ m₁) from rfl] at hrest
    rw [run_split_bind S [Move.stackPile c b]
      ([Move.pileStack c] ++ m₁)] at hrest
    simp only [State.run] at hrest
    cases hs₁ : S.apply (Move.stackPile c b) with
    | none => rw [hs₁] at hrest; simp at hrest
    | some s₁ =>
      rw [hs₁] at hrest
      have hrest₂ : s₁.run ([Move.pileStack c] ++ m₁) = some W := hrest
      rw [run_split_bind s₁ [Move.pileStack c] m₁] at hrest₂
      simp only [State.run] at hrest₂
      cases hs₂ : s₁.apply (Move.pileStack c) with
      | none => rw [hs₂] at hrest₂; simp at hrest₂
      | some s₂ =>
        rw [hs₂] at hrest₂
        have htail : s₂.run m₁ = some W := hrest₂
        have hret := stackPile_pileStack_return (run_wf m₀ st S hS hwf) hs₁
        have hS₂ : s₂ = S := (Option.some.inj (hret.symm.trans hs₂)).symm
        rw [hS₂] at htail
        exact run_append_some hS htail

/-! ## The haccess derivation at engine corpora — the no-landing
reduction, REPAIRED (wave 19), PROVEN (wave 20)

`haccess` — the mid is replayable at the pre-firing state — is the
window's no-landing premise in executable form.  The model-level
reduction below PROVES it at the no-landing premise: at WF, the
source's own mid plus the per-seat exclusions (`noSeat` — the landing
bases off the twin's vacated base `β` and off the twin's own seat)
derive the WHOLE replay, and the twin's deferred firing lands exactly
on the source's mid successor `C`.

THE REPAIR (honest history): wave 18 pinned this believing the seat
exclusions needed only the three LANDING kinds.  Wave 19's audit of
every per-kind A-side guard found TWO further exclusion classes the
pinned premise missed, so the as-pinned statement was FALSE (each has
a witness-A-shaped obstruction the `match` in `noSeat` said nothing
about):

* **pileStack seats** — a mid raise card can be buried under the twin
  (`β = Sum.inr c`: the twin sits ON the catch-up card, whose seat
  guard then reads the twin's cell — witness A's own corner, at WF
  via `board_edges`' deal-adjacency clause).  The repaired premise
  adds `b = Sum.inr c` to the exclusion set.
* **reveal cells** — the reveal's two board reads are deal data, not
  program constants: the boundary card's own seat
  (`topOf (Sum.inr r)`, `r` the CURRENT `topHidden` of pile `a` —
  a twin dealt onto the hidden boundary blocks it at the pre-firing
  side only) and the attach base (`hiddenBase a` — a twin-king at the
  pile's anchor blocks it the same way).  The repaired premise
  excludes the pile's whole future reveal structure STATICALLY: the
  anchor, `A.hiddenBase a`, and the seat of every card of `A.hidden a`
  — every later boundary/attach cell of the pile's reveal chain lies
  in this set (reveal only decrements the take, and `mem_of_getLast`
  keeps the boundary inside the shrinking prefix).

The engine-corpus half — which reached states' between-mids satisfy
`noSeat` — remains §8's audit (the histogram pull); this theorem is
its model-side certificate.  The proof is the B→A mirror of the six
exchange steps, run on a per-step delta invariant
(`TwinReplayTrace`): the mid fires on BOTH sides with the boards
agreeing on every cell but `β` and the heights on every suit but the
twin's, so each A-side guard re-reads its B-side value verbatim; the
`pilePile` self-landing guard is the one genuinely new walk argument
(`aboveOf_twin_delta`: the A-side run above a card gains at most the
twin, as a top-of-run head).

Wave-20 elaboration notes (the polish the draft needed, recorded for
the next file written in this style): this Lean build REJECTS
multi-line structure instances (every `{ st with ... }` must sit on
one physical line); the replay pair-states must be `let`-bound (a
`have`-bound state is opaque to unification, so no trace slot's
literal projection can reduce to its fields); and the corpus's reveal
decrements the SPECIFIC pile's depth (`fun x => if x = a' then
S.depths a' - 1 else S.depths x` — the revealed anchor in the
then-branch, not the binder). -/

/-- The take-mono list lemma (kept local to avoid core-name
collisions). -/
private theorem take_subset_mono {α : Type} : ∀ (m n : Nat), m ≤ n →
    ∀ (l : List α), l.take m ⊆ l.take n := by
  intro m n h l
  induction l generalizing m n with
  | nil => simp
  | cons x ls ih =>
      cases m with
      | zero => simp
      | succ m' =>
          cases n with
          | zero => omega
          | succ n' =>
              show x :: ls.take m' ⊆ x :: ls.take n'
              intro r hr
              simp only [List.mem_cons] at hr
              rcases hr with rfl | hr
              · exact List.mem_cons_self
              · exact List.mem_cons_of_mem _ (ih m' n' (by omega) hr)

private theorem hidden_sub_of_deal {S A : State} {a : Anchor}
    (hdeal : S.deal = A.deal) (hle : S.depths a ≤ A.depths a) :
    S.hidden a ⊆ A.hidden a := by
  intro r hr
  have h1 : r ∈ (S.deal.piles a).take (S.depths a) := hr
  have h2 : r ∈ (A.deal.piles a).take (A.depths a) := by
    rw [← hdeal]
    exact take_subset_mono _ _ hle (S.deal.piles a) h1
  exact h2

/-- The replay pair's delta, carried by the induction: the A-side
state still has the twin seated at `β` (its own seat bare), the
B-side state is the fired image — the boards agree on every cell
but `β`, the heights on every suit but the twin's own, and the deal,
depths, stock and draw step are literally equal.  Slot order (= the
anonymous constructor's positions): `topOf β = some t`,
`topOf β = none` (B), cell-agreement off `β`, `bottomOf t = some β`,
`topOf (inr t) = none`, `bottomOf`-agreement off the twin,
deal/depths/stock equality, `S'.heights t.suit = S.heights t.suit + 1`,
heights-agreement off the twin's suit, draw step equality. -/
private def TwinReplayTrace (t : Card) (β : Base) (S S' : State) : Prop :=
  S.board.topOf β = some t ∧
  S'.board.topOf β = none ∧
  (∀ b, b ≠ β → S.board.topOf b = S'.board.topOf b) ∧
  S.board.bottomOf t = some β ∧
  S.board.topOf (Sum.inr t) = none ∧
  (∀ c, c ≠ t → S.board.bottomOf c = S'.board.bottomOf c) ∧
  S.deal = S'.deal ∧
  S.depths = S'.depths ∧
  S.stock = S'.stock ∧
  S'.heights t.suit = S.heights t.suit + 1 ∧
  (∀ s, s ≠ t.suit → S.heights s = S'.heights s) ∧
  S.drawStep = S'.drawStep

/-- Detach keeps every other card's holder (the twin's cell is the
only one written). -/
private theorem bottomOf_detach_of_ne {S : State} {β : Base} {c t : Card}
    (hbotT : S.board.topOf β = some t) (hc : c ≠ t) :
    (S.board.detach β).bottomOf c = S.board.bottomOf c := by
  cases hb : S.board.bottomOf c with
  | none =>
      refine (Board.bottomOf_eq_none _ _).mpr (fun b hb' => ?_)
      by_cases hbb : b = β
      · rw [hbb, Board.detach_topOf] at hb'; exact absurd hb' (by simp)
      · rw [Board.detach_topOf_ne _ _ _ hbb] at hb'
        exact ((Board.bottomOf_eq_none _ _).mp hb) b hb'
  | some b₁ =>
      have hb₁ : S.board.topOf b₁ = some c := (Board.bottomOf_eq _ _ _).mp hb
      have hne : b₁ ≠ β := by
        intro hcon; rw [hcon] at hb₁
        rw [hbotT] at hb₁
        exact absurd (Option.some.inj hb₁) (fun hcc => hc hcc.symm)
      exact (Board.bottomOf_eq _ _ b₁).mpr
        (by rw [Board.detach_topOf_ne _ _ _ hne]; exact hb₁)

/-- Cell agreement outside `β` transfers every non-twin card's holder
across the fired pair (the successor pack's `bottomOf` slot). -/
private theorem bottomOf_cell_transfer {bdA bdB : Board} {β : Base} {t c : Card}
    (hc : c ≠ t)
    (hβA : bdA.topOf β = some t) (hβB : bdB.topOf β = none)
    (hcells : ∀ x, x ≠ β → bdA.topOf x = bdB.topOf x) :
    bdA.bottomOf c = bdB.bottomOf c := by
  cases hb : bdA.bottomOf c with
  | none =>
      refine (((Board.bottomOf_eq_none _ _).mpr (fun x hx => ?_)).symm)
      by_cases hxx : x = β
      · rw [hxx, hβB] at hx; exact absurd hx (by simp)
      · rw [← hcells x hxx] at hx
        exact ((Board.bottomOf_eq_none _ _).mp hb) x hx
  | some b₁ =>
      have hb₁ : bdA.topOf b₁ = some c := (Board.bottomOf_eq _ _ _).mp hb
      have hne : b₁ ≠ β := by
        intro hcon; rw [hcon] at hb₁
        rw [hβA] at hb₁
        exact absurd (Option.some.inj hb₁) (fun hcc => hc hcc.symm)
      exact ((Board.bottomOf_eq _ _ b₁).mpr (by rw [← hcells b₁ hne]; exact hb₁)).symm

/-- The base case: the twin's own firing sets the delta. -/
private theorem twinReplayTrace_of_firing {t : Card} {β : Base} {S B : State}
    (hfire : S.apply (Move.pileStack t) = some B)
    (hβ : S.board.bottomOf t = some β) :
    TwinReplayTrace t β S B := by
  rw [apply_pileStack_iff] at hfire
  obtain ⟨htop, b₀, hb₀, -, hshape⟩ := hfire
  have hbotT : S.board.topOf β = some t := (Board.bottomOf_eq S.board t β).mp hβ
  have hβb : β = b₀ := (Option.some.inj (hb₀.symm.trans hβ)).symm
  subst hβb
  refine ⟨hbotT, ?_, ?_, hβ, htop, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hshape]
    exact Board.detach_topOf S.board β
  · intro b hbb2
    rw [hshape]
    exact (Board.detach_topOf_ne S.board β b hbb2).symm
  · intro c hc
    rw [hshape]
    exact (bottomOf_detach_of_ne hbotT hc).symm
  · rw [hshape]; try rfl
  · rw [hshape]; try rfl
  · rw [hshape]; try rfl
  · rw [hshape]
    show (if t.suit = t.suit then S.heights t.suit + 1 else S.heights t.suit) = _
    rw [ite_eq_left rfl]
  · intro s hs
    rw [hshape]
    show S.heights s = (if s = t.suit then S.heights s + 1 else S.heights s)
    rw [ite_eq_right hs]
  · rw [hshape]; try rfl

/-- The t-suit rung is untouched by every twinMid move (the three
foundation kinds are suit-gated off the twin's suit by `twinMid`;
everything else does not read heights at all). -/
private theorem heights_tSuit_stable {t : Card} {m : Move} {S S₁ : State}
    (hm : Move.twinMid t m = true) (hfire : S.apply m = some S₁) :
    S₁.heights t.suit = S.heights t.suit := by
  cases m with
  | draw =>
      rw [apply_draw_iff] at hfire
      rw [hfire]
  | reveal a =>
      rw [apply_reveal_iff] at hfire
      obtain ⟨r, bd, -, -, -, hshape⟩ := hfire
      rw [hshape]
  | deckPile c b =>
      rw [apply_deckPile_iff] at hfire
      obtain ⟨-, -, bd, -, hshape⟩ := hfire
      rw [hshape]
  | deckStack c =>
      obtain ⟨hsu, -⟩ := (Move.twinMid_deckStack t c).mp hm
      rw [apply_deckStack_iff] at hfire
      obtain ⟨-, -, hshape⟩ := hfire
      rw [hshape]
      show (if t.suit = c.suit then S.heights t.suit + 1 else S.heights t.suit) = _
      rw [ite_eq_right (fun h => hsu h.symm)]
  | pileStack c =>
      obtain ⟨hsu, -⟩ := (Move.twinMid_pileStack t c).mp hm
      rw [apply_pileStack_iff] at hfire
      obtain ⟨-, b₀, -, -, hshape⟩ := hfire
      rw [hshape]
      show (if t.suit = c.suit then S.heights t.suit + 1 else S.heights t.suit) = _
      rw [ite_eq_right (fun h => hsu h.symm)]
  | stackPile c b =>
      obtain ⟨hsu, -⟩ := (Move.twinMid_stackPile t c b).mp hm
      rw [apply_stackPile_iff] at hfire
      obtain ⟨-, -, bd, -, hshape⟩ := hfire
      rw [hshape]
      show (if t.suit = c.suit then S.heights t.suit - 1 else S.heights t.suit) = _
      rw [ite_eq_right (fun h => hsu h.symm)]
  | pilePile c b =>
      rw [apply_pilePile_iff] at hfire
      obtain ⟨b₀, -, -, -, bd, -, hshape⟩ := hfire
      rw [hshape]

/-- No move re-deals; reveals only shrink the hidden depth. -/
private theorem deal_stable_move {S S₁ : State} {m : Move}
    (hfire : S.apply m = some S₁) : S.deal = S₁.deal := by
  cases m with
  | draw =>
      rw [apply_draw_iff] at hfire
      rw [hfire]; try rfl
  | reveal a =>
      rw [apply_reveal_iff] at hfire
      obtain ⟨r, bd, -, -, -, hshape⟩ := hfire
      rw [hshape]; try rfl
  | deckPile c b =>
      rw [apply_deckPile_iff] at hfire
      obtain ⟨-, -, bd, -, hshape⟩ := hfire
      rw [hshape]; try rfl
  | deckStack c =>
      rw [apply_deckStack_iff] at hfire
      obtain ⟨-, -, hshape⟩ := hfire
      rw [hshape]; try rfl
  | pileStack c =>
      rw [apply_pileStack_iff] at hfire
      obtain ⟨-, b₀, -, -, hshape⟩ := hfire
      rw [hshape]; try rfl
  | stackPile c b =>
      rw [apply_stackPile_iff] at hfire
      obtain ⟨-, -, bd, -, hshape⟩ := hfire
      rw [hshape]; try rfl
  | pilePile c b =>
      rw [apply_pilePile_iff] at hfire
      obtain ⟨b₀, -, -, -, bd, -, hshape⟩ := hfire
      rw [hshape]; try rfl

private theorem depths_mono_move {S S₁ : State} {m : Move}
    (hfire : S.apply m = some S₁) : ∀ a, S₁.depths a ≤ S.depths a := by
  intro a
  cases m with
  | draw =>
      rw [apply_draw_iff] at hfire
      rw [hfire]; exact Nat.le_refl _
  | reveal a' =>
      rw [apply_reveal_iff] at hfire
      obtain ⟨r, bd, -, -, -, hshape⟩ := hfire
      have hdeq : S₁.depths = fun x => if x = a' then S.depths a' - 1
          else S.depths x := by rw [hshape]
      rw [hdeq]
      show (if a = a' then S.depths a' - 1 else S.depths a) ≤ S.depths a
      by_cases h : a = a'
      · rw [ite_eq_left h, h]; omega
      · rw [ite_eq_right h]; exact Nat.le_refl _
  | deckPile c b =>
      rw [apply_deckPile_iff] at hfire
      obtain ⟨-, -, bd, -, hshape⟩ := hfire
      rw [hshape]; exact Nat.le_refl _
  | deckStack c =>
      rw [apply_deckStack_iff] at hfire
      obtain ⟨-, -, hshape⟩ := hfire
      rw [hshape]; exact Nat.le_refl _
  | pileStack c =>
      rw [apply_pileStack_iff] at hfire
      obtain ⟨-, b₀, -, -, hshape⟩ := hfire
      rw [hshape]; exact Nat.le_refl _
  | stackPile c b =>
      rw [apply_stackPile_iff] at hfire
      obtain ⟨-, -, bd, -, hshape⟩ := hfire
      rw [hshape]; exact Nat.le_refl _
  | pilePile c b =>
      rw [apply_pilePile_iff] at hfire
      obtain ⟨b₀, -, -, -, bd, -, hshape⟩ := hfire
      rw [hshape]; exact Nat.le_refl _

/-- The reveal's attach base is the anchor of a one-hidden-card pile,
or the seat of a hidden card. -/
private theorem hiddenBase_cases {st : State} (a : Anchor) :
    st.hiddenBase a = Sum.inl a ∨
      (∃ d, st.hiddenBase a = Sum.inr d ∧ d ∈ st.hidden a) := by
  unfold State.hiddenBase
  cases h : ((st.hidden a).reverse.drop 1).head? with
  | none => exact Or.inl rfl
  | some d =>
      exact Or.inr ⟨d, rfl, List.mem_reverse.mp (List.drop_subset 1 _ (mem_of_head? h))⟩

/-- **The walk delta** (the `pilePile` self-landing transfer's back):
over the fired pair, the A-side run above a card is the B-side run,
or the twin consed on top of it (the A-walk reads the twin's cell,
gains `t`, and stops — the twin's own seat is bare — the guard reads
see a card already accumulated exactly when the walk would have
looped). -/
private theorem aboveOf_twin_delta {t : Card} {β : Base} {S S' : State}
    (hdp : TwinReplayTrace t β S S') (z : Card) :
    S.board.aboveOf z = S'.board.aboveOf z ∨
      S.board.aboveOf z = t :: S'.board.aboveOf z := by
  obtain ⟨hβA, hβB, hcells, hbotβ, hseatt, -, -, -, -, -, -, -⟩ := hdp
  have main : ∀ (n : Nat) (b : Base) (acc : List Card),
      Board.aboveOf.go S.board n b acc = Board.aboveOf.go S'.board n b acc ∨
        ∃ acc', Board.aboveOf.go S.board n b acc = t :: acc' ∧
          Board.aboveOf.go S'.board n b acc = acc' := by
    intro n
    induction n with
    | zero => intro b acc; exact Or.inl rfl
    | succ n ih =>
        intro b acc
        by_cases hbb : b = β
        · subst hbb
          by_cases hcon : acc.contains t = true
          · rw [aboveOf_go_succ S.board, aboveOf_go_succ S'.board, hβA, hβB]
            refine Or.inl ?_
            dsimp only
            rw [ite_eq_left hcon]
          · rw [aboveOf_go_succ S.board, aboveOf_go_succ S'.board, hβA, hβB]
            refine Or.inr ⟨acc, ?_, ?_⟩
            · show (if acc.contains t = true then acc
                else Board.aboveOf.go S.board n (Sum.inr t) (t :: acc)) = t :: acc
              rw [ite_eq_right hcon]
              cases n with
              | zero => rfl
              | succ n' =>
                  show Board.aboveOf.go S.board (n' + 1) (Sum.inr t) (t :: acc) = t :: acc
                  rw [aboveOf_go_succ S.board, hseatt]
            · rfl
        · rw [aboveOf_go_succ S.board, aboveOf_go_succ S'.board, hcells b hbb]
          cases htop : S'.board.topOf b with
          | none => exact Or.inl rfl
          | some c =>
              by_cases hcon : acc.contains c = true
              · dsimp only
                rw [ite_eq_left hcon, ite_eq_left hcon]
                exact Or.inl rfl
              · dsimp only
                rw [ite_eq_right hcon, ite_eq_right hcon]
                exact ih (Sum.inr c) (c :: acc)
  rcases main 53 (Sum.inr z) [] with h | ⟨acc', hA, hB⟩
  · rw [Board.aboveOf_eq_go 53 (by omega), Board.aboveOf_eq_go 53 (by omega)]
    exact Or.inl h
  · rw [← Board.aboveOf_eq_go 53 (by omega)] at hA
    have hB' : S'.board.aboveOf z = acc' := by
      rw [Board.aboveOf_eq_go 53 (by omega)]
      exact hB
    rw [hB']
    exact Or.inr hA

/-! ### The per-kind B→A transfers

Each mirror takes the replay pair (the delta above), the move's
B-side firing (the source play's own mid step), and the move's
local seat exclusions, and concludes the SAME move fires at the
A-side state leaving the pair intact. -/

/-- The `draw` transfer: the draw reads only the stock cursor, which
the twin's firing does not touch. -/
private theorem mid_access_draw {t : Card} {β : Base} {S S' T₁ : State}
    (hdp : TwinReplayTrace t β S S')
    (hfire : S'.apply Move.draw = some T₁) :
    ∃ S₁, S.apply Move.draw = some S₁ ∧ TwinReplayTrace t β S₁ T₁ := by
  obtain ⟨hβA, hβB, hcells, hbotβ, hseatt, hbofs, hdeal, hdep, hstock, hhβ, hhh,
    hds⟩ := hdp
  rw [apply_draw_iff] at hfire
  obtain rfl := hfire
  let swit : State := { S with stock := S.stock.dealOnce S.drawStep }
  refine ⟨swit, rfl, ?_⟩
  refine ⟨hβA, hβB, hcells, hbotβ, hseatt, hbofs, hdeal, hdep, ?_, hhβ, hhh,
    hds⟩
  show S.stock.dealOnce S.drawStep = S'.stock.dealOnce S'.drawStep
  rw [hstock, hds]

/-- The `deckStack` transfer: the rung guard reads the moved card's
suit (off the twin's suit by `twinMid`), so the same height answers
on both sides. -/
private theorem mid_access_deckStack {t : Card} {β : Base} {S S' T₁ : State}
    {c : Card}
    (hdp : TwinReplayTrace t β S S')
    (hsu : c.suit ≠ t.suit)
    (hfire : S'.apply (Move.deckStack c) = some T₁) :
    ∃ S₁, S.apply (Move.deckStack c) = some S₁ ∧ TwinReplayTrace t β S₁ T₁ := by
  obtain ⟨hβA, hβB, hcells, hbotβ, hseatt, hbofs, hdeal, hdep, hstock, hhβ, hhh,
    hds⟩ := hdp
  rw [apply_deckStack_iff] at hfire
  obtain ⟨hprev, hrk, rfl⟩ := hfire
  let swit : State := { S with stock := S.stock.removeAt (S.stock.cursor - 1), heights := fun s => if s = c.suit then S.heights s + 1 else S.heights s }
  refine ⟨swit, ?_, ?_⟩
  · rw [apply_deckStack_iff]
    refine ⟨?_, ?_, rfl⟩
    · rw [hstock]; exact hprev
    · rw [hrk, hhh c.suit hsu]
  · refine ⟨hβA, hβB, hcells, hbotβ, hseatt, hbofs, hdeal, hdep, ?_, ?_, ?_, hds⟩
    · show S.stock.removeAt (S.stock.cursor - 1)
          = S'.stock.removeAt (S'.stock.cursor - 1)
      rw [hstock]
    · show (if t.suit = c.suit then S'.heights t.suit + 1 else S'.heights t.suit)
          = (if t.suit = c.suit then S.heights t.suit + 1 else S.heights t.suit) + 1
      rw [ite_eq_right (fun h => hsu h.symm),
        ite_eq_right (fun h => hsu h.symm)]
      exact hhβ
    · intro s hs
      show (if s = c.suit then S.heights s + 1 else S.heights s)
          = (if s = c.suit then S'.heights s + 1 else S'.heights s)
      by_cases hsc : s = c.suit
      · rw [ite_eq_left hsc, ite_eq_left hsc]
        rw [hhh s hs]
      · rw [ite_eq_right hsc, ite_eq_right hsc]
        exact hhh s hs

/-- The `pileStack` transfer: the raise's seat guard reads its own
cell (`Sum.inr c`, excluded from `β` by the repair — witness A's
corner), and the rung guard reads the off-suit height. -/
private theorem mid_access_pileStack {t : Card} {β : Base} {S S' T₁ : State}
    {c : Card}
    (hdp : TwinReplayTrace t β S S')
    (hsu : c.suit ≠ t.suit)
    (hseat : β ≠ Sum.inr c)
    (hfire : S'.apply (Move.pileStack c) = some T₁) :
    ∃ S₁, S.apply (Move.pileStack c) = some S₁ ∧ TwinReplayTrace t β S₁ T₁ := by
  obtain ⟨hβA, hβB, hcells, hbotβ, hseatt, hbofs, hdeal, hdep, hstock, hhβ, hhh,
    hds⟩ := hdp
  rw [apply_pileStack_iff] at hfire
  obtain ⟨htop', b₀, hbot', hrk', rfl⟩ := hfire
  have hct : c ≠ t := fun h => hsu (congrArg Card.suit h)
  have hbotS : S.board.bottomOf c = some b₀ := by
    rw [hbofs c hct]; exact hbot'
  have hb₀β : b₀ ≠ β := by
    intro hcon
    rw [hcon] at hbotS
    have hthis := (Board.bottomOf_eq S.board c β).mp hbotS
    rw [hβA] at hthis
    exact absurd (Option.some.inj hthis) (fun hcc => hct hcc.symm)
  have hb₀t : b₀ ≠ Sum.inr t := by
    intro hcon
    rw [hcon] at hbotS
    rw [(Board.bottomOf_eq S.board c (Sum.inr t)).mp hbotS] at hseatt
    exact absurd hseatt (by simp)
  let swit : State := { S with board := S.board.detach b₀, heights := fun s => if s = c.suit then S.heights s + 1 else S.heights s }
  refine ⟨swit, ?_, ?_⟩
  · rw [apply_pileStack_iff]
    refine ⟨?_, b₀, hbotS, ?_, rfl⟩
    · rw [hcells (Sum.inr c) (Ne.symm hseat)]; exact htop'
    · rw [hrk', hhh c.suit hsu]
  · have hcells' : ∀ x, x ≠ β →
        (S.board.detach b₀).topOf x = (S'.board.detach b₀).topOf x := by
      intro x hx
      by_cases hxb₀ : x = b₀
      · rw [hxb₀, Board.detach_topOf, Board.detach_topOf]
      · rw [Board.detach_topOf_ne _ _ _ hxb₀, Board.detach_topOf_ne _ _ _ hxb₀]
        exact hcells x hx
    have hβA' : (S.board.detach b₀).topOf β = some t := by
      rw [Board.detach_topOf_ne _ _ _ (Ne.symm hb₀β)]; exact hβA
    have hβB' : (S'.board.detach b₀).topOf β = none := by
      rw [Board.detach_topOf_ne _ _ _ (Ne.symm hb₀β)]; exact hβB
    refine ⟨hβA', hβB', hcells', ?_, ?_, ?_, hdeal, hdep, hstock, ?_, ?_, hds⟩
    · exact (Board.bottomOf_eq _ _ β).mpr hβA'
    · show (S.board.detach b₀).topOf (Sum.inr t) = none
      rw [Board.detach_topOf_ne _ _ _ (Ne.symm hb₀t)]
      exact hseatt
    · exact fun c' hc' => bottomOf_cell_transfer hc' hβA' hβB' hcells'
    · show (if t.suit = c.suit then S'.heights t.suit + 1 else S'.heights t.suit)
          = (if t.suit = c.suit then S.heights t.suit + 1 else S.heights t.suit) + 1
      rw [ite_eq_right (fun h => hsu h.symm),
        ite_eq_right (fun h => hsu h.symm)]
      exact hhβ
    · intro s hs
      show (if s = c.suit then S.heights s + 1 else S.heights s)
          = (if s = c.suit then S'.heights s + 1 else S'.heights s)
      by_cases hsc : s = c.suit
      · rw [ite_eq_left hsc, ite_eq_left hsc, hhh s hs]
      · rw [ite_eq_right hsc, ite_eq_right hsc]
        exact hhh s hs

/-- The `deckPile` transfer: the landing cell is off `β` and off the
twin's seat (the no-landing premise), the waste top cannot be the
twin itself (visible at A, off the stock cycle by WF). -/
private theorem mid_access_deckPile {t : Card} {β : Base} {S S' T₁ : State}
    {X : Card} {b : Base}
    (hwf : S.WF)
    (hdp : TwinReplayTrace t β S S')
    (hseatβ : b ≠ β) (hseatt : b ≠ Sum.inr t)
    (hfire : S'.apply (Move.deckPile X b) = some T₁) :
    ∃ S₁, S.apply (Move.deckPile X b) = some S₁ ∧ TwinReplayTrace t β S₁ T₁ := by
  obtain ⟨hβA, hβB, hcells, hbotβT, hseatT, hbofs, hdeal, hdep, hstock, hhβ, hhh,
    hds⟩ := hdp
  rw [apply_deckPile_iff] at hfire
  obtain ⟨hprev, hcp', bd', hatt', rfl⟩ := hfire
  have hXt : X ≠ t := by
    intro hcon
    have hxs : t ∈ S.stock.cards := by
      rw [← hcon, hstock]
      exact Cycle.prev_mem hprev
    have hvt : S.isVis t = true := by
      show (S.board.bottomOf t).isSome = true
      rw [hbotβT]; rfl
    have hpos : S.stock.posOf t = none := hwf.vis_off_cycle t hvt
    exact absurd (Cycle.posOf_ne_none_of_mem hxs) (by rw [hpos]; simp)
  have hbx : S.board.bottomOf X = none := by
    rw [hbofs X hXt]
    exact ((Board.attach_eq_some_iff _ _ _).mp (by rw [hatt']; simp)).2
  have htopb : S.board.topOf b = none := by
    rw [hcells b hseatβ]; exact topOf_of_canPlace hcp'
  obtain ⟨bdA, hattA⟩ := Option.ne_none_iff_exists'.mp
    ((Board.attach_eq_some_iff _ _ _).mpr ⟨htopb, hbx⟩)
  let swit : State := { S with board := bdA, stock := S.stock.removeAt (S.stock.cursor - 1) }
  refine ⟨swit, ?_, ?_⟩
  · rw [apply_deckPile_iff]
    refine ⟨?_, ?_, bdA, hattA, rfl⟩
    · rw [hstock]; exact hprev
    · cases b with
      | inl a =>
          have htopb' : S.board.topOf (Sum.inl a) = none := htopb
          exact (canPlace_inl_iff).mpr
            ⟨htopb', ((canPlace_inl_iff).mp hcp').2⟩
      | inr d =>
          have hd : d ≠ t := by
            intro hcon; exact hseatt (congrArg Sum.inr hcon)
          have hvisA : S.isVis d = true := by
            show (S.board.bottomOf d).isSome = true
            rw [hbofs d hd]
            exact ((canPlace_inr_iff).mp hcp').2.1
          exact (canPlace_inr_iff).mpr
            ⟨htopb, hvisA, ((canPlace_inr_iff).mp hcp').2.2⟩
  · have hcells' : ∀ x, x ≠ β → bdA.topOf x = bd'.topOf x := by
      intro x hx
      by_cases hxb : x = b
      · rw [hxb, Board.attach_topOf _ _ _ hattA, Board.attach_topOf _ _ _ hatt']
      · rw [Board.attach_topOf_ne _ _ _ hattA hxb, Board.attach_topOf_ne _ _ _ hatt' hxb]
        exact hcells x hx
    have hβA' : bdA.topOf β = some t := by
      rw [Board.attach_topOf_ne _ _ _ hattA (Ne.symm hseatβ)]; exact hβA
    have hβB' : bd'.topOf β = none := by
      rw [Board.attach_topOf_ne _ _ _ hatt' (Ne.symm hseatβ)]; exact hβB
    refine ⟨hβA', hβB', hcells', ?_, ?_, ?_, hdeal, hdep, ?_, hhβ, hhh, hds⟩
    · exact (Board.bottomOf_eq _ _ β).mpr hβA'
    · rw [Board.attach_topOf_ne _ _ _ hattA (Ne.symm hseatt)]; exact hseatT
    · exact fun c' hc' => bottomOf_cell_transfer hc' hβA' hβB' hcells'
    · show S.stock.removeAt (S.stock.cursor - 1)
          = S'.stock.removeAt (S'.stock.cursor - 1)
      rw [hstock]

/-- The `stackPile` transfer (the low-suit worry-back): the un-stack
rung reads the moved card's suit (off the twin's), the landing cell
is off `β` and the twin's seat. -/
private theorem mid_access_stackPile {t : Card} {β : Base} {S S' T₁ : State}
    {c : Card} {b : Base}
    (hdp : TwinReplayTrace t β S S')
    (hsu : c.suit ≠ t.suit)
    (hseatβ : b ≠ β) (hseatt : b ≠ Sum.inr t)
    (hfire : S'.apply (Move.stackPile c b) = some T₁) :
    ∃ S₁, S.apply (Move.stackPile c b) = some S₁ ∧ TwinReplayTrace t β S₁ T₁ := by
  obtain ⟨hβA, hβB, hcells, hbotβT, hseatT, hbofs, hdeal, hdep, hstock, hhβ, hhh,
    hds⟩ := hdp
  rw [apply_stackPile_iff] at hfire
  obtain ⟨hrk', hcp', bd', hatt', rfl⟩ := hfire
  have hct : c ≠ t := fun h => hsu (congrArg Card.suit h)
  have hbc : S.board.bottomOf c = none := by
    rw [hbofs c hct]
    exact ((Board.attach_eq_some_iff _ _ _).mp (by rw [hatt']; simp)).2
  have htopb : S.board.topOf b = none := by
    rw [hcells b hseatβ]; exact topOf_of_canPlace hcp'
  obtain ⟨bdA, hattA⟩ := Option.ne_none_iff_exists'.mp
    ((Board.attach_eq_some_iff _ _ _).mpr ⟨htopb, hbc⟩)
  let swit : State := { S with board := bdA, heights := fun s => if s = c.suit then S.heights s - 1 else S.heights s }
  refine ⟨swit, ?_, ?_⟩
  · rw [apply_stackPile_iff]
    refine ⟨?_, ?_, bdA, hattA, rfl⟩
    · rw [hrk', hhh c.suit hsu]
    · cases b with
      | inl a =>
          exact (canPlace_inl_iff).mpr
            ⟨htopb, ((canPlace_inl_iff).mp hcp').2⟩
      | inr d =>
          have hd : d ≠ t := by
            intro hcon; exact hseatt (congrArg Sum.inr hcon)
          have hvisA : S.isVis d = true := by
            show (S.board.bottomOf d).isSome = true
            rw [hbofs d hd]
            exact ((canPlace_inr_iff).mp hcp').2.1
          exact (canPlace_inr_iff).mpr
            ⟨htopb, hvisA, ((canPlace_inr_iff).mp hcp').2.2⟩
  · have hcells' : ∀ x, x ≠ β → bdA.topOf x = bd'.topOf x := by
      intro x hx
      by_cases hxb : x = b
      · rw [hxb, Board.attach_topOf _ _ _ hattA, Board.attach_topOf _ _ _ hatt']
      · rw [Board.attach_topOf_ne _ _ _ hattA hxb, Board.attach_topOf_ne _ _ _ hatt' hxb]
        exact hcells x hx
    have hβA' : bdA.topOf β = some t := by
      rw [Board.attach_topOf_ne _ _ _ hattA (Ne.symm hseatβ)]; exact hβA
    have hβB' : bd'.topOf β = none := by
      rw [Board.attach_topOf_ne _ _ _ hatt' (Ne.symm hseatβ)]; exact hβB
    refine ⟨hβA', hβB', hcells', ?_, ?_, ?_, hdeal, hdep, hstock, ?_, ?_, hds⟩
    · exact (Board.bottomOf_eq _ _ β).mpr hβA'
    · rw [Board.attach_topOf_ne _ _ _ hattA (Ne.symm hseatt)]; exact hseatT
    · exact fun c' hc' => bottomOf_cell_transfer hc' hβA' hβB' hcells'
    · show (if t.suit = c.suit then S'.heights t.suit - 1 else S'.heights t.suit)
          = (if t.suit = c.suit then S.heights t.suit - 1 else S.heights t.suit) + 1
      rw [ite_eq_right (fun h => hsu h.symm),
        ite_eq_right (fun h => hsu h.symm)]
      exact hhβ
    · intro s hs
      show (if s = c.suit then S.heights s - 1 else S.heights s)
          = (if s = c.suit then S'.heights s - 1 else S'.heights s)
      by_cases hsc : s = c.suit
      · rw [ite_eq_left hsc, ite_eq_left hsc, hhh s hs]
      · rw [ite_eq_right hsc, ite_eq_right hsc]
        exact hhh s hs

/-- The `reveal` transfer: the boundary card and the attach cell are
the same deal data on both sides (deal/depths are in the delta), so
only the two board cells matter — the boundary's own seat and the
`hiddenBase` cell — both excluded by the repaired premise. -/
private theorem mid_access_reveal {t : Card} {β : Base} {S S' T₁ : State}
    {a : Anchor}
    (hwf : S.WF)
    (hdp : TwinReplayTrace t β S S')
    (hseatR : ∀ r, S.topHidden a = some r → β ≠ Sum.inr r)
    (hseatB : β ≠ S.hiddenBase a)
    (hfire : S'.apply (Move.reveal a) = some T₁) :
    ∃ S₁, S.apply (Move.reveal a) = some S₁ ∧ TwinReplayTrace t β S₁ T₁ := by
  obtain ⟨hβA, hβB, hcells, hbotβT, hseatT, hbofs, hdeal, hdep, hstock, hhβ, hhh,
    hds⟩ := hdp
  rw [apply_reveal_iff] at hfire
  obtain ⟨r, bd', htopH', hbare', hatt', rfl⟩ := hfire
  have hTH : S.topHidden a = S'.topHidden a := by
    show ((S.deal.piles a).take (S.depths a)).getLast?
      = ((S'.deal.piles a).take (S'.depths a)).getLast?
    rw [hdeal, hdep]
  have htopH : S.topHidden a = some r := by rw [hTH]; exact htopH'
  have hβr : β ≠ Sum.inr r := hseatR r htopH
  have hrs : r ≠ t := by
    intro hcon
    have hvt : S.isVis t = true := by
      show (S.board.bottomOf t).isSome = true
      rw [hbotβT]; rfl
    rw [hcon] at htopH
    exact hwf.vis_not_hidden t hvt a (mem_of_getLast htopH)
  have hfreeR : S.board.topOf (Sum.inr r) = none := by
    rw [hcells (Sum.inr r) (Ne.symm hβr)]; exact hbare'
  have hhid : S.hidden a = S'.hidden a := by
    show (S.deal.piles a).take (S.depths a) = (S'.deal.piles a).take (S'.depths a)
    rw [hdeal, hdep]
  have hbase : S.hiddenBase a = S'.hiddenBase a := by
    unfold State.hiddenBase
    rw [hhid]
  have hguardB := (Board.attach_eq_some_iff _ _ _).mp (by rw [hatt']; simp)
  have hfreeB : S.board.topOf (S.hiddenBase a) = none := by
    rw [hcells (S.hiddenBase a) (Ne.symm hseatB), hbase]
    exact hguardB.1
  have hnewR : S.board.bottomOf r = none := by
    rw [hbofs r hrs]; exact hguardB.2
  obtain ⟨bdA, hattA⟩ := Option.ne_none_iff_exists'.mp
    ((Board.attach_eq_some_iff _ _ _).mpr ⟨hfreeB, hnewR⟩)
  let swit : State := { S with board := bdA, depths := fun a' => if a' = a then S.depths a - 1 else S.depths a' }
  refine ⟨swit, ?_, ?_⟩
  · rw [apply_reveal_iff]
    exact ⟨r, bdA, htopH, hfreeR, hattA, rfl⟩
  · have hbaseT : S.hiddenBase a ≠ Sum.inr t := by
      intro hcon
      rcases hiddenBase_cases (st := S) a with hbase | ⟨d, hbase, hd⟩
      · rw [hbase] at hcon; exact absurd hcon (by simp)
      · rw [hbase] at hcon
        have hdt : d ≠ t := by
          intro hcd
          have hvt : S.isVis t = true := by
            show (S.board.bottomOf t).isSome = true
            rw [hbotβT]; rfl
          have hmem : t ∈ S.hidden a := by rw [← hcd]; exact hd
          exact hwf.vis_not_hidden t hvt a hmem
        exact absurd (Sum.inr.inj hcon) hdt
    have hcells' : ∀ x, x ≠ β → bdA.topOf x = bd'.topOf x := by
      intro x hx
      by_cases hxb : x = S.hiddenBase a
      · rw [hxb, Board.attach_topOf _ _ _ hattA, hbase, Board.attach_topOf _ _ _ hatt']
      · rw [Board.attach_topOf_ne _ _ _ hattA hxb, Board.attach_topOf_ne _ _ _ hatt' (fun h' => hxb (by rw [hbase]; exact h'))]
        exact hcells x hx
    have hβA' : bdA.topOf β = some t := by
      rw [Board.attach_topOf_ne _ _ _ hattA hseatB]
      exact hβA
    have hβB' : bd'.topOf β = none := by
      rw [Board.attach_topOf_ne _ _ _ hatt' (fun h' => hseatB (by rw [hbase]; exact h'))]
      exact hβB
    refine ⟨hβA', hβB', hcells', ?_, ?_, ?_, hdeal, ?_, hstock, hhβ, hhh, hds⟩
    · exact (Board.bottomOf_eq _ _ β).mpr hβA'
    · rw [Board.attach_topOf_ne _ _ _ hattA (Ne.symm hbaseT)]
      exact hseatT
    · exact fun c' hc' => bottomOf_cell_transfer hc' hβA' hβB' hcells'
    · funext a'
      show (if a' = a then S.depths a - 1 else S.depths a')
          = (if a' = a then S'.depths a - 1 else S'.depths a')
      rw [hdep]

/-- The `pilePile` transfer: the run head cannot be the twin (the
fired side does not have it), the detach cell is the run head's own
holder, and the self-landing guard transfers through the walk delta
(the A-side run gains at most the twin as its head — `aboveOf_twin_delta`). -/
private theorem mid_access_pilePile {t : Card} {β : Base} {S S' T₁ : State}
    {z : Card} {b : Base}
    (hdp : TwinReplayTrace t β S S')
    (hseatβ : b ≠ β) (hseatt : b ≠ Sum.inr t)
    (hfire : S'.apply (Move.pilePile z b) = some T₁) :
    ∃ S₁, S.apply (Move.pilePile z b) = some S₁ ∧ TwinReplayTrace t β S₁ T₁ := by
  have hdp2 : TwinReplayTrace t β S S' := hdp
  obtain ⟨hβA, hβB, hcells, hbotβT, hseatT, hbofs, hdeal, hdep, hstock, hhβ, hhh,
    hds⟩ := hdp
  rw [apply_pilePile_iff] at hfire
  obtain ⟨b₀, hbot', hne', hcmr', bd', hatt', rfl⟩ := hfire
  have hzt : z ≠ t := by
    intro hcon
    have hnone : S'.board.bottomOf t = none := by
      refine (Board.bottomOf_eq_none _ _).mpr (fun x hx => ?_)
      by_cases hxb : x = β
      · rw [hxb, hβB] at hx; exact absurd hx (by simp)
      · rw [← hcells x hxb] at hx
        have hbx2 : S.board.bottomOf t = some x := (Board.bottomOf_eq _ _ _).mpr hx
        rw [hbotβT] at hbx2
        exact absurd (Option.some.inj hbx2).symm hxb
    rw [hcon, hnone] at hbot'
    exact absurd hbot' (by simp)
  have hbotS : S.board.bottomOf z = some b₀ := by
    rw [hbofs z hzt]; exact hbot'
  have hb₀β : b₀ ≠ β := by
    intro hcon
    rw [hcon] at hbotS
    have hthis := (Board.bottomOf_eq S.board z β).mp hbotS
    rw [hβA] at hthis
    exact absurd (Option.some.inj hthis) (fun hcc => hzt hcc.symm)
  have hb₀t : b₀ ≠ Sum.inr t := by
    intro hcon
    rw [hcon] at hbotS
    rw [(Board.bottomOf_eq S.board z (Sum.inr t)).mp hbotS] at hseatT
    exact absurd hseatT (by simp)
  -- the B-side landing data, split per base kind
  have hfreeb : S.board.topOf b = none := by
    rw [hcells b hseatβ]
    cases b with
    | inl a => exact topOf_of_canPlace ((canMoveRun_inl_iff).mp hcmr')
    | inr d => exact topOf_of_canPlace (((canMoveRun_inr_iff).mp hcmr').1)
  have hcpA : S.canPlace z b = true := by
    cases b with
    | inl a =>
        exact (canPlace_inl_iff).mpr
          ⟨hfreeb, ((canPlace_inl_iff).mp
            ((canMoveRun_inl_iff).mp hcmr')).2⟩
    | inr d =>
        have hd : d ≠ t := by
          intro hcon; exact hseatt (congrArg Sum.inr hcon)
        have hBcp : S'.canPlace z (Sum.inr d) = true :=
          ((canMoveRun_inr_iff).mp hcmr').1
        have hvisA : S.isVis d = true := by
          show (S.board.bottomOf d).isSome = true
          rw [hbofs d hd]
          exact ((canPlace_inr_iff).mp hBcp).2.1
        exact (canPlace_inr_iff).mpr
          ⟨hfreeb, hvisA, ((canPlace_inr_iff).mp hBcp).2.2⟩
  have hselfA : S.canMoveRun z b = true := by
    cases b with
    | inl a => exact (canMoveRun_inl_iff).mpr hcpA
    | inr d =>
        have hBcp : S'.canPlace z (Sum.inr d) = true :=
          ((canMoveRun_inr_iff).mp hcmr').1
        have hBnot : (S'.board.aboveOf z).contains d = false :=
          ((canMoveRun_inr_iff).mp hcmr').2
        have hnot : (S.board.aboveOf z).contains d = false := by
          rcases aboveOf_twin_delta hdp2 z with h | h
          · rw [h]; exact hBnot
          · rw [h]
            by_cases hdt : d = t
            · exact absurd (congrArg Sum.inr hdt) hseatt
            · show (t :: S'.board.aboveOf z).contains d = false
              have hmemB : d ∉ S'.board.aboveOf z := by
                intro dm
                rw [(List.contains_iff_mem).mpr dm] at hBnot
                exact Bool.noConfusion hBnot
              have hmem : d ∉ t :: S'.board.aboveOf z := by
                intro dm
                rcases List.mem_cons.mp dm with rfl | dm
                · exact hdt rfl
                · exact hmemB dm
              by_cases hhc : (t :: S'.board.aboveOf z).contains d = true
              · exact absurd ((List.contains_iff_mem).mp hhc) hmem
              · cases hhv : (t :: S'.board.aboveOf z).contains d with
                | false => rfl
                | true => exact absurd hhv hhc
        exact (canMoveRun_inr_iff).mpr ⟨hcpA, hnot⟩
  have hfreeA : (S.board.detach b₀).topOf b = none := by
    rw [Board.detach_topOf_ne _ _ _ (Ne.symm hne')]
    exact hfreeb
  have hnewz : (S.board.detach b₀).bottomOf z = none := by
    refine (Board.bottomOf_eq_none _ _).mpr (fun x hx => ?_)
    by_cases hxb : x = b₀
    · rw [hxb, Board.detach_topOf] at hx; exact absurd hx (by simp)
    · rw [Board.detach_topOf_ne _ _ _ hxb] at hx
      have hbxA : S.board.bottomOf z = some x := (Board.bottomOf_eq _ _ x).mpr hx
      rw [hbotS] at hbxA
      exact absurd (Option.some.inj hbxA) (Ne.symm hxb)
  obtain ⟨bdA, hattA⟩ := Option.ne_none_iff_exists'.mp
    ((Board.attach_eq_some_iff _ _ _).mpr ⟨hfreeA, hnewz⟩)
  let swit : State := { S with board := bdA }
  refine ⟨swit, ?_, ?_⟩
  · exact apply_pilePile_iff.mpr ⟨b₀, hbotS, hne', hselfA, bdA, hattA, rfl⟩
  · have hdetβA : (S.board.detach b₀).topOf β = some t := by
      rw [Board.detach_topOf_ne _ _ _ (Ne.symm hb₀β)]; exact hβA
    have hdetβB : (S'.board.detach b₀).topOf β = none := by
      rw [Board.detach_topOf_ne _ _ _ (Ne.symm hb₀β)]; exact hβB
    have hcells' : ∀ x, x ≠ β → bdA.topOf x = bd'.topOf x := by
      intro x hx
      by_cases hxb : x = b
      · rw [hxb, Board.attach_topOf _ _ _ hattA, Board.attach_topOf _ _ _ hatt']
      · rw [Board.attach_topOf_ne _ _ _ hattA hxb, Board.attach_topOf_ne _ _ _ hatt' hxb]
        by_cases hxb₀ : x = b₀
        · rw [hxb₀, Board.detach_topOf, Board.detach_topOf]
        · rw [Board.detach_topOf_ne _ _ _ hxb₀, Board.detach_topOf_ne _ _ _ hxb₀]
          exact hcells x hx
    have hβA' : bdA.topOf β = some t := by
      rw [Board.attach_topOf_ne _ _ _ hattA (Ne.symm hseatβ)]
      exact hdetβA
    have hβB' : bd'.topOf β = none := by
      rw [Board.attach_topOf_ne _ _ _ hatt' (Ne.symm hseatβ)]
      exact hdetβB
    refine ⟨hβA', hβB', hcells', ?_, ?_, ?_, hdeal, hdep, hstock, hhβ, hhh, hds⟩
    · exact (Board.bottomOf_eq _ _ β).mpr hβA'
    · rw [Board.attach_topOf_ne _ _ _ hattA (Ne.symm hseatt),
        Board.detach_topOf_ne _ _ _ (Ne.symm hb₀t)]
      exact hseatT
    · exact fun c' hc' => bottomOf_cell_transfer hc' hβA' hβB' hcells'

/-! ### The replay chain and the repaired reduction

The per-kind transfers assemble by induction on the mid: the whole
mid runs on the A-side of the pair, and the A-side t-suit rung — the
`twinMid` gate excludes every t-suit foundation move, so no replay
step touches it — is exactly the fired twin's own rung, so the
deferred firing at the replay's end lands on the source's `C` itself. -/

private theorem mid_access_chain {t : Card} {β : Base} {A : State} :
    ∀ (mid : List Move) (S S' C : State),
    (∀ m ∈ mid, Move.twinMid t m = true) →
    TwinReplayTrace t β S S' →
    S.WF →
    S.deal = A.deal →
    (∀ a, S.depths a ≤ A.depths a) →
    S.heights t.suit = A.heights t.suit →
    (∀ m ∈ mid, ∀ b : Base,
      (match m with
       | .deckPile _ b' => b = b'
       | .stackPile _ b' => b = b'
       | .pilePile _ b' => b = b'
       | .pileStack c' => b = Sum.inr c'
       | .reveal a' => b = Sum.inl a' ∨ b = A.hiddenBase a' ∨
           (∃ r, r ∈ A.hidden a' ∧ b = Sum.inr r)
       | _ => False) →
      b ≠ β ∧ b ≠ Sum.inr t) →
    S'.run mid = some C →
    ∃ M₀, S.run mid = some M₀ ∧ TwinReplayTrace t β M₀ C ∧
      M₀.heights t.suit = A.heights t.suit := by
  intro mid
  induction mid with
  | nil =>
      intro S S' C _ hdp _ _ _ hrk _ hrun
      obtain rfl := run_nil_elim hrun
      exact ⟨S, rfl, hdp, hrk⟩
  | cons m ms ih =>
      intro S S' C hmid hdp hwf hdeal hdep hrk hno hrun
      obtain ⟨S'₁, hmB, hrest⟩ := run_cons_elim hrun
      cases m with
      | draw =>
          obtain ⟨S₁, hmA, hdp₁⟩ := mid_access_draw hdp hmB
          obtain ⟨M₀, hMs, hpack₂, hrk₂⟩ :=
            ih S₁ S'₁ C (fun m' hm' => hmid m' (List.mem_cons_of_mem _ hm'))
              hdp₁ (apply_wf hwf Move.draw S₁ hmA)
              ((deal_stable_move hmA).symm.trans hdeal)
              (fun a => Nat.le_trans (depths_mono_move hmA a) (hdep a))
              ((heights_tSuit_stable (hmid Move.draw List.mem_cons_self) hmA).trans hrk)
              (fun m' hm' => hno m' (List.mem_cons_of_mem _ hm')) hrest
          refine ⟨M₀, ?_, hpack₂, hrk₂⟩
          show (match S.apply Move.draw with
            | some st' => st'.run ms
            | none => none) = some M₀
          rw [hmA]; exact hMs
      | deckStack x =>
          obtain ⟨S₁, hmA, hdp₁⟩ := mid_access_deckStack hdp
            ((Move.twinMid_deckStack t x).mp (hmid (Move.deckStack x)
              List.mem_cons_self)).1 hmB
          obtain ⟨M₀, hMs, hpack₂, hrk₂⟩ :=
            ih S₁ S'₁ C (fun m' hm' => hmid m' (List.mem_cons_of_mem _ hm'))
              hdp₁ (apply_wf hwf (Move.deckStack x) S₁ hmA)
              ((deal_stable_move hmA).symm.trans hdeal)
              (fun a => Nat.le_trans (depths_mono_move hmA a) (hdep a))
              ((heights_tSuit_stable (hmid (Move.deckStack x) List.mem_cons_self)
                hmA).trans hrk)
              (fun m' hm' => hno m' (List.mem_cons_of_mem _ hm')) hrest
          refine ⟨M₀, ?_, hpack₂, hrk₂⟩
          show (match S.apply (Move.deckStack x) with
            | some st' => st'.run ms
            | none => none) = some M₀
          rw [hmA]; exact hMs
      | pileStack x =>
          obtain ⟨S₁, hmA, hdp₁⟩ := mid_access_pileStack hdp
            ((Move.twinMid_pileStack t x).mp (hmid (Move.pileStack x)
              List.mem_cons_self)).1
            (Ne.symm (hno (Move.pileStack x) List.mem_cons_self (Sum.inr x) rfl).1)
            hmB
          obtain ⟨M₀, hMs, hpack₂, hrk₂⟩ :=
            ih S₁ S'₁ C (fun m' hm' => hmid m' (List.mem_cons_of_mem _ hm'))
              hdp₁ (apply_wf hwf (Move.pileStack x) S₁ hmA)
              ((deal_stable_move hmA).symm.trans hdeal)
              (fun a => Nat.le_trans (depths_mono_move hmA a) (hdep a))
              ((heights_tSuit_stable (hmid (Move.pileStack x) List.mem_cons_self)
                hmA).trans hrk)
              (fun m' hm' => hno m' (List.mem_cons_of_mem _ hm')) hrest
          refine ⟨M₀, ?_, hpack₂, hrk₂⟩
          show (match S.apply (Move.pileStack x) with
            | some st' => st'.run ms
            | none => none) = some M₀
          rw [hmA]; exact hMs
      | deckPile x b' =>
          obtain ⟨S₁, hmA, hdp₁⟩ := mid_access_deckPile hwf hdp
            (hno (Move.deckPile x b') List.mem_cons_self b' rfl).1
            (hno (Move.deckPile x b') List.mem_cons_self b' rfl).2 hmB
          obtain ⟨M₀, hMs, hpack₂, hrk₂⟩ :=
            ih S₁ S'₁ C (fun m' hm' => hmid m' (List.mem_cons_of_mem _ hm'))
              hdp₁ (apply_wf hwf (Move.deckPile x b') S₁ hmA)
              ((deal_stable_move hmA).symm.trans hdeal)
              (fun a => Nat.le_trans (depths_mono_move hmA a) (hdep a))
              ((heights_tSuit_stable (hmid (Move.deckPile x b') List.mem_cons_self)
                hmA).trans hrk)
              (fun m' hm' => hno m' (List.mem_cons_of_mem _ hm')) hrest
          refine ⟨M₀, ?_, hpack₂, hrk₂⟩
          show (match S.apply (Move.deckPile x b') with
            | some st' => st'.run ms
            | none => none) = some M₀
          rw [hmA]; exact hMs
      | stackPile x b' =>
          obtain ⟨S₁, hmA, hdp₁⟩ := mid_access_stackPile hdp
            ((Move.twinMid_stackPile t x b').mp (hmid (Move.stackPile x b')
              List.mem_cons_self)).1
            (hno (Move.stackPile x b') List.mem_cons_self b' rfl).1
            (hno (Move.stackPile x b') List.mem_cons_self b' rfl).2 hmB
          obtain ⟨M₀, hMs, hpack₂, hrk₂⟩ :=
            ih S₁ S'₁ C (fun m' hm' => hmid m' (List.mem_cons_of_mem _ hm'))
              hdp₁ (apply_wf hwf (Move.stackPile x b') S₁ hmA)
              ((deal_stable_move hmA).symm.trans hdeal)
              (fun a => Nat.le_trans (depths_mono_move hmA a) (hdep a))
              ((heights_tSuit_stable (hmid (Move.stackPile x b') List.mem_cons_self)
                hmA).trans hrk)
              (fun m' hm' => hno m' (List.mem_cons_of_mem _ hm')) hrest
          refine ⟨M₀, ?_, hpack₂, hrk₂⟩
          show (match S.apply (Move.stackPile x b') with
            | some st' => st'.run ms
            | none => none) = some M₀
          rw [hmA]; exact hMs
      | pilePile x b' =>
          obtain ⟨S₁, hmA, hdp₁⟩ := mid_access_pilePile hdp
            (hno (Move.pilePile x b') List.mem_cons_self b' rfl).1
            (hno (Move.pilePile x b') List.mem_cons_self b' rfl).2 hmB
          obtain ⟨M₀, hMs, hpack₂, hrk₂⟩ :=
            ih S₁ S'₁ C (fun m' hm' => hmid m' (List.mem_cons_of_mem _ hm'))
              hdp₁ (apply_wf hwf (Move.pilePile x b') S₁ hmA)
              ((deal_stable_move hmA).symm.trans hdeal)
              (fun a => Nat.le_trans (depths_mono_move hmA a) (hdep a))
              ((heights_tSuit_stable (hmid (Move.pilePile x b') List.mem_cons_self)
                hmA).trans hrk)
              (fun m' hm' => hno m' (List.mem_cons_of_mem _ hm')) hrest
          refine ⟨M₀, ?_, hpack₂, hrk₂⟩
          show (match S.apply (Move.pilePile x b') with
            | some st' => st'.run ms
            | none => none) = some M₀
          rw [hmA]; exact hMs
      | reveal a =>
          have hseatR : ∀ r, S.topHidden a = some r → β ≠ Sum.inr r := by
            intro r hr
            have hrS : r ∈ S.hidden a := mem_of_getLast hr
            have hrA : r ∈ A.hidden a := hidden_sub_of_deal hdeal (hdep a) hrS
            exact Ne.symm (hno (Move.reveal a) List.mem_cons_self (Sum.inr r)
              (Or.inr (Or.inr ⟨r, hrA, rfl⟩))).1
          have hseatB : β ≠ S.hiddenBase a := by
            rcases hiddenBase_cases (st := S) a with hbase | ⟨d, hbase, hd⟩
            · rw [hbase]
              exact Ne.symm (hno (Move.reveal a) List.mem_cons_self (Sum.inl a)
                (Or.inl rfl)).1
            · have hdA : d ∈ A.hidden a := hidden_sub_of_deal hdeal (hdep a) hd
              rw [hbase]
              exact Ne.symm (hno (Move.reveal a) List.mem_cons_self (Sum.inr d)
                (Or.inr (Or.inr ⟨d, hdA, rfl⟩))).1
          obtain ⟨S₁, hmA, hdp₁⟩ := mid_access_reveal hwf hdp hseatR hseatB hmB
          obtain ⟨M₀, hMs, hpack₂, hrk₂⟩ :=
            ih S₁ S'₁ C (fun m' hm' => hmid m' (List.mem_cons_of_mem _ hm'))
              hdp₁ (apply_wf hwf (Move.reveal a) S₁ hmA)
              ((deal_stable_move hmA).symm.trans hdeal)
              (fun a => Nat.le_trans (depths_mono_move hmA a) (hdep a))
              ((heights_tSuit_stable (hmid (Move.reveal a) List.mem_cons_self)
                hmA).trans hrk)
              (fun m' hm' => hno m' (List.mem_cons_of_mem _ hm')) hrest
          refine ⟨M₀, ?_, hpack₂, hrk₂⟩
          show (match S.apply (Move.reveal a) with
            | some st' => st'.run ms
            | none => none) = some M₀
          rw [hmA]; exact hMs

/-- **HACCESS DERIVED (the repaired reduction, PROVEN wave 20)**: at
WF, the source's own mid plus the per-seat exclusions derive the WHOLE
replay at the pre-firing state, and the deferred twin firing lands
exactly on the source's mid successor `C` — the model-side certificate
of §8's landing-site audit.  Drafted wave 19 (parked as
`attic/MidAccessDraft.lean`, never built), reinstated and elaborated
to green wave 20: the pair-states ride as `let`-bound structure
instances so each trace slot's literal projections reduce, and the
B→A mirrors assemble by the `mid_access_chain` induction holding the
deal/depths/t-rung frame invariant across the replay.

The `noSeat` premise is wave 19's REPAIRED form (the wave-18 pin was
false as stated; see the section note above): beyond the three
landing kinds it now excludes the `pileStack` seat cells — the twin
may sit ON a raise card (witness A's corner, live at WF through
`board_edges`' deal-adjacency clause) — and the reveal's boundary
structure: the pile's anchor, `A.hiddenBase a`, and the seats of all
of `A.hidden a`'s cards — the current AND every future
boundary/attach cell of that pile's reveal chain (reveal only
decrements the take; every later boundary stays inside the shrinking
prefix). -/
theorem State.mid_access_of_noSeat {st : State} {t : Card}
    {p₁ mid : List Move} {A B C : State} {β : Base}
    (hwf : st.WF)
    (hp₁ : st.run p₁ = some A)
    (hf₁ : A.apply (Move.pileStack t) = some B)
    (hβ : A.board.bottomOf t = some β)
    (hmid : ∀ m ∈ mid, Move.twinMid t m = true)
    (hBmid : B.run mid = some C)
    (hnoseat : ∀ m ∈ mid, ∀ b : Base,
      (match m with
       | .deckPile _ b' => b = b'
       | .stackPile _ b' => b = b'
       | .pilePile _ b' => b = b'
       | .pileStack c' => b = Sum.inr c'
       | .reveal a' => b = Sum.inl a' ∨ b = A.hiddenBase a' ∨
           (∃ r, r ∈ A.hidden a' ∧ b = Sum.inr r)
       | _ => False) →
      b ≠ β ∧ b ≠ Sum.inr t) :
    ∃ M₀, A.run mid = some M₀ ∧ M₀.apply (Move.pileStack t) = some C := by
  have hwfA : A.WF := run_wf p₁ st A hp₁ hwf
  have hpack := twinReplayTrace_of_firing hf₁ hβ
  rw [apply_pileStack_iff] at hf₁
  obtain ⟨-, b₁, -, hrkA, -⟩ := hf₁
  obtain ⟨M₀, hArun, hpack₂, hrkM⟩ :=
    mid_access_chain (A := A) mid A B C hmid hpack hwfA rfl (fun _ => Nat.le_refl _)
      rfl hnoseat hBmid
  obtain ⟨hβM, hβC, hcellsM, hbotβM, hseatM, hbofsM, hdealM, hdepM, hstockM,
    hhβM, hhhM, hdsM⟩ := hpack₂
  have hshC : { M₀ with board := M₀.board.detach β, heights := fun s => if s = t.suit then M₀.heights s + 1 else M₀.heights s } = C := by
    apply state_ext
    · exact hdealM
    · apply Board.ext_topOf
      funext x
      by_cases hxb : x = β
      · rw [hxb, Board.detach_topOf, hβC]
      · rw [Board.detach_topOf_ne _ _ _ hxb]
        exact hcellsM x hxb
    · funext s
      show (if s = t.suit then M₀.heights s + 1 else M₀.heights s) = C.heights s
      by_cases hs : s = t.suit
      · rw [ite_eq_left hs, hs]
        exact hhβM.symm
      · rw [ite_eq_right hs]
        exact hhhM s hs
    · exact hdepM
    · exact hstockM
    · exact hdsM
  refine ⟨M₀, hArun, ?_⟩
  rw [apply_pileStack_iff]
  exact ⟨hseatM, β, hbotβM, by rw [hrkM]; exact hrkA, hshC.symm⟩

/-! ## §6.5 residue — the covered-twin corner's sweep-word safety

At the ambiguous-twin corner (`canonicalize`'s confluence gap: both
twins visible, one covered, `present=2, placed=1`), the word-level
sweep must CHOOSE which twin is the covered one, and §6.5 pins the
semantic obligation: the chosen reading never uniquely loses wins.
The model-side corner at WF is the DEALT-ADJACENT mate — the twin
pair dealt consecutively in one pile, the upper mate sitting on the
lower's seat — because `canSitOn` is false at the mate's own rank
(same rank, unlike a fitting cover), so deal-adjacency is the only WF
justification for the cover edge.  The two word-readings of the
corner are exchange-conjugate: `exchangeTwinCargo L` swaps the two
twin cells (the raw seat relabel, `Board.exchangeTwin_topOf`), so the
covered corner maps to its flipped cover. -/

/-- The covered corner's exchange image IS the flipped cover: at the
ambiguous corner the cell readings of `st.exchangeTwinCargo L` are
the corner's cells with the twin pair exchanged — the two
identity-resolutions of the word are the two exchange-images.

Note the image's own-seat cell: the exchange is the RAW seat swap
(no card relabel on values), so the covering mate's VALUE rides to
its own seat — for the word level this is immaterial (the word reads
placedness, not identities), but it is why the SAFETY reduction
below must route through the discipline kit rather than a pure
literal symmetry. -/
theorem exchangeTwinCargo_flip_cover {st : State} {L H : Card}
    (htwin : H = L.flipSuit)
    (hcover : st.board.topOf (Sum.inr L) = some H)
    (hHseat : st.board.topOf (Sum.inr H) = none) :
    (st.exchangeTwinCargo L).board.topOf (Sum.inr L) = none ∧
    (st.exchangeTwinCargo L).board.topOf (Sum.inr H) = some H := by
  constructor
  · show st.board.topOf (Base.swapTwin L (Sum.inr L)) = none
    have h : Base.swapTwin L (Sum.inr L) = Sum.inr H := by
      show Sum.inr (Card.swapTwin L L) = Sum.inr H
      rw [Card.swapTwin_self_left, htwin]
    rw [h, hHseat]
  · show st.board.topOf (Base.swapTwin L (Sum.inr H)) = some H
    have h : Base.swapTwin L (Sum.inr H) = Sum.inr L := by
      show Sum.inr (Card.swapTwin L H) = Sum.inr L
      rw [show Card.swapTwin L H = L from by rw [htwin]; exact Card.swapTwin_self_right L]
    rw [h, hcover]

/-! ### The paid pieces (wave 20)

The safety's plan steps (1) and (2) land as free-standing theorems
ahead of the reduction itself, so the pin's residue is only the
assembly (3) and the license-fit (4). -/

/-- **The covered corner is deal-adjacent at WF (plan step (1), PAID)**:
the covering mate's cover edge can never be justified by the `canSitOn`
clause — its rank arithmetic (`toIdx H + 1 = toIdx L`) dies at the
twin's shared rank, regardless of the color conjunct — so WF's
`board_edges` must attribute the edge to the buried-base clause: the
pair was dealt consecutively, `L :: H` adjacent in some deal pile
(the plan's premise for every license-fit analysis: the mate is the
DEAL's neighbor, not a fitting cover). -/
theorem sweep_covered_corner_deal_adjacent {st : State} {L H : Card}
    (hwf : st.WF)
    (htwin : H = L.flipSuit)
    (hcover : st.board.topOf (Sum.inr L) = some H) :
    ∃ a t rest, st.deal.piles a = t ++ L :: H :: rest := by
  have hedge := hwf.board_edges (Sum.inr L) H hcover
  rcases hedge.2 with hbur | ⟨-, hfit⟩
  · obtain ⟨a, t, rest, hpiles, -⟩ := hbur
    exact ⟨a, t, rest, hpiles⟩
  · exfalso
    obtain ⟨hrk, -⟩ := (canSitOn_eq H L).mp hfit
    have hL : L.rank.toIdx = H.rank.toIdx := by
      rw [htwin, Card.flipSuit_rank]
    omega

/-- **A vacated covered cell forces the mate's own move (plan step
(2)'s keystone, PAID)**: if the covered seat `Sum.inr L` — held by the
covering mate `H` — reads EMPTY after a move, the move was the mate's
own departure: `pilePile H b` (the dodge aside) or `pileStack H` (the
direct foundationing).  The board-inert and attach-kind moves cannot
empty a cell (attach can only FILL a free one, and the covered cell is
occupied), and the detach-kind moves empty exactly the moved card's
own base — so for the covered cell THAT card IS the mate.  This is
the dislodge-shape audit the safety's normalization rides: a winning
line's first clearing of the covered seat is a MATE move. -/
theorem vacated_covered_cell_imp_mate_move {st s' : State} {m : Move} {L H : Card}
    (happly : st.apply m = some s')
    (hten : st.board.bottomOf H = some (Sum.inr L))
    (hvac : s'.board.topOf (Sum.inr L) = none) :
    ∃ b : Base, m = Move.pilePile H b ∨ m = Move.pileStack H := by
  have htop : st.board.topOf (Sum.inr L) = some H :=
    (Board.bottomOf_eq st.board H (Sum.inr L)).mp hten
  cases m with
  | draw =>
      rw [apply_draw_iff] at happly
      obtain rfl := happly
      have hcon : st.board.topOf (Sum.inr L) = none := hvac
      rw [htop] at hcon
      exact absurd hcon (by simp)
  | reveal a =>
      rw [apply_reveal_iff] at happly
      obtain ⟨r, bd, -, -, hatt, rfl⟩ := happly
      have hf : st.board.topOf (st.hiddenBase a) = none := attach_frees hatt
      by_cases hb : st.hiddenBase a = Sum.inr L
      · rw [hb] at hf
        rw [hf] at htop
        exact absurd htop (by simp)
      · have hcon : bd.topOf (Sum.inr L) = none := hvac
        rw [Board.attach_topOf_ne _ _ _ hatt (Ne.symm hb), htop] at hcon
        exact absurd hcon (by simp)
  | deckPile X b =>
      rw [apply_deckPile_iff] at happly
      obtain ⟨-, -, bd, hatt, rfl⟩ := happly
      have hf : st.board.topOf b = none := attach_frees hatt
      by_cases hb : b = Sum.inr L
      · rw [hb] at hf
        rw [hf] at htop
        exact absurd htop (by simp)
      · have hcon : bd.topOf (Sum.inr L) = none := hvac
        rw [Board.attach_topOf_ne _ _ _ hatt (Ne.symm hb), htop] at hcon
        exact absurd hcon (by simp)
  | deckStack c =>
      rw [apply_deckStack_iff] at happly
      obtain ⟨-, -, rfl⟩ := happly
      have hcon : st.board.topOf (Sum.inr L) = none := hvac
      rw [htop] at hcon
      exact absurd hcon (by simp)
  | pileStack c =>
      rw [apply_pileStack_iff] at happly
      obtain ⟨-, b₀, hb₁, -, rfl⟩ := happly
      by_cases hb : b₀ = Sum.inr L
      · have hcH : c = H := by
          have hc : st.board.topOf (Sum.inr L) = some c :=
            (Board.bottomOf_eq st.board c (Sum.inr L)).mp (by rw [← hb]; exact hb₁)
          rw [htop] at hc
          exact (Option.some.inj hc).symm
        subst hcH
        exact ⟨b₀, Or.inr rfl⟩
      · have hcon : (st.board.detach b₀).topOf (Sum.inr L) = none := hvac
        rw [Board.detach_topOf_ne _ _ _ (Ne.symm hb), htop] at hcon
        exact absurd hcon (by simp)
  | stackPile c b =>
      rw [apply_stackPile_iff] at happly
      obtain ⟨-, -, bd, hatt, rfl⟩ := happly
      have hf : st.board.topOf b = none := attach_frees hatt
      by_cases hb : b = Sum.inr L
      · rw [hb] at hf
        rw [hf] at htop
        exact absurd htop (by simp)
      · have hcon : bd.topOf (Sum.inr L) = none := hvac
        rw [Board.attach_topOf_ne _ _ _ hatt (Ne.symm hb), htop] at hcon
        exact absurd hcon (by simp)
  | pilePile c b =>
      rw [apply_pilePile_iff] at happly
      obtain ⟨b', hb', -, -, bd, hatt, rfl⟩ := happly
      by_cases hb : b' = Sum.inr L
      · have hcH : c = H := by
          have hc : st.board.topOf (Sum.inr L) = some c :=
            (Board.bottomOf_eq st.board c (Sum.inr L)).mp (by rw [← hb]; exact hb')
          rw [htop] at hc
          exact (Option.some.inj hc).symm
        subst hcH
        exact ⟨b, Or.inl rfl⟩
      · have hf : (st.board.detach b').topOf b = none := attach_frees hatt
        by_cases hbb : b = Sum.inr L
        · rw [hbb] at hf
          rw [Board.detach_topOf_ne _ _ _ (Ne.symm hb), htop] at hf
          exact absurd hf (by simp)
        · have hcon : bd.topOf (Sum.inr L) = none := hvac
          rw [Board.attach_topOf_ne _ _ _ hatt (Ne.symm hbb),
            Board.detach_topOf_ne _ _ _ (Ne.symm hb), htop] at hcon
          exact absurd hcon (by simp)

/-! ### The exchange-conjugation identities (wave 20)

The safety's reduction runs the covered corner and its exchange image
as TWO THREADS of one play, and the threads' shared engine is a small
kit of per-card conjugation identities for `exchangeTwinCargo`: the
visibility preservation (the swapped cells re-seat their occupants), and
the self-cover corner's run structure — in the exchange image the mate
sits only at its own cell, so the run above it is the one-step
self-cycle.  These are state-level facts, no WF consumed. -/

/-- A card never fits onto itself (the rank arithmetic of
`canSitOn` at the shared rung — the receiver of the antisymmetry law). -/
theorem canSitOn_self {c : Card} : canSitOn c c ≠ true := fun h =>
  canSitOn_antisymm h h

/-- The seat exchange preserves every card's VISIBILITY: `bottomOf`
commutes with the base swap (an `Option.map`), so a card is seated in
the image exactly when it was seated in the source. -/
theorem exchangeTwinCargo_isVis {S : State} {t d : Card} :
    (S.exchangeTwinCargo t).isVis d = S.isVis d := by
  show ((S.board.exchangeTwin t).bottomOf d).isSome = (S.board.bottomOf d).isSome
  rw [Board.bottomOf_exchangeTwin]
  cases S.board.bottomOf d with
  | none => rfl
  | some b => simp

/-- **In the exchange image the mate's own run is the self-cycle
alone**: the image's run above the mate `H` reads the mate at its own
cell (the raw seat swap put it there — the covered cell renames to
`Sum.inr H`), then stops on the accumulator check.  Consequence below:
no card other than `H` itself is ever IN the image's run above `H`, so
the self-landing guard of any `pilePile` onto the image's mate passes
whenever its host is not the mate. -/
theorem exchangeTwinCargo_aboveOf_mate_self {S : State} {L H : Card}
    (htwin : H = L.flipSuit)
    (hcover : S.board.topOf (Sum.inr L) = some H) :
    ((S.exchangeTwinCargo L).board.aboveOf H) = [H] := by
  have hread : (S.board.exchangeTwin L).topOf (Sum.inr H) = some H := by
    rw [Board.exchangeTwin_topOf]
    show S.board.topOf (Sum.inr (Card.swapTwin L H)) = some H
    rw [show Card.swapTwin L H = L from by rw [htwin]; exact Card.swapTwin_self_right L]
    exact hcover
  -- once the mate is in the accumulator, every further step stops
  have main : ∀ (n : Nat) (acc : List Card), acc.contains H = true →
      Board.aboveOf.go (S.board.exchangeTwin L) (n + 1) (Sum.inr H) acc = acc := by
    intro n acc hc
    rw [aboveOf_go_succ, hread]
    dsimp only
    rw [ite_eq_left hc]
  show Board.aboveOf.go (S.board.exchangeTwin L) (51 + 1) (Sum.inr H) ([] : List Card) = [H]
  rw [aboveOf_go_succ, hread]
  dsimp only
  rw [ite_eq_right (by simp)]
  exact main 50 [H] (by simp)

/-- The self-cover exclusion: a card fitting on the mate is never the
mate itself (the self-fit's rank arithmetic). -/
theorem canSitOn_ne_of_fits_mate {H d : Card}
    (hfit : canSitOn H d = true) : d ≠ H := by
  obtain ⟨hrk, -⟩ := (canSitOn_eq H d).mp hfit
  intro hcon
  rw [hcon] at hrk
  omega

/-! ### The run audits at the covered corner (wave 20)

Plan (2)'s remaining half: the §12.1 extraction at the corner (every
winning line STACKS the covered twin `L`), and the first-clearing audit
(the moment the covered cell `Sum.inr L` first reads `none` is the MATE's
own departure).  Both are consumed by the reduction below; both are
free-standing. -/

/-- **WF pins the covered twin to the tableau classes**: the cover edge
at `Sum.inr L` must be justified by `board_edges`, and its two clauses
put `L` in §12.1's classes — the buried-base clause's base condition
(`L` is some pile's hidden boundary, or `L` is itself placed), or the
fitting clause (which also demands `L` placed). -/
theorem sweep_covered_corner_L_tableau {st : State} {L H : Card}
    (hwf : st.WF) (htwin : H = L.flipSuit)
    (hcover : st.board.topOf (Sum.inr L) = some H) :
    st.isVis L = true ∨ ∃ a, L ∈ st.hidden a := by
  have hedge := hwf.board_edges (Sum.inr L) H hcover
  rcases hedge.2 with hbur | ⟨hplaced, hfit⟩
  · rcases hbur with ⟨a, t, rest, hpiles, hbase⟩
    rcases hbase with ⟨a', htop⟩ | hvis
    · exact Or.inr ⟨a', mem_of_getLast htop⟩
    · exact Or.inl hvis
  · exfalso
    obtain ⟨hrk, -⟩ := (canSitOn_eq H L).mp hfit
    have hL : L.rank.toIdx = H.rank.toIdx := by
      rw [htwin, Card.flipSuit_rank]
    omega

/-- **The run audit (a): every winning play from the covered corner
STACKS the covered twin** — `L` is a tableau card at WF (the lemma
above), so §12.1's extraction applies.  The `pileStack L` guard reads
the covered cell empty, which is the first-clearing audit's anchor. -/
theorem sweep_covered_corner_wins_stack_L {st : State} {L H : Card} {S : State}
    {play : List Move}
    (hwf : st.WF) (htwin : H = L.flipSuit)
    (hcover : st.board.topOf (Sum.inr L) = some H)
    (hrun : st.run play = some S) (hwin : S.isWin = true) :
    Move.pileStack L ∈ play := by
  rcases sweep_covered_corner_L_tableau hwf htwin hcover with hvis | ⟨a, hin⟩
  · exact State.pileStack_mem_of_win hwf hrun hwin hvis
  · exact State.pileStack_mem_of_win_hidden hwf hrun hwin hin

/-- One step at the covered corner: a move leaves the covered cell in
exactly two shapes — still the mate, or empty.  The attach kinds only
write free cells (the covered cell is occupied, so an attach onto it
cannot fire), the board-inert kinds do not touch it, and the detach
kinds write exactly the moved card's own base — so the covered cell
empties only when its occupant IS the moved card. -/
theorem covered_cell_after_move {st st' : State} {m : Move} {L H : Card}
    (happly : st.apply m = some st')
    (hcover : st.board.topOf (Sum.inr L) = some H) :
    st'.board.topOf (Sum.inr L) = some H ∨ st'.board.topOf (Sum.inr L) = none := by
  cases m with
  | draw =>
      rw [apply_draw_iff] at happly
      obtain rfl := happly
      exact Or.inl hcover
  | reveal a =>
      rw [apply_reveal_iff] at happly
      obtain ⟨r, bd, -, -, hatt, rfl⟩ := happly
      have hf : st.board.topOf (st.hiddenBase a) = none := attach_frees hatt
      by_cases hb : st.hiddenBase a = Sum.inr L
      · rw [hb] at hf
        rw [hf] at hcover
        exact absurd hcover (by simp)
      · refine Or.inl ?_
        show bd.topOf (Sum.inr L) = some H
        rw [Board.attach_topOf_ne _ _ _ hatt (Ne.symm hb)]
        exact hcover
  | deckPile X b =>
      rw [apply_deckPile_iff] at happly
      obtain ⟨-, -, bd, hatt, rfl⟩ := happly
      have hf : st.board.topOf b = none := attach_frees hatt
      by_cases hb : b = Sum.inr L
      · rw [hb] at hf
        rw [hf] at hcover
        exact absurd hcover (by simp)
      · refine Or.inl ?_
        show bd.topOf (Sum.inr L) = some H
        rw [Board.attach_topOf_ne _ _ _ hatt (Ne.symm hb)]
        exact hcover
  | deckStack c =>
      rw [apply_deckStack_iff] at happly
      obtain ⟨-, -, rfl⟩ := happly
      exact Or.inl hcover
  | pileStack c =>
      rw [apply_pileStack_iff] at happly
      obtain ⟨-, b₀, -, -, rfl⟩ := happly
      by_cases hb : b₀ = Sum.inr L
      · refine Or.inr ?_
        show (st.board.detach b₀).topOf (Sum.inr L) = none
        rw [hb, Board.detach_topOf]
      · refine Or.inl ?_
        show (st.board.detach b₀).topOf (Sum.inr L) = some H
        rw [Board.detach_topOf_ne _ _ _ (Ne.symm hb)]
        exact hcover
  | stackPile c b =>
      rw [apply_stackPile_iff] at happly
      obtain ⟨-, -, bd, hatt, rfl⟩ := happly
      have hf : st.board.topOf b = none := attach_frees hatt
      by_cases hb : b = Sum.inr L
      · rw [hb] at hf
        rw [hf] at hcover
        exact absurd hcover (by simp)
      · refine Or.inl ?_
        show bd.topOf (Sum.inr L) = some H
        rw [Board.attach_topOf_ne _ _ _ hatt (Ne.symm hb)]
        exact hcover
  | pilePile c b =>
      rw [apply_pilePile_iff] at happly
      obtain ⟨b', hb', hne, hcmr, bd, hatt, rfl⟩ := happly
      have hf : (st.board.detach b').topOf b = none := attach_frees hatt
      by_cases hb' : b' = Sum.inr L
      · have hcb : Sum.inr L ≠ b := by rw [hb'] at hne; exact hne
        have hstep : (st.board.detach b').topOf (Sum.inr L) = none := by
          rw [hb', Board.detach_topOf]
        refine Or.inr ?_
        show bd.topOf (Sum.inr L) = none
        rw [Board.attach_topOf_ne _ _ _ hatt hcb]
        exact hstep
      · by_cases hbb : b = Sum.inr L
        · rw [hbb] at hf
          rw [Board.detach_topOf_ne _ _ _ (Ne.symm hb')] at hf
          rw [hcover] at hf
          exact absurd hf (by simp)
        · refine Or.inl ?_
          show bd.topOf (Sum.inr L) = some H
          rw [Board.attach_topOf_ne _ _ _ hatt (Ne.symm hbb),
            Board.detach_topOf_ne _ _ _ (Ne.symm hb')]
          exact hcover

/-- **The first-clearing audit**: if a play from the covered corner
reaches a state where the covered cell reads `none`, then the play
factors as `π₁ ++ m :: π₂` where the pre-state still seats the mate and
`m` vacates the cell — the first such moment exists, and the mate never
left the cell before it (a cell changes occupant only through an empty
intermediate, the step lemma above). -/
theorem exists_covered_first_clearing {L H : Card} :
    ∀ (play : List Move) (st S : State),
    st.board.topOf (Sum.inr L) = some H →
    st.run play = some S →
    S.board.topOf (Sum.inr L) = none →
    ∃ (π₁ : List Move) (m : Move) (π₂ : List Move) (S₀ S₁ : State),
      play = π₁ ++ m :: π₂ ∧
      st.run π₁ = some S₀ ∧
      S₀.board.topOf (Sum.inr L) = some H ∧
      S₀.apply m = some S₁ ∧
      S₁.board.topOf (Sum.inr L) = none := by
  intro play
  induction play with
  | nil =>
      intro st S hcover hrun hend
      obtain rfl : st = S := run_nil_elim hrun
      rw [hcover] at hend
      exact absurd hend (by simp)
  | cons m ms ih =>
      intro st S hcover hrun hend
      obtain ⟨S₁, hm, hrest⟩ := run_cons_elim hrun
      rcases covered_cell_after_move hm hcover with hkeep | hclear
      · obtain ⟨π₁, m', π₂, S₀, S₁', hfact, hrun₁, hcover₀, hap, hclear₁⟩ :=
          ih S₁ S hkeep hrest hend
        refine ⟨m :: π₁, m', π₂, S₀, S₁', ?_, ?_, hcover₀, hap, hclear₁⟩
        · exact congrArg (fun l => m :: l) hfact
        · show (match st.apply m with
              | some st' => st'.run π₁
              | none => none) = some S₀
          rw [hm]
          exact hrun₁
      · exact ⟨[], m, ms, st, S₁, rfl, rfl, hcover, hm, hclear⟩

/-- **The first clearing is the mate's own move** — the audit composed
with the dislodge-shape keystone: the vacating move carries the mate's
own card (`pilePile H b` or `pileStack H`).  This is the plan's (2),
complete: a winning line's first clearing of the covered seat is a MATE
move, and the moment exists whenever the line stacks `L` (§12.1's
extraction supplies the none-reading anchor state). -/
theorem sweep_covered_corner_first_clearing {st S : State} {L H : Card}
    {play : List Move}
    (hcover : st.board.topOf (Sum.inr L) = some H)
    (hrun : st.run play = some S)
    (hend : S.board.topOf (Sum.inr L) = none) :
    ∃ (π₁ : List Move) (m : Move) (π₂ : List Move) (S₀ S₁ : State) (b : Base),
      play = π₁ ++ m :: π₂ ∧
      st.run π₁ = some S₀ ∧
      S₀.board.topOf (Sum.inr L) = some H ∧
      S₀.apply m = some S₁ ∧
      S₁.board.topOf (Sum.inr L) = none ∧
      (m = Move.pilePile H b ∨ m = Move.pileStack H) := by
  obtain ⟨π₁, m, π₂, S₀, S₁, hfact, hrun₁, hcover₀, hap, hclear₁⟩ :=
    exists_covered_first_clearing play st S hcover hrun hend
  have hten : S₀.board.bottomOf H = some (Sum.inr L) :=
    (Board.bottomOf_eq S₀.board H (Sum.inr L)).mpr hcover₀
  obtain ⟨b, hmate⟩ := vacated_covered_cell_imp_mate_move hap hten hclear₁
  exact ⟨π₁, m, π₂, S₀, S₁, b, hfact, hrun₁, hcover₀, hap, hclear₁, hmate⟩

/-! ### The mate's dodge: the two threads' convergence (wave 20)

The exchange image's dislodge counterpart of the source's mate-dodge:
the SAME `pilePile H b` fires in the image (the mate leaves its parked
cell for the same base), and the two results stand in the EXCHANGE
relation at the MATE — the cross-identification (the covering cargo of
the corner IS the twin itself, so the post-dodge seat-swap is the
exchange at `H`).  At the clean corner (no rider on the mate) the two
results are literally EQUAL: the threads merge, and everything after
the merge is shared. -/

/-- At a state whose two twin cells read `none`, the exchange is the
identity (the swap swaps two empty cells). -/
theorem exchangeTwinCargo_id_of_bare_pair {S : State} {t : Card}
    (hb : S.board.topOf (Sum.inr t) = none)
    (hb' : S.board.topOf (Sum.inr t.flipSuit) = none) :
    S.exchangeTwinCargo t = S := by
  apply state_ext
  · rfl
  · apply Board.ext_topOf
    funext b
    rw [State.exchangeTwinCargo_board, Board.exchangeTwin_topOf]
    by_cases hbl : b = Sum.inr t
    · rw [hbl]
      show S.board.topOf (Sum.inr (Card.swapTwin t t)) = S.board.topOf (Sum.inr t)
      rw [Card.swapTwin_self_left, hb', hb]
    · by_cases hbr : b = Sum.inr t.flipSuit
      · rw [hbr]
        show S.board.topOf (Sum.inr (Card.swapTwin t t.flipSuit)) =
          S.board.topOf (Sum.inr t.flipSuit)
        rw [Card.swapTwin_self_right, hb, hb']
      · rw [Base.swapTwin_eq_self hbl hbr]
  · rfl
  · rfl
  · rfl
  · rfl

/-- **The mate's dodge converges the threads** (the reduction's engine,
wave 20): at the covered corner, if the mate's dodge `pilePile H b`
fires in the source, then the SAME dodge fires in the exchange image —
the mate leaves its parked cell for the same base — and the image's
result stands in the EXCHANGE relation at the MATE: the cross
identification.  The covering cargo of the corner IS the twin itself,
so the two-thread consequence of the dodge is the seat swap of the two
twin cells read at `H` (`S₁.exchangeTwinCargo H`).

Guard transfer: the fit/rank/king/visibility guards are state-free or
preserved by `exchangeTwinCargo_isVis`; the self-landing run guard
reads the image's run above the mate, which is the self-cycle alone
(`exchangeTwinCargo_aboveOf_mate_self`).  The dodge base is off both
twin cells (the covered cell is occupied, and the self-fit
`canSitOn H H` is false), so the cells the dodge writes agree between
the threads. -/
theorem covered_dodge_converges {S : State} {L H : Card} {b : Base} {S₁ : State}
    (htwin : H = L.flipSuit)
    (hcover : S.board.topOf (Sum.inr L) = some H)
    (hdodge : S.apply (Move.pilePile H b) = some S₁) :
    (S.exchangeTwinCargo L).apply (Move.pilePile H b) = some (S₁.exchangeTwinCargo H) := by
  have hHL : L = H.flipSuit := by rw [htwin, Card.flipSuit_flipSuit]
  rw [apply_pilePile_iff] at hdodge
  obtain ⟨b₀, hb₀, hne, hcmr, bd, hatt, hshape⟩ := hdodge
  have hb₀L : b₀ = Sum.inr L := by
    have h₁ : S.board.topOf b₀ = some H := (Board.bottomOf_eq S.board H b₀).mp hb₀
    exact S.board.inj b₀ (Sum.inr L) H h₁ hcover
  subst hb₀L
  -- the dodge base is off both twin cells
  have hbL : b ≠ Sum.inr L := fun h => hne h.symm
  have hbH : b ≠ Sum.inr H := by
    intro hcon
    cases b with
    | inl a => exact absurd hcon (by simp)
    | inr d =>
        have hcp : S.canPlace H (Sum.inr d) = true := (canMoveRun_inr_iff.mp hcmr).1
        have hfit := (canPlace_inr_iff.mp hcp).2.2
        rw [Sum.inr.inj hcon] at hfit
        exact canSitOn_self hfit
  have hbσL : b.swapTwin L = b := Base.swapTwin_eq_self hbL (by rw [← htwin]; exact hbH)
  have hbσH : b.swapTwin H = b := Base.swapTwin_eq_self hbH (by rw [← hHL]; exact hbL)
  -- the exchange image's mate seat: the mate sits at its own cell
  have hread : (S.board.exchangeTwin L).topOf (Sum.inr H) = some H := by
    rw [Board.exchangeTwin_topOf]
    show S.board.topOf (Sum.inr (Card.swapTwin L H)) = some H
    rw [show Card.swapTwin L H = L from by rw [htwin]; exact Card.swapTwin_self_right L]
    exact hcover
  -- the image's firing: bottomOf, the free-and-fit guards, the attach
  have hbotT : (S.exchangeTwinCargo L).board.bottomOf H = some (Sum.inr H) := by
    rw [State.exchangeTwinCargo_board, Board.bottomOf_exchangeTwin, hb₀]
    show Option.map (fun x => Base.swapTwin L x) (some (Sum.inr L)) = some (Sum.inr H)
    show some (Base.swapTwin L (Sum.inr L)) = some (Sum.inr H)
    show some (Sum.inr (Card.swapTwin L L)) = some (Sum.inr H)
    rw [Card.swapTwin_self_left, htwin]
  have haboveT : ((S.exchangeTwinCargo L).board.aboveOf H) = [H] :=
    exchangeTwinCargo_aboveOf_mate_self htwin hcover
  have hreadL : (S.board.exchangeTwin L).topOf (Sum.inr L) = S.board.topOf (Sum.inr H) := by
    rw [Board.exchangeTwin_topOf]
    show S.board.topOf (Sum.inr (Card.swapTwin L L)) = S.board.topOf (Sum.inr H)
    rw [Card.swapTwin_self_left, htwin]
  have hLH : (Sum.inr L : Base) ≠ Sum.inr H := by
    intro h
    rw [Sum.inr.inj h] at htwin
    exact Card.flipSuit_ne H htwin.symm
  have hbHT : Sum.inr H ≠ b := fun h => hbH h.symm
  -- the image's firing guards at `b`
  have hcpS : S.canPlace H b = true := by
    cases b with
    | inl a => exact canMoveRun_inl_iff.mp hcmr
    | inr d => exact (canMoveRun_inr_iff.mp hcmr).1
  have hfreeT : (S.exchangeTwinCargo L).board.topOf b = none := by
    rw [State.exchangeTwinCargo_board, Board.exchangeTwin_topOf, hbσL]
    exact topOf_of_canPlace hcpS
  have hcmrT : (S.exchangeTwinCargo L).canMoveRun H b = true := by
    cases b with
    | inl a =>
        obtain ⟨hfree, hking⟩ := canPlace_inl_iff.mp hcpS
        refine (canMoveRun_inl_iff (st := S.exchangeTwinCargo L)).mpr ?_
        refine (canPlace_inl_iff (st := S.exchangeTwinCargo L)).mpr ⟨?_, hking⟩
        rw [State.exchangeTwinCargo_board, Board.exchangeTwin_topOf,
          show Base.swapTwin L (Sum.inl a) = Sum.inl a from rfl]
        exact hfree
    | inr d =>
        obtain ⟨hfree, hvis, hfit⟩ := (canPlace_inr_iff).mp ((canMoveRun_inr_iff.mp hcmr).1)
        have hdL : d ≠ L := by intro h; exact hbL (by rw [h])
        have hdH : d ≠ H := canSitOn_ne_of_fits_mate hfit
        have hzσ : Base.swapTwin L (Sum.inr d) = Sum.inr d := by
          show Sum.inr (Card.swapTwin L d) = Sum.inr d
          rw [Card.swapTwin_of_ne hdL (by rw [← htwin]; exact hdH)]
        refine (canMoveRun_inr_iff (st := S.exchangeTwinCargo L)).mpr ⟨?_, ?_⟩
        · refine (canPlace_inr_iff (st := S.exchangeTwinCargo L)).mpr ⟨?_, ?_, hfit⟩
          · rw [State.exchangeTwinCargo_board, Board.exchangeTwin_topOf, hzσ]
            exact hfree
          · rw [exchangeTwinCargo_isVis]
            exact hvis
        · rw [haboveT]
          simp [hdH]
  -- the image's attach and firing
  have hfreeT' : ((S.exchangeTwinCargo L).board.detach (Sum.inr H)).topOf b = none := by
    rw [Board.detach_topOf_ne _ _ _ hbH]
    exact hfreeT
  have hbotT' : ((S.exchangeTwinCargo L).board.detach (Sum.inr H)).bottomOf H = none :=
    Board.bottomOf_detach_self hread
  obtain ⟨bdT, hattT⟩ := Option.ne_none_iff_exists'.mp
    ((Board.attach_eq_some_iff _ _ _).mpr ⟨hfreeT', hbotT'⟩)
  have hneT : Sum.inr H ≠ b := fun h => hbH h.symm
  have hfire : (S.exchangeTwinCargo L).apply (Move.pilePile H b)
      = some { S.exchangeTwinCargo L with board := bdT } :=
    apply_pilePile_iff.mpr ⟨Sum.inr H, hbotT, hneT, hcmrT, bdT, hattT, rfl⟩
  subst hshape
  rw [hfire]
  refine congrArg some ?_
  -- the cross identification: `bdT` is `bd` seat-swapped at `H`
  apply state_ext
  · rfl
  · apply Board.ext_topOf
    funext z
    show bdT.topOf z = bd.topOf (Base.swapTwin H z)
    have Sbd_off : ∀ z : Base, z ≠ b → z ≠ Sum.inr L →
        bd.topOf z = S.board.topOf z := by
      intro z hzb hzL
      rw [Board.attach_topOf_ne _ _ _ hatt hzb, Board.detach_topOf_ne _ _ _ hzL]
    have Tbd_off : ∀ z : Base, z ≠ b → z ≠ Sum.inr H →
        bdT.topOf z = (S.board.exchangeTwin L).topOf z := by
      intro z hzb hzH
      rw [Board.attach_topOf_ne _ _ _ hattT hzb, Board.detach_topOf_ne _ _ _ hzH]
      rfl
    by_cases hzb : z = b
    · rw [hzb, Board.attach_topOf _ _ _ hattT, hbσH]
      exact (Board.attach_topOf _ _ _ hatt).symm
    · by_cases hzL : z = Sum.inr L
      · have hzσLH : Base.swapTwin H (Sum.inr L) = Sum.inr H := by
          show Sum.inr (Card.swapTwin H L) = Sum.inr H
          rw [show Card.swapTwin H L = H from by rw [hHL]; exact Card.swapTwin_self_right H]
        rw [hzL, hzσLH, Tbd_off (Sum.inr L) hne hLH, hreadL,
          Sbd_off (Sum.inr H) hbHT hLH.symm]
      · by_cases hzH : z = Sum.inr H
        · have hzσHH : Base.swapTwin H (Sum.inr H) = Sum.inr L := by
            show Sum.inr (Card.swapTwin H H) = Sum.inr L
            rw [Card.swapTwin_self_left, hHL]
          rw [hzH, hzσHH, Board.attach_topOf_ne _ _ _ hattT hneT, Board.detach_topOf,
            Board.attach_topOf_ne _ _ _ hatt hne, Board.detach_topOf]
        · rw [Tbd_off z hzb hzH, Board.exchangeTwin_topOf]
          rw [show Base.swapTwin L z = z from
              Base.swapTwin_eq_self hzL (by rw [← htwin]; exact hzH),
            show Base.swapTwin H z = z from
              Base.swapTwin_eq_self hzH (by rw [← hHL]; exact hzL)]
          rw [Sbd_off z hzb hzL]
  · rfl
  · rfl
  · rfl
  · rfl

/-- **The clean-corner corollary: the two threads MERGE.**  With no
rider on the mate (`Sum.inr H` reads `none`), the dodge's two results are
LITERALLY equal — the cross identification collapses by
`exchangeTwinCargo_id_of_bare_pair` — so everything after the mate's
departure is shared by the two readings: the covered corner and its
exchange image are one game from the dislodge moment on. -/
theorem covered_dodge_merges_clean {S : State} {L H : Card} {b : Base} {S₁ : State}
    (htwin : H = L.flipSuit)
    (hcover : S.board.topOf (Sum.inr L) = some H)
    (hHseat : S.board.topOf (Sum.inr H) = none)
    (hdodge : S.apply (Move.pilePile H b) = some S₁) :
    (S.exchangeTwinCargo L).apply (Move.pilePile H b) = some S₁ := by
  have h := covered_dodge_converges htwin hcover hdodge
  rw [apply_pilePile_iff] at hdodge
  obtain ⟨b₀, hb₀, hne, hcmr, bd, hatt, hshape⟩ := hdodge
  have hb₀L : b₀ = Sum.inr L := by
    have h₁ : S.board.topOf b₀ = some H := (Board.bottomOf_eq S.board H b₀).mp hb₀
    exact S.board.inj b₀ (Sum.inr L) H h₁ hcover
  subst hb₀L
  subst hshape
  have hHL : L = H.flipSuit := by rw [htwin, Card.flipSuit_flipSuit]
  have hLH : (Sum.inr L : Base) ≠ Sum.inr H := by
    intro h
    rw [Sum.inr.inj h] at htwin
    exact Card.flipSuit_ne H htwin.symm
  have hbH : b ≠ Sum.inr H := by
    intro hcon
    cases b with
    | inl a => exact absurd hcon (by simp)
    | inr d =>
        have hcp : S.canPlace H (Sum.inr d) = true := (canMoveRun_inr_iff.mp hcmr).1
        have hfit := (canPlace_inr_iff.mp hcp).2.2
        rw [Sum.inr.inj hcon] at hfit
        exact canSitOn_self hfit
  rw [h]
  refine congrArg some (exchangeTwinCargo_id_of_bare_pair ?_ ?_)
  · show bd.topOf (Sum.inr H) = none
    rw [Board.attach_topOf_ne _ _ _ hatt (fun h => hbH h.symm),
      Board.detach_topOf_ne _ _ _ (fun h => hLH h.symm)]
    exact hHseat
  · rw [← hHL]
    show bd.topOf (Sum.inr L) = none
    rw [Board.attach_topOf_ne _ _ _ hatt hne]
    exact Board.detach_topOf _ _

/-- **The dodge-first instance, PAID (the safety's first independently
closed window)**: if a winning line exists whose FIRST move is the
mate's own dodge, the exchange image is solvable too — the image plays
the SAME dodge first, lands LITERALLY on the source's post-dodge state
(`covered_dodge_merges_clean`), and wins with the source's own tail.
The covered corner and its image are one game from the dislodge moment
on; this is the assembly's π₁ = [] case — the class the general
reduction (the π₁ pre-dodge replay) narrows to once the mirrors land. -/
theorem sweep_covered_corner_dodge_first_forward {st S₁ : State} {L H : Card} {b : Base}
    (htwin : H = L.flipSuit)
    (hcover : st.board.topOf (Sum.inr L) = some H)
    (hHseat : st.board.topOf (Sum.inr H) = none)
    (hdodge : st.apply (Move.pilePile H b) = some S₁)
    (hsol : S₁.solvableFrom) :
    (st.exchangeTwinCargo L).solvableFrom := by
  obtain ⟨π, w, hrun, hwin⟩ := hsol
  have hmerge : (st.exchangeTwinCargo L).apply (Move.pilePile H b) = some S₁ :=
    covered_dodge_merges_clean htwin hcover hHseat hdodge
  refine ⟨Move.pilePile H b :: π, w, ?_, hwin⟩
  show (match (st.exchangeTwinCargo L).apply (Move.pilePile H b) with
    | some st' => st'.run π
    | none => none) = some w
  rw [hmerge]
  exact hrun

/-! ### The clean-corridor π₁ replay (wave 21)

Residue piece (i) of the safety's plan — the prefix replay before the
mate's first clearing — paid at the CLEAN CORRIDOR: a prefix whose every
intermediate state keeps the corner shape (the covered cell still the
mate's, the mate's own cell bare, the covered twin unseated) at WF.  The
mirror of each source move is then the SAME move: the corridor excludes
exactly the moves that would need a base relabel — the mate's own moves
are the clearing (`hkeep`), a landing on the mate's cell would break its
bareness (`hkeep'`), a landing on the covered cell is attach-blocked
(occupied), and the unseated covered twin can neither move nor be
seated (`hid`; at WF `board_edges` pins it to a pile's hidden boundary,
the deal-adjacent cover's only justification) — so every fireable move
reads and writes only cells where the exchange image agrees with the
source, and the same move fires there with the image staying the
source's exchange.  The final assembly combines the replay with the
wave-20 dodge merge: the safety's forward leg for every winning line
whose first clearing of the covered seat is the mate's DODGE along a
clean corridor. -/

/-- The seat exchange commutes with a detach at a cell off the twin
pair (the image of a cleared cell is the cleared cell of the image). -/
theorem Board.exchangeTwin_detach_off {bd : Board} {t : Card} {β : Base}
    (h₁ : β ≠ Sum.inr t) (h₂ : β ≠ Sum.inr t.flipSuit) :
    (bd.exchangeTwin t).detach β = (bd.detach β).exchangeTwin t := by
  apply Board.ext_topOf
  funext x
  have hfix : β.swapTwin t = β := Base.swapTwin_eq_self h₁ h₂
  by_cases hxβ : x = β
  · rw [hxβ, Board.detach_topOf, Board.exchangeTwin_topOf, hfix, Board.detach_topOf]
  · have hσx : x.swapTwin t ≠ β := by
      intro hcon
      refine hxβ ?_
      have := congrArg (fun b => b.swapTwin t) hcon
      rwa [Base.swapTwin_swapTwin, hfix] at this
    rw [Board.detach_topOf_ne _ _ _ hxβ, Board.exchangeTwin_topOf,
      Board.exchangeTwin_topOf, Board.detach_topOf_ne _ _ _ hσx]

/-- The seat exchange commutes with an attach at a cell off the twin
pair. -/
theorem Board.exchangeTwin_attach_off {bd bd' : Board} {t : Card} {β : Base} {r : Card}
    (h₁ : β ≠ Sum.inr t) (h₂ : β ≠ Sum.inr t.flipSuit)
    (hatt : bd.attach β r = some bd') :
    (bd.exchangeTwin t).attach β r = some (bd'.exchangeTwin t) := by
  obtain ⟨hfree, hbot⟩ := (Board.attach_eq_some_iff bd β r).mp (by rw [hatt]; simp)
  have hfix : β.swapTwin t = β := Base.swapTwin_eq_self h₁ h₂
  have hfreeI : (bd.exchangeTwin t).topOf β = none := by
    rw [Board.exchangeTwin_topOf, hfix]; exact hfree
  have hbotI : (bd.exchangeTwin t).bottomOf r = none := by
    rw [Board.bottomOf_exchangeTwin, hbot]; rfl
  obtain ⟨bd'', hatt''⟩ := Option.ne_none_iff_exists'.mp
    ((Board.attach_eq_some_iff _ _ _).mpr ⟨hfreeI, hbotI⟩)
  rw [hatt'']
  refine congrArg some ?_
  apply Board.ext_topOf
  funext x
  by_cases hσx : x.swapTwin t = β
  · have hxβ : x = β := by
      have := congrArg (fun b => b.swapTwin t) hσx
      rwa [Base.swapTwin_swapTwin, hfix] at this
    rw [hxβ, Board.attach_topOf _ _ _ hatt'', Board.exchangeTwin_topOf, hfix,
      Board.attach_topOf _ _ _ hatt]
  · have hxβ : x ≠ β := fun hcon => hσx (by rw [hcon, hfix])
    rw [Board.attach_topOf_ne _ _ _ hatt'' hxβ, Board.exchangeTwin_topOf,
      Board.exchangeTwin_topOf, Board.attach_topOf_ne _ _ _ hatt hσx]

/-- An attach keeps an unseated card unseated (the attached value
differs from it). -/
theorem Board.bottomOf_none_attach_off {bd bd' : Board} {β : Base} {r L : Card}
    (hatt : bd.attach β r = some bd') (hr : r ≠ L)
    (hbot : bd.bottomOf L = none) : bd'.bottomOf L = none := by
  refine (Board.bottomOf_eq_none _ _).mpr (fun b hb' => ?_)
  by_cases hb : b = β
  · rw [hb, Board.attach_topOf _ _ _ hatt] at hb'
    exact hr (Option.some.inj hb')
  · rw [Board.attach_topOf_ne _ _ _ hatt hb] at hb'
    exact (Board.bottomOf_eq_none _ _).mp hbot b hb'

/-- A detach keeps an unseated card unseated (a cleared cell cannot
seat it either). -/
theorem Board.bottomOf_none_detach_off {bd : Board} {β : Base} {L : Card}
    (hbot : bd.bottomOf L = none) : (bd.detach β).bottomOf L = none := by
  refine (Board.bottomOf_eq_none _ _).mpr (fun b hb' => ?_)
  by_cases hb : b = β
  · rw [hb, Board.detach_topOf] at hb'; simp at hb'
  · rw [Board.detach_topOf_ne _ _ _ hb] at hb'
    exact (Board.bottomOf_eq_none _ _).mp hbot b hb'

/-- **The walk stays off the pair at a corner whose covered twin is
unseated**: walking up from any card off the pair, no board read ever
yields the covered twin (it is unseated — no cell hosts it) or the mate
(only its own covered cell hosts it, and the walk reads that cell only
from the covered twin itself, which the walk never reaches).  Used to
see that the run guards' `aboveOf` walks agree between the source and
its exchange image at the corner. -/
theorem Board.aboveOf_go_off_pair {bd : Board} {L H : Card}
    (hcover : bd.topOf (Sum.inr L) = some H)
    (hid : bd.bottomOf L = none) :
    ∀ (n : Nat) (x : Card) (acc : List Card),
      x ≠ L → x ≠ H →
      (∀ y ∈ acc, y ≠ L ∧ y ≠ H) →
      ∀ z ∈ Board.aboveOf.go bd n (Sum.inr x) acc, z ≠ L ∧ z ≠ H := by
  intro n
  induction n with
  | zero =>
      intro x acc hxL hxH hacc z hz
      have hz2 : z ∈ acc := hz
      exact hacc z hz2
  | succ n ih =>
      intro x acc hxL hxH hacc z hz
      rw [Board.aboveOf_go_succ] at hz
      cases hread : bd.topOf (Sum.inr x) with
      | none =>
          rw [hread] at hz
          have hz2 : z ∈ acc := hz
          exact hacc z hz2
      | some y =>
          rw [hread] at hz
          by_cases hcy : acc.contains y = true
          · have hz2 : z ∈ (if acc.contains y = true then acc
                else Board.aboveOf.go bd n (Sum.inr y) (y :: acc)) := hz
            rw [ite_eq_left hcy] at hz2
            exact hacc z hz2
          · have hz2 : z ∈ (if acc.contains y = true then acc
                else Board.aboveOf.go bd n (Sum.inr y) (y :: acc)) := hz
            rw [ite_eq_right hcy] at hz2
            have hyL : y ≠ L := by
              intro hyl; rw [hyl] at hread
              have h₁ : bd.bottomOf L = some (Sum.inr x) :=
                (Board.bottomOf_eq bd L (Sum.inr x)).mpr hread
              rw [hid] at h₁; simp at h₁
            have hyH : y ≠ H := by
              intro hyh; rw [hyh] at hread
              exact hxL (Sum.inr.inj (bd.inj (Sum.inr x) (Sum.inr L) H hread hcover))
            exact ih y (y :: acc) hyL hyH
              (by intro z' hz'
                  rcases List.mem_cons.mp hz' with h | hmem'
                  · exact ⟨by rw [h]; exact hyL, by rw [h]; exact hyH⟩
                  · exact hacc z' hmem') z hz2

/-- **The clean-corridor step** (the π₁ replay's engine): at a WF
clean-corner state — the covered cell the mate's, the mate's own cell
bare, the covered twin unseated — any move that PRESERVES the corridor
shape (`hkeep`/`hkeep'`) mirrors VERBATIM into the exchange image: the
same move fires there and the image stays the source's exchange.  The
corridor's shape exclusions are exactly the relabel cases: the mate's
own moves would empty the covered cell (`hkeep` kills them), landings on
the mate's cell would break its bareness (`hkeep'`), and landings on the
covered cell are attach-blocked (occupied); everything else reads and
writes only off-pair cells, where the two threads agree — and the
unseaten covered twin keeps the `aboveOf` walks off the pair, so even
the run guards read the same values.  The unseaten covered twin also
survives the step (the second conjunct): nothing can attach it, and at
WF the stock and foundation channels are closed to it. -/
theorem covered_clean_step {T T₁ : State} {m : Move} {L H : Card}
    (hwf : T.WF) (htwin : H = L.flipSuit)
    (hcover : T.board.topOf (Sum.inr L) = some H)
    (hclean : T.board.topOf (Sum.inr H) = none)
    (hid : T.board.bottomOf L = none)
    (hap : T.apply m = some T₁)
    (hkeep : T₁.board.topOf (Sum.inr L) = some H)
    (hkeep' : T₁.board.topOf (Sum.inr H) = none) :
    (T.exchangeTwinCargo L).apply m = some (T₁.exchangeTwinCargo L) ∧
    T₁.board.bottomOf L = none := by
  have isVisH : T.isVis H = true := by
    show (T.board.bottomOf H).isSome = true
    rw [(Board.bottomOf_eq T.board H (Sum.inr L)).mpr hcover]
    rfl
  -- at WF the covered corner pins the covered twin to a hidden boundary
  have hLbound : ∃ a', T.topHidden a' = some L := by
    have hedge := hwf.board_edges (Sum.inr L) H hcover
    rcases hedge.2 with hbur | ⟨-, hfit⟩
    · obtain ⟨a, t, rest, hpiles, hbase⟩ := hbur
      rcases hbase with ⟨a', htop⟩ | hvis
      · exact ⟨a', htop⟩
      · rw [hid] at hvis; simp at hvis
    · exfalso
      obtain ⟨hrk, -⟩ := (canSitOn_eq H L).mp hfit
      have hrank : L.rank.toIdx = H.rank.toIdx := by rw [htwin, Card.flipSuit_rank]
      omega
  obtain ⟨a₀, hLa₀⟩ := hLbound
  have hLhidden : L ∈ T.hidden a₀ := mem_of_getLast hLa₀
  -- the exchange image agrees with the source off the pair
  have htopOff : ∀ x : Card, x ≠ L → x ≠ H →
      (T.exchangeTwinCargo L).board.topOf (Sum.inr x) = T.board.topOf (Sum.inr x) := by
    intro x hxL hxH
    have hxFS : x ≠ L.flipSuit := by
      intro h; apply hxH; rw [h, htwin]
    rw [State.exchangeTwinCargo_board, Board.exchangeTwin_topOf,
      show Base.swapTwin L (Sum.inr x) = Sum.inr x from
        Base.swapTwin_eq_self (fun h => hxL (Sum.inr.inj h))
          (fun h => hxFS (Sum.inr.inj h))]
  have hbotOff : ∀ c : Card, c ≠ L → c ≠ H →
      (T.exchangeTwinCargo L).board.bottomOf c = T.board.bottomOf c := by
    intro c hcL hcH
    rw [State.exchangeTwinCargo_board, Board.bottomOf_exchangeTwin]
    cases hb : T.board.bottomOf c with
    | none => rfl
    | some b =>
        have hbL : b ≠ Sum.inr L := by
          intro h
          have h₁ : T.board.topOf b = some c := (Board.bottomOf_eq T.board c b).mp hb
          rw [h] at h₁; rw [hcover] at h₁
          exact absurd (Option.some.inj h₁).symm hcH
        have hbFS : b ≠ Sum.inr L.flipSuit := by
          intro h
          have h₁ : T.board.topOf b = some c := (Board.bottomOf_eq T.board c b).mp hb
          rw [h] at h₁; rw [← htwin] at h₁; rw [hclean] at h₁
          exact absurd h₁ (by simp)
        show some (b.swapTwin L) = some b
        rw [Base.swapTwin_eq_self hbL hbFS]
  have hcpOff : ∀ (c : Card) (b : Base), b ≠ Sum.inr L → b ≠ Sum.inr L.flipSuit →
      T.canPlace c b = true → (T.exchangeTwinCargo L).canPlace c b = true := by
    intro c b hbL hbFS hcp
    cases b with
    | inl a =>
        obtain ⟨hfree, hking⟩ := canPlace_inl_iff.mp hcp
        refine canPlace_inl_iff.mpr ⟨?_, hking⟩
        rw [State.exchangeTwinCargo_board, Board.exchangeTwin_topOf]
        exact hfree
    | inr d =>
        obtain ⟨hfree, hvis, hfit⟩ := canPlace_inr_iff.mp hcp
        refine canPlace_inr_iff.mpr ⟨?_, ?_, hfit⟩
        · rw [State.exchangeTwinCargo_board, Board.exchangeTwin_topOf,
            Base.swapTwin_eq_self hbL hbFS]
          exact hfree
        · rw [exchangeTwinCargo_isVis]; exact hvis
  cases m with
  | draw =>
      rw [apply_draw_iff] at hap
      obtain rfl := hap
      exact ⟨apply_draw_iff.mpr rfl, hid⟩
  | reveal a =>
      rw [apply_reveal_iff] at hap
      obtain ⟨r, bd, htop, hbare, hatt, rfl⟩ := hap
      have hrL : r ≠ L := by
        intro h; rw [h] at hbare; rw [hcover] at hbare; simp at hbare
      have hrH : r ≠ H := by
        intro h; rw [h] at htop
        exact absurd (mem_of_getLast htop) (hwf.vis_not_hidden H isVisH a)
      obtain ⟨hfreeB, -⟩ := (Board.attach_eq_some_iff T.board (T.hiddenBase a) r).mp
        (by rw [hatt]; simp)
      have hβL : T.hiddenBase a ≠ Sum.inr L := by
        intro h; rw [h] at hfreeB; rw [hcover] at hfreeB; simp at hfreeB
      have hβFS : T.hiddenBase a ≠ Sum.inr L.flipSuit := by
        intro h
        have hread : bd.topOf (Sum.inr L.flipSuit) = some r := by
          rw [← h]; exact Board.attach_topOf _ _ _ hatt
        rw [← htwin] at hread
        have hpost : bd.topOf (Sum.inr H) = none := hkeep'
        rw [hread] at hpost; simp at hpost
      refine ⟨?_, ?_⟩
      · rw [apply_reveal_iff]
        refine ⟨r, bd.exchangeTwin L, htop, ?_, ?_, rfl⟩
        · rw [htopOff r hrL hrH]; exact hbare
        · rw [State.exchangeTwinCargo_board]
          exact Board.exchangeTwin_attach_off hβL hβFS hatt
      · exact Board.bottomOf_none_attach_off hatt hrL hid
  | deckPile c b =>
      rw [apply_deckPile_iff] at hap
      obtain ⟨hprev, hcp, bd, hatt, rfl⟩ := hap
      have hcL : c ≠ L := by
        intro h; rw [h] at hprev
        exact absurd hLhidden (State.stock_prev_not_mem_hidden hwf hprev (a := a₀))
      have hcH : c ≠ H := by
        intro h
        have h₁ := Cycle.posOf_mem (Cycle.prev_mem hprev)
        rw [h] at h₁
        rw [hwf.vis_off_cycle H isVisH] at h₁
        simp at h₁
      have hbL' : b ≠ Sum.inr L := by
        intro h
        have h₁ : T.board.topOf (Sum.inr L) = none := by
          rw [← h]; exact topOf_of_canPlace hcp
        rw [hcover] at h₁; simp at h₁
      have hbFS' : b ≠ Sum.inr L.flipSuit := by
        intro h
        have hread : bd.topOf (Sum.inr L.flipSuit) = some c := by
          rw [← h]; exact Board.attach_topOf _ _ _ hatt
        rw [← htwin] at hread
        have hpost : bd.topOf (Sum.inr H) = none := hkeep'
        rw [hread] at hpost; simp at hpost
      refine ⟨?_, ?_⟩
      · rw [apply_deckPile_iff]
        refine ⟨hprev, hcpOff c b hbL' hbFS' hcp, bd.exchangeTwin L, ?_, rfl⟩
        · rw [State.exchangeTwinCargo_board]
          exact Board.exchangeTwin_attach_off hbL' hbFS' hatt
      · exact Board.bottomOf_none_attach_off hatt hcL hid
  | deckStack c =>
      rw [apply_deckStack_iff] at hap
      obtain ⟨hprev, hrk, rfl⟩ := hap
      exact ⟨apply_deckStack_iff.mpr ⟨hprev, hrk, rfl⟩, hid⟩
  | pileStack c =>
      rw [apply_pileStack_iff] at hap
      obtain ⟨htop, b₀, hb, hrk, rfl⟩ := hap
      have hcH : c ≠ H := by
        intro h; rw [h] at hb
        have hHbot : T.board.bottomOf H = some (Sum.inr L) :=
          (Board.bottomOf_eq T.board H (Sum.inr L)).mpr hcover
        have hb₀ : b₀ = Sum.inr L := Option.some.inj (hb.symm.trans hHbot)
        have hclr : (T.board.detach b₀).topOf (Sum.inr L) = none := by
          rw [hb₀]; exact Board.detach_topOf _ _
        have hpost : (T.board.detach b₀).topOf (Sum.inr L) = some H := hkeep
        rw [hclr] at hpost; simp at hpost
      have hcL : c ≠ L := by
        intro h; rw [h] at htop; rw [hcover] at htop; simp at htop
      have hb₀L : b₀ ≠ Sum.inr L := by
        intro h; rw [h] at hb
        have h₁ : T.board.topOf (Sum.inr L) = some c :=
          (Board.bottomOf_eq T.board c (Sum.inr L)).mp hb
        rw [hcover] at h₁
        exact absurd (Option.some.inj h₁).symm hcH
      have hb₀FS : b₀ ≠ Sum.inr L.flipSuit := by
        intro h; rw [h] at hb
        have h₁ : T.board.topOf (Sum.inr L.flipSuit) = some c :=
          (Board.bottomOf_eq T.board c (Sum.inr L.flipSuit)).mp hb
        rw [← htwin] at h₁; rw [hclean] at h₁; simp at h₁
      refine ⟨?_, ?_⟩
      · rw [apply_pileStack_iff]
        refine ⟨by rw [htopOff c hcL hcH]; exact htop, b₀, ?_, hrk, ?_⟩
        · rw [State.exchangeTwinCargo_board, Board.bottomOf_exchangeTwin, hb]
          show some (b₀.swapTwin L) = some b₀
          rw [Base.swapTwin_eq_self hb₀L hb₀FS]
        · rw [State.exchangeTwinCargo_board, Board.exchangeTwin_detach_off hb₀L hb₀FS]
          rfl
      · exact Board.bottomOf_none_detach_off hid
  | stackPile c b =>
      rw [apply_stackPile_iff] at hap
      obtain ⟨hrk, hcp, bd, hatt, rfl⟩ := hap
      have hcL : c ≠ L := by
        intro h; rw [h] at hrk
        have hlt : L.rank.toIdx < T.heights L.suit := by omega
        exact absurd hLhidden ((hwf.founds_gone L hlt).2.2 a₀)
      have hcH : c ≠ H := by
        intro h; rw [h] at hrk
        have hlt : H.rank.toIdx < T.heights H.suit := by omega
        have hvc := (hwf.founds_gone H hlt).1
        rw [hvc] at isVisH; simp at isVisH
      have hbL' : b ≠ Sum.inr L := by
        intro h
        have h₁ : T.board.topOf (Sum.inr L) = none := by
          rw [← h]; exact topOf_of_canPlace hcp
        rw [hcover] at h₁; simp at h₁
      have hbFS' : b ≠ Sum.inr L.flipSuit := by
        intro h
        have hread : bd.topOf (Sum.inr L.flipSuit) = some c := by
          rw [← h]; exact Board.attach_topOf _ _ _ hatt
        rw [← htwin] at hread
        have hpost : bd.topOf (Sum.inr H) = none := hkeep'
        rw [hread] at hpost; simp at hpost
      refine ⟨?_, ?_⟩
      · rw [apply_stackPile_iff]
        refine ⟨hrk, hcpOff c b hbL' hbFS' hcp, bd.exchangeTwin L, ?_, rfl⟩
        · rw [State.exchangeTwinCargo_board]
          exact Board.exchangeTwin_attach_off hbL' hbFS' hatt
      · exact Board.bottomOf_none_attach_off hatt hcL hid
  | pilePile c b =>
      rw [apply_pilePile_iff] at hap
      obtain ⟨b₀, hb, hne, hcmr, bd, hatt, rfl⟩ := hap
      have hcL : c ≠ L := by
        intro h; rw [h] at hb; rw [hid] at hb; simp at hb
      have hcH : c ≠ H := by
        intro h; rw [h] at hb
        have hHbot : T.board.bottomOf H = some (Sum.inr L) :=
          (Board.bottomOf_eq T.board H (Sum.inr L)).mpr hcover
        have hb₀ : b₀ = Sum.inr L := Option.some.inj (hb.symm.trans hHbot)
        rw [hb₀] at hne
        have hpost : bd.topOf (Sum.inr L) = none := by
          rw [Board.attach_topOf_ne _ _ _ hatt hne, hb₀]
          exact Board.detach_topOf _ _
        have hsome : bd.topOf (Sum.inr L) = some H := hkeep
        rw [hpost] at hsome; simp at hsome
      have hb₀L : b₀ ≠ Sum.inr L := by
        intro h; rw [h] at hb
        have h₁ : T.board.topOf (Sum.inr L) = some c :=
          (Board.bottomOf_eq T.board c (Sum.inr L)).mp hb
        rw [hcover] at h₁
        exact absurd (Option.some.inj h₁).symm hcH
      have hb₀FS : b₀ ≠ Sum.inr L.flipSuit := by
        intro h; rw [h] at hb
        have h₁ : T.board.topOf (Sum.inr L.flipSuit) = some c :=
          (Board.bottomOf_eq T.board c (Sum.inr L.flipSuit)).mp hb
        rw [← htwin] at h₁; rw [hclean] at h₁; simp at h₁
      have hbL' : b ≠ Sum.inr L := by
        intro h
        have h₁ : T.board.topOf (Sum.inr L) = none := by
          rw [← h]; exact topOf_of_canPlace (canPlace_of_canMoveRun hcmr)
        rw [hcover] at h₁; simp at h₁
      have hbFS' : b ≠ Sum.inr L.flipSuit := by
        intro h
        have hread : bd.topOf (Sum.inr L.flipSuit) = some c := by
          rw [← h]; exact Board.attach_topOf _ _ _ hatt
        rw [← htwin] at hread
        have hpost : bd.topOf (Sum.inr H) = none := hkeep'
        rw [hread] at hpost; simp at hpost
      -- the run guard's walk agrees: the walk stays off the pair
      have hmemR : ∀ z ∈ T.board.aboveOf c, z ≠ L ∧ z ≠ H := by
        intro z hz
        have hz' : z ∈ Board.aboveOf.go T.board 52 (Sum.inr c) ([] : List Card) := hz
        exact Board.aboveOf_go_off_pair hcover hid 52 c [] hcL hcH (by simp) z hz'
      have hrwo : (T.exchangeTwinCargo L).board.aboveOf c = T.board.aboveOf c :=
        Board.aboveOf_congr (fun x hx => by
          rcases List.mem_cons.mp hx with h | hx'
          · rw [h]; exact (htopOff c hcL hcH).symm
          · obtain ⟨hxL, hxH⟩ := hmemR x hx'
            exact (htopOff x hxL hxH).symm)
      have hrw : (T.board.exchangeTwin L).aboveOf c = T.board.aboveOf c := by
        rw [← State.exchangeTwinCargo_board]; exact hrwo
      refine ⟨?_, ?_⟩
      · rw [apply_pilePile_iff]
        have hcp' := canPlace_of_canMoveRun hcmr
        refine ⟨b₀, ?_, hne, ?_, bd.exchangeTwin L, ?_, rfl⟩
        · rw [State.exchangeTwinCargo_board, Board.bottomOf_exchangeTwin, hb]
          show some (b₀.swapTwin L) = some b₀
          rw [Base.swapTwin_eq_self hb₀L hb₀FS]
        · cases b with
          | inl a => exact canMoveRun_inl_iff.mpr (hcpOff c (Sum.inl a) hbL' hbFS' hcp')
          | inr d =>
              refine (canMoveRun_inr_iff (st := T.exchangeTwinCargo L)).mpr
                ⟨hcpOff c (Sum.inr d) hbL' hbFS' hcp', ?_⟩
              rw [State.exchangeTwinCargo_board, hrw]
              exact (canMoveRun_inr_iff.mp hcmr).2
        · rw [State.exchangeTwinCargo_board, Board.exchangeTwin_detach_off hb₀L hb₀FS]
          exact Board.exchangeTwin_attach_off hbL' hbFS' hatt
      · exact Board.bottomOf_none_attach_off hatt hcL
          (Board.bottomOf_none_detach_off hid)

/-- **The clean-corridor π₁ replay**: a prefix run from the covered
corner to a still-covered state, all of whose intermediate states keep
the corner shape, replays VERBATIM in the exchange image — the image
runs the same prefix and lands on the source's end state, exchanged.
The `hmids` premise is the corridor: every prefix's end state keeps the
covered cell the mate's, the mate's own cell bare, and the covered twin
unseated. -/
theorem covered_clean_replay {L H : Card} :
    ∀ (π : List Move) (T T' : State),
      T.WF → H = L.flipSuit →
      T.board.topOf (Sum.inr L) = some H →
      T.board.topOf (Sum.inr H) = none →
      T.board.bottomOf L = none →
      T.run π = some T' →
      (∀ (πa πb : List Move), π = πa ++ πb →
        ∃ Tm, T.run πa = some Tm ∧
          Tm.board.topOf (Sum.inr L) = some H ∧
          Tm.board.topOf (Sum.inr H) = none ∧
          Tm.board.bottomOf L = none) →
      (T.exchangeTwinCargo L).run π = some (T'.exchangeTwinCargo L) := by
  intro π
  induction π with
  | nil =>
      intro T T' hwf htwin hcover hclean hid hrun hmids
      obtain rfl := run_nil_elim hrun
      rfl
  | cons m ms ih =>
      intro T T' hwf htwin hcover hclean hid hrun hmids
      obtain ⟨S₁, hap, hrest⟩ := run_cons_elim hrun
      -- the corridor's next state (the one-move prefix's end)
      obtain ⟨A, hrunA, hcellA, hcleanA, hidA⟩ := hmids [m] ms (by simp)
      obtain ⟨Sx, hapx, hrestx⟩ := run_cons_elim hrunA
      have hAX : A = S₁ := by
        have hnil : Sx.run [] = some A := hrestx
        rw [show Sx = S₁ from Option.some.inj (hapx.symm.trans hap)] at hnil
        obtain rfl := run_nil_elim hnil
        rfl
      rw [hAX] at hcellA hcleanA hidA
      obtain ⟨hstep, hid₁⟩ :=
        covered_clean_step hwf htwin hcover hclean hid hap hcellA hcleanA
      have hmids' : ∀ (πa πb : List Move), ms = πa ++ πb →
          ∃ Tm, S₁.run πa = some Tm ∧
            Tm.board.topOf (Sum.inr L) = some H ∧
            Tm.board.topOf (Sum.inr H) = none ∧
            Tm.board.bottomOf L = none := by
        intro πa πb hsplit
        obtain ⟨Tm, hrunπ, hcell', hcl', hidd'⟩ := hmids (m :: πa) πb (by simp [hsplit])
        obtain ⟨Sy, hapy, hresty⟩ := run_cons_elim hrunπ
        have hSy : Sy = S₁ := Option.some.inj (hapy.symm.trans hap)
        rw [hSy] at hresty
        exact ⟨Tm, hresty, hcell', hcl', hidd'⟩
      exact run_cons_intro hstep
        (ih S₁ T' (apply_wf hwf m S₁ hap) htwin hcellA hcleanA hid₁ hrest hmids')

/-- **The dodge-clearing forward leg (the safety's assembly, clean
corridor)**: a winning line whose first clearing of the covered seat is
the mate's DODGE — factorized as a corridor prefix `π₁`, the dodge, and
the tail — transfers to the exchange image: the image replays `π₁`
verbatim (the clean-corridor replay), plays the SAME dodge and lands
LITERALLY on the source's post-dodge state (the clean merge), and wins
with the source's own tail.  This is the forward half of
`sweep_covered_corner_safety` for the dodge branch; the wave-20
π₁ = [] instance `sweep_covered_corner_dodge_first_forward` above *is*
its empty-corridor special case. -/
theorem sweep_covered_corner_dodge_clearing_forward
    {st S₀ S₁ W : State} {L H : Card} {b : Base} {π₁ π₂ : List Move}
    (hwf : st.WF) (htwin : H = L.flipSuit)
    (hcover : st.board.topOf (Sum.inr L) = some H)
    (hclean : st.board.topOf (Sum.inr H) = none)
    (hid : st.board.bottomOf L = none)
    (hp₁ : st.run π₁ = some S₀)
    (hmids : ∀ (πa πb : List Move), π₁ = πa ++ πb →
      ∃ Tm, st.run πa = some Tm ∧
        Tm.board.topOf (Sum.inr L) = some H ∧
        Tm.board.topOf (Sum.inr H) = none ∧
        Tm.board.bottomOf L = none)
    (hdodge : S₀.apply (Move.pilePile H b) = some S₁)
    (hrest : S₁.run π₂ = some W) (hwin : W.isWin = true) :
    (st.exchangeTwinCargo L).solvableFrom := by
  obtain ⟨Tm, hrunT, hcell₀, hcl₀, hid₀⟩ := hmids π₁ [] (by simp)
  have hTm : Tm = S₀ := Option.some.inj (hrunT.symm.trans hp₁)
  rw [hTm] at hcell₀ hcl₀
  have hrep := covered_clean_replay π₁ st S₀ hwf htwin hcover hclean hid hp₁ hmids
  have hmerge : (S₀.exchangeTwinCargo L).apply (Move.pilePile H b) = some S₁ :=
    covered_dodge_merges_clean htwin hcell₀ hcl₀ hdodge
  have hImg : (S₀.exchangeTwinCargo L).run [Move.pilePile H b] = some S₁ :=
    run_cons_intro hmerge rfl
  exact ⟨π₁ ++ [Move.pilePile H b] ++ π₂, W,
    run_append_some (run_append_some hrep hImg) hrest, hwin⟩

/-! ### The wave-22 residue certificate: the class split + the channel map

The pin's residue is now CERTIFIED as one reachability gate and two
discipline-shaped premises, each anchored by a proved lemma below or
a decided witness state (the full statement-level analysis:
witnesses/TwinCompletionWitness.lean, sections D/E).

* **THE CLASS SPLIT (proved).**  At `visClean` states — hence at every
  `initialReachable` state (`initialReachable_visClean`) — the
  covered corner is forced into the HIDDEN class:
  `sweep_covered_corner_visClean_class_A` gives `isVis L = false`,
  `topHidden a = some L`, `board.bottomOf L = none` — the wave-20/21
  corridor premise `hid` is now a THEOREM at the reach-gated form.  The
  dual L-SEATED corner (class B: `L` visible, the mate covering it) is
  `board_edges`-legal at bare WF but `visClean`-IMPOSSIBLE — the
  mate's cover never fits the twin (`covered_corner_mate_unfit`) — so
  `run_visClean` makes it unreachable from every deal; the witness
  file's section E exhibits the WF class-B state
  (`initialReachable wstE → False` machine-checked) where the
  image's `pileStack L` channel is live while the source's is
  mate-blocked — the state family the ungated statement must still
  win (no counterexample found in three waves; both sides are
  equally stuck there, so the iff holds vacuously at the exhibit).
* **THE LICENSE-FIT HOLE (decided, why the PROVEN exchange family
  cannot seat the corner).**  The corner's covering cargo IS the mate:
  `canSitOn H L = false` kills `hfit`, and the mate's own cell is
  bare (no `z'` cargo), so `solvable_cargoTwin_exchange_licensed` /
  `_of_visClean` / the bare companion all fail premises at BOTH
  threads.  At class A the same hole reappears as the RIDER-UNMIRRORABLE
  park: `canPlace x (Sum.inr H)` holds at the source but the
  relabeled `canPlace x (Sum.inr L)` dies at the image on
  `isVis L = false` (the w15fithole license-fit shape) — decided at
  the witness.  The rider-unclean corridors therefore need the
  mod-rider correspondence (a normalization), not the licensed family.
* **THE REVEAL-CHANNEL DIVERGENCE (proved).**  At class A the
  source's `reveal` of `L`'s pile is BLOCKED by the riding mate
  (`covered_corner_reveal_blocked` reads `apply_reveal_iff`'s
  own-cell guard — a ridden boundary never flips), while the image's
  copy of the same guard reads `none`
  (`exchangeTwinCargo_flip_cover`), so THE IMAGE'S REVEAL OF `L`
  FIRES (`sweep_covered_corner_image_reveal_fires`, the ≥2-hidden
  shape; the single-hidden/anchor variant is gated by the anchor's
  freeness): the reverse leg must simulate image plays that open
  `L`'s channels early while the source's mate still parks — the
  source can only follow after moving `H` (a dodge needs a fitted
  free base; a found needs the rung).  This one channel plus the
  image's self-seated-mate found block (the dual of the forward
  found-branch below) is the whole content of old residue (iii).
* **WHAT REMAINS (the minimal premises, stated exactly).**  (i) *the
  no-park discipline at the source* — every solvable class-A corner is
  solvable by a winning line whose pre-clearing segment never parks a
  rider on `Sum.inr H`; with conjuncts 1 and 3 of `hmids` now
  derivable (`covered_corner_reveal_blocked` maintains
  `bottomOf L = none` up to the first clearing, since only the reveal
  can seat a hidden unseated card, and it is blocked precisely while
  the cover stands; the first-clearing factorization maintains the
  cover), conjunct 2 IS this premise; the general rider case is the
  mod-rider correspondence.  (ii) *the deferred-unpark of the found
  branch* — at the source's `pileStack H` clearing the image's mate is
  self-seat-frozen and must dodge; the hoped bridge seats it when the
  source's tail seats a crossed host (REFUTE-FIRST candidate: both
  crossed hosts deckStack-founded — unprobed on the engine corpus;
  static guard-reads decided at the witnesses).  (iii) *the dual of
  (i)+(ii) at the image* — the same lemma families conjugated by the
  Board conjugation kit, with the reveal channel substituting for the
  park.  With (i) both dodge branches close through the PAID
  corridor + merge (`sweep_covered_corner_dodge_clearing_forward`).
  RECOMMENDATION (wave-22, to the orchestrator): CONTINUE-THE-SIEGE —
  the reach-gate is non-vacuous (witness D: the corner is
  `State.initial` itself for any deal placing the twin pair
  consecutively atop a pile), no counterexample to the ungated
  statement was found, and the three remaining pieces are scoped
  lemma families with the corridor principle paid and reusable.  The
  census pin stays here alone. -/

/-- **The twin never fits its mate** — the license-fit hole's rank
core: `canSitOn` demands a rank gap, and the twins share the rank
(via `Card.ne_pair_of_canSitOn`'s second arm).  This is the one-line
reason the corner's covering cargo (the mate itself) can never satisfy
the licensed exchange family's `hfit`, and why every rider-level
mirror at the covered pair runs through twin-blindness instead. -/
theorem covered_corner_mate_unfit {L H : Card} (htwin : H = L.flipSuit) :
    canSitOn H L ≠ true :=
  fun h => (Card.ne_pair_of_canSitOn h).2 htwin

/-- **At `visClean` states the covered corner is the HIDDEN class-A
shape**: the covered twin is an unseated hidden reveal boundary.  The
`board_edges` audit of the cover edge admits only the buried-base
clause (the mate's own fit clause dies at the shared rank), and its
base condition then forces `L` to be some pile's `topHidden` — while a
seated `L` would make the edge a visClean violation (the unfit mate
over a visible host).  Consequences: at every `initialReachable`
corner (a) the corridor premise `hid : bottomOf L = none` HOLDS, (b)
`L`'s reveal is the pile's own next offer (and see
`covered_corner_reveal_blocked` for why it cannot fire while the mate
rides), and (c) the L-seated corner of the old plan (class B) is
unreachable — `covered_corner_mate_unfit` + `run_visClean`. -/
theorem sweep_covered_corner_visClean_class_A {st : State} {L H : Card}
    (hwf : st.WF) (hvc : st.visClean) (htwin : H = L.flipSuit)
    (hcover : st.board.topOf (Sum.inr L) = some H) :
    st.isVis L = false ∧ ∃ a, st.topHidden a = some L ∧
      st.board.bottomOf L = none := by
  have hunfit : canSitOn H L ≠ true :=
    covered_corner_mate_unfit htwin
  have hVis : st.isVis L ≠ true :=
    fun hVisL => hunfit (hvc H L hcover hVisL)
  have hVisF : st.isVis L = false := by
    cases hL : st.isVis L with
    | false => first | rfl | exact hL
    | true => exact absurd hL hVis
  have hEx : ∃ a, st.topHidden a = some L := by
    obtain ⟨-, hleg⟩ := hwf.board_edges (Sum.inr L) H hcover
    rcases hleg with ⟨a₀, t₀, rest₀, hpiles, hbase⟩ | ⟨hisL, hfit⟩
    · rcases hbase with ⟨a₁, htop⟩ | hisL2
      · exact ⟨a₁, htop⟩
      · exfalso
        have hisL2' : st.isVis L = true := hisL2
        exact hunfit (hvc H L hcover hisL2')
    · exact absurd hfit hunfit
  have hBot : st.board.bottomOf L = none := by
    cases hb : st.board.bottomOf L with
    | none => first | rfl | exact hb
    | some β =>
        exfalso
        have hisL : st.isVis L = true := by
          show (st.board.bottomOf L).isSome = true
          rw [hb]; rfl
        exact hVis hisL
  obtain ⟨a₁, htop⟩ := hEx
  exact ⟨hVisF, a₁, htop, hBot⟩

/-- **A ridden reveal boundary never flips**: at the covered corner,
the source's `reveal` of `L`'s pile cannot fire — `apply_reveal_iff`'s
bareness guard reads `L`'s OWN cell, and the mate sits there.  The
mid-corridor twin therefore stays unseated for forced reasons: until
the mate's first clearing, `L`'s only seating channel is closed.  (The
exchange image's copy of the same guard reads the swapped cell —
see `sweep_covered_corner_image_reveal_fires` for the divergence.) -/
theorem covered_corner_reveal_blocked {st : State} {a : Anchor} {L H : Card}
    (hcover : st.board.topOf (Sum.inr L) = some H)
    (htop : st.topHidden a = some L) :
    st.apply (Move.reveal a) = none := by
  cases hap : st.apply (Move.reveal a) with
  | none => first | rfl | exact hap
  | some st' =>
      exfalso
      rw [apply_reveal_iff] at hap
      obtain ⟨r, bd, htoph, hbar, -⟩ := hap
      rw [Option.some.inj (htoph.symm.trans htop)] at hbar
      rw [hcover] at hbar
      exact absurd hbar (by simp)

/-- **THE IMAGE'S REVEAL OF THE COVERED TWIN FIRES** — the reverse
leg's extra channel, formalized: at a `visClean` (hence reachable)
class-A corner whose boundary's under-card is a `Sum.inr d` (the
≥2-hidden shape; the single-hidden/anchor variant is gated by the
anchor cell's own freeness), the source cannot reveal `L` (ridden —
`covered_corner_reveal_blocked`), but the exchange image CAN: the guard
reads the swapped cell (bare, by `exchangeTwinCargo_flip_cover`), the
under-card's cell is forced-bare at WF (a hidden non-boundary base
justifies no edge: neither `topHidden` nor `bottomOf` disjunct lives),
and `L`'s image `bottomOf` is still `none`.  The reverse leg of the
safety must simulate exactly these image-early-`L` plays. -/
theorem sweep_covered_corner_image_reveal_fires {st : State}
    {L H d : Card} {a : Anchor}
    (hwf : st.WF) (hvc : st.visClean) (htwin : H = L.flipSuit)
    (hcover : st.board.topOf (Sum.inr L) = some H)
    (hHseat : st.board.topOf (Sum.inr H) = none)
    (hbase : st.hiddenBase a = Sum.inr d)
    (htop : st.topHidden a = some L) :
    ∃ st', (st.exchangeTwinCargo L).apply (Move.reveal a) = some st' := by
  obtain ⟨-, -, -, hbotL⟩ :=
    sweep_covered_corner_visClean_class_A hwf hvc htwin hcover
  have hdL : d ≠ L := hiddenBase_ne_topHidden hwf hbase htop
  -- the under-card d of the boundary L: hidden, hence never the
  -- (visible) mate, and its cell forced-bare
  have hdmem : d ∈ st.hidden a := by
    obtain ⟨pre, hpre⟩ := hiddenBase_split hbase htop
    rw [hpre]; simp
  have hdH : d ≠ H := by
    intro hcon
    have hdmem' : H ∈ st.hidden a := by rw [← hcon]; exact hdmem
    have hbH : st.board.bottomOf H = some (Sum.inr L) :=
      (Board.bottomOf_eq st.board H (Sum.inr L)).mpr hcover
    have hisH : st.isVis H = true := by
      show (st.board.bottomOf H).isSome = true
      rw [hbH]; rfl
    exact hwf.vis_not_hidden H hisH a hdmem'
  have hdBare : st.board.topOf (Sum.inr d) = none := by
    cases hX : st.board.topOf (Sum.inr d) with
    | none => first | rfl | exact hX
    | some X =>
        exfalso
        obtain ⟨-, hlegX⟩ := hwf.board_edges (Sum.inr d) X hX
        rcases hlegX with ⟨a', t', rest', hpilesX, hcondX⟩ | ⟨hisX, hfitX⟩
        · rcases hcondX with ⟨a'', htop''⟩ | hisX2
          · have hdP1 : d ∈ st.deal.piles a :=
              List.take_subset (st.depths a) (st.deal.piles a) hdmem
            have hdP2 : d ∈ st.deal.piles a'' :=
              List.take_subset (st.depths a'') (st.deal.piles a'')
                (mem_of_getLast htop'')
            have haa : a'' = a := Deal.piles_disj hwf.deal_wf hdP2 hdP1
            rw [haa] at htop''
            have hcon : d = L :=
              Option.some.inj (htop''.symm.trans htop)
            exact hdL hcon
          · have hisd : st.isVis d = true := hisX2
            exact hwf.vis_not_hidden d hisd a hdmem
        · have hisd : st.isVis d = true := hisX
          exact hwf.vis_not_hidden d hisd a hdmem
  -- the image's three guard reads, then the firing via the iff
  have hfree : (st.exchangeTwinCargo L).board.topOf (Sum.inr d) = none := by
    rw [State.exchangeTwinCargo_board, Board.exchangeTwin_topOf]
    have hσ : Base.swapTwin L (Sum.inr d) = Sum.inr d := by
      show Sum.inr (Card.swapTwin L d) = Sum.inr d
      rw [Card.swapTwin_of_ne hdL (by rw [← htwin]; exact hdH)]
    rw [hσ]; exact hdBare
  have hhb : st.hiddenBase a = Sum.inr d := hbase
  have hfreeB : (st.exchangeTwinCargo L).board.topOf (st.hiddenBase a)
      = none := by rw [hhb]; exact hfree
  have hbot : (st.exchangeTwinCargo L).board.bottomOf L = none := by
    rw [State.exchangeTwinCargo_board, Board.bottomOf_exchangeTwin, hbotL]
    rfl
  obtain ⟨bd', hatt'⟩ := Option.ne_none_iff_exists'.mp
    ((Board.attach_eq_some_iff _ (st.hiddenBase a) L).mpr ⟨hfreeB, hbot⟩)
  have hbar : (st.exchangeTwinCargo L).board.topOf (Sum.inr L) = none := by
    rw [State.exchangeTwinCargo_board, Board.exchangeTwin_topOf]
    show st.board.topOf (Sum.inr (Card.swapTwin L L)) = none
    rw [Card.swapTwin_self_left, ← htwin]
    exact hHseat
  refine ⟨{ st.exchangeTwinCargo L with
      board := bd',
      depths := fun a' => if a' = a then st.depths a - 1 else st.depths a' },
    apply_reveal_iff.mpr ⟨L, bd', htop, hbar, hatt', rfl⟩⟩

/-- **§6.5's semantic safety at the covered corner (planned)**: the
covered corner and its exchange image — the two identity-resolutions
of the ambiguous word — are solvability-equivalent, so the sweep's
deterministic lowest-first choice can never UNIQUELY lose a win at
the AMBIGUOUS corner.  Reduces to the both-occupied exchange family
at the covered seat.
PLAN RE-ANCHORED (wave 20; three named pieces PAID below the original
(1)/(2), plus the dodge convergence engine): (1) **PAID**
`sweep_covered_corner_deal_adjacent` (:2613). (2) **KEYSTONE PAID**
`vacated_covered_cell_imp_mate_move` (:2638), and its run-audit
remainder is NOW PAID TOO: `sweep_covered_corner_wins_stack_L` +
`sweep_covered_corner_first_clearing` — every winning line stacks the
covered twin (§12.1 at the corner via `sweep_covered_corner_L_tableau`),
so a first clearing of the covered cell exists and is the mate's own
move. (3) **THE DODGE CONVERGENCE, PAID** — `covered_dodge_converges` /
`covered_dodge_merges_clean; the π₁ = [] instance is CLOSED as
`sweep_covered_corner_dodge_first_forward`. WAVE 21: piece (i) PAID on
the CLEAN CORRIDOR (`covered_clean_step` + `covered_clean_replay` +
`sweep_covered_corner_dodge_clearing_forward`: the forward leg is
closed whenever the first clearing is the mate's DODGE along a
corridor-clean prefix). WAVE 22 — THE CERTIFIED RESIDUE MAP (the
certificate section above; every remaining piece named, anchored,
and recommended): (i) *the rider-unclean corridors* — premised at the
no-park discipline (the w15fithole license-fit shape decides why the
relabel cannot mirror: `canPlace x (inr L)` dies on the unseated
host at the hidden class, while class B is visClean-unreachable);
(ii) *the `pileStack H` clearing* — the deferred-unpark bridge or the
deckStack-founded-crossed-hosts witness (REFUTE-FIRST on the engine
corpus, unprobed); (iii) *the reverse leg* — THE REVEAL-CHANNEL
DIVERGENCE is its whole new content
(`covered_corner_reveal_blocked` / `_image_reveal_fires`), the dual
of the found-branch's self-seat block; the class split
(`sweep_covered_corner_visClean_class_A`) licenses the `hid`
corridor premise for free at every reachable corner. Every sorry
carries this plan; the census pin stays here alone. -/
theorem State.sweep_covered_corner_safety {st : State} {L H : Card}
    (hwf : st.WF)
    (htwin : H = L.flipSuit)
    (hcover : st.board.topOf (Sum.inr L) = some H)
    (hHseat : st.board.topOf (Sum.inr H) = none) :
    st.solvableFrom ↔ (st.exchangeTwinCargo L).solvableFrom := sorry



