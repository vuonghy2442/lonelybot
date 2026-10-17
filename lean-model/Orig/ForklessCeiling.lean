import Orig.ForkAscent
import Orig.ForkCensus
import Orig.LowSlab

/-!
# Orig.ForklessCeiling — THE FORKLESS-CLASS CEILING (the ascent's twin dream)

The owner's ASCEND-CEILING-UNIQUENESS program: IN A FORKLESS MACRO
CLASS, the maximal slide-stacking ascent's exhaustion endpoint is
UNIQUE UP TO BARE CARGO EXCHANGE.  The descent twin of this dream
was REFUTED (2026-10-13, `Orig/ForkDescent.lean`: the buried-host
expose-raise board and the owner's one-seat/two-reds
resource-contention board — read there, §3R/§3R2) — and the lesson
is banked here from line one: FALSIFIER-FIRST, in GRADES, with the
probe leaf (`Orig/ForklessCeilingProbe.lean`) deciding before any
proof starts.  THIS leaf owns the frozen statements; the boards own
the verdicts.

* **§0a THE CARGO ORBIT FACTORING** (owner decisions, relayed
  2026-10-13): `CargoLetter` — the DUMB closure generator (any
  `tabToTab` letter; the burn/reveal arms get excluded BY THEOREM,
  not by definition); `CargoPlay` — the inductive play at the
  letter alphabet; `BareCargoEquiv A B` — both-ways plays (the
  `RevEqW` shape); `cargoSetoid`/`CargoOrbit` — the orbit factoring
  on the `sameOrbitSetoid` precedent (rev-orientation kept); the
  zone-fix row (`CargoPlay_fix_zone`).
* **§0b THE DETECTOR BRIDGE** — `classCensus_false_forkless`: the
  decidable no-go side — `classCensusB st = false` at a `WF` head
  certifies `Forkless st` (cites `class_forks_decidable`, never
  re-derives).
* **§0c THE EXCLUSION THEOREM** — the HIDDEN-TOTAL monotone kills
  the reveal arms of any both-ways pair (a reveal drops a hidden
  deck's head and no tabToTab letter ever restocks one) — THIS
  HALF LANDED: the monotone kernels ride the public Table-2 rows,
  the composite-position kernel `cargoLeg_revealfree` freezes each
  leg with a return, and `cargo_revealfree_of_equiv` reads both
  witness plays reveal-free wholesale over the `CargoPlayRF`
  vehicle; then the VACANT-SEAT monotone (on the reveal-free pass,
  the only `-1` on topped piles is the seated burn and nothing
  adds one) kills the burn arms — priced.  The surviving alphabet
  is exactly the two witness-grade arms — the under-armed seated
  slide (`census_tabToTab_under`'s identity-cell economy) and the
  clean king-corner (`census_tabToTab_inl`'s census-neutral row)
  — packaged as the constructive vehicle `CargoShuffle` (with the
  burn half, the priced residue).
* **§0d THE MIRRORS AND THE REFINEMENT** — every surviving leg is
  one-move reversible IN PLACE (the back-slide onto the exposed
  identity-cell seat; the king-run's return to the emptied source
  anchor), so a `CargoShuffle` IS a `ShufflePlayW`, and
  `cargo_refines_sameOrbit` lands: at `WF` the dumb closure, once
  both-ways, REFINES the macro class (each bare leg witness-grade;
  the `Quotient.sound` bridge is staged with the μ-packaging §2).
* **§0e THE FIX THEOREM** `cargo_fix` — what bare exchange can never
  touch: the founds verbatim (hence every `rungAt`), the stock, the
  waste, the deal size, the per-anchor hidden decks — the cargo-fix
  data the Grade-B probe checks first.
* **§1 THE FLOATING STRUCTURE LAYER** — `Vacant`/`FreeKing`/
  `ParentOf`/`Floater` and the kernels: the run-granularity
  reading (a run's HEAD floats/kings/locks, the tail rides rigid),
  the parent-twin hop arithmetic (`fc_cell_pair`,
  `fc_contention_is_twin` — contention for ONE host is always a
  twin pair), the cover-seat drag (`fc_cover_seat_twin`), the
  king-bottom bar.  The characterization IFF is frozen as the named
  residue `cargo_structure_characterization` with its route.
* **§2 THE GRADED CEILING CONJECTURES** — the three frozen grades
  of the owner's dream plus the μ-DESCENT packaging: **GRADE-A**
  `ceiling_gradeA` (rung-vector uniqueness of maximal ascent
  endpoints in a forkless class), **GRADE-B** `ceiling_gradeB` (the
  flagship: the endpoints are `BareCargoEquiv`), **GRADE-C**
  `ceiling_gradeC` (state-unique — EXPECTED FALSE, documented, not
  chased), and `ceiling_descends`/`ceiling_descent_imp` (the
  map-descent form: μ determined iff Grade-B, the descent direction
  proved).  No §2 proof starts before the probe leaf's verdicts;
  the routes record what the verdicts license.

House compliance: additive leaf (`Orig.ForkAscent` +
`Orig.ForkCensus` + `Orig.LowSlab` — the AscentRun/AscentMove/
AscentStuck vocabulary, the classCensusB/CensusPass detector and
the class algebra, the pull-mirror and the witness machinery, all
transitively); NO mathlib; every fresh head audited in the battery;
zero `Classical.choice` (all splits ride `Bool`/`Option`/decidable
reads; `exfalso`/`absurd` before `omega` at non-arithmetic goals);
frozen statements with complete priced routes; the private kit rows
are per-file copies per the house dedup discipline.  No git commits
from this leaf. -/

set_option linter.unusedVariables false

/-! ## §0a. The cargo orbit factoring: the dumb closure -/

/-- **THE CARGO LETTER** — the DUMB closure generator (owner
decision 2026-10-13): any `tabToTab` letter, no arm filter.  The
burn/reveal arms are excluded BY THEOREM (§0c), not by this
definition. -/
def CargoLetter (st : State) (m : Move) : Prop :=
  ∃ (c : Card) (b : Base), m = Move.tabToTab c b

/-- **THE CARGO PLAY** — a legal play every letter of which is a
cargo letter. -/
inductive CargoPlay : State → List Move → State → Prop
  | nil (st : State) : CargoPlay st [] st
  | cons {st s₁ W : State} {m : Move} {ρ : List Move}
      (hlet : CargoLetter st m) (hstep : State.step st m = some s₁)
      (hrest : CargoPlay s₁ ρ W) :
      CargoPlay st (m :: ρ) W

/-- A cargo play is, in particular, a legal run. -/
theorem CargoPlay_run {st : State} : ∀ {ρ : List Move} {W : State},
    CargoPlay st ρ W → st.run ρ = some W := by
  intro ρ W h
  induction h with
  | nil s => rfl
  | cons _ hstep _ ih =>
      simp only [State.run, hstep]
      exact ih

/-- Cargo plays concatenate (the transitivity engine of the closure). -/
theorem CargoPlay_append {a b : State} : ∀ {l₁ : List Move},
    CargoPlay a l₁ b → ∀ {l₂ : List Move} {c : State},
    CargoPlay b l₂ c → CargoPlay a (l₁ ++ l₂) c := by
  intro l₁ h
  induction h with
  | nil s => intro l₂ c h₂; exact h₂
  | @cons st s₁ b' m ρ' hlet hstep hrest ih =>
      intro l₂ c h₂
      rw [List.cons_append]
      exact .cons hlet hstep (ih h₂)

/-- **THE BARE CARGO EQUIVALENCES** `BareCargoEquiv` — the owner's
bare-cargo exchange: two states joined by tabToTab-only plays in
both directions (the `RevEqW` both-ways shape; single-direction
reachability is symmetric by §0c's exclusion plus §0d's mirrors —
every surviving leg carries its one-move return — but the
definition stays canonical and dumb).  Rungs and founds can never
move under it (§0e); what it exchanges is the face-up ARRANGEMENT
within the cargo-fix slack. -/
def BareCargoEquiv (A B : State) : Prop :=
  ∃ (τ : List Move), CargoPlay A τ B ∧
    ∃ (ρ : List Move), CargoPlay B ρ A

/-- **THE CARGO ORBIT SETOID** — the orbit factoring on the
`sameOrbitSetoid` precedent: the relation is the rev-closure
(`r a b := BareCargoEquiv b a`), matching the house orientation of
the macro state's own instance. -/
instance cargoSetoid : Setoid State where
  r a b := BareCargoEquiv b a
  iseqv :=
    ⟨fun a => ⟨[], .nil a, [], .nil a⟩,
      fun h => by obtain ⟨τ, hτ, ρ, hρ⟩ := h; exact ⟨ρ, hρ, τ, hτ⟩,
      fun h k => by
        obtain ⟨τ, hτ, ρ, hρ⟩ := h
        obtain ⟨ν, hν, μ, hμ⟩ := k
        exact ⟨ν ++ τ, CargoPlay_append hν hτ, ρ ++ μ,
          CargoPlay_append hρ hμ⟩⟩

/-- Positions modulo bare cargo exchange. -/
abbrev CargoOrbit := Quotient cargoSetoid

/-- The per-leg paperwork: a fired cargo letter touches no zone
outside the piles (`setPile` writes no foundation, `putRun` keeps
the four non-pile fields). -/
private theorem fc_step_zone {st s' : State} {c : Card} {b : Base}
    (hstep : State.step st (Move.tabToTab c b) = some s') :
    s'.found = st.found ∧ s'.stock = st.stock ∧
      s'.waste = st.waste ∧ s'.drawStep = st.drawStep := by
  obtain ⟨a, hhold, hcp, hrunne, hs⟩ := step_tabToTab_inv hstep
  rw [hs]
  have hR := putRun_keep
    (st := st.setPile a (Pile.afterRunRemoved (st.piles a)
      (below c (st.piles a).faceUp)))
    (run := fromCard c (st.piles a).faceUp) (b := b)
  rw [hR.1, hR.2.1, hR.2.2.1, hR.2.2.2]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- **THE ZONE FIX OF A CARGO PLAY** — no cargo play of any letter
alphabet writes a foundation, a zone, or the deal size. -/
theorem CargoPlay_fix_zone {st W : State} {ρ : List Move}
    (h : CargoPlay st ρ W) :
    W.found = st.found ∧ W.stock = st.stock ∧ W.waste = st.waste ∧
      W.drawStep = st.drawStep := by
  induction h with
  | nil s => exact ⟨rfl, rfl, rfl, rfl⟩
  | @cons st s₁ W' m ρ' hlet hstep hrest ih =>
      obtain ⟨c, b, hcb⟩ := hlet
      rw [hcb] at hstep
      exact ⟨ih.1.trans (fc_step_zone hstep).1,
        ih.2.1.trans (fc_step_zone hstep).2.1,
        ih.2.2.1.trans (fc_step_zone hstep).2.2.1,
        ih.2.2.2.trans (fc_step_zone hstep).2.2.2⟩

/-! ## §0b. The detector bridge: the decidable no-go side -/

/-- **THE FORKLESS READ** — the owner's scope condition: the
state's macro CLASS carries no fork (the detector's no-go side). -/
def Forkless (st : State) : Prop := ¬ ClassForkHeaded st

/-- **THE DECIDABLE NO-GO CERTIFICATE** — at a `WF` state, a
silent 26-board census (`classCensusB st = false`) certifies the
class forkless: `class_forks_decidable`'s necessity direction
demands a passing `CensusPass` candidate of every class head, and
the census probe reads the whole 26-board Bool.  The probe boards
cite this row; none re-derives the detector. -/
theorem classCensus_false_forkless {st : State} (hwf : st.WF)
    (h : classCensusB st = false) : Forkless st := by
  intro hhead
  obtain ⟨x, hcand, -⟩ := (class_forks_decidable hwf).mp hhead
  rw [(classCensusB_true_iff st).2 ⟨x, hcand⟩] at h
  exact absurd h (by simp)

/-! ## §0c. The exclusion kernels: the degenerate arms never ride a
both-ways pair -/

/-- **THE HIDDEN TOTAL** — the number of face-down tableau cards
(the reveal-arm monotone's counter; the per-file private copy of
the program's `hiddenTotal` measure). -/
private def fcHiddenTotal (st : State) : Nat :=
  Anchor.all.foldl (fun n a => n + (st.piles a).hidden.length) 0

/-- The two sum shapes of the hidden deck agree (the per-file kit
row every reading below cites): a flat-mapped concatenation length
IS the fold's running sum. -/
private theorem fc_hidden_sum (f : Anchor → List Card) :
    ∀ (l : List Anchor) (acc : Nat),
      (l.flatMap f).length + acc =
        l.foldl (fun n a => n + (f a).length) acc := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons x t ih =>
      intro acc
      simp only [List.flatMap_cons, List.length_append, List.foldl_cons]
      have h := ih (acc + (f x).length)
      omega

/-- **THE BRIDGE ROW** — the per-file copy reads the program's
`hiddenTotal` verbatim (the delegation seam: this leaf cites the
public Table-2 monotone below, never re-derives it). -/
private theorem fcHiddenTotal_eq (st : State) :
    fcHiddenTotal st = hiddenTotal st := by
  have h := fc_hidden_sum (fun a => (st.piles a).hidden) Anchor.all 0
  unfold fcHiddenTotal hiddenTotal
  omega

/-- The per-`runOK` king bar (per-file kit copy of the adjacent-fit
discipline): a legal face-up run cannot place a king above a card
(`canSitOn` would demand a rank thirteen), so at `WF` a king is
always its pile's face-up BOTTOM — the definitional edge the owner's
`FreeKing` no-hidden condition rides (a king with hidden behind it
can still lift, reveal/burn-armed; a king with a face-up below-card
cannot exist at all). -/
private theorem fc_runOK_king_first {K : Card} (hK : K.rank = Rank.king) :
    ∀ (pre rest : List Card), runOK (pre ++ K :: rest) = true → pre = [] := by
  intro pre
  induction pre with
  | nil => intro rest _; rfl
  | cons x t ih =>
      intro rest h
      cases t with
      | nil =>
          rw [List.cons_append, List.nil_append] at h
          have hpair : runOK (x :: K :: rest) =
              (canSitOn K x && runOK (K :: rest)) := rfl
          rw [hpair, Bool.and_eq_true] at h
          obtain ⟨hr1, -⟩ := h
          obtain ⟨hrank, -⟩ := (canSitOn_eq K x).mp hr1
          have hK13 : K.rank.toIdx = 12 := by rw [hK]; rfl
          have hlt := Rank.toIdx_lt x.rank
          exfalso
          omega
      | cons y t' =>
          rw [List.cons_append, List.cons_append] at h
          have hpair : runOK (x :: y :: (t' ++ K :: rest)) =
              (canSitOn y x && runOK (y :: (t' ++ K :: rest))) := rfl
          rw [hpair, Bool.and_eq_true] at h
          obtain ⟨-, h2⟩ := h
          have hfalse : y :: t' = [] := ih rest h2
          exact absurd hfalse (by simp)

/-- **THE GLOBAL HIDDEN MONOTONE** — NO move of the game restocks a
face-down tableau card: the pile surgeries only drop or keep hidden
heads (the reveal arms), the two-zone and foundation letters touch
no hidden deck.  This is the monotone the reveal-exclusion rides;
proved as the public Table-2 row (`Orig.Irreversible`'s
`hiddenTotal_step`) read through the per-file bridge — the leaf
cites, never re-derives. -/
theorem fcHiddenTotal_step {st s' : State} {m : Move}
    (hstep : State.step st m = some s') :
    fcHiddenTotal s' ≤ fcHiddenTotal st := by
  simp only [fcHiddenTotal_eq]
  exact hiddenTotal_step hstep

/-- **THE PLAY-SIDE HIDDEN MONOTONE** — along any legal play the
hidden total never rises; `Mono`'s walk combinator composes the
per-step row. -/
theorem fcHiddenTotal_play {st : State} : ∀ (play : List Move) (w : State),
    st.run play = some w → fcHiddenTotal w ≤ fcHiddenTotal st := by
  intro play w hrun
  simp only [fcHiddenTotal_eq]
  exact mono_run hiddenTotal (fun s m s' h => hiddenTotal_step h) hrun

/-- **THE REVEAL-ARMED LEG NEVER RETURNS** — a fired `tabToTab`
whose source is stripped (empty below-content over a nonempty
hidden deck) consumes a hidden head, and no continuation ever
restocks one: the leg is a COMMITMENT (`irreversibleAt`), so it can
never ride a both-ways pair (§0c's first half, at the per-leg
grade; the second half — the seated-burn arm — is priced in the
exclusion theorem's route below).  Proved as the public standing
pattern (`hiddenTotal_step_tabToTab_reveal` + `Mono`'s
`irr_of_desc`, the `journey_tabToTab_never_reveal` read pulled at
the stronger `irreversibleAt` grade). -/
theorem fc_revealleg_irreversible {st s' : State} {c : Card} {b : Base} {a : Anchor}
    (hhold : st.pileHolding c = some a)
    (hbel : below c (st.piles a).faceUp = [])
    (hhid : (st.piles a).hidden ≠ [])
    (hstep : State.step st (Move.tabToTab c b) = some s') :
    irreversibleAt st (Move.tabToTab c b) := by
  have hdrop : hiddenTotal s' < hiddenTotal st := by
    have h := hiddenTotal_step_tabToTab_reveal hstep hhold hbel hhid
    omega
  exact irr_of_desc hiddenTotal (fun s m s'' h => hiddenTotal_step h) hstep hdrop

/-- The class-exit corollary of the reveal bar (the banked
`commit_exits_class`, consumed at the leg's own grade). -/
theorem fc_revealleg_exits {st s' : State} {c : Card} {b : Base} {a : Anchor}
    (hhold : st.pileHolding c = some a)
    (hbel : below c (st.piles a).faceUp = [])
    (hhid : (st.piles a).hidden ≠ [])
    (hstep : State.step st (Move.tabToTab c b) = some s') :
    ¬ sameOrbitSetoid.r st s' :=
  commit_exits_class hstep (fc_revealleg_irreversible hhold hbel hhid hstep)

/-! ## §0c.1 The reveal half, landed: the composite-position read

`cargo_clean_of_equiv`'s route item 1, in full: no reveal-armed leg
rides a both-ways pair of the dumb closure.  Three grades: the join
kit (the per-file copy of the `p_run_append` precedent), the
composite-position kernel (a leg with a return is reveal-free —
`irreversibleAt` reads the grain-free no-return bar), and the
play-side vehicle, closed wholesale over either witness play of a
`BareCargoEquiv` by return-induction: each leg's pre-state returns
via its own tail plays joined through the endpoint to the origin,
then the origin's one-move re-entry. -/

/-- The run-append compose (the per-file private kit copy of the
`p_run_append` precedent, `Orig/LowSlab.lean`; the forward-facing
companion of Play's public split reader `run_append_split`) — the
join every returning-cycle read below runs through. -/
private theorem fc_run_append : ∀ (a : State) (A B : List Move) (z w : State),
    a.run A = some z → z.run B = some w → a.run (A ++ B) = some w := by
  intro a A
  induction A generalizing a with
  | nil =>
      intro B z w h1 h2
      have hz : some a = some z := h1
      injection hz with hc
      subst hc
      exact h2
  | cons m rest ih =>
      intro B z w h1 h2
      obtain ⟨a₁, hs, hr⟩ := State.run_cons h1
      have h3 := ih a₁ B z w hr h2
      rw [List.cons_append]
      show (match State.step a m with
        | some st' => st'.run (rest ++ B)
        | none => none) = some w
      rw [hs]
      exact h3

/-- **A LEG WITH A RETURN IS REVEAL-FREE** — the composite-position
kernel at the single-leg grade: a fired `tabToTab` whose successor
runs back to its own pre-state — by any return play, any grain —
cannot be reveal-armed (the reveal bar is the grain-free no-return
commitment; the exclusion theorem's first half). -/
theorem cargoLeg_revealfree {P s₁ : State} {c : Card} {b : Base}
    (hstep : State.step P (Move.tabToTab c b) = some s₁) :
    ∀ (back : List Move), s₁.run back = some P →
      ∀ (a : Anchor), P.pileHolding c = some a →
        below c (P.piles a).faceUp ≠ [] ∨ (P.piles a).hidden = [] := by
  intro back hback a hhold
  by_cases hbel : below c (P.piles a).faceUp = []
  · by_cases hhid : (P.piles a).hidden = []
    · exact Or.inr hhid
    · exact absurd hback
        (fc_revealleg_irreversible hhold hbel hhid hstep s₁ back hstep)
  · exact Or.inl hbel

/-- **THE REVEAL-FREE PASS VEHICLE** — a cargo play every leg of
which is reveal-free: at each fired `tabToTab c b`, whatever pile
holds `c`, either the below-window is nonempty (an under-armed seat
survives) or the hidden deck under it is empty (nothing consumed).
The exclusion theorem's item-3 packaging re-inducts over this
pass; the burn half's route composes on it. -/
inductive CargoPlayRF : State → List Move → State → Prop
  | nil (st : State) : CargoPlayRF st [] st
  | cons {st s₁ W : State} {c : Card} {b : Base} {ρ : List Move}
      (hstep : State.step st (Move.tabToTab c b) = some s₁)
      (hrf : ∀ (a : Anchor), st.pileHolding c = some a →
        below c (st.piles a).faceUp ≠ [] ∨ (st.piles a).hidden = [])
      (hrest : CargoPlayRF s₁ ρ W) :
      CargoPlayRF st (Move.tabToTab c b :: ρ) W

/-- The pass is, in particular, a cargo play. -/
theorem CargoPlayRF_cargo {st W : State} {ρ : List Move}
    (h : CargoPlayRF st ρ W) : CargoPlay st ρ W := by
  induction h with
  | nil s => exact .nil s
  | @cons st s₁ W' c b ρ' hstep hrf hrest ih =>
      exact .cons ⟨c, b, rfl⟩ hstep ih

/-- **THE PLAY-GRADE REVEAL FREEZING** — every leg of a cargo play
whose endpoint runs back to its own origin passes the reveal-free
grade: each leg sits on a returning cycle (its own tail plays
joined through the endpoint to the origin, then the origin's
one-move re-entry), so the grain-free no-return bar applies at
each leg in turn. -/
theorem CargoPlayRF_of_return {S W : State} {τ : List Move}
    (h : CargoPlay S τ W) :
    ∀ (back : List Move), W.run back = some S → CargoPlayRF S τ W := by
  induction h with
  | nil _ => intro _ _; exact .nil _
  | @cons st s₁ W' m ρ' hlet hstep hrest ih =>
      intro back hback
      obtain ⟨c, b, hm⟩ := hlet
      subst hm
      exact .cons hstep
        (cargoLeg_revealfree hstep (ρ' ++ back)
          (fc_run_append s₁ ρ' back W' st (CargoPlay_run hrest) hback))
        (ih (back ++ [Move.tabToTab c b])
          (fc_run_append W' back [Move.tabToTab c b] st s₁ hback
            (run_one hstep)))

/-- **THE REVEAL HALF OF THE EXCLUSION THEOREM** — no reveal-armed
leg rides either witness play of a bare both-ways cargo pair: both
passes read reveal-free, wholesale.  (The burn half remains the
priced residue below; the surviving alphabet's packaging lands on
this vehicle.) -/
theorem cargo_revealfree_of_equiv {A B : State} {τ ρ : List Move}
    (hτ : CargoPlay A τ B) (hρ : CargoPlay B ρ A) :
    CargoPlayRF A τ B ∧ CargoPlayRF B ρ A :=
  ⟨CargoPlayRF_of_return hτ ρ (CargoPlay_run hρ),
   CargoPlayRF_of_return hρ τ (CargoPlay_run hτ)⟩

/-! ## §0c.2 The burn half's foundation kit

The topped-piles counter and its fold kit (the vacant-seat monotone's
meter), plus the leg-surgery rows the burn half's per-leg delta lemmas
read: the below/fromCard split of the moved run and the head-shape of
the run a fired `tabToTab` carries.  Designed read-only in the third
succession's recon pass; landed here kernel-first per the priced
route.  The `inr` mid-search stabilizer and the reveal/bare
restock rows land with the delta lemmas in the follow-up batch. -/

/-- **THE TOPPED TOTAL** — the number of anchors whose face-up deck
is nonempty (the vacant-seat counter; the kit twin of
`fcHiddenTotal`: the reveal half rides the hidden decks, the burn
half rides the face-up emptiness census). -/
private def fcToppedTotal (st : State) : Nat :=
  Anchor.all.foldl (fun n a => n + if (st.piles a).faceUp = [] then 0 else 1) 0

/-- The fold congruence: pointwise-equal summands give equal folds
(the per-file fold kit, first row). -/
private theorem fcTopFold_congr {F G : Anchor → Nat} :
    ∀ (l : List Anchor), (∀ y ∈ l, F y = G y) →
      ∀ acc, List.foldl (fun n a => n + F a) acc l
        = List.foldl (fun n a => n + G a) acc l := by
  intro l
  induction l with
  | nil => intro _ acc; rfl
  | cons x t ih =>
      intro h acc
      have hxy : F x = G x := h x (by simp)
      have ht : ∀ y ∈ t, F y = G y :=
        fun y hy => h y (List.mem_cons_of_mem x hy)
      simp only [List.foldl_cons]
      rw [hxy]
      exact ih ht (acc + G x)

/-- The fold is affine in a trailing summand (the fold kit's shift
row: what makes the single-exception induction close). -/
private theorem fcTopFold_shift {l : List Anchor} {F : Anchor → Nat} :
    ∀ acc d, List.foldl (fun n a => n + F a) (acc + d) l
      = List.foldl (fun n a => n + F a) acc l + d := by
  induction l with
  | nil => intro acc d; rfl
  | cons x t ih =>
      intro acc d
      simp only [List.foldl_cons]
      rw [show (acc + d) + F x = (acc + F x) + d from by omega]
      exact ih (acc + F x) d

/-- **THE SINGLE-EXCEPTION WORKHORSE** — a fold whose summand
changes at exactly one (nodup-witnessed) member differs by exactly
that member's delta: the row every per-leg topped-delta lemma rides.
(The nodup premise is discharged at `Anchor.all` by the public
`Anchor.all_nodup`.) -/
private theorem fcTopFold_oneChange {F G : Anchor → Nat} (a : Anchor) {d : Nat}
    (hrest : ∀ y, y ≠ a → F y = G y) (hwa : F a + d = G a) :
    ∀ (l : List Anchor), l.Nodup → a ∈ l →
      ∀ acc, List.foldl (fun n y => n + F y) acc l + d
        = List.foldl (fun n y => n + G y) acc l := by
  intro l
  induction l with
  | nil => intro _ ha _; exact absurd ha (by simp)
  | cons x t ih =>
      intro hnd ha acc
      simp only [List.foldl_cons]
      by_cases hxa : x = a
      · rw [hxa]
        have hxa' : a = x := hxa.symm
        have hnt : a ∉ t := fun hmem =>
          (List.nodup_cons.mp hnd).1 (hxa' ▸ hmem)
        have hc : List.foldl (fun n y => n + G y) (acc + G a) t
            = List.foldl (fun n y => n + F y) (acc + G a) t :=
          fcTopFold_congr (l := t)
            (fun y hy => (hrest y (fun hya => hnt (hya ▸ hy))).symm)
            (acc + G a)
        rw [hc, show acc + G a = (acc + F a) + d from by omega]
        exact (fcTopFold_shift (l := t) (F := F) (acc + F a) d).symm
      · have hxAG : F x = G x := hrest x hxa
        have hat : a ∈ t :=
          (List.mem_cons.mp ha).elim (fun hax => absurd hax.symm hxa)
            (fun hmem => hmem)
        rw [← hxAG]
        exact ih ((List.nodup_cons.mp hnd).2) hat (acc + F x)

/-- The moved run splits at its head card: everything below it,
then the run from it (the per-file copy of the split row, the
`Orig/ForkStateS.lean` precedent's idiom verbatim). -/
private theorem fc_below_join (c : Card) :
    ∀ (l : List Card), l = below c l ++ fromCard c l := by
  intro l
  induction l with
  | nil => rfl
  | cons x t ih =>
      by_cases hxt : x = c
      · rw [hxt, below_cons_self, fromCard_cons_self]
        rfl
      · rw [below_cons_ne t hxt, fromCard_cons_ne t hxt, List.cons_append]
        exact congrArg (x :: ·) ih

/-- A nonempty run read from `c` starts at `c` (the fromCard head
shape: the window's membership pin for fired legs). -/
private theorem fc_fromCard_head {c : Card} :
    ∀ (l : List Card), fromCard c l ≠ [] →
      ∃ rest, fromCard c l = c :: rest := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons x t ih =>
      intro h
      by_cases hxc : x = c
      · rw [hxc, fromCard_cons_self]; exact ⟨t, rfl⟩
      · rw [fromCard_cons_ne t hxc] at h ⊢
        exact ih h

/-- The bare read: removing the WHOLE face-up over an empty hidden
deck empties the pile outright (the seated burn's source-shape, the
revealTop []-arm returning the emptied record). -/
private theorem fc_afterRunRemoved_bare {p : Pile} (hhid : p.hidden = []) :
    Pile.afterRunRemoved p [] = ⟨[], []⟩ := by
  simp only [Pile.afterRunRemoved, hhid, Pile.revealTop]

/-- The reveal read: removing the whole face-up over a NONEMPTY
hidden deck restocks a face-up head (the reveal arms keep the source
topped — never a burn). -/
private theorem fc_afterRunRemoved_reveal {p : Pile} (hhid : p.hidden ≠ []) :
    (Pile.afterRunRemoved p []).faceUp ≠ [] := by
  intro hcontra
  rcases ph : p.hidden with _ | ⟨h, t⟩
  · exact absurd ph hhid
  · simp only [Pile.afterRunRemoved, Pile.revealTop, ph] at hcontra
    simp at hcontra

/-- The under read: a removal leaving nonempty below-content keeps
exactly that content face-up (the under-armed slides' source-shape).
Public-flavored duplicate check: the cons case is the def's own arm;
the Classify row of the same name was consulted and cited instead of
duplicated where this file needed only this narrow read. -/
private theorem fc_afterRunRemoved_faceUp_ne {p : Pile} {pre : List Card}
    (hne : pre ≠ []) :
    (Pile.afterRunRemoved p pre).faceUp = pre := by
  cases pre with
  | nil => exact absurd rfl hne
  | cons x t => rfl

/-! ### §0c.3 The per-leg topped deltas

The burn half's leg table at the inr grade: the under-armed slide
and the reveal restock preserve the topped count exactly (the source
keeps a nonempty face-up head, the target was topped by its host);
the seated burn — bare source over an empty hidden deck, no WF — is
the one strict drop.  The king-corner exchange, the aggregate and
the play-side rows follow in the next batch. -/

/-- **THE UNDER-ARMED SLIDE PRESERVES THE TOPPED COUNT.** -/
private theorem fcTopped_slide_step {st s₁ : State} {c z : Card} {a : Anchor}
    (hstep : State.step st (Move.tabToTab c (Sum.inr z)) = some s₁)
    (hhold : st.pileHolding c = some a)
    (hbelow : below c (st.piles a).faceUp ≠ []) :
    fcToppedTotal s₁ = fcToppedTotal st := by
  obtain ⟨a₀, hh₀, -, -, hs'⟩ := step_tabToTab_inv hstep
  have ha : a₀ = a := Option.some.inj (hh₀.symm.trans hhold)
  subst ha
  obtain ⟨M, hMdef⟩ : ∃ M : State,
      M = st.setPile a₀ (Pile.afterRunRemoved (st.piles a₀)
        (below c (st.piles a₀).faceUp)) := ⟨_, rfl⟩
  rw [← hMdef] at hs'
  have hself : M.piles a₀
      = Pile.afterRunRemoved (st.piles a₀) (below c (st.piles a₀).faceUp) := by
    rw [hMdef]
    exact setPile_afterRunRemoved_piles_self st a₀ c
  have hother : ∀ a' ≠ a₀, M.piles a' = st.piles a' := by
    intro a' hne'
    rw [hMdef]
    exact setPile_afterRunRemoved_piles_ne st a₀ c a' hne'
  have hstfu : (st.piles a₀).faceUp ≠ [] := by
    rw [fc_below_join c (st.piles a₀).faceUp]
    intro hcon
    cases hb : below c (st.piles a₀).faceUp with
    | nil => exact hbelow hb
    | cons x t =>
        rw [hb, List.cons_append] at hcon
        exact absurd hcon (by simp)
  have ha0fu : (Pile.afterRunRemoved (st.piles a₀)
      (below c (st.piles a₀).faceUp)).faceUp = below c (st.piles a₀).faceUp :=
    fc_afterRunRemoved_faceUp_ne hbelow
  rw [hs']
  simp only [fcToppedTotal]
  cases hz : M.pileOfTop z with
  | none =>
      rw [putRun_inr_none hz]
      refine fcTopFold_congr (l := Anchor.all) (fun a' _ => ?_) 0
      by_cases haa : a₀ = a'
      · subst haa
        rw [hself, ha0fu, if_neg hbelow, if_neg hstfu]
      · rw [hother a' (fun h => haa h.symm)]
  | some k =>
      have hq2 : M.topOf k = some z :=
        of_decide_eq_true (firstWhere_sound (p := fun a' =>
          decide (M.topOf a' = some z)) hz)
      have hkm : (M.piles k).faceUp ≠ [] := by
        intro hcon
        have htopnone : M.topOf k = none := by
          show lastOf (M.piles k).faceUp = none
          rw [hcon]
          rfl
        rw [htopnone] at hq2
        cases hq2
      have hkS : (st.piles k).faceUp ≠ [] := by
        by_cases hke : k = a₀
        · rw [hke]; exact hstfu
        · intro hcon
          exact hkm (by rw [hother k hke]; exact hcon)
      simp only [putRun_piles_inr M (fromCard c (st.piles a₀).faceUp) z k hz]
      refine fcTopFold_congr (l := Anchor.all) (fun a' _ => ?_) 0
      by_cases hka : k = a'
      · subst hka
        simp only [if_pos (rfl : k = k)]
        have hL : ((M.piles k).faceUp ++ fromCard c (st.piles a₀).faceUp) ≠ [] := by
          intro hc2
          cases hbk : (M.piles k).faceUp with
          | nil => exact hkm hbk
          | cons x t =>
              rw [hbk, List.cons_append] at hc2
              exact absurd hc2 (by simp)
        show (if ((M.piles k).faceUp ++ fromCard c (st.piles a₀).faceUp) = []
              then 0 else 1)
          = (if (st.piles k).faceUp = [] then 0 else 1)
        rw [if_neg hL, if_neg hkS]
      · rw [if_neg (c := a' = k) (fun h => hka h.symm)]
        by_cases haa : a₀ = a'
        · subst haa
          rw [hself, ha0fu, if_neg hbelow, if_neg hstfu]
        · rw [hother a' (fun h => haa h.symm)]

/-- **THE REVEAL RESTOCK PRESERVES THE TOPPED COUNT.** -/
private theorem fcTopped_reveal_step {st s₁ : State} {c z : Card} {a : Anchor}
    (hstep : State.step st (Move.tabToTab c (Sum.inr z)) = some s₁)
    (hhold : st.pileHolding c = some a)
    (hbel : below c (st.piles a).faceUp = [])
    (hhid : (st.piles a).hidden ≠ []) :
    fcToppedTotal s₁ = fcToppedTotal st := by
  obtain ⟨a₀, hh₀, -, hfr, hs'⟩ := step_tabToTab_inv hstep
  have ha : a₀ = a := Option.some.inj (hh₀.symm.trans hhold)
  subst ha
  obtain ⟨M, hMdef⟩ : ∃ M : State,
      M = st.setPile a₀ (Pile.afterRunRemoved (st.piles a₀)
        (below c (st.piles a₀).faceUp)) := ⟨_, rfl⟩
  rw [← hMdef] at hs'
  have hself : M.piles a₀
      = Pile.afterRunRemoved (st.piles a₀) (below c (st.piles a₀).faceUp) := by
    rw [hMdef]
    exact setPile_afterRunRemoved_piles_self st a₀ c
  have hother : ∀ a' ≠ a₀, M.piles a' = st.piles a' := by
    intro a' hne'
    rw [hMdef]
    exact setPile_afterRunRemoved_piles_ne st a₀ c a' hne'
  have hstfu : (st.piles a₀).faceUp ≠ [] := by
    rw [fc_below_join c (st.piles a₀).faceUp, hbel, List.nil_append]
    exact hfr
  have ha0ne : (Pile.afterRunRemoved (st.piles a₀)
      (below c (st.piles a₀).faceUp)).faceUp ≠ [] := by
    rw [hbel]
    exact fc_afterRunRemoved_reveal hhid
  rw [hs']
  simp only [fcToppedTotal]
  cases hz : M.pileOfTop z with
  | none =>
      rw [putRun_inr_none hz]
      refine fcTopFold_congr (l := Anchor.all) (fun a' _ => ?_) 0
      by_cases haa : a₀ = a'
      · subst haa
        rw [hself]
        show (if (Pile.afterRunRemoved (st.piles a₀)
              (below c (st.piles a₀).faceUp)).faceUp = [] then 0 else 1)
          = (if (st.piles a₀).faceUp = [] then 0 else 1)
        rw [if_neg ha0ne, if_neg hstfu]
      · rw [hother a' (fun h => haa h.symm)]
  | some k =>
      have hq2 : M.topOf k = some z :=
        of_decide_eq_true (firstWhere_sound (p := fun a' =>
          decide (M.topOf a' = some z)) hz)
      have hkm : (M.piles k).faceUp ≠ [] := by
        intro hcon
        have htopnone : M.topOf k = none := by
          show lastOf (M.piles k).faceUp = none
          rw [hcon]
          rfl
        rw [htopnone] at hq2
        cases hq2
      have hkS : (st.piles k).faceUp ≠ [] := by
        by_cases hke : k = a₀
        · rw [hke]; exact hstfu
        · intro hcon
          exact hkm (by rw [hother k hke]; exact hcon)
      simp only [putRun_piles_inr M (fromCard c (st.piles a₀).faceUp) z k hz]
      refine fcTopFold_congr (l := Anchor.all) (fun a' _ => ?_) 0
      by_cases hka : k = a'
      · subst hka
        simp only []
        have hL : ((M.piles k).faceUp ++ fromCard c (st.piles a₀).faceUp) ≠ [] := by
          intro hc2
          cases hbk : (M.piles k).faceUp with
          | nil => exact hkm hbk
          | cons x t =>
              rw [hbk, List.cons_append] at hc2
              exact absurd hc2 (by simp)
        show (if ((M.piles k).faceUp ++ fromCard c (st.piles a₀).faceUp) = []
              then 0 else 1)
          = (if (st.piles k).faceUp = [] then 0 else 1)
        rw [if_neg hL, if_neg hkS]
      · rw [if_neg (c := a' = k) (fun h => hka h.symm)]
        by_cases haa : a₀ = a'
        · subst haa
          rw [hself]
          show (if (Pile.afterRunRemoved (st.piles a₀)
                (below c (st.piles a₀).faceUp)).faceUp = [] then 0 else 1)
            = (if (st.piles a₀).faceUp = [] then 0 else 1)
          rw [if_neg ha0ne, if_neg hstfu]
        · rw [hother a' (fun h => haa h.symm)]

/-- **THE SEATED BURN IS THE ONE STRICT DROP** — a fired `tabToTab`
whose bare source sits over an EMPTY hidden deck moves the WHOLE
face-up content onto the target: the source empties for good (no
reveal restock), and no WF premise is needed — the mid-pile tops
nothing, so no search can re-seat the run at the source. -/
private theorem fcTopped_burn_step {st s₁ : State} {c z : Card} {a : Anchor}
    (hstep : State.step st (Move.tabToTab c (Sum.inr z)) = some s₁)
    (hhold : st.pileHolding c = some a)
    (hbel : below c (st.piles a).faceUp = [])
    (hhid : (st.piles a).hidden = []) :
    fcToppedTotal s₁ + 1 = fcToppedTotal st := by
  obtain ⟨a₀, hh₀, -, hfr, hs'⟩ := step_tabToTab_inv hstep
  have ha : a₀ = a := Option.some.inj (hh₀.symm.trans hhold)
  subst ha
  obtain ⟨M, hMdef⟩ : ∃ M : State,
      M = st.setPile a₀ (Pile.afterRunRemoved (st.piles a₀)
        (below c (st.piles a₀).faceUp)) := ⟨_, rfl⟩
  rw [← hMdef] at hs'
  have hself : M.piles a₀
      = Pile.afterRunRemoved (st.piles a₀) (below c (st.piles a₀).faceUp) := by
    rw [hMdef]
    exact setPile_afterRunRemoved_piles_self st a₀ c
  have hother : ∀ a' ≠ a₀, M.piles a' = st.piles a' := by
    intro a' hne'
    rw [hMdef]
    exact setPile_afterRunRemoved_piles_ne st a₀ c a' hne'
  have hstfu : (st.piles a₀).faceUp ≠ [] := by
    rw [fc_below_join c (st.piles a₀).faceUp, hbel, List.nil_append]
    exact hfr
  have ha0bare : M.piles a₀ = ⟨[], []⟩ := by
    rw [hMdef]
    rw [setPile_afterRunRemoved_piles_self st a₀ c, hbel]
    exact fc_afterRunRemoved_bare hhid
  have ha0none : M.topOf a₀ = none := by
    show lastOf (M.piles a₀).faceUp = none
    rw [ha0bare]
    rfl
  rw [hs']
  simp only [fcToppedTotal]
  cases hz : M.pileOfTop z with
  | none =>
      rw [putRun_inr_none hz]
      refine fcTopFold_oneChange a₀ (fun y hya => ?_) ?_
        Anchor.all Anchor.all_nodup (Anchor.mem_all a₀) 0
      · by_cases hyy : a₀ = y
        · exact absurd hyy.symm hya
        · rw [hother y (fun h => hyy h.symm)]
      · show (if (M.piles a₀).faceUp = [] then 0 else 1) + 1
          = (if (st.piles a₀).faceUp = [] then 0 else 1)
        rw [ha0bare]
        show (if ([] : List Card) = [] then 0 else 1) + 1
          = (if (st.piles a₀).faceUp = [] then 0 else 1)
        rw [if_pos rfl, if_neg hstfu]
  | some k =>
      have hq2 : M.topOf k = some z :=
        of_decide_eq_true (firstWhere_sound (p := fun a' =>
          decide (M.topOf a' = some z)) hz)
      have hke : k ≠ a₀ := by
        intro hcon
        rw [hcon] at hq2
        rw [ha0none] at hq2
        cases hq2
      have hkm : (M.piles k).faceUp ≠ [] := by
        intro hcon
        have htopnone : M.topOf k = none := by
          show lastOf (M.piles k).faceUp = none
          rw [hcon]
          rfl
        rw [htopnone] at hq2
        cases hq2
      have hkS : (st.piles k).faceUp ≠ [] := by
        intro hcon
        exact hkm (by rw [hother k hke]; exact hcon)
      simp only [putRun_piles_inr M (fromCard c (st.piles a₀).faceUp) z k hz]
      refine fcTopFold_oneChange a₀ (fun y hya => ?_) ?_
        Anchor.all Anchor.all_nodup (Anchor.mem_all a₀) 0
      · by_cases hyy : a₀ = y
        · exact absurd hyy.symm hya
        · by_cases hyk : k = y
          · subst hyk
            simp only []
            have hL : ((M.piles k).faceUp ++ fromCard c (st.piles a₀).faceUp) ≠ [] := by
              intro hc2
              cases hbk : (M.piles k).faceUp with
              | nil => exact hkm hbk
              | cons x t =>
                  rw [hbk, List.cons_append] at hc2
                  exact absurd hc2 (by simp)
            show (if ((M.piles k).faceUp ++ fromCard c (st.piles a₀).faceUp) = []
                  then 0 else 1)
              = (if (st.piles k).faceUp = [] then 0 else 1)
            rw [if_neg hL, if_neg hkS]
          · rw [if_neg (c := y = k) (fun h => hyk h.symm),
              hother y (fun h => hyy h.symm)]
      · rw [if_neg (c := a₀ = k) (fun hconk => hke hconk.symm)]
        show (if (M.piles a₀).faceUp = [] then 0 else 1) + 1
          = (if (st.piles a₀).faceUp = [] then 0 else 1)
        rw [ha0bare]
        show (if ([] : List Card) = [] then 0 else 1) + 1
          = (if (st.piles a₀).faceUp = [] then 0 else 1)
        rw [if_pos rfl, if_neg hstfu]

/-- **THE KING-CORNER EXCHANGE PRESERVES THE TOPPED COUNT** — a
king-headed run landing on an empty seat from a BARE source (empty
below-content, empty hidden deck) swaps the topped seat: the source
empties outright, the empty landing fills with the nonempty run.
WF-free given the premises — the WF-aggregate row derives the
source's bareness from `fc_runOK_king_first`. -/
private theorem fcTopped_corner_step {st s₁ : State} {K : Card} {a a₀ : Anchor}
    (hstep : State.step st (Move.tabToTab K (Sum.inl a₀)) = some s₁)
    (hhold : st.pileHolding K = some a)
    (hbel : below K (st.piles a).faceUp = [])
    (hhid : (st.piles a).hidden = []) :
    fcToppedTotal s₁ = fcToppedTotal st := by
  obtain ⟨a₁, hh₀, hcp, hfr, hs'⟩ := step_tabToTab_inv hstep
  have ha : a₁ = a := Option.some.inj (hh₀.symm.trans hhold)
  subst ha
  obtain ⟨hemp, -⟩ := canPlace_inl hcp
  obtain ⟨-, hf0⟩ := (Pile.isEmpty_eq (st.piles a₀)).mp hemp
  obtain ⟨M, hMdef⟩ : ∃ M : State,
      M = st.setPile a₁ (Pile.afterRunRemoved (st.piles a₁)
        (below K (st.piles a₁).faceUp)) := ⟨_, rfl⟩
  rw [← hMdef] at hs'
  have hself : M.piles a₁
      = Pile.afterRunRemoved (st.piles a₁) (below K (st.piles a₁).faceUp) := by
    rw [hMdef]
    exact setPile_afterRunRemoved_piles_self st a₁ K
  have hother : ∀ a' ≠ a₁, M.piles a' = st.piles a' := by
    intro a' hne'
    rw [hMdef]
    exact setPile_afterRunRemoved_piles_ne st a₁ K a' hne'
  have ha0M : (M.piles a₁).faceUp = [] := by
    rw [hself, hbel]
    show (Pile.afterRunRemoved (st.piles a₁) []).faceUp = ([] : List Card)
    rw [fc_afterRunRemoved_bare hhid]
  have hstfu : (st.piles a₁).faceUp ≠ [] := by
    rw [fc_below_join K (st.piles a₁).faceUp, hbel, List.nil_append]
    exact hfr
  rw [hs']
  simp only [fcToppedTotal]
  -- exchange, step 1: M vs st at a₁ only (the bare source drops one)
  have hwa1 : (if (M.piles a₁).faceUp = [] then 0 else 1) + 1
      = (if (st.piles a₁).faceUp = [] then 0 else 1) := by
    rw [ha0M, if_pos rfl, if_neg hstfu]
  have hrest1 : ∀ y, y ≠ a₁ →
      (if (M.piles y).faceUp = [] then 0 else 1)
      = (if (st.piles y).faceUp = [] then 0 else 1) := fun y hya => by
    rw [hother y hya]
  have hstep1 : List.foldl (fun n a' => n +
      if (M.piles a').faceUp = [] then 0 else 1) 0 Anchor.all + 1
      = List.foldl (fun n a' => n +
          if (st.piles a').faceUp = [] then 0 else 1) 0 Anchor.all :=
    fcTopFold_oneChange a₁ hrest1 hwa1 Anchor.all Anchor.all_nodup
      (Anchor.mem_all a₁) 0
  -- exchange, step 2: s₁ vs M at a₀ only (the empty landing gains one)
  have ha₀ne : a₀ ≠ a₁ := fun hcon => hstfu (hcon ▸ hf0)
  have hfa0M : (M.piles a₀).faceUp = [] := by
    rw [hother a₀ ha₀ne]
    exact hf0
  have hwa2 : (if (M.piles a₀).faceUp = [] then 0 else 1) + 1
      = if ((M.putRun (fromCard K (st.piles a₁).faceUp) (Sum.inl a₀)).piles a₀).faceUp = []
        then 0 else 1 := by
    rw [putRun_piles_inl_self M (fromCard K (st.piles a₁).faceUp) a₀]
    show (if (M.piles a₀).faceUp = [] then 0 else 1) + 1
      = if (fromCard K (st.piles a₁).faceUp : List Card) = [] then 0 else 1
    rw [if_pos hfa0M, if_neg hfr]
  have hrest2 : ∀ y, y ≠ a₀ →
      (if (M.piles y).faceUp = [] then 0 else 1)
      = if ((M.putRun (fromCard K (st.piles a₁).faceUp) (Sum.inl a₀)).piles y).faceUp = []
        then 0 else 1 := by
    intro y hya
    rw [putRun_piles_inl_ne M (fromCard K (st.piles a₁).faceUp) a₀ y hya]
  have hstep2 : List.foldl (fun n a' => n +
      if (M.piles a').faceUp = [] then 0 else 1) 0 Anchor.all + 1
      = List.foldl (fun n a' => n +
          if ((M.putRun (fromCard K (st.piles a₁).faceUp) (Sum.inl a₀)).piles a').faceUp = []
            then 0 else 1) 0 Anchor.all :=
    fcTopFold_oneChange a₀ hrest2 hwa2 Anchor.all Anchor.all_nodup
      (Anchor.mem_all a₀) 0
  omega

/-- **THE RF LEG-LEVEL MONOTONE** — at a WF state, every reveal-free
`tabToTab` leg keeps the topped count or strictly drops it: the
under-armed slide and the reveal restock preserve it; the seated burn
is the strict drop; the inl case is the bare king-corner by force —
`fc_runOK_king_first` empties the below-content at WF, and the RF
premise then empties the hidden deck. -/
private theorem fcToppedRF_step {st s₁ : State} {c : Card} {b : Base} {a : Anchor}
    (hwf : st.WF)
    (hstep : State.step st (Move.tabToTab c b) = some s₁)
    (hhold : st.pileHolding c = some a)
    (hrf : below c (st.piles a).faceUp ≠ [] ∨ (st.piles a).hidden = []) :
    fcToppedTotal s₁ ≤ fcToppedTotal st := by
  cases b with
  | inl a₀ =>
      obtain ⟨a₁, hh₀, hcp, hfr, -⟩ := step_tabToTab_inv hstep
      have ha : a₁ = a := Option.some.inj (hh₀.symm.trans hhold)
      subst ha
      obtain ⟨hemp, hK⟩ := canPlace_inl hcp
      obtain ⟨rest, hKrest⟩ := fc_fromCard_head (st.piles a₁).faceUp hfr
      have hjoin : (st.piles a₁).faceUp
          = below c (st.piles a₁).faceUp ++ c :: rest := by
        rw [← hKrest]
        exact fc_below_join c (st.piles a₁).faceUp
      have hbel : below c (st.piles a₁).faceUp = [] :=
        fc_runOK_king_first hK _ rest (by
          rw [← hjoin]
          exact hwf.runOK_of a₁)
      have hhid : (st.piles a₁).hidden = [] := by
        rcases hrf with hbl | hhn
        · exact absurd hbel hbl
        · exact hhn
      exact Nat.le_of_eq (fcTopped_corner_step hstep hhold hbel hhid)
  | inr z =>
      rcases hrf with hbl | hhn
      · exact Nat.le_of_eq (fcTopped_slide_step hstep hhold hbl)
      · by_cases hbel : below c (st.piles a).faceUp = []
        · have hb := fcTopped_burn_step hstep hhold hbel hhn
          omega
        · exact Nat.le_of_eq (fcTopped_slide_step hstep hhold hbel)

/-- **THE RF PLAY-SIDE MONOTONE** — along any reveal-free cargo play
from a WF origin the topped counter never rises: per-leg
`fcToppedRF_step` composed through the vehicle's induction, the
WF-thread carried by `step_wf`. -/
private theorem fcToppedRF_play : ∀ (st : State) (τ : List Move) (W : State),
    st.WF → CargoPlayRF st τ W → fcToppedTotal W ≤ fcToppedTotal st := by
  intro st τ W hwf h
  induction h with
  | nil st => exact Nat.le_refl _
  | @cons st s₁ W c b ρ hstep hrf hrest ih =>
      obtain ⟨a, hh, -, -, -⟩ := step_tabToTab_inv hstep
      have h1 := fcToppedRF_step hwf hstep hh (hrf a hh)
      have h2 := ih (step_wf hwf hstep)
      omega

/-- **A SEATED BURN WITH AN RF RETURN NEVER RIDES** — the composite-
position kernel of the burn half, mirroring `cargoLeg_revealfree`:
a fired seated burn (bare source over an empty hidden deck) strictly
drops the topped counter, and no reveal-free return play can ever
raise it back — so a leg carrying an RF return cannot be a burn
(the no-return bar, grain-free over the vehicle's plays). -/
theorem cargoLeg_burnfree {st s₁ : State} {c z : Card} {a : Anchor}
    (hwf : st.WF)
    (hstep : State.step st (Move.tabToTab c (Sum.inr z)) = some s₁)
    (hhold : st.pileHolding c = some a)
    (hbel : below c (st.piles a).faceUp = [])
    (hhid : (st.piles a).hidden = []) :
    ∀ (back : List Move), ¬ CargoPlayRF s₁ back st := by
  intro back hback
  have hdrop := fcTopped_burn_step hstep hhold hbel hhid
  have hrise := fcToppedRF_play s₁ back st (step_wf hwf hstep) hback
  omega

/-! **THE EXCLUSION THEOREM** `cargo_clean_of_equiv` [H — THE NAMED
RESIDUE OF THIS §0c] — the degenerate arms never ride a both-ways
pair of the dumb closure: every leg of either witness play is
reveal-free (first half) and burn-free (second half), so the
surviving alphabet is exactly the two witness-grade arms — the
UNDER-ARMED SEATED SLIDE (below ≠ []; `census_tabToTab_under`'s
identity-cell economy) and the CLEAN KING-CORNER
(`census_tabToTab_inl`'s king-headed census-neutral row).

ROUTE (the reveal half LANDED above; the burn half and the final
packaging priced):

1. THE REVEAL HALF — LANDED IN FULL, §0c.1: the kernel monotone
   family (`fcHiddenTotal_step`/`fcHiddenTotal_play`, the public
   Table-2 delegation through `fcHiddenTotal_eq`), the per-leg bar
   `fc_revealleg_irreversible` (`irreversibleAt`, the grain-free
   no-return commitment), the composite-position kernel
   `cargoLeg_revealfree` (a leg with any return never consumes a
   hidden head), and the vehicle closure: `CargoPlayRF_of_return`
   freezes each leg by return-induction — each leg's pre-state
   returns via its own tail plays joined through the endpoint to
   the origin, then the origin's one-move re-entry — so
   `cargo_revealfree_of_equiv` reads both witness plays of any
   `BareCargoEquiv` reveal-free, wholesale.
2. THE BURN HALF — the same composite at the VACANT-SEAT counter:
   after the reveal-free pass the only `tabToTab` letter that
   drops the number of topped piles is the seated burn (below =
   []: source vanishes with no replacement; under-arms transfer a
   top; the clean king-corner transfers a top; the under-armed
   `inl` lifter that would ADD a top cannot exist at `WF` —
   `fc_runOK_king_first` above: a king is its pile's face-up
   bottom), and nothing ADDS one, so a returning cycle meters
   zero burns.
3. THE PACKAGING — re-induct the two passes into a clean-play
   vehicle (the under constructor with the below ≠ [] premise,
   the king constructor with the bare-source premise), which
   §0d's mirrors then read as `ShufflePlayW`s. -/

/-! ## §0d. The mirrors, the refinement, and the fix

**THE RUNG FACE OF THE FIX** — bare cargo exchange can never move a
rung: both witness plays agree on the foundations verbatim (hence
on every `rungAt`, componentwise).  This is the Grade-B probe's
first check, at theorem grade. -/

theorem cargo_fix_rungs {A B : State} (h : BareCargoEquiv A B) :
    A.found = B.found ∧ ∀ (σ : Suit), rungAt A σ = rungAt B σ := by
  obtain ⟨τ, hτ, ρ, hρ⟩ := h
  have hz₁ := CargoPlay_fix_zone hτ
  refine ⟨hz₁.1.symm, ?_⟩
  intro σ
  show (A.found σ).length = (B.found σ).length
  rw [hz₁.1]

/- **THE ONE-MOVE CARGO MIRRORS** [H-mini, THE §0d NAMED KIT] —
every surviving letter of the exclusion's alphabet carries its
return in place: the under-armed slide returns onto the exposed
identity-cell seat (`census_tabToTab_under`'s y ≡ z cell row is
the fit arithmetic; the exact-pile restore is the
`ascent_cover_slide_fork` one-move-restore pattern, re-landed here
at the letter grade), and the clean king-corner returns onto the
emptied source anchor (`census_tabToTab_inl`'s own king-headed
premises).  The kit assembles: a clean cargo play is a
`ShufflePlayW` (per-leg mirror + induction), hence
`cargo_refines_sameOrbit : A.WF → BareCargoEquiv A B →
sameOrbitSetoid.r A B` — the dumb closure, once both-ways,
REFINES the macro class at `WF` — and the refinement map
`cargoOrbit_to_sameOrbit` rides the `Quotient.sound` bridge staged
with §2's μ-packaging (the global extension off the `WF` fragment
is the priced corner: the under-armed `inl` lifter exists only
there).  Frozen here as the named residue; the probe boards never
fly outside `WF`. -/

/-! ## §0e. The floating structure layer (the owner's concept,
run-granularity resolution) -/

/-- **THE VACANT PILE** — no hidden deck, and either fully empty or
topped by a LONE king (at `WF` a king-topped pile is always
the singleton run: nothing fits under a king —
`fc_runOK_king_first`). -/
def Vacant (st : State) (a : Anchor) : Prop :=
  (st.piles a).hidden = [] ∧
    ((st.piles a).faceUp = [] ∨
      ∃ (K : Card), (st.piles a).faceUp = [K] ∧ K.rank = Rank.king)

/-- **THE FREE KING** — a lone king topping a bare pile: the only
face-up BOTTOM that can ever move by a clean cargo letter (every
other bottom either reveals or burns — both excluded on a
both-ways pair). -/
def FreeKing (st : State) (K : Card) : Prop :=
  K.rank = Rank.king ∧ ∃ (a : Anchor),
    (st.piles a).faceUp = [K] ∧ (st.piles a).hidden = []

/-- **THE PARENT READ** — `p` is the card directly below face-up
`c` in its pile. -/
def ParentOf (st : State) (c p : Card) : Prop :=
  ∃ (a : Anchor) (pre rest : List Card),
    (st.piles a).faceUp = pre ++ p :: c :: rest

/-- **THE FLOATER** (the owner's concept) — a face-up card whose
own twin is ABSENT from the face-up (the twin-absent cell: with
both cards of a cell live they contest the same two parent slots
and obstruct each other's hops — the contended-cell corner,
documented and priced in the characterization, never silently
assumed away), and both its fitting parents (the two legal bases,
rank-one up, opposite family) are present face-up.  A floater's
clean moves are exactly the parent-twin hops: its run re-parents
from one parent to the other whenever the other TOPS a pile. -/
def Floater (st : State) (c : Card) : Prop :=
  (∃ (a : Anchor), c ∈ (st.piles a).faceUp) ∧
    (∀ (a : Anchor), c.twin ∉ (st.piles a).faceUp) ∧
    (∀ (p : Card), p.rank.toIdx + 1 = c.rank.toIdx ∧
        p.suit.color ≠ c.suit.color →
      ∃ (a : Anchor), p ∈ (st.piles a).faceUp)

/-- **THE FIT-CELL ALGEBRA** — two cards of the same color family
and rank index are the same card or twins (the banked
`census_pair_named` read through the color-family split). -/
theorem fc_cell_pair {c d : Card}
    (hcol : c.suit.color = d.suit.color)
    (hrk : c.rank.toIdx = d.rank.toIdx) :
    d = c ∨ d = c.twin := by
  have hfam : d.suit = c.suit ∨ d.suit = c.twin.suit := by
    rcases c with ⟨cs, cr⟩
    rcases d with ⟨ds, dr⟩
    cases cs <;> cases ds <;>
      simp_all [Suit.twin, Suit.color, Card.twin]
  exact census_pair_named hfam hrk.symm

/-- **THE CONTENTION IS ALWAYS A TWIN PAIR** — two cards fitting
the one HOST are same-index same-family: the one-seat/two-consumers
split that killed the descent twin can only be staged by TWIN
contenders.  At `WF` both contenders face-up makes the pair mobile,
so the ascent's full-time no-eat guard declines BOTH raises
forever (face-up-ness proves persistent along ascent runs per the
banked `ascent_pair_persists` pattern) — the rescue mechanism the
(i)-contention board's verdict dates. -/
theorem fc_contention_is_twin {u v z : Card}
    (hfitu : canSitOn u z = true) (hfitv : canSitOn v z = true) :
    v = u ∨ v = u.twin := by
  obtain ⟨hu1, hu2⟩ := (canSitOn_eq u z).mp hfitu
  obtain ⟨hv1, hv2⟩ := (canSitOn_eq v z).mp hfitv
  refine fc_cell_pair (by
    cases hu : u.suit.color <;>
      cases hv : v.suit.color <;>
        cases hzc : z.suit.color <;> simp_all) (by omega)

/-- **THE COVER-SEAT DRAG** — a seated slide that buries a host `z`
drags its own exposed below-seat into `z`'s CELL (the
`census_tabToTab_under` identity-cell arithmetic): the only
reversibly-buryable cards come with their cover's seat-mate — the
covered host's twin — face-up.  This is the rigidity heart the
Grade-A route rides: a hot, guard-free cover target cannot be
reversibly buried, because its burial would demand its twin
face-up, and both-twins-face-up IS the guard's MobileTwin freeze. -/
theorem fc_cover_cell {e y z : Card}
    (hy : canSitOn e y = true) (hz : canSitOn e z = true) :
    y.suit.color = z.suit.color ∧ y.rank.toIdx = z.rank.toIdx := by
  obtain ⟨hy1, hy2⟩ := (canSitOn_eq e y).mp hy
  obtain ⟨hz1, hz2⟩ := (canSitOn_eq e z).mp hz
  refine ⟨by
    cases hyc : y.suit.color <;>
      cases hzc : z.suit.color <;>
        cases hec : e.suit.color <;> simp_all, ?_⟩
  omega

/-! ## §1f. The characterization iff (the owner's structure theorem,
header-promised; the statement frozen here) -/

/-- **THE SAME CARGO FIX** — the closure's invariants: foundations,
stock, waste, and every pile's hidden deck.  `CargoPlay_fix_zone`
carries each conjunct per leg, so `BareCargoEquiv` implies the
fix; the fix is the fiber inside which the floating moves act. -/
def SameCargoFix (A B : State) : Prop :=
  A.found = B.found ∧ A.stock = B.stock ∧ A.waste = B.waste ∧
    ∀ (a : Anchor), (A.piles a).hidden = (B.piles a).hidden

/-- **THE ELEMENTARY FLOATING MOVES** — the owner's two connection
kinds, at run-head granularity (the tail rides rigid in both):

* the FREE-KING HOP — a lone king over a bare pile re-lands on a
  fully bare pile (the clean king-corner of §0c's surviving
  alphabet; its mirror is the return hop);
* the FLOATER RE-PARENT — a floater's run, seated on one fitting
  parent, re-lands on the OTHER parent (the parent-twin hop; its
  mirror is the reverse hop; the twin-absent premise of `Floater`
  keeps the target seat obstruction-free). -/
inductive FloatingMove : State → State → Prop
  | kingHop {S T : State} {K : Card} {a b : Anchor}
      (hfree : FreeKing S K)
      (hsrc : (S.piles a).faceUp = [K] ∧ (S.piles a).hidden = [])
      (htgt : (S.piles b).faceUp = [] ∧ (S.piles b).hidden = [] ∧ a ≠ b)
      (hstep : S.run [Move.tabToTab K (Sum.inl b)] = some T) :
      FloatingMove S T
  | floaterHop {S T : State} {c p₁ p₂ : Card}
      (hfl : Floater S c)
      (hfit : canSitOn c p₁ = true ∧ canSitOn c p₂ = true)
      (hseat : ParentOf S c p₁)
      (htgt : ∃ (b : Anchor), S.pileOfTop p₂ = some b)
      (hstep : ∃ (b : Base), S.run [Move.tabToTab c b] = some T ∧
                ParentOf T c p₂) :
      FloatingMove S T

/-- **THE FLOATING JOIN** — the reflexive-transitive closure of the
elementary moves. -/
inductive FloatingJoin : State → State → Prop
  | refl (S : State) : FloatingJoin S S
  | step {S T U : State} (h : FloatingMove S T)
      (ih : FloatingJoin T U) : FloatingJoin S U

/-- **THE CARGO STRUCTURE CHARACTERIZATION** [H, THE §1F NAMED
RESIDUE — the header-promised iff, statement frozen] — two states
are `BareCargoEquiv` EXACTLY WHEN they share the cargo fix AND are
joined by the elementary floating moves: the dumb closure, once
both-ways, IS the skeleton (the fix) plus the floating connections
(free kings over the bare-pile graph, floaters between their two
parents), nothing else.

ROUTE (the two arms, each priced):

* (⟸) GENERATEDNESS — every elementary move is a CargoLetter leg
  with its one-move in-place mirror (§0d's kit: the king-corner
  return onto the emptied source anchor, the floater re-parent's
  back-return); induction over `FloatingJoin` lifts to the
  both-ways closure.  Straightforward assembly.
* (⟹) RIGIDITY — the real content: every surviving closure letter
  (the §0c alphabet: the under-armed seated slide, the king-corner)
  DECOMPOSES into elementary moves.  Case one: a king-corner letter
  is exactly the `kingHop`.  Case two: a seated slide whose head c
  has a TWIN-PRESENT cell is LOCKED — its both-ways survival forces
  the seat-pair and identity-cell arithmetic (`fc_cover_cell`: the
  cover drag is a twin; `fc_contention_is_twin`: the one-host race
  is twin-only) so the slide is its own mirror's inverse and joins
  trivially.  Case three: a seated slide whose head is twin-absent
  with both parents live IS the `floaterHop` (the `Floater`
  definition discharges the premises); the tail rides rigid by
  the run move's suffix discipline.  The hidden corner: a
  twin-absent head whose OTHER parent is NOT live — the slide has
  no mirror home and dies on the both-ways pass (the exclusion
  algebra), so it never appears in a `BareCargoEquiv` pair.  This
  decomposition is the theorem's heart and the one priced residue. -/

theorem cargo_structure_characterization (A B : State) :
    BareCargoEquiv A B ↔ SameCargoFix A B ∧ FloatingJoin A B := by
  sorry

/-! ## §2. The graded ceiling conjectures (frozen; the probe leaf
decides before any proof starts) -/

/-- **THE MAXIMAL-ASCENT ENDPOINT** — a state a maximal stacking run
exhausts to (ForkAscent's `AscentRun` to its `AscentStuck` end). -/
def MaxAscentEndpoint (st W : State) : Prop :=
  ∃ (ρ : List Move), AscentRun st ρ W ∧ AscentStuck W

/-- **GRADE-A** `ceiling_gradeA` [H, CARRIES — the mission's
rung-vector uniqueness] — in a forkless macro class, any two
in-class endpoints of maximal ascents from a `WF` start agree on
EVERY rung.

ROUTE (per the probe verdicts — the (i) content board is
certified forkless yet its two maximal endpoints AGREE, the
twin-freeze mechanism; the (iii) hunt board's burn-split endpoint
EXITS the class, the mate-weld mechanism):

1. THE TWIN CONTENTION IS GUARD-FROZEN — any one-host raise race is
   a twin race (`fc_contention_is_twin`), and at `WF` two face-up
   twins form the no-eat guard's freeze: NEITHER member is ever
   raised along ANY ascent run from the start (face-up-ness
   persists along runs; the guard declines both members at every
   raise leg).  The twins sit at their start seats' rungs forever.
2. NO REVERSIBLE BURIAL OF A RAISE LICENSE — the only rung-moving
   letters are raises; a raise's license dies only under burial or
   seat-loss, and a reversibly-slidable cover drags the covered
   card's own twin face-up (`fc_cover_cell`), so any
   in-class-coverable hot card is guard-frozen and never a raise
   candidate.  What remains: raises are ENABLING-MONOTONE (a raise
   exposes its seat and frees the under-card; the guard toggles
   only toward the unblocked), so maximal runs raise the same
   eventual set — the confluence grade.
3. THE BURN LOOPHOLE IS THE EXIT — a burn-armed slide CAN bury a
   raise license irreversibly (the (iii) board's split, on
   record), but its leg is a commitment: an in-class endpoint
   (the `sameOrbitSetoid` premise rides the start's weld) cannot
   ride a first-leg burn (the exit algebra;
   `commit_blocks_class_return`'s pattern), and every interior
   burn on a returning journey is priced against the
   mint-and-burn interleave census — the one open weave the route
   carries, the same weave that killed the descent twin. -/

theorem ceiling_gradeA {st : State} (hwf : st.WF)
    (hfrk : Forkless st)
    {ρ₁ : List Move} {W₁ : State}
    (hr₁ : AscentRun st ρ₁ W₁) (hs₁ : AscentStuck W₁)
    (hm₁ : sameOrbitSetoid.r st W₁)
    {ρ₂ : List Move} {W₂ : State}
    (hr₂ : AscentRun st ρ₂ W₂) (hs₂ : AscentStuck W₂)
    (hm₂ : sameOrbitSetoid.r st W₂) :
    ∀ (σ : Suit), rungAt W₁ σ = rungAt W₂ σ := by
  sorry

/-- **GRADE-B — THE FLAGSHIP** `ceiling_gradeB` [H, CARRIES] — the
same endpoints are `BareCargoEquiv`: unique up to bare cargo
exchange, the owner's dream frozen at the dumb closure.

ROUTE (Grade-A + the floating structure layer):

1. THE FIX AGREES — `cargo_fix_rungs` + the exclusion's per-leg
   hidden preservation: the endpoints agree on every rung, every
   hidden deck, the two-zone cells — the cargo-fix data.
2. THE SKELETON AGREES — by Grade-A both runs raise the same set,
   so every never-raised face-up card keeps its parent within its
   own two-parent cell along both runs (`fc_cover_cell`'s
   algebra); the endpoints differ at most in the floating slack
   (floater seats among the two parents) and the free-king
   placements over the Vacant graph.
3. MAXIMALITY PINS THE SLACK — at an `AscentStuck` endpoint NO
   `tabToTab` fires at all (the slide arm of `AscentMove` refuses
   every slide), so every floater's parent-twin hop and every
   king-hop the arrangement still licenses is REQUIRED to have
   been taken — the surviving slack is hop-locked by the
   contended-cell freeze and the Vacant-frozen corners
   (all-kings-no-empties), which the exclusion and rigidity rows
   pin to the same placements on both endpoints.
4. THE BRIDGE — the pinned slack differences are bridged by the
   clean-cargo hops themselves (§0d's mirrors witness each), so
   the endpoints are joined by a both-ways dumb-cargo pair. -/

theorem ceiling_gradeB {st : State} (hwf : st.WF)
    (hfrk : Forkless st)
    {ρ₁ : List Move} {W₁ : State}
    (hr₁ : AscentRun st ρ₁ W₁) (hs₁ : AscentStuck W₁)
    (hm₁ : sameOrbitSetoid.r st W₁)
    {ρ₂ : List Move} {W₂ : State}
    (hr₂ : AscentRun st ρ₂ W₂) (hs₂ : AscentStuck W₂)
    (hm₂ : sameOrbitSetoid.r st W₂) :
    BareCargoEquiv W₁ W₂ := by
  sorry

/-- **GRADE-C** `ceiling_gradeC` [H, EXPECTED FALSE — documented,
not chased] — the same endpoints are EQUAL.  The (i) content
board's twin runs land at TWO DISTINCT maximal endpoints
(both `AscentStuck`, both reachable from the same certified-forkless
start, rung vectors agreeing, NOT `BareCargoEquiv`), so any phrasing
without the class-mate premise dies there; with the class-mate
premise the endpoints there are not comparable (each run's seating
slide is burn-armed and COMMITS — the boundary datum the probe
leaf certifies).  Frozen for falsifier-first honesty; the probe
leaf's boundary exhibits are the expected witnesses. -/

theorem ceiling_gradeC {st : State} (hwf : st.WF)
    (hfrk : Forkless st)
    {ρ₁ : List Move} {W₁ : State}
    (hr₁ : AscentRun st ρ₁ W₁) (hs₁ : AscentStuck W₁)
    (hm₁ : sameOrbitSetoid.r st W₁)
    {ρ₂ : List Move} {W₂ : State}
    (hr₂ : AscentRun st ρ₂ W₂) (hs₂ : AscentStuck W₂)
    (hm₂ : sameOrbitSetoid.r st W₂) :
    W₁ = W₂ := by
  sorry

/-- **THE μ-DESCENT PACKAGING** `ceiling_descends` [H, STAGED] —
the map-descent form of the flagship: there is a CEILING MAP μ
from macro classes to cargo orbits such that EVERY maximal ascent
from ANY member of the class exhausts INTO μ of the class.  The
well-definedness of μ IS Grade-B (the contention boards exhibit
two μ-values on one class if any grade dies); the constructor
direction needs a canonical endpoint picker and stays priced.  The
implication direction is proved below (`ceiling_descent_imp`). -/

theorem ceiling_descends :
    ∃ (μ : SameOrbit → CargoOrbit),
      ∀ (s : State) (ρ : List Move) (W : State),
        s.WF → Forkless s → AscentRun s ρ W → AscentStuck W →
          sameOrbitSetoid.r s W →
            Quotient.mk cargoSetoid W =
              μ (Quotient.mk sameOrbitSetoid s) := by
  sorry

/-- **DESCENT IMPLIES MEMBER-SCOPED CONFLUENCE** (proved) — the
map-descent form, read at one class: two in-class maximal ascent
endpoints land in the SAME cargo orbit — Grade-B's packaging is
one quotient-equality away.  This row is the μ-form's honest sound
half; it converts the staged map into the frozen confluence
statement without any picker. -/
theorem ceiling_descent_imp
    (hdesc : ∃ (μ : SameOrbit → CargoOrbit),
      ∀ (s : State) (ρ : List Move) (W : State),
        s.WF → Forkless s → AscentRun s ρ W → AscentStuck W →
          sameOrbitSetoid.r s W →
            Quotient.mk cargoSetoid W =
              μ (Quotient.mk sameOrbitSetoid s))
    {st : State} (hwf : st.WF) (hfrk : Forkless st)
    {ρ₁ : List Move} {W₁ : State}
    (hr₁ : AscentRun st ρ₁ W₁) (hs₁ : AscentStuck W₁)
    (hm₁ : sameOrbitSetoid.r st W₁)
    {ρ₂ : List Move} {W₂ : State}
    (hr₂ : AscentRun st ρ₂ W₂) (hs₂ : AscentStuck W₂)
    (hm₂ : sameOrbitSetoid.r st W₂) :
    BareCargoEquiv W₁ W₂ := by
  obtain ⟨μ, hμ⟩ := hdesc
  have hEq : Quotient.mk cargoSetoid W₁ = Quotient.mk cargoSetoid W₂ := by
    rw [hμ st ρ₁ W₁ hwf hfrk hr₁ hs₁ hm₁,
      hμ st ρ₂ W₂ hwf hfrk hr₂ hs₂ hm₂]
  obtain ⟨τ, hτ, ρ, hρ⟩ := Quotient.exact hEq
  exact ⟨ρ, hρ, τ, hτ⟩

/-! ## The audit battery

`#print axioms` per fresh head.  The §0a/§0b/§0c machinery reads at
the house's clean grade (`[propext, Quot.sound]`, zero
`Classical.choice`, zero sorry): the hidden-monotone kernel family
delegates to the public `hiddenTotal_step` /
`hiddenTotal_step_tabToTab_reveal` tables and `Mono`'s walk
combinators through the per-file bridge, `fc_revealleg_exits` rides
the clean irreversibility row, the exclusion's REVEAL half lands at
vehicle grade (`cargoLeg_revealfree`, `CargoPlayRF_of_return`,
`cargo_revealfree_of_equiv`), and the BURN half's monotone-graded
core is LANDED (§0c.2-§0c.5: the topped counter `fcToppedTotal`, the
fold kit, the per-leg deltas — slide/reveal preserve, the seated burn
the one strict drop at −1 WF-free, the king-corner exchange — the
RF leg/play monotones, and the kernel `cargoLeg_burnfree`); the
burn-side composite and the `CargoShuffle` packaging remain the
priced route item-2/3 tail; the §0d named residues carry their
priced routes in their docstrings; the frozen §2 grades (and, with
them, the §1f characterization) carry `sorryAx`, each with the
complete route recorded where it is declared. -/

#print axioms CargoPlay_run
#print axioms CargoPlay_append
#print axioms CargoPlay_fix_zone
#print axioms classCensus_false_forkless
#print axioms fc_runOK_king_first
#print axioms fcHiddenTotal_step
#print axioms fcHiddenTotal_play
#print axioms fc_revealleg_irreversible
#print axioms fc_revealleg_exits
#print axioms cargoLeg_revealfree
#print axioms cargoLeg_burnfree
#print axioms CargoPlayRF_cargo
#print axioms CargoPlayRF_of_return
#print axioms cargo_revealfree_of_equiv
#print axioms cargo_fix_rungs
#print axioms fc_cell_pair
#print axioms fc_contention_is_twin
#print axioms fc_cover_cell
#print axioms ceiling_gradeA
#print axioms ceiling_gradeB
#print axioms ceiling_gradeC
#print axioms ceiling_descends
#print axioms ceiling_descent_imp
#print axioms cargo_structure_characterization
