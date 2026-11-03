import Temp.Reorder_front_proof
import Orig2.Fork.Class.ForkOneColourClosure

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Rank-sort + front-move probe, and the fork status of `probeState`

Two questions about `probeState` (`Temp/Reorder_front_proof.lean`):

    pile p0:  K♥          (c, a bare king, raisableS now)
    pile p1:  K♦  Q♠      (c.twin = K♦, covered by Q♠)
    found:    ♠↦A..J, ♥↦A..Q, ♦↦A..Q, ♣↦[]
    stock:    K♠ + all of ♣

## Q1 — the parent's composition `P' = [K♥, Q♠, K♦]`

In the word encoding (head = last raise) that is the word

    w' = [K♦, Q♠, K♥]        chronological: K♥, then Q♠, then K♦

This is **legal** (`probe_rankfront_exists`).  After `K♥` is founded the next
card is `Q♠`, which *is* the pile top of `p1`: the cover does not have to be
moved for `Q♠`'s raise, and raising `Q♠` then exposes `K♦`, whose bare-king
seat is intact.  The predicted obstruction ("after K♥ is founded, Q♠ has no
seat") belongs to the *other* word `[Q♠, K♦, K♥]`, where `K♦` is the card that
must be raised while still covered — refuted in
`Temp/Reorder_front_proof.lean`.  So the probe **does not** refute the
rank-sort-then-front composition.

## Q2 — fork status

`ForkWitness st x` is the ↔ reading (`Orig2/Substrate/Vocab.lean:592`):

    (∀ c, (c = x ∨ c = x.twin) ↔ CanRaiseS st c) ∧ ¬ CanRaise st x.twin

i.e. the S-spectrum must be **exactly** the twin pair `{x, x.twin}`.

Kernel-checked here:

* `probe_three_live` — three distinct live cards at the probe
  (`K♥`, `K♦`, `Q♠`), so the spectrum is **not** a twin pair;
* `probe_not_forkWitness` / `probe_not_forkState` — the probe state itself is
  not a fork witness/fork state;
* `probe_forkLive` — a twin pair *is* live at the probe.

**Not settled here (explicit):** the class-level alternative
`Fork probeState` vs `Forkless probeState`.  `Forkless` quantifies over every
orbit mate `F` — at *any* rungs, since `sameOrbitSetoid` does not fix the
ledger — so it needs the state-space invariant

    (Ih) every pile has `hidden = []`;
    (I2) every face-up card is one of `K♥, K♦, Q♠`;
    (I3) rungs: ♠ ∈ {11,12}, ♥ ∈ {12,13}, ♦ ∈ {12,13}, ♣ = 0,

maintained along witness shuffles (draw no tableau change; slide preserves the
face-up set; raise removes a card; and no pull of `J♠, Q♥, Q♦` is ever legal,
while `Q♣, K♠, K♣` never leave the stock).  Given (Ih)–(I3) no class mate is a
fork: a live card is held, hence in `{K♥,K♦,Q♠}`; the only twin pair there is
`{K♥,K♦}`; and the pin fails, because the *un*covered king is a bare king with
`hidden = []` (vanilla-raisable) and the covered one can only be covered by
`Q♠`, which would then itself be live and break "spectrum = pair".  I have
**not** machine-checked (Ih)–(I3) here, so neither `probe_fork` nor
`probe_forkless` is claimed.

House compliance: no `sorry`, no `Classical`, no `noncomputable`; battery at
the tail.
-/

namespace OneColourClosure

/-! ## §1. The spectrum at the probe -/

/-- The card `Q♣` (the twin of `Q♠`), used in the spectrum argument. -/
def cQC : Card := ⟨Suit.club, Rank.queen⟩

theorem cQS_twin : cQS.twin = cQC := by decide

theorem cKH_twin : cKH.twin = cKD := by decide

/-- `Q♠` is raisableS at the probe state (pile top of `p1` with `K♦` beneath). -/
theorem probe_canRaiseS_QS : CanRaiseS probeState cQS :=
  CanRaiseS.now cQS
    ⟨by decide, ⟨Anchor.p1, by decide, Or.inl (by decide)⟩⟩

/-- `K♦` is raisableS at the probe state: slide `Q♠` off it (onto `K♥`), then
`K♦` is a bare king on `p1`. -/
theorem probe_canRaiseS_KD : CanRaiseS probeState cKD :=
  CanRaiseS.via cKD probe_slide_cargoLeg
    (CanRaiseS.now cKD
      ⟨by decide, ⟨Anchor.p1, by decide, Or.inr ⟨by decide, by decide⟩⟩⟩)

/-- The probe's spectrum has (at least) three distinct live cards. -/
theorem probe_three_live :
    CanRaiseS probeState cKH ∧ CanRaiseS probeState cKD ∧ CanRaiseS probeState cQS :=
  ⟨probe_canRaiseS_KH, probe_canRaiseS_KD, probe_canRaiseS_QS⟩

/-! ## §2. Q1 — the rank-sorted front-move word is legal -/

/-- The landing of raising `K♥` at the probe state. -/
def afterKH : State :=
  { probeState.setFound cKH.suit (probeState.found cKH.suit ++ [cKH]) with
    piles := fun a' =>
      if a' = Anchor.p0 then
        Pile.afterRunRemoved (probeState.piles Anchor.p0)
          (chop (probeState.piles Anchor.p0).faceUp)
      else probeState.piles a' }

theorem probe_step_KH : State.step probeState (Move.tabToFound cKH) = some afterKH :=
  step_tabToFound_splice (by decide) (by decide)

theorem afterKH_nextUp_QS : afterKH.nextUp cQS = true := by decide

theorem afterKH_pileOfTop_QS : afterKH.pileOfTop cQS = some Anchor.p1 := by decide

/-- The landing of raising `Q♠` at `afterKH`. -/
def afterKHQ : State :=
  { afterKH.setFound cQS.suit (afterKH.found cQS.suit ++ [cQS]) with
    piles := fun a' =>
      if a' = Anchor.p1 then
        Pile.afterRunRemoved (afterKH.piles Anchor.p1)
          (chop (afterKH.piles Anchor.p1).faceUp)
      else afterKH.piles a' }

theorem afterKH_step_QS : State.step afterKH (Move.tabToFound cQS) = some afterKHQ :=
  step_tabToFound_splice afterKH_nextUp_QS afterKH_pileOfTop_QS

theorem afterKHQ_nextUp_KD : afterKHQ.nextUp cKD = true := by decide

theorem afterKHQ_pileOfTop_KD : afterKHQ.pileOfTop cKD = some Anchor.p1 := by decide

/-- The landing of raising `K♦` at `afterKHQ`. -/
def afterKHQD : State :=
  { afterKHQ.setFound cKD.suit (afterKHQ.found cKD.suit ++ [cKD]) with
    piles := fun a' =>
      if a' = Anchor.p1 then
        Pile.afterRunRemoved (afterKHQ.piles Anchor.p1)
          (chop (afterKHQ.piles Anchor.p1).faceUp)
      else afterKHQ.piles a' }

theorem afterKHQ_step_KD : State.step afterKHQ (Move.tabToFound cKD) = some afterKHQD :=
  step_tabToFound_splice afterKHQ_nextUp_KD afterKHQ_pileOfTop_KD

/-- **Q1 ANSWER: the rank-sorted front-move word is legal.**

Word `[K♦, Q♠, K♥]` = chronologically `K♥`, `Q♠`, `K♦` — the parent's
composition `P' = [K♥, Q♠, K♦]` (chronological).  No cargo slide is needed:
each of the three raises fires from the bare tableau. -/
theorem probe_rankfront_exists : ∃ z', RaiseSSeq probeState [cKD, cQS, cKH] z' :=
  ⟨afterKHQD,
    RaiseSSeq.cons
      (RaiseSSeq.cons
        (RaiseSSeq.cons (RaiseSSeq.nil probeState) (Steps.refl probeState) probe_step_KH)
        (Steps.refl afterKH) afterKH_step_QS)
      (Steps.refl afterKHQ) afterKHQ_step_KD⟩

/-! ## §3. Q2 — the probe's spectrum is not a twin pair -/

/-- **The probe state is not a fork witness**: its spectrum contains three
distinct live cards, so it can never be exactly a twin pair. -/
theorem probe_not_forkWitness (x : Card) : ¬ ForkWitness probeState x := by
  rintro ⟨hiff, -⟩
  -- `K♥` live ⟹ `x ∈ {K♥, K♦}`
  have h1 : x = cKH ∨ x = cKD := by
    rcases (hiff cKH).mpr probe_canRaiseS_KH with h | h
    · exact Or.inl h.symm
    · refine Or.inr ?_
      calc x = x.twin.twin := (card_twin_twin x).symm
        _ = cKH.twin := by rw [← h]
        _ = cKD := cKH_twin
  -- `Q♠` live ⟹ `x ∈ {Q♠, Q♣}`
  have h2 : x = cQS ∨ x = cQC := by
    rcases (hiff cQS).mpr probe_canRaiseS_QS with h | h
    · exact Or.inl h.symm
    · refine Or.inr ?_
      calc x = x.twin.twin := (card_twin_twin x).symm
        _ = cQS.twin := by rw [← h]
        _ = cQC := cQS_twin
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.symm.trans h2) (by decide)
  · exact absurd (h1.symm.trans h2) (by decide)
  · exact absurd (h1.symm.trans h2) (by decide)
  · exact absurd (h1.symm.trans h2) (by decide)

/-- So the probe state is not a `forkState`. -/
theorem probe_not_forkState : ¬ forkState probeState := by
  rintro ⟨x, hiff, hpin⟩
  exact probe_not_forkWitness x ⟨hiff, hpin⟩

/-- A twin pair is live at the probe state (`ForkLive`). -/
theorem probe_forkLive : ∃ x c, (c = x ∨ c = x.twin) ∧ CanRaiseS probeState c :=
  ⟨cKH, cKD, Or.inr (by rw [cKH_twin]), probe_canRaiseS_KD⟩

/-! ## §4. The state-level fork gate does not rescue the statement

`probeState` is *not* a fork state (`probe_not_forkState`), yet it refutes the
front-reordering word.  So gating the reordering by `¬ forkState s` at the
starting state does not make it true. -/

/-- **Q2-side consequence** — the front-reordering statement is false even
under the state-level fork gate `¬ forkState s`. -/
theorem gated_front_statement_false :
    ¬ (∀ {s : State} {c : Card}, s.WF → ¬ forkState s → CanRaiseS s c →
        ∀ {ws : List Card} {z : State}, RaiseSSeq s ws z → c ∈ ws →
          ∃ z', RaiseSSeq s (ws.erase c ++ [c]) z') := by
  intro hR
  have hmem : cKH ∈ [cKH, cQS, cKD] := by simp
  obtain ⟨z', hz'⟩ := hR probeState_WF probe_not_forkState probe_canRaiseS_KH
    probe_raiseSeq hmem
  have hw : [cKH, cQS, cKD].erase cKH ++ [cKH] = [cQS, cKD, cKH] := by decide
  rw [hw] at hz'
  exact probe_not_raiseSeq_front ⟨z', hz'⟩

end OneColourClosure

#print axioms OneColourClosure.probe_canRaiseS_QS
#print axioms OneColourClosure.probe_canRaiseS_KD
#print axioms OneColourClosure.probe_three_live
#print axioms OneColourClosure.probe_rankfront_exists
#print axioms OneColourClosure.probe_not_forkWitness
#print axioms OneColourClosure.probe_not_forkState
#print axioms OneColourClosure.probe_forkLive
#print axioms OneColourClosure.gated_front_statement_false
