import Orig2.ForkMinCross
import Orig2.ForkMechanism

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Ledger_Residual — the exodus dip residual, and its exact reduction

READ-ONLY scratch card.  No source file is modified; nothing is committed.

`Ledger_Core.lean` proves steps 1 and 2 of the route named in the
`SatDifferFork` docstring (`Orig2/Vocab.lean:610-629`): the rung ledger,
and the first-passage exodus (the first non-free letter out of a
saturated origin is a pull; its card is the foundation top, live at the
landing; a raise still occurs later).

This card isolates **step 3, the twin coincidence / dip**, as a single
named `Prop`, `ExodusAfterFork`, and proves the exact reduction

    ExodusAfterFork ↔ MinKit.MinCrossesFork.

The residual says: *after the canonical exodus pull, the remaining play
visits a fork*.  It is not a trivial restatement of the target:

* the cut is canonical (`pre` free, `m` the first non-free letter, a pull)
  and supplied by the ledger (`Ledger_Core.exodus_cut`);
* no fork can lie on the free prefix (saturation is free-invariant, and a
  fork state is not saturated) — `Ledger_Core.not_fork_of_free_play`;
* so *every* fork of a witness play automatically sits after the exodus
  cut, which is why the converse holds too.

What remains open is exactly the local mechanism at the dip: showing that
the tail after the exodus pull *does* visit a fork.  The repository's
mechanism kit (`Orig2/ForkMechanism.lean`: `coverEvent_iff_block`,
`twinLivePair_landing_iff`, `mechanism_yields`) is the intended tool;
`Temp/TwinPin_Report.md` shows that no pure `CanRaiseS`-spectrum
argument can do it (the live set can be an exact twin pair with both
twins raisable), so the proof must consume the minimality hypothesis
carried by this residual and the saturation of the target.

House compliance: `sorry`-free, choice-free, `native_decide`-free; the
axiom battery is at the tail.
-/

namespace LedgerKit

/-! ## §1. List-prefix alignment -/

/-- If `α ++ β = pre ++ m :: rest` and `α` is no longer than `pre`, then
`α` is a prefix of `pre`. -/
theorem prefix_of_left_le :
    ∀ (pre α β rest : List Move) (m : Move),
      α ++ β = pre ++ m :: rest → α.length ≤ pre.length →
        ∃ δ : List Move, pre = α ++ δ
  | [], α, β, rest, m, h, hle => by
      cases α with
      | nil => exact ⟨[], rfl⟩
      | cons a as => simp at hle
  | p :: ps, α, β, rest, m, h, hle => by
      cases α with
      | nil => exact ⟨p :: ps, rfl⟩
      | cons a as =>
          simp only [List.cons_append] at h
          have ha : a = p := (List.cons.inj h).1
          have htail : as ++ β = ps ++ m :: rest := (List.cons.inj h).2
          have hle' : as.length ≤ ps.length := by
            simp only [List.length_cons] at hle
            omega
          obtain ⟨δ, hδ⟩ := prefix_of_left_le ps as β rest m htail hle'
          exact ⟨δ, by rw [ha, hδ]; simp only [List.cons_append]⟩

/-- If `α ++ β = pre ++ m :: rest` and `α` is strictly longer than `pre`,
then `α = pre ++ m :: δ`. -/
theorem suffix_of_left_lt :
    ∀ (pre α β rest : List Move) (m : Move),
      α ++ β = pre ++ m :: rest → pre.length < α.length →
        ∃ δ : List Move, α = pre ++ m :: δ
  | [], α, β, rest, m, h, hlt => by
      cases α with
      | nil => simp at hlt
      | cons a as =>
          simp only [List.nil_append, List.cons_append] at h
          have ha : a = m := (List.cons.inj h).1
          have htail : as ++ β = rest := (List.cons.inj h).2
          exact ⟨as, by rw [ha]; rfl⟩
  | p :: ps, α, β, rest, m, h, hlt => by
      cases α with
      | nil => simp at hlt
      | cons a as =>
          simp only [List.cons_append] at h
          have ha : a = p := (List.cons.inj h).1
          have htail : as ++ β = ps ++ m :: rest := (List.cons.inj h).2
          have hlt' : ps.length < as.length := by
            simp only [List.length_cons] at hlt
            omega
          obtain ⟨δ, hδ⟩ := suffix_of_left_lt ps as β rest m htail hlt'
          exact ⟨δ, by rw [ha, hδ]; simp only [List.cons_append]⟩

/-- A fork state is not saturated: its witness card is S-live. -/
theorem not_ssaturated_of_fork_res {F : State} {x : Card}
    (hx : ForkWitness F x) : ¬ SSaturated F :=
  fun hs => hs x ((hx.1 x).mp (Or.inl rfl))

/-! ## §2. The residual -/

/-- **`ExodusAfterFork` — the step-3 residual (the dip).**

Every minimal witness play between saturated endpoints with differing
rungs, cut at its canonical exodus pull (free prefix, then the first
non-free letter, which is a `foundToTab c b`), visits a fork somewhere on
the remaining play after the pull's landing.

The minimality hypothesis is part of the residual on purpose: the local
state-level statement is false (`Temp/TwinPin_Report.md`), so the missing
proof must consume minimality and/or the saturated target. -/
def ExodusAfterFork : Prop :=
  ∀ (u v : State) (ρ : List Move),
    u.WF → SSaturated u → SSaturated v →
    ShufflePlayW u ρ v →
    (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) →
    (∃ σ : Suit, rungAt u σ ≠ rungAt v σ) →
    ∀ (pre : List Move) (m : Move) (rest : List Move)
      (mid post : State) (c : Card) (b : Base),
      ρ = pre ++ m :: rest →
      (∀ x ∈ pre, ValleyElim.FreeMove x) →
      ShufflePlayW u pre mid →
      State.step mid m = some post →
      ShufflePlayW post rest v →
      m = Move.foundToTab c b →
      ∃ (F : State) (x : Card) (β γ : List Move),
        rest = β ++ γ ∧ ShufflePlayW post β F ∧ ForkWitness F x

/-! ## §3. The residual proves `MinCrossesFork` -/

/-- **STEP 3 ⇒ THE CAMPAIGN TARGET.**  `MinKit.MinCrossesFork` follows from
the exodus-dip residual: the ledger supplies the canonical cut
(`first_nonfree_pull`, using `SSaturated u` and `WF`), the residual yields
a fork on the tail, and the prefix is glued by `ShufflePlayW_append`. -/
theorem minCrossesFork_of_exodusAfterFork (h : ExodusAfterFork) :
    MinKit.MinCrossesFork := by
  intro u v ρ huwf hsu hsv hplay hdiff hmin
  have hex : ∃ m ∈ ρ, ¬ ValleyElim.FreeMove m := by
    apply ValleyElim.exists_nonfree_of_not_all_free
    intro hall
    obtain ⟨σ, hσ⟩ := hdiff
    exact hσ (ValleyElim.rungAt_eq_of_free_play hplay hall σ).symm
  obtain ⟨m₀, hm₀, hnf₀⟩ := hex
  obtain ⟨pre, c, b, rest, heq, hpre⟩ :=
    ValleyElim.first_nonfree_pull huwf hsu hplay ⟨m₀, hm₀, hnf₀⟩
  obtain ⟨mid, hpreplay, hrest⟩ :=
    ValleyElim.ShufflePlayW_split hplay pre (Move.foundToTab c b :: rest) heq
  cases hrest with
  | @cons _ post _ _ _ hrev hstep htail =>
      obtain ⟨F, x, β, γ, hrestEq, hβ, hx⟩ :=
        h u v ρ huwf hsu hsv hplay hmin hdiff pre (Move.foundToTab c b) rest
          mid post c b heq hpre hpreplay hstep htail rfl
      refine ⟨F, x, pre ++ Move.foundToTab c b :: β, γ, ?_, ?_, hx⟩
      · rw [heq, hrestEq]
        simp only [List.append_assoc, List.cons_append]
      · exact ShufflePlayW_append hpreplay (Walk.cons hrev hstep hβ)

/-! ## §4. The target implies the residual (the cut is canonical) -/

/-- **`MinCrossesFork` ⇒ STEP 3.**  Conversely, a fork on some prefix of
the play cannot lie on the free prefix before the exodus pull: the free
prefix stays saturated, and a fork state is not saturated.  Hence the
fork found by `MinCrossesFork` sits after the cut, which is exactly the
residual. -/
theorem exodusAfterFork_of_minCrossesFork (h : MinKit.MinCrossesFork) :
    ExodusAfterFork := by
  intro u v ρ huwf hsu hsv hplay hmin hdiff pre m rest mid post c b
    heq hpre hpreplay hstep hpostplay hm
  have hrev : reversibleAtW mid m := by
    obtain ⟨mid', hprePlay, hrestPlay⟩ :=
      ValleyElim.ShufflePlayW_split hplay pre (m :: rest) heq
    have hmidEq : mid' = mid :=
      Option.some.inj ((Walk_run _ hprePlay).symm.trans (Walk_run _ hpreplay))
    subst hmidEq
    cases hrestPlay with
    | cons hrev' _ _ => exact hrev'
  obtain ⟨F, x, α, γ, hρEq, hαplay, hx⟩ :=
    h u v ρ huwf hsu hsv hplay hdiff hmin
  have hcomb : α ++ γ = pre ++ m :: rest := hρEq.symm.trans heq
  rcases Nat.lt_or_ge pre.length α.length with hlt | hge
  · -- `α` runs past the cut: the fork is on the residual's tail
    obtain ⟨β, hαEq⟩ := suffix_of_left_lt pre α γ rest m hcomb hlt
    have hα' : α = (pre ++ [m]) ++ β := by
      rw [hαEq]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    obtain ⟨P, hP1, hP2⟩ := ValleyElim.ShufflePlayW_split hαplay (pre ++ [m]) β hα'
    have hprePost : ShufflePlayW u (pre ++ [m]) post :=
      ShufflePlayW_append hpreplay (Walk.cons hrev hstep (Walk.nil post))
    have hPpost : P = post :=
      Option.some.inj ((Walk_run _ hP1).symm.trans
        (Walk_run _ hprePost))
    subst hPpost
    have hsplit : rest = β ++ γ := by
      have h1 : pre ++ m :: rest = pre ++ m :: (β ++ γ) := by
        rw [← hcomb, hαEq]
        simp only [List.append_assoc, List.cons_append]
      have h2 := List.append_cancel_left h1
      exact (List.cons.inj h2).2
    exact ⟨F, x, β, γ, hsplit, hP2, hx⟩
  · -- `α` is a prefix of `pre`: the fork would sit on a free prefix
    exfalso
    have hle : α.length ≤ pre.length := by omega
    obtain ⟨δ, hpreEq⟩ := prefix_of_left_le pre α γ rest m hcomb hle
    obtain ⟨G, hαplay', hδplay⟩ :=
      ValleyElim.ShufflePlayW_split hpreplay α δ hpreEq
    have hGF : G = F :=
      Option.some.inj ((Walk_run _ hαplay').symm.trans
        (Walk_run _ hαplay))
    have hαfree : ∀ y ∈ α, ValleyElim.FreeMove y := by
      intro y hy
      exact hpre y (by rw [hpreEq]; exact List.mem_append_left δ hy)
    have hsatG : SSaturated G :=
      ValleyElim.ssaturated_free_prefix hαplay' hαfree huwf hsu
    rw [hGF] at hsatG
    exact not_ssaturated_of_fork_res hx hsatG

/-! ## §5. The exact equivalence -/

/-- **STEP 3 IS EXACTLY THE CAMPAIGN TARGET.**  The exodus-dip residual is
not a weakening or a strengthening: cutting at the canonical first pull
loses nothing, because no fork can sit on the saturated free prefix. -/
theorem exodusAfterFork_iff_minCrossesFork :
    ExodusAfterFork ↔ MinKit.MinCrossesFork :=
  ⟨minCrossesFork_of_exodusAfterFork, exodusAfterFork_of_minCrossesFork⟩

/-- **THE CAMPAIGN CHAIN FROM THE DIP RESIDUAL.**  The residual plus the
choice-free shortest-play interface gives `SatDifferForkWF` through the
source's `satDifferForkWF_of_minCrossesFork`. -/
theorem satDifferForkWF_of_exodusAfterFork
    (h : ExodusAfterFork) (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF :=
  MinKit.satDifferForkWF_of_minCrossesFork (minCrossesFork_of_exodusAfterFork h) hmin

/-! ## §6. The mechanism kit closes the residual

`Mech.MechanismResidual` (`Orig2/ForkMechanism.lean:414`) is the
repository's already named pair of landing clauses (`LandingLivePair` +
`CoverEvent`).  `mechanism_yields` turns them into `d = c.twin`, the exact
twin live set and the orientation pin — literally a `ForkWitness` at the
valley bottom.  Hence the mechanism residual discharges both
`MinCrossesFork` and the exodus-dip residual, so the *only* remaining
content of step 3 is those two landing clauses. -/

/-- **THE MECHANISM PUTS A FORK AT EVERY MINIMAL VALLEY BOTTOM.** -/
theorem forkAtValley_of_mechanismResidual (h : Mech.MechanismResidual)
    {u v : State} {ρ : List Move} {F : State}
    (huwf : u.WF) (hsu : SSaturated u) (hsv : SSaturated v)
    (hplay : ShufflePlayW u ρ v)
    (hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length)
    (hsplit : ValleyElim.ValleySplitAt u v ρ F) :
    ∃ x : Card, ForkWitness F x := by
  obtain ⟨left, right, c, d, b, pre, post, tail,
    hρ, hleft, hright, hshape, hfree, hrightShape⟩ := hsplit
  have hsplit' : ValleyElim.ValleySplitAt u v ρ F :=
    ⟨left, right, c, d, b, pre, post, tail,
      hρ, hleft, hright, hshape, hfree, hrightShape⟩
  have hh : SplitKit.SplitHyp u v ρ F left right c d b pre post tail :=
    ⟨huwf, hsu, hsv, hplay, hsplit', hmin, hρ, hleft, hright, hshape, hfree,
      hrightShape⟩
  obtain ⟨hd, hlive, hblock, -⟩ :=
    Mech.mechanism_yields hh (h u v ρ F left right c d b pre post tail hh)
  refine ⟨d, (forkWitness_iff F d).mpr ⟨hlive, ?_⟩⟩
  rw [hd, card_twin_twin]
  exact hblock

/-- **THE TWO LANDING CLAUSES GIVE THE DIP FORK.**  This is the local
"twin coincidence" law, stated exactly on the geometry rows: the landing
carries `LandingLivePair B c`; `Mech.twinLivePair_of_landing` upgrades it
to the exact pair `TwinLivePair B c` using the pull's rung pin, the free
tail transports it to the bottom (`twinLivePair_landing_iff`), and
`CoverEvent` blocks `c` there (`block_of_coverEvent`).  The fork witness
is `c.twin`: its live pair is `{c, c.twin}` and its pin is `¬ CanRaise F c`. -/
theorem fork_of_landing_cover
    {B F : State} {post : List Move} {c : Card}
    (hB : B.WF) (hpost : ShufflePlayW B post F)
    (hfree : ∀ m ∈ post, ValleyElim.FreeMove m)
    (hcanB : CanRaise B c)
    (hrungB : rungAt B c.suit = c.rank.toIdx)
    (hland : Mech.LandingLivePair B c)
    (hcov : Mech.CoverEvent B F post c) :
    ∃ x : Card, ForkWitness F x := by
  have hF : F.WF := SatDifferCensus.ShufflePlayW.wf_end hpost hB
  have hBpair : TwinLivePair B c :=
    Mech.twinLivePair_of_landing hcanB hrungB hland
  have hFpair : TwinLivePair F c :=
    (Mech.twinLivePair_landing_iff hB hpost hfree).mp hBpair
  have hFtwin : TwinLivePair F c.twin :=
    Mech.twinLivePair_of_eq_twin hFpair rfl
  have hblock : ¬ CanRaise F c := Mech.block_of_coverEvent hF hcov
  exact ⟨c.twin, (forkWitness_iff F c.twin).mpr
    ⟨hFtwin, by rw [card_twin_twin]; exact hblock⟩⟩

/-- **THE MECHANISM RESIDUAL DISCHARGES `MinCrossesFork`.** -/
theorem minCrossesFork_of_mechanismResidual (h : Mech.MechanismResidual) :
    MinKit.MinCrossesFork := by
  intro u v ρ huwf hsu hsv hplay hdiff hmin
  obtain ⟨F, hsplit⟩ := ValleyElim.valley_exists huwf hsu hsv hdiff hplay
  obtain ⟨x, hx⟩ :=
    forkAtValley_of_mechanismResidual h huwf hsu hsv hplay hmin hsplit
  obtain ⟨left, right, c, d, b, pre, post, tail,
    hρ, hleft, hright, hshape, hfree, hrightShape⟩ := hsplit
  exact ⟨F, x, left, right, hρ, hleft, hx⟩

/-- **THE MECHANISM RESIDUAL DISCHARGES THE EXODUS DIP RESIDUAL.** -/
theorem exodusAfterFork_of_mechanismResidual (h : Mech.MechanismResidual) :
    ExodusAfterFork :=
  exodusAfterFork_of_minCrossesFork (minCrossesFork_of_mechanismResidual h)

/-! ## §7. Axiom battery -/

#print axioms LedgerKit.prefix_of_left_le
#print axioms LedgerKit.suffix_of_left_lt
#print axioms LedgerKit.not_ssaturated_of_fork_res
#print axioms LedgerKit.minCrossesFork_of_exodusAfterFork
#print axioms LedgerKit.exodusAfterFork_of_minCrossesFork
#print axioms LedgerKit.exodusAfterFork_iff_minCrossesFork
#print axioms LedgerKit.satDifferForkWF_of_exodusAfterFork
#print axioms LedgerKit.forkAtValley_of_mechanismResidual
#print axioms LedgerKit.fork_of_landing_cover
#print axioms LedgerKit.minCrossesFork_of_mechanismResidual
#print axioms LedgerKit.exodusAfterFork_of_mechanismResidual

end LedgerKit
