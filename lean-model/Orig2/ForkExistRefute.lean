import Orig2.ForkReadBracket
import Orig2.ForkBubble

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Exist_Refute — `R12.ReadBracketElim` is FALSE (and so is
`NonforkKit.NonforkBracketLocal`)

Scratch card.  READ-ONLY on repository source; no commit.

## The witness

A four-letter witness play on one board:

```text
pull 5H -> 6C ; slide 4C -> 5H ; slide 4C -> 5D ; raise 5H
```

The two slides cancel (`4C` leaves `p2`, sits on `5H`, returns to `5D`), so
the play is a cycle `u -> u`.  Both endpoints are `SSaturated`, the valley
split sits at the state `F` after the two slides (the pull card is `5H`, the
turn raise is `raise 5H`), and `F` is NOT a fork (`live F = {5H}`, a
singleton, so no twin pair).

The only same-card `pull/raise` pair of the play is `(pull 5H, raise 5H)`,
whose interior is the two slides; the first of them lands on `5H`
(`base = Sum.inr 5H`), so `ReadOK 5H` fails there.  There is no other
bracket, hence both disjuncts of `ReadBracketElim` fail.

The `ReadMatches`-style escape (a strictly shorter play) is available — the
empty play is a witness `u -> u` — so `ValleyElimNonfork` itself is not
refuted; only the symmetric bracket residual is.

The refutation is a *loop*: exactly the kind of play that cannot occur at a
minimum-length play.  This is why the corrected residual needs the
minimality gate (`Temp/Exist_Kit.lean`).
-/

namespace ExistRefute

open ValleyElim

/-! ## §0. Cards -/

def AH : Card := ⟨.heart, .ace⟩
def H2 : Card := ⟨.heart, .two⟩
def H3 : Card := ⟨.heart, .three⟩
def H4 : Card := ⟨.heart, .four⟩
def H5 : Card := ⟨.heart, .five⟩
def H6 : Card := ⟨.heart, .six⟩
def H7 : Card := ⟨.heart, .seven⟩
def H8 : Card := ⟨.heart, .eight⟩
def H9 : Card := ⟨.heart, .nine⟩
def HT : Card := ⟨.heart, .ten⟩
def HJ : Card := ⟨.heart, .jack⟩
def HQ : Card := ⟨.heart, .queen⟩
def HK : Card := ⟨.heart, .king⟩

def AD : Card := ⟨.diamond, .ace⟩
def D2 : Card := ⟨.diamond, .two⟩
def D3 : Card := ⟨.diamond, .three⟩
def D4 : Card := ⟨.diamond, .four⟩
def D5 : Card := ⟨.diamond, .five⟩
def D6 : Card := ⟨.diamond, .six⟩
def D7 : Card := ⟨.diamond, .seven⟩
def D8 : Card := ⟨.diamond, .eight⟩
def D9 : Card := ⟨.diamond, .nine⟩
def DT : Card := ⟨.diamond, .ten⟩
def DJ : Card := ⟨.diamond, .jack⟩
def DQ : Card := ⟨.diamond, .queen⟩
def DK : Card := ⟨.diamond, .king⟩

def AS : Card := ⟨.spade, .ace⟩
def S2 : Card := ⟨.spade, .two⟩
def S3 : Card := ⟨.spade, .three⟩
def S4 : Card := ⟨.spade, .four⟩
def S5 : Card := ⟨.spade, .five⟩
def S6 : Card := ⟨.spade, .six⟩
def S7 : Card := ⟨.spade, .seven⟩
def S8 : Card := ⟨.spade, .eight⟩
def S9 : Card := ⟨.spade, .nine⟩
def ST : Card := ⟨.spade, .ten⟩
def SJ : Card := ⟨.spade, .jack⟩
def SQ : Card := ⟨.spade, .queen⟩
def SK : Card := ⟨.spade, .king⟩

def AC : Card := ⟨.club, .ace⟩
def C2 : Card := ⟨.club, .two⟩
def C3 : Card := ⟨.club, .three⟩
def C4 : Card := ⟨.club, .four⟩
def C5 : Card := ⟨.club, .five⟩
def C6 : Card := ⟨.club, .six⟩
def C7 : Card := ⟨.club, .seven⟩
def C8 : Card := ⟨.club, .eight⟩
def C9 : Card := ⟨.club, .nine⟩
def CT : Card := ⟨.club, .ten⟩
def CJ : Card := ⟨.club, .jack⟩
def CQ : Card := ⟨.club, .queen⟩
def CK : Card := ⟨.club, .king⟩

/-! ## §1. The board `u` -/

/-- The hidden stack of pile `p6` (29 cards). -/
def hidden6 : List Card :=
  [AD, D3, S5, D6, S6, H7, C7, H8, C8, H9, D9, S9, C9,
   HT, DT, ST, CT, HJ, DJ, SJ, CJ, HQ, DQ, SQ, CQ, HK, DK, SK, CK]

/-- The saturated starting position. -/
def u : State :=
  { found := fun s => match s with
      | .heart => [AH, H2, H3, H4, H5]
      | .diamond => []
      | .spade => [AS, S2, S3, S4]
      | .club => [AC, C2]
    piles := fun a => match a with
      | .p0 => ⟨[], [D4, C3, D2]⟩
      | .p1 => ⟨[], [D8, S7]⟩
      | .p2 => ⟨[], [D5, C4]⟩
      | .p3 => ⟨[], [H6, C5]⟩
      | .p4 => ⟨[], [C6]⟩
      | .p5 => ⟨[], [S8, D7]⟩
      | .p6 => ⟨hidden6, []⟩
    stock := []
    waste := []
    drawStep := 1 }

/-! ## §2. Well-formedness of `u` -/

theorem u_wf_found : ∀ s : Suit, ∃ n, u.found s = s.upCards.take n := by
  intro s
  cases s with
  | heart => exact ⟨5, rfl⟩
  | diamond => exact ⟨0, rfl⟩
  | spade => exact ⟨4, rfl⟩
  | club => exact ⟨2, rfl⟩

theorem u_wf_runs : ∀ a : Anchor, runOK (u.piles a).faceUp = true := by
  intro a
  cases a <;> decide

theorem u_wf_count : ∀ c ∈ Card.universe, u.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

theorem u_wf : u.WF := ⟨u_wf_found, u_wf_runs, u_wf_count, by decide⟩

/-! ## §3. The four letters and their landings -/

/-- The pull landing (`= F`, see §5). -/
def B : State := (u.setFound .heart (chop (u.found .heart))).putCard H5 (Sum.inr C6)

/-- The intermediate state after `slide 4C -> 5H`. -/
def S : State :=
  (B.setPile .p2 (Pile.afterRunRemoved (B.piles .p2) (below C4 (B.piles .p2).faceUp))).putRun
    (fromCard C4 (B.piles .p2).faceUp) (Sum.inr H5)

/-- The state after the second slide (the valley bottom `F`). -/
def F : State :=
  (S.setPile .p4 (Pile.afterRunRemoved (S.piles .p4) (below C4 (S.piles .p4).faceUp))).putRun
    (fromCard C4 (S.piles .p4).faceUp) (Sum.inr D5)

/-- The landing of the closing raise. -/
def V : State :=
  (F.setFound .heart (F.found .heart ++ [H5])).setPile .p4
    (Pile.afterRunRemoved (F.piles .p4) (chop (F.piles .p4).faceUp))

def mPull : Move := Move.foundToTab H5 (Sum.inr C6)
def mS1 : Move := Move.tabToTab C4 (Sum.inr H5)
def mS2 : Move := Move.tabToTab C4 (Sum.inr D5)
def mRaise : Move := Move.tabToFound H5

/-- The witness move list. -/
def rho : List Move := [mPull, mS1, mS2, mRaise]

theorem step_pull : State.step u mPull = some B := by rfl
theorem step_s1 : State.step B mS1 = some S := by rfl
theorem step_s2 : State.step S mS2 = some F := by rfl
theorem step_raise : State.step F mRaise = some V := by rfl

theorem B_wf : B.WF := step_wf u_wf step_pull
theorem S_wf : S.WF := step_wf B_wf step_s1
theorem F_wf : F.WF := step_wf S_wf step_s2
theorem V_wf : V.WF := step_wf F_wf step_raise

theorem pull_rev : reversibleAtW u mPull :=
  (foundToTabR_iff_reversibleAtW u_wf H5 (Sum.inr C6)).mp (by decide)

theorem s1_rev : reversibleAtW B mS1 :=
  (tabToTabR_iff_reversibleAtW B_wf C4 (Sum.inr H5)).mp (by decide)

theorem s2_rev : reversibleAtW S mS2 :=
  (tabToTabR_iff_reversibleAtW S_wf C4 (Sum.inr D5)).mp (by decide)

theorem raise_rev : reversibleAtW F mRaise :=
  (tabToFoundR_iff_reversibleAtW F_wf H5).mp (by decide)

/-! ## §4. Saturation of the endpoints -/

/-- `canRaiseSB` is false at every card at `u`. -/
theorem u_liveB_false : ∀ c ∈ Card.universe, canRaiseSB u c = false := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

theorem u_sat : SSaturated u := by
  intro c hS
  have h1 : canRaiseSB u c = true := (canRaiseSB_iff u_wf).mpr hS
  have h2 : canRaiseSB u c = false := u_liveB_false c (Card.mem_universe c)
  rw [h2] at h1
  cases h1

/-- At the bottom `F` the S-live set is a SINGLETON: `5H` (and nothing else). -/
theorem F_liveB :
    (Card.universe.all (fun c => !(canRaiseSB F c) || decide (c = H5))) = true := by
  decide

theorem F_liveB_eq_false {c : Card} (hc : c ≠ H5) : canRaiseSB F c = false := by
  have h1 := (List.all_eq_true.mp F_liveB) c (Card.mem_universe c)
  cases hb : canRaiseSB F c with
  | false => rfl
  | true =>
      simp only [hb, Bool.not_true, Bool.false_or] at h1
      exact absurd (of_decide_eq_true h1) hc

theorem F_twin_liveB_false : canRaiseSB F H5.twin = false := by
  have hne : H5.twin ≠ H5 := by decide
  exact F_liveB_eq_false hne

theorem V_liveB_false : ∀ c ∈ Card.universe, canRaiseSB V c = false := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

theorem V_sat : SSaturated V := by
  intro c hS
  have h1 : canRaiseSB V c = true := (canRaiseSB_iff V_wf).mpr hS
  have h2 : canRaiseSB V c = false := V_liveB_false c (Card.mem_universe c)
  rw [h2] at h1
  cases h1

/-! ## §5. The play, the valley split, and the fork-free bottom -/

theorem play_u_B : ShufflePlayW u [mPull, mS1, mS2] F :=
  Walk.cons pull_rev step_pull
    (Walk.cons s1_rev step_s1 (Walk.cons s2_rev step_s2 (Walk.nil F)))

theorem play_F_V : ShufflePlayW F [mRaise] V :=
  Walk.cons raise_rev step_raise (Walk.nil V)

theorem play : ShufflePlayW u rho V :=
  Walk.cons pull_rev step_pull
    (Walk.cons s1_rev step_s1
      (Walk.cons s2_rev step_s2 (Walk.cons raise_rev step_raise (Walk.nil V))))

theorem split : ValleySplitAt u V rho F :=
  ⟨[mPull, mS1, mS2], [mRaise], H5, H5, Sum.inr C6, [], [mS1, mS2], [],
    rfl, play_u_B, play_F_V, rfl,
    by intro m hm
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
       rcases hm with rfl | rfl
       · exact free_slide C4 (Sum.inr H5)
       · exact free_slide C4 (Sum.inr D5),
    rfl⟩

/-- The bottom is not a fork: `ForkWitness F x` forces the twin pair of `x`
to be S-live, but the S-live set at `F` is the singleton `{5H}`. -/
theorem not_fork : ¬ ∃ x : Card, ForkWitness F x := by
  rintro ⟨x, hx⟩
  by_cases hxH : x = H5
  · subst hxH
    have hS : CanRaiseS F H5.twin := (hx.1 H5.twin).mp (Or.inr rfl)
    have h1 : canRaiseSB F H5.twin = true := (canRaiseSB_iff F_wf).mpr hS
    rw [F_twin_liveB_false] at h1
    cases h1
  · have hS : CanRaiseS F x := (hx.1 x).mp (Or.inl rfl)
    have h1 : canRaiseSB F x = true := (canRaiseSB_iff F_wf).mpr hS
    rw [F_liveB_eq_false hxH] at h1
    cases h1

/-! ## §6. No read-safe bracket exists in this play -/

theorem pullTotal_append : ∀ a b : List Move, pullTotal (a ++ b) = pullTotal a + pullTotal b
  | [], b => by simp [pullTotal]
  | m :: t, b => by cases m <;> simp [pullTotal, pullTotal_append t b] <;> omega

theorem rho_pullTotal : pullTotal rho = 1 := by decide

/-- **THE LIST FACT.**  The four-letter word `rho` has NO same-card bracket
with a read-safe interior: it has exactly one pull (`5H`) and one raise
(`5H`), so the bracket is forced to be `(pull 5H, raise 5H)` with the two
slides as interior — and the first slide lands on `5H`. -/
theorem alpha_nil_and_pull {α γ β : List Move} {z : Card} {bz : Base}
    (hρ : rho = α ++ Move.foundToTab z bz :: γ ++ Move.tabToFound z :: β) :
    α = [] ∧ mPull = Move.foundToTab z bz := by
  have hpT :
      pullTotal (α ++ Move.foundToTab z bz :: γ ++ Move.tabToFound z :: β) = 1 := by
    rw [← hρ]
    exact rho_pullTotal
  have hsum : (pullTotal α + (pullTotal γ + 1)) + pullTotal β = 1 := by
    have h := hpT
    rw [pullTotal_append, pullTotal_append] at h
    simpa only [pullTotal] using h
  have hα0 : pullTotal α = 0 := by omega
  -- the prefix has no pull, but `rho` begins with one: it must be empty
  have hαnil : α = [] := by
    cases hα : α with
    | nil => rfl
    | cons a as =>
        exfalso
        rw [hα, List.cons_append] at hρ
        have ha : mPull = a := (List.cons.inj hρ).1
        have hpos : 0 < pullTotal (a :: as) := by
          rw [← ha]
          exact Nat.succ_pos _
        rw [hα] at hα0
        omega
  refine ⟨hαnil, ?_⟩
  subst hαnil
  exact (List.cons.inj hρ).1

theorem no_bracket_data :
    ¬ ∃ (α γ β : List Move) (z : Card) (bz : Base),
      rho = α ++ Move.foundToTab z bz :: γ ++ Move.tabToFound z :: β ∧
      (∀ q ∈ γ, R12.ReadOK z q) := by
  rintro ⟨α, γ, β, z, bz, hρ, hread⟩
  obtain ⟨hαnil, hpull⟩ := alpha_nil_and_pull hρ
  subst hαnil
  cases hpull
  -- the interior is forced
  have hγ : [mS1, mS2, mRaise] = γ ++ Move.tabToFound H5 :: β := (List.cons.inj hρ).2
  cases γ with
  | nil =>
      have h1 : mS1 = Move.tabToFound H5 := (List.cons.inj hγ).1
      cases h1
  | cons g gs =>
      cases gs with
      | nil =>
          have h2 : [mS2, mRaise] = Move.tabToFound H5 :: β := (List.cons.inj hγ).2
          have h1 : mS2 = Move.tabToFound H5 := (List.cons.inj h2).1
          cases h1
      | cons g2 rest =>
          have hg : mS1 = g := (List.cons.inj hγ).1
          have hmem : mS1 ∈ g :: g2 :: rest := by
            rw [← hg]
            exact List.mem_cons_self ..
          have hbad : R12.ReadOK H5 mS1 := hread mS1 hmem
          simp [R12.ReadOK, mS1] at hbad

/-- **`R12.ReadBracketElim` IS FALSE.** -/
theorem not_readBracketElim : ¬ R12.ReadBracketElim := by
  intro h
  rcases h u V rho F u_wf u_sat V_sat play split with hf | hb
  · exact not_fork hf
  · obtain ⟨α, γ, β, z, bz, P, Q, hρ, -, -, -, hread⟩ := hb
    exact no_bracket_data ⟨α, γ, β, z, bz, hρ, hread⟩

/-- The state reached by raising `5H` at the pull landing `B`. -/
def W : State :=
  (B.setFound .heart (B.found .heart ++ [H5])).setPile .p4
    (Pile.afterRunRemoved (B.piles .p4) (chop (B.piles .p4).faceUp))

theorem step_raise_B : State.step B mRaise = some W := by rfl

/-- After `raise 5H` the slide `4C -> 5H` is illegal: `5H` is on the
foundation, so it is not a pile top. -/
theorem step_s1_W : State.step W mS1 = none := by rfl

theorem no_raise_swap :
    ¬ ∃ e, ShufflePlayW B [mRaise, mS1] e := by
  rintro ⟨e, hplay⟩
  obtain ⟨B', -, hstep1, hrest⟩ := Bubble.walk_cons_inv hplay
  obtain ⟨e', -, hstep2, -⟩ := Bubble.walk_cons_inv hrest
  have hB' : B' = W := Option.some.inj (hstep1.symm.trans step_raise_B)
  subst hB'
  rw [step_s1_W] at hstep2
  cases hstep2

/-- **`NonforkKit.NonforkBracketLocal` IS ALSO FALSE** — the same loop: the
only same-card bracket is `(pull 5H, raise 5H)`, whose interior begins with
a slide that CANNOT be crossed by `raise 5H` (the raise founds the slide's
base). -/
theorem not_nonforkBracketLocal : ¬ NonforkKit.NonforkBracketLocal := by
  intro h
  rcases h u V rho F u_wf u_sat V_sat play split with hf | hb
  · exact not_fork hf
  · obtain ⟨α, γ, β, z, bz, P, Q, hρ, hαplay, hstep, hsw⟩ := hb
    obtain ⟨hαnil, hpull⟩ := alpha_nil_and_pull hρ
    subst hαnil
    cases hpull
    -- `α = []` pins `P = u`
    have hP : P = u := by
      have hrun := Walk_run (fun st m => reversibleAtW st m) hαplay
      exact Option.some.inj (by simpa [State.run] using hrun.symm)
    subst hP
    -- the pull pins `Q = B`
    have hQ : Q = B := Option.some.inj (hstep.symm.trans step_pull)
    subst hQ
    -- the head of the interior is the S2-violating slide
    have hγ : [mS1, mS2, mRaise] = γ ++ Move.tabToFound H5 :: β :=
      (List.cons.inj hρ).2
    obtain ⟨gs, hγeq⟩ : ∃ gs, γ = mS1 :: gs := by
      cases γ with
      | nil =>
          have h1 : mS1 = Move.tabToFound H5 := (List.cons.inj hγ).1
          cases h1
      | cons g gs =>
          have h1 : mS1 = g := (List.cons.inj hγ).1
          exact ⟨gs, by rw [h1]⟩
    obtain ⟨e, hplay2, -⟩ := hsw [] B mS1 gs (by simp [hγeq]) (Walk.nil B)
    exact no_raise_swap ⟨e, hplay2⟩

/-- The loop closes: the landing `V` IS the starting position `u`. -/
theorem V_eq_u : V = u := by
  apply State.ext
  · funext s
    cases s <;> rfl
  · funext a
    cases a <;> rfl
  · rfl
  · rfl
  · rfl

/-- The strictly shorter witness play `u -> V` (the empty play). -/
theorem shorter_play_V :
    ∃ ρ' : List Move, ShufflePlayW u ρ' V ∧ ρ'.length < rho.length := by
  refine ⟨[], ?_, by decide⟩
  rw [V_eq_u]
  exact Walk.nil u

end ExistRefute

#print axioms ExistRefute.u_wf
#print axioms ExistRefute.u_sat
#print axioms ExistRefute.V_sat
#print axioms ExistRefute.play
#print axioms ExistRefute.split
#print axioms ExistRefute.not_fork
#print axioms ExistRefute.no_bracket_data
#print axioms ExistRefute.not_readBracketElim
#print axioms ExistRefute.no_raise_swap
#print axioms ExistRefute.not_nonforkBracketLocal
#print axioms ExistRefute.V_eq_u
#print axioms ExistRefute.shorter_play_V
