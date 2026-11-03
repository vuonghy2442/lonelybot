import Temp.PullTwin
import Temp.SpectrumCollapse
import Temp.RaisesOrFork
import Temp.SatDiffer_config


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false

/-!
# Temp/ForkDeadTwin — the dead-twin fork statement, and its refutation

`Temp/PullTwin.lean` reduces the pull case to

```lean
hfork : c.twin ∈ ws → ¬ CanRaiseS v c → Fork s
```

with the data `s.WF`, `State.step s (Move.foundToTab c b) = some u`,
`RaiseSSeqLicensed u ws v`, `∀ d ∈ ws, d.suit ≠ c.suit`.

## What this card proves

* **§1 `dead_twin_z`**: split `ws` at the *chronologically first* `c.twin`
  letter.  The state `z` just before it keeps `c` `S`-live (the preceding
  letters are suit-avoiding and twin-free, so the two licence-inert rows
  apply) and has `c.twin` `S`-live by the letter itself.
* **§2 `fork_of_dead_twin_or_both_vanilla`**: the exact reduction.
  `SpectrumCollapse.spectrum_pair_fork_or_both` at `z` gives either `Fork s`
  (the fork arm, lifted along the orbit) **or** a class-mate `z'` at which the
  spectrum has collapsed onto `{c, c.twin}` and *both* twins are
  vanilla-raisable.  The second arm is the residual.
* **§3 the counterexample**: `hfork` is **false**.  A 15-state orbit
  (`ForkDeadTwinBoard`) contains a pull `5♠` from the foundation, a licensed
  one-letter word `[5♣]` whose cargo leg slides `4♦` onto the pulled `5♠`
  and then raises `5♣`, leaving `5♠` dead — and the orbit is fork-free.
  The positive data (WF, the pull, the play, the death, the both-vanilla
  state) is proved in Lean.  The orbit certificate is a pair of kernel
  `decide` checks — `orbit_closed` (every reversible candidate move of every
  listed state stays in the fifteen-state list) and `orbitForkFree` (no
  listed state is a fork state) — turned into `¬ Fork o0` by the soundness
  lemmas `InOrb_of_shuffle` and `noForkB_sound`.
* **§3.7 `fork_of_dead_twin_false`**: the universal statement is refuted.

House rules: no `sorry`, no `Classical`, no `noncomputable`, no new `Prop`
wrapper.  `#print axioms` on every theorem.
-/

namespace OneColourClosure

/-! ## §1. The first twin letter and the state before it -/

/-- Split a list at its **last** occurrence of `x`: the tail contains no `x`.
(Read on `ws`, whose head is the *last* raise, the last occurrence is the
chronologically first letter.) -/
theorem exists_split_last {α : Type} [DecidableEq α] :
    ∀ (l : List α) (x : α), x ∈ l → ∃ a b : List α, l = a ++ x :: b ∧ x ∉ b
  | [], _, h => absurd h (List.not_mem_nil)
  | y :: t, x, h => by
      by_cases hxt : x ∈ t
      · obtain ⟨a, b, hab, hb⟩ := exists_split_last t x hxt
        exact ⟨y :: a, b, by rw [hab]; rfl, hb⟩
      · have hyx : x = y := by
          rcases List.mem_cons.mp h with h' | h'
          · exact h'
          · exact absurd h' hxt
        subst hyx
        exact ⟨[], t, rfl, hxt⟩

/-- **THE z-STATE.**  `ws` splits as `pre ++ c.twin :: post` with `c.twin ∉ post`,
and at the state `z` after the chronological prefix `post` (before the twin
letter) both `c` and `c.twin` are `S`-live.

`c`'s licence is carried across `post`: every letter of `post` lies in `ws`, so
its suit is not `c`'s (`hno`), and none of them is `c.twin` (`c.twin ∉ post`).
The two rows `canRaiseS_step_of_rank_ne` and
`SatDifferConfig.licence_lost_only_by_twin` are exactly the licence-inert
cases. -/
theorem dead_twin_z {s u v : State} {c : Card} {b : Base} {ws : List Card}
    (hs : s.WF) (hpull : State.step s (Move.foundToTab c b) = some u)
    (hρ : RaiseSSeqLicensed u ws v) (hno : ∀ d ∈ ws, d.suit ≠ c.suit)
    (htw : c.twin ∈ ws) :
    ∃ (pre post : List Card) (z : State),
      ws = pre ++ c.twin :: post ∧ c.twin ∉ post ∧
      RaiseSSeqLicensed u post z ∧ CanRaiseS z c ∧ CanRaiseS z c.twin := by
  obtain ⟨pre, post, hsplit, hpost⟩ := exists_split_last ws c.twin htw
  -- the chronological decomposition: `post` first, then the twin letter
  have hword : ws = playWord (playWord post ++ c.twin :: playWord pre) := by
    rw [hsplit, show playWord post ++ c.twin :: playWord pre
        = (pre ++ c.twin :: post).reverse from by
      simp [playWord, List.reverse_append, List.reverse_cons]]
    exact (List.reverse_reverse _).symm
  have hρ' : RaiseSSeqLicensed u
      (playWord (playWord post ++ c.twin :: playWord pre)) v := by
    rw [← hword]; exact hρ
  obtain ⟨z, hpostz, hrest⟩ :=
    RaiseSSeqLicensed.split_chron (A := playWord post) (R := c.twin :: playWord pre) hρ'
  -- the second component's word is `pre ++ [c.twin]`
  have hrest' : RaiseSSeqLicensed z (pre ++ [c.twin]) v := by
    have hw : playWord (c.twin :: playWord pre) = pre ++ [c.twin] := by
      simp [playWord, List.reverse_cons]
    rw [← hw]; exact hrest
  obtain ⟨z', hsingle, -⟩ := RaiseSSeqLicensed.split_head hrest'
  have hct : CanRaiseS z c.twin := canRaiseS_of_raiseSSeqLicensed_head hsingle
  -- `c`'s licence survives the `post` prefix
  have hpp : playWord (playWord post) = post := by simp [playWord]
  have hpostword : RaiseSSeqLicensed u post z := by
    rw [hpp] at hpostz
    exact hpostz
  have hu : u.WF := step_wf hs hpull
  have hc : CanRaiseS u c := SatDifferConfig.canRaiseS_after_pull hs hpull
  have hself : c ∉ post := by
    intro hmem
    have hws : c ∈ ws := by
      rw [hsplit]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ hmem)
    exact hno c hws rfl
  have htwin : c.twin ∉ post := hpost
  have hcz : CanRaiseS z c :=
    canRaiseS_of_word_notMem hpostword hu hc hself htwin
  exact ⟨pre, post, z, hsplit, hpost, hpostword, hcz, hct⟩

/-! ## §2. Fork, or the both-vanilla arm -/

/-- The pull source and the pull landing are orbit-mates. -/
theorem orbit_source_landing {s u : State} {c : Card} {b : Base}
    (hs : s.WF) (hpull : State.step s (Move.foundToTab c b) = some u) :
    sameOrbitSetoid.r s u := by
  have hback : State.step u (Move.tabToFound c) = some s :=
    step_tabToFound_of_foundToTab hs hpull
  have hrev : reversibleAtW s (Move.foundToTab c b) :=
    reversible_mirrorW hpull hback
  exact sameOrbitSetoid.iseqv.symm
    (shufflePlayW_revEqW (Walk.cons hrev hpull (Walk.nil u)))

/-- **THE EXACT DICHOTOMY.**  Either the pull source is already a fork, or
some orbit-mate `z'` of the pull source has its `S`-live spectrum collapsed
onto `{c, c.twin}` with **both** twins vanilla-raisable.

The second arm is exactly what `SpectrumCollapse.spectrum_pair_fork_or_both`
leaves open; `hdead` plays no role in it, which is the obstruction. -/
theorem fork_of_dead_twin_or_both_vanilla {s u v : State} {c : Card} {b : Base}
    {ws : List Card}
    (hs : s.WF) (hpull : State.step s (Move.foundToTab c b) = some u)
    (hρ : RaiseSSeqLicensed u ws v) (hno : ∀ d ∈ ws, d.suit ≠ c.suit)
    (htw : c.twin ∈ ws) (hdead : ¬ CanRaiseS v c) :
    Fork s ∨
      ∃ z', sameOrbitSetoid.r s z' ∧
        (∀ d, CanRaiseS z' d → d = c ∨ d = c.twin) ∧
        CanRaise z' c ∧ CanRaise z' c.twin := by
  obtain ⟨pre, post, z, hsplit, hpost, hplay, hcz, hctz⟩ :=
    dead_twin_z hs hpull hρ hno htw
  have hu : u.WF := step_wf hs hpull
  have hz : z.WF := RaiseSSeqLicensed.wf hplay hu
  have hsu : sameOrbitSetoid.r s u := orbit_source_landing hs hpull
  have huz : sameOrbitSetoid.r u z :=
    sameOrbitSetoid.iseqv.symm (RaiseSSeqLicensed.revEqW hplay hu)
  have hsz : sameOrbitSetoid.r s z := sameOrbitSetoid.iseqv.trans hsu huz
  rcases SpectrumCollapse.spectrum_pair_fork_or_both hz hcz hctz with hfork | hboth
  · obtain ⟨F, x, hF, hwit⟩ := hfork
    exact Or.inl ⟨F, x, sameOrbitSetoid.iseqv.trans hsz hF, hwit⟩
  · obtain ⟨z', hzz', hsub, hvz, hvtz⟩ := hboth
    exact Or.inr ⟨z', sameOrbitSetoid.iseqv.trans hsz hzz', hsub, hvz, hvtz⟩

/-! ## §3. The counterexample

Board (all other cards are in the stock, `waste = []`, `drawStep = 1`):

```
♥ = A..5   ♦ = A,2,3   ♠ = A..5   ♣ = A..4
p0 = [6♥]        p1 = [6♦, 5♣, 4♦]
```

`pull 5♠ --> 6♥` is legal (`foundToTab 5♠ (inr 6♥)`).  The one-letter word
`[5♣]` is licensed: its cargo leg slides `4♦` from `p1` onto the pulled
`5♠` (legal and reversible), exposing `5♣`; the raise of `5♣` then fires
(`5♣` sits on `6♦`).  At the endpoint `5♠` is covered by `4♦`, `5♣` is on
the foundation, and `4♦` has no legal base — so `5♠` is not `S`-live.

The orbit of the source has exactly 15 states (the `o0 … o14` list below);
it is fork-free.  In `o5` the spectrum is exactly `{5♠, 5♣}` and **both**
twins are vanilla-raisable: the both-vanilla arm of
`fork_of_dead_twin_or_both_vanilla` is realized. -/

namespace ForkDeadTwinBoard

open OneColourClosure

/-! ### §3.1 Cards and states -/

def cH6 : Card := ⟨.heart, .six⟩
def cD6 : Card := ⟨.diamond, .six⟩
def cC5 : Card := ⟨.club, .five⟩
def cD4 : Card := ⟨.diamond, .four⟩
def cS5 : Card := ⟨.spade, .five⟩

/-- The twenty-one cards that are on the board (foundations plus tableau) in
every state of the orbit. -/
def placed : List Card :=
  (Suit.heart.upCards.take 5) ++ (Suit.diamond.upCards.take 3) ++
  (Suit.spade.upCards.take 5) ++ (Suit.club.upCards.take 4) ++
  [cH6, cD6, cC5, cD4]

def rest : List Card :=
  Card.universe.filter (fun x => decide (x ∉ placed))

/-- A board with the given rungs (`h d sp c` = founded counts) and tableau
piles `p0`, `p1`; every other pile is empty. -/
def base (h d sp c : Nat) (p0 p1 : Pile) : State where
  found := fun σ => σ.upCards.take (match σ with
    | .heart => h | .diamond => d | .spade => sp | .club => c)
  piles := fun a => match a with
    | .p0 => p0 | .p1 => p1
    | .p2 => ⟨[], []⟩ | .p3 => ⟨[], []⟩ | .p4 => ⟨[], []⟩
    | .p5 => ⟨[], []⟩ | .p6 => ⟨[], []⟩
  stock := rest
  waste := []
  drawStep := 1

/-! ### §3.2 The fifteen orbit states -/

def o0 : State := base 5 3 5 4 ⟨[], [cH6]⟩ ⟨[], [cD6, cC5, cD4]⟩
def o1 : State := base 5 4 5 4 ⟨[], [cH6]⟩ ⟨[], [cD6, cC5]⟩
def o2 : State := base 5 3 4 4 ⟨[], [cH6, cS5]⟩ ⟨[], [cD6, cC5, cD4]⟩
def o3 : State := base 5 3 5 4 ⟨[], [cH6, cC5, cD4]⟩ ⟨[], [cD6]⟩
def o4 : State := base 5 4 5 5 ⟨[], [cH6]⟩ ⟨[], [cD6]⟩
def o5 : State := base 5 4 4 4 ⟨[], [cH6, cS5]⟩ ⟨[], [cD6, cC5]⟩
def o6 : State := base 5 4 5 4 ⟨[], [cH6, cC5]⟩ ⟨[], [cD6]⟩
def o7 : State := base 5 3 4 4 ⟨[], [cH6, cS5, cD4]⟩ ⟨[], [cD6, cC5]⟩
def o8 : State := base 5 3 4 4 ⟨[], [cH6, cC5, cD4]⟩ ⟨[], [cD6, cS5]⟩
def o9 : State := base 5 4 4 5 ⟨[], [cH6, cS5]⟩ ⟨[], [cD6]⟩
def o10 : State := base 5 4 4 5 ⟨[], [cH6]⟩ ⟨[], [cD6, cS5]⟩
def o11 : State := base 5 4 4 4 ⟨[], [cH6, cC5]⟩ ⟨[], [cD6, cS5]⟩
def o12 : State := base 5 3 4 5 ⟨[], [cH6, cS5, cD4]⟩ ⟨[], [cD6]⟩
def o13 : State := base 5 3 4 4 ⟨[], [cH6, cC5]⟩ ⟨[], [cD6, cS5, cD4]⟩
def o14 : State := base 5 3 4 5 ⟨[], [cH6]⟩ ⟨[], [cD6, cS5, cD4]⟩

def ORB : List State :=
  [o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14]

/-! ### §3.3 The board data, proved -/

/-- Computable well-formedness (the four `State.WF` conjuncts). -/
def wfB (st : State) : Bool :=
  (Suit.all.all (fun σ =>
      st.found σ == σ.upCards.take (st.found σ).length)) &&
  (Anchor.all.all (fun a => runOK (st.piles a).faceUp)) &&
  (Card.universe.all (fun c => st.cardCount c == 1)) &&
  decide (0 < st.drawStep)

theorem wfB_sound {st : State} (h : wfB st = true) : st.WF := by
  rw [wfB, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro σ
    have hσ := (List.all_eq_true.mp h1) σ (Suit.mem_all σ)
    rw [beq_iff_eq] at hσ
    exact ⟨_, hσ⟩
  · intro a
    exact (List.all_eq_true.mp h2) a (Anchor.mem_all a)
  · intro c hc
    have hc' := (List.all_eq_true.mp h3) c hc
    rw [beq_iff_eq] at hc'
    exact hc'
  · exact of_decide_eq_true h4

theorem orb_wfB : ORB.all wfB = true := by decide

theorem orb_wf {w : State} (hw : w ∈ ORB) : w.WF :=
  wfB_sound ((List.all_eq_true.mp orb_wfB) w hw)

theorem o0_wf : o0.WF := orb_wf (by simp [ORB])
theorem o2_wf : o2.WF := orb_wf (by simp [ORB])
theorem o5_wf : o5.WF := orb_wf (by simp [ORB])
theorem o7_wf : o7.WF := orb_wf (by simp [ORB])
theorem o12_wf : o12.WF := orb_wf (by simp [ORB])

/-- The pull: `5♠` leaves the spade foundation and lands on `6♥`. -/
theorem pull : State.step o0 (Move.foundToTab cS5 (Sum.inr cH6)) = some o2 := by
  rw [step_foundToTab_splice (by decide) (by decide)]
  congr 1
  refine State.ext (funext fun σ => ?_) (funext fun a => ?_) rfl rfl rfl
  · cases σ <;> decide
  · cases a <;> decide

/-- The cargo leg: `4♦` slides from `p1` onto the pulled `5♠`. -/
theorem slide : State.step o2 (Move.tabToTab cD4 (Sum.inr cS5)) = some o7 := by
  have hph : o2.pileHolding cD4 = some Anchor.p1 := by decide
  have hcp : o2.canPlace cD4 (Sum.inr cS5) = true := by decide
  have hfrom : fromCard cD4 (o2.piles Anchor.p1).faceUp = [cD4] := by decide
  have hbelow : below cD4 (o2.piles Anchor.p1).faceUp = [cD6, cC5] := by decide
  rw [step_tabToTab_eq]
  simp only [hph, hcp, hfrom, hbelow, ite_true]
  congr 1
  refine State.ext (funext fun σ => ?_) (funext fun a => ?_) rfl rfl rfl
  · cases σ <;> decide
  · cases a <;> decide

/-- The reverse slide (so the leg is reversible). -/
theorem slide_back : State.step o7 (Move.tabToTab cD4 (Sum.inr cC5)) = some o2 := by
  have hph : o7.pileHolding cD4 = some Anchor.p0 := by decide
  have hcp : o7.canPlace cD4 (Sum.inr cC5) = true := by decide
  have hfrom : fromCard cD4 (o7.piles Anchor.p0).faceUp = [cD4] := by decide
  have hbelow : below cD4 (o7.piles Anchor.p0).faceUp = [cH6, cS5] := by decide
  rw [step_tabToTab_eq]
  simp only [hph, hcp, hfrom, hbelow, ite_true]
  congr 1
  refine State.ext (funext fun σ => ?_) (funext fun a => ?_) rfl rfl rfl
  · cases σ <;> decide
  · cases a <;> decide

theorem leg : CargoLeg o2 o7 :=
  ⟨cD4, Sum.inr cS5, slide, reversible_mirrorW slide slide_back⟩

theorem path : CargoPath o2 o7 := Steps.cons leg (Steps.refl o7)

/-- `5♣` is `S`-live at the landing (the slide exposes it). -/
theorem o2_live_cC5 : CanRaiseS o2 cC5 :=
  (canRaiseSB_iff o2_wf).mp (by decide)

/-- The raise of `5♣`, firing at the end of the cargo leg. -/
theorem raise5C : State.step o7 (Move.tabToFound cC5) = some o12 := by
  rw [step_tabToFound_splice (k := Anchor.p1) (by decide) (by decide)]
  congr 1
  refine State.ext (funext fun σ => ?_) (funext fun a => ?_) rfl rfl rfl
  · cases σ <;> decide
  · cases a <;> decide

/-- **The licensed word `[5♣]` from the pull landing.** -/
theorem play : RaiseSSeqLicensed o2 [cC5] o12 :=
  RaiseSSeqLicensed.cons (RaiseSSeqLicensed.nil o2) o2_live_cC5 path raise5C

theorem hno : ∀ d ∈ [cC5], d.suit ≠ cS5.suit := by
  intro d hd
  rw [List.mem_singleton] at hd
  subst hd
  decide

theorem twin_mem : cS5.twin ∈ [cC5] := by decide

/-- **The pulled `5♠` is dead at the endpoint** (covered by `4♦`, whose only
legal base is `5♠` itself, and `5♣` no longer tops a pile). -/
theorem o12_dead_cS5 : ¬ CanRaiseS o12 cS5 := by
  intro h
  have hSB : canRaiseSB o12 cS5 = true := (canRaiseSB_iff o12_wf).mpr h
  have hfalse : canRaiseSB o12 cS5 = false := by decide
  rw [hfalse] at hSB
  exact Bool.noConfusion hSB

/-! ### §3.4 The both-vanilla state -/

/-- At `o5` both twins are vanilla-raisable. -/
theorem o5_canRaise_cS5 : CanRaise o5 cS5 := by
  refine ⟨by decide, Anchor.p0, by decide, Or.inl (by decide)⟩

theorem o5_canRaise_cC5 : CanRaise o5 cC5 := by
  refine ⟨by decide, Anchor.p1, by decide, Or.inl (by decide)⟩

/-- At `o5` the `S`-live spectrum is exactly the twin pair. -/
theorem o5_spectrum : ∀ d : Card, CanRaiseS o5 d → d = cS5 ∨ d = cC5 := by
  intro d hd
  have hSB : canRaiseSB o5 d = true := (canRaiseSB_iff o5_wf).mpr hd
  rcases d with ⟨σ, r⟩
  cases σ <;> cases r <;>
    first
      | decide
      | (exfalso; revert hSB; decide)


/-! ### §3.5 The orbit certificate

The orbit of `o0` under reversible moves is certified computably.  `stateEqB`
is a structural equality test on states (`State` has function fields, so no
`DecidableEq`); `InOrb` tests membership in the fifteen-state list; `checkStep`
tests that every reversible candidate move of a state lands in the list.
`orbit_closed` and `orbitForkFree` are kernel `decide` checks, and the
soundness lemmas turn them into the statement that every reversible
orbit-mate of `o0` is fork-free. -/

def stateEqB (x y : State) : Bool :=
  decide (
    x.found .heart = y.found .heart ∧
    x.found .diamond = y.found .diamond ∧
    x.found .spade = y.found .spade ∧
    x.found .club = y.found .club ∧
    (x.piles .p0).hidden = (y.piles .p0).hidden ∧
    (x.piles .p0).faceUp = (y.piles .p0).faceUp ∧
    (x.piles .p1).hidden = (y.piles .p1).hidden ∧
    (x.piles .p1).faceUp = (y.piles .p1).faceUp ∧
    (x.piles .p2).hidden = (y.piles .p2).hidden ∧
    (x.piles .p2).faceUp = (y.piles .p2).faceUp ∧
    (x.piles .p3).hidden = (y.piles .p3).hidden ∧
    (x.piles .p3).faceUp = (y.piles .p3).faceUp ∧
    (x.piles .p4).hidden = (y.piles .p4).hidden ∧
    (x.piles .p4).faceUp = (y.piles .p4).faceUp ∧
    (x.piles .p5).hidden = (y.piles .p5).hidden ∧
    (x.piles .p5).faceUp = (y.piles .p5).faceUp ∧
    (x.piles .p6).hidden = (y.piles .p6).hidden ∧
    (x.piles .p6).faceUp = (y.piles .p6).faceUp ∧
    x.stock = y.stock ∧ x.waste = y.waste ∧ x.drawStep = y.drawStep)

theorem pile_eq_of {p q : Pile} (h1 : p.hidden = q.hidden) (h2 : p.faceUp = q.faceUp) :
    p = q := by
  cases p; cases q; simp_all

theorem stateEqB_refl (x : State) : stateEqB x x = true := by
  rw [stateEqB, decide_eq_true_eq]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem stateEqB_sound {x y : State} (h : stateEqB x y = true) : x = y := by
  rw [stateEqB, decide_eq_true_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
    h15, h16, h17, h18, h19, h20, h21⟩ := h
  refine State.ext ?_ ?_ h19 h20 h21
  · funext σ; cases σ <;> assumption
  · funext a; cases a <;> (refine pile_eq_of ?_ ?_ <;> assumption)

/-- Membership in the fifteen-state list, as a Boolean. -/
def InOrb (x : State) : Bool := ORB.any (fun w => stateEqB x w)

theorem InOrb_sound {x : State} (h : InOrb x = true) : x ∈ ORB := by
  rw [InOrb, List.any_eq_true] at h
  obtain ⟨w, hw, heq⟩ := h
  rw [stateEqB_sound heq]
  exact hw

theorem InOrb_self {w : State} (hw : w ∈ ORB) : InOrb w = true :=
  List.any_eq_true.mpr ⟨w, hw, stateEqB_refl w⟩

/-- Every base, listed. -/
def allBases (st : State) : List Base :=
  Anchor.all.map Sum.inl ++ Card.universe.map Sum.inr

theorem mem_allBases (st : State) (b : Base) : b ∈ allBases st := by
  cases b with
  | inl a => exact List.mem_append_left _ (List.mem_map.mpr ⟨a, Anchor.mem_all a, rfl⟩)
  | inr z => exact List.mem_append_right _ (List.mem_map.mpr ⟨z, Card.mem_universe z, rfl⟩)

/-- Every candidate move: the draw, and every card against every base. -/
def allMoves (st : State) : List Move :=
  [Move.draw] ++
    Card.universe.flatMap (fun c =>
      [Move.wasteToFound c, Move.tabToFound c] ++
        (allBases st).flatMap (fun b =>
          [Move.wasteToTab c b, Move.foundToTab c b, Move.tabToTab c b]))

theorem mem_allMoves {st : State} {m : Move} (hm : reversibleOf st m = true) :
    m ∈ allMoves st := by
  cases m with
  | draw => exact List.mem_append_left _ (List.mem_singleton_self _)
  | wasteToFound c => exact Bool.noConfusion hm
  | wasteToTab c b => exact Bool.noConfusion hm
  | tabToFound c =>
      refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨c, Card.mem_universe c, ?_⟩)
      simp
  | foundToTab c b =>
      refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨c, Card.mem_universe c, ?_⟩)
      refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨b, mem_allBases st b, ?_⟩)
      simp
  | tabToTab c b =>
      refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨c, Card.mem_universe c, ?_⟩)
      refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨b, mem_allBases st b, ?_⟩)
      simp

/-- The closure test for one state. -/
def checkStep (st : State) : Bool :=
  (allMoves st).all (fun m =>
    if reversibleOf st m then
      match State.step st m with
      | none => true
      | some w => InOrb w
    else true)

theorem checkStep_sound {st : State} {m : Move} {v : State}
    (hcheck : checkStep st = true) (hm : reversibleOf st m = true)
    (hstep : State.step st m = some v) : InOrb v = true := by
  have hb := (List.all_eq_true.mp hcheck) m (mem_allMoves hm)
  simp only [hm, ite_true] at hb
  rw [hstep] at hb
  exact hb

theorem orbit_closed : ORB.all checkStep = true := by decide

theorem InOrb_of_shuffle {s F : State} {play : List Move}
    (h : ShufflePlayW s play F) :
    s.WF → InOrb s = true → InOrb F = true := by
  induction h with
  | nil => intro _ h0; exact h0
  | cons hw hstep hrest ih =>
      intro hs h0
      have hwf1 : _ := step_wf hs hstep
      have hm : reversibleOf _ _ = true :=
        (reversibleOf_iff_reversibleAtW hs _).mpr hw
      have hch : checkStep _ = true :=
        (List.all_eq_true.mp orbit_closed) _ (InOrb_sound h0)
      exact ih hwf1 (checkStep_sound hch hm hstep)

/-! ### §3.6 Fork-freeness of the orbit -/

/-- The pair-spectrum clause as a Boolean. -/
def twinPairSpecB (st : State) (x : Card) : Bool :=
  Card.universe.all (fun c =>
    (decide (c = x) || decide (c = x.twin)) == canRaiseSB st c)

def forkWitnessB (st : State) (x : Card) : Bool :=
  twinPairSpecB st x && !(tabToFoundR st x.twin)

def noForkB (st : State) : Bool :=
  Card.universe.all (fun x => !(forkWitnessB st x))

/-- The pair-spectrum clause is *complete*: a spectrum equality forces the
Boolean. -/
theorem twinPairSpecB_complete {st : State} (hwf : st.WF) {x : Card}
    (h : ∀ c, (c = x ∨ c = x.twin) ↔ CanRaiseS st c) :
    twinPairSpecB st x = true := by
  rw [twinPairSpecB, List.all_eq_true]
  intro c _
  rw [beq_iff_eq]
  have hiff := h c
  by_cases hc : c = x ∨ c = x.twin
  · have hS : CanRaiseS st c := hiff.mp hc
    have hb : canRaiseSB st c = true := (canRaiseSB_iff hwf).mpr hS
    have hl : (decide (c = x) || decide (c = x.twin)) = true := by
      rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      exact hc
    rw [hl, hb]
  · have hS : ¬ CanRaiseS st c := fun hs => hc (hiff.mpr hs)
    have hb : canRaiseSB st c = false := by
      cases hh : canRaiseSB st c with
      | true => exact absurd ((canRaiseSB_iff hwf).mp hh) hS
      | false => rfl
    have hl : (decide (c = x) || decide (c = x.twin)) = false := by
      rw [Bool.or_eq_false_iff]
      exact ⟨by simpa using fun h1 => hc (Or.inl h1),
        by simpa using fun h2 => hc (Or.inr h2)⟩
    rw [hl, hb]

theorem noForkB_sound {st : State} (hwf : st.WF) (h : noForkB st = true) :
    ¬ forkState st := by
  rintro ⟨x, hwit⟩
  obtain ⟨hspec, hblock⟩ := hwit
  have hx := (List.all_eq_true.mp h) x (Card.mem_universe x)
  have hsp : twinPairSpecB st x = true := twinPairSpecB_complete hwf hspec
  have hcb : tabToFoundR st x.twin = false := by
    cases hh : tabToFoundR st x.twin with
    | true => exact absurd ((tabToFoundR_iff_canRaise st x.twin).mp hh) hblock
    | false => rfl
  have hfw : forkWitnessB st x = true := by
    rw [forkWitnessB, hsp, hcb]
    rfl
  rw [hfw] at hx
  exact Bool.noConfusion hx

theorem orbitForkFree : ORB.all noForkB = true := by decide

/-- **The source is not a fork.**  Every reversible orbit-mate of `o0` is one
of the fifteen states, and none of them is a fork state. -/
theorem not_fork_o0 : ¬ Fork o0 := by
  intro hfork
  obtain ⟨F, x, horb, hwit⟩ := hfork
  obtain ⟨_, _, play, hplay⟩ := horb
  have hin : InOrb F = true :=
    InOrb_of_shuffle hplay o0_wf (InOrb_self (by simp [ORB]))
  have hFORB : F ∈ ORB := InOrb_sound hin
  have hnf : noForkB F = true := (List.all_eq_true.mp orbitForkFree) F hFORB
  exact noForkB_sound (orb_wf hFORB) hnf ⟨x, hwit⟩

/-! ### §3.7 The refutation -/

/-- **THE UNIVERSAL STATEMENT IS FALSE.**  `fork_of_dead_twin` fails on the
board above: `c = 5♠`, `ws = [5♣]`, `c.twin = 5♣`, and `5♠` dies. -/
theorem fork_of_dead_twin_false :
    ¬ (∀ (s u v : State) (c : Card) (b : Base) (ws : List Card),
        s.WF → State.step s (Move.foundToTab c b) = some u →
        RaiseSSeqLicensed u ws v → (∀ d ∈ ws, d.suit ≠ c.suit) →
        c.twin ∈ ws → ¬ CanRaiseS v c → Fork s) := by
  intro h
  exact not_fork_o0
    (h o0 o2 o12 cS5 (Sum.inr cH6) [cC5] o0_wf pull play hno twin_mem o12_dead_cS5)

end ForkDeadTwinBoard

end OneColourClosure

#print axioms OneColourClosure.exists_split_last
#print axioms OneColourClosure.dead_twin_z
#print axioms OneColourClosure.orbit_source_landing
#print axioms OneColourClosure.fork_of_dead_twin_or_both_vanilla
#print axioms OneColourClosure.ForkDeadTwinBoard.wfB_sound
#print axioms OneColourClosure.ForkDeadTwinBoard.orb_wfB
#print axioms OneColourClosure.ForkDeadTwinBoard.orb_wf
#print axioms OneColourClosure.ForkDeadTwinBoard.o0_wf
#print axioms OneColourClosure.ForkDeadTwinBoard.o2_wf
#print axioms OneColourClosure.ForkDeadTwinBoard.o5_wf
#print axioms OneColourClosure.ForkDeadTwinBoard.o7_wf
#print axioms OneColourClosure.ForkDeadTwinBoard.o12_wf
#print axioms OneColourClosure.ForkDeadTwinBoard.pull
#print axioms OneColourClosure.ForkDeadTwinBoard.slide
#print axioms OneColourClosure.ForkDeadTwinBoard.slide_back
#print axioms OneColourClosure.ForkDeadTwinBoard.leg
#print axioms OneColourClosure.ForkDeadTwinBoard.path
#print axioms OneColourClosure.ForkDeadTwinBoard.o2_live_cC5
#print axioms OneColourClosure.ForkDeadTwinBoard.raise5C
#print axioms OneColourClosure.ForkDeadTwinBoard.play
#print axioms OneColourClosure.ForkDeadTwinBoard.hno
#print axioms OneColourClosure.ForkDeadTwinBoard.twin_mem
#print axioms OneColourClosure.ForkDeadTwinBoard.o12_dead_cS5
#print axioms OneColourClosure.ForkDeadTwinBoard.o5_canRaise_cS5
#print axioms OneColourClosure.ForkDeadTwinBoard.o5_canRaise_cC5
#print axioms OneColourClosure.ForkDeadTwinBoard.o5_spectrum
#print axioms OneColourClosure.ForkDeadTwinBoard.pile_eq_of
#print axioms OneColourClosure.ForkDeadTwinBoard.stateEqB_refl
#print axioms OneColourClosure.ForkDeadTwinBoard.stateEqB_sound
#print axioms OneColourClosure.ForkDeadTwinBoard.InOrb_sound
#print axioms OneColourClosure.ForkDeadTwinBoard.InOrb_self
#print axioms OneColourClosure.ForkDeadTwinBoard.mem_allBases
#print axioms OneColourClosure.ForkDeadTwinBoard.mem_allMoves
#print axioms OneColourClosure.ForkDeadTwinBoard.checkStep_sound
#print axioms OneColourClosure.ForkDeadTwinBoard.orbit_closed
#print axioms OneColourClosure.ForkDeadTwinBoard.InOrb_of_shuffle
#print axioms OneColourClosure.ForkDeadTwinBoard.twinPairSpecB_complete
#print axioms OneColourClosure.ForkDeadTwinBoard.noForkB_sound
#print axioms OneColourClosure.ForkDeadTwinBoard.orbitForkFree
#print axioms OneColourClosure.ForkDeadTwinBoard.not_fork_o0
#print axioms OneColourClosure.ForkDeadTwinBoard.fork_of_dead_twin_false
