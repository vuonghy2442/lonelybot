import Orig2.ForkRelocate
import Orig2.ForkSplit
import Orig2.ForkLedger
import Orig2.ForkSafeTransport
import Orig2.ForkBaseEnabling

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# CrossSuit_Vacuity - the cross-suit raise-before-pull reduction

**THE CENTRAL PREMISE IS FALSE — KERNEL-CERTIFIED.**  The certificate is
`Archive/Cert/ForkCertMain.lean` / `Archive/Cert/ForkCertInv.lean` (leaf chain; build with
`Tools/build_crosssuit_cert.ps1`, ~406 s parallel): a 17-letter shortest
`SSaturated → SSaturated` witness play (`Cert.play`, `Cert.play_shortest`,
`d(u,v) = 17` from a 2308-state distance table) with `Cert.inv_rho : inv = 8`,
and

```lean
Cert.not_crossSuitCorridorResidual      : ¬ CrossSuitCorridorResidual
Cert.not_crossSuitPureCorridorResidual  : ¬ CrossSuitPureCorridorResidual
Cert.not_crossSuitVacuityTarget         : ¬ CrossSuitVacuityTarget
```

Axioms `[propext, Quot.sound]` only.  So `crossSuitVacuity`,
`noCrossCorridor` and the corridor residuals are FALSE; the cross-suit case
is REAL.  Do not cite these rows as residuals.  The kernel-checked companion
`Orig2/ForkSeatTwinNoGo.lean` shows the literal seat-mate pattern is
impossible — the counterexample is not seat-mate.

Source card (`Orig2/`).  Zero `sorry`, zero `Classical.choice`, zero
`native_decide`; axiom battery at the tail.

## The target

```text
crossSuitVacuity
  u.WF → SSaturated u → SSaturated v → ShufflePlayW u ρ v → (ρ is minimal) →
  ∀ i j c d b, i < j → ρ[i] = raise c → ρ[j] = pull d b → c.suit ≠ d.suit → False
```

A minimal witness play between two `SSaturated` endpoints never raises one suit
and later pulls a different one.  The same-card raise-then-pull is net-ONE
(`MtnPr.raise_pull_eq_slide`, `MtnPr.adjacent_raise_pull_shortens`) with its own
residual machinery (`MtnPr.SameCardRelocation`,
`BaseEnabling.sameCardRelocation_of_baseEnabling`), so cross-suit vacuity is
exactly what would collapse the mountain's hardest case into the same-card case.

## What this card proves (all kernel-checked)

* **§1 the lock** (lever 1 of the brief).  A letter of suit `≠ σ` cannot change
  the `σ`-column of the foundation (`found_eq_of_avoids`,
  `foundTop_eq_of_avoids`), so the first `σ`-pull after `raise c` pulls **`c`
  itself** (`first_suit_pull_card`, `lock_pull_eq_raised`).
* **§1.4 the ledger face of the lock.**  With no `σ`-pull the `σ`-rung climbs by
  exactly the `σ`-raises (`rung_eq_add_raises_of_no_pull`), so a locked column
  strictly rises.
* **§2 the corridor normal form** (`clean_of_cross`).  Any cross-suit
  raise-before-pull pair can be replaced by one whose **corridor** carries no
  raise off the pull's suit and no pull off the raise's suit.  The theorem
  therefore reduces, losslessly, to the corridor shape.
* **§2.4 the corridor lock** (`corridor_pull_is_c`).  In a clean cross-suit
  corridor, the **first** pull of the corridor pulls the raised card.  So a
  corridor that pulls at all contains the same-card seat `raise c ; … ; pull c`;
  the genuinely cross-suit content is the **pull-free** corridor.
* **§3 the named residual** `CrossSuitCorridorResidual` — an explicit
  minimal-play statement about corridor-shaped plays — and
  **`crossSuitVacuity_of_residual : CrossSuitCorridorResidual → crossSuitVacuity`**
  (`crossSuitVacuity_of_residual`, index form).
* **§4 the sharpened split** (`pureResidual_of_sameCard`): the corridor residual
  follows from
  * `SameCardFreeInteriorShortens` — the same-card relocation with an arbitrary
    interior (the gated `MtnPr.SameCardRelocation` is its read-safe/seat-inert
    face), and
  * `CrossSuitPureCorridorResidual` — the **pull-free** corridor only.

  So the whole cross-suit weight sits on the pull-free corridor; see
  `Temp/CrossSuit_Report.md`.
-/

namespace CrossSuit

open ValleyElim

/-!
## §1. The lock: a `σ`-free letter leaves the `σ`-column alone
-/

/-- **`AvoidsSuit σ m`** — the letter `m` does not touch suit `σ`: it is a
`draw`/`tabToTab` (`FreeMove`, rung-preserving) or a raise/pull of another suit.
(The waste letters are never witness letters; they are deliberately `True` here
so the predicate is total.) -/
def AvoidsSuit (σ : Suit) : Move → Prop
  | Move.tabToFound c => c.suit ≠ σ
  | Move.foundToTab c _ => c.suit ≠ σ
  | _ => True

theorem avoidsSuit_raise {σ : Suit} {c : Card} (h : c.suit ≠ σ) :
    AvoidsSuit σ (Move.tabToFound c) := h

theorem avoidsSuit_pull {σ : Suit} {c : Card} {b : Base} (h : c.suit ≠ σ) :
    AvoidsSuit σ (Move.foundToTab c b) := h

/-- A slide moves only piles: the whole foundation is fixed. -/
theorem found_tabToTab_eq {st w : State} {c : Card} {b : Base}
    (hstep : State.step st (Move.tabToTab c b) = some w) : w.found = st.found := by
  obtain ⟨a, -, -, -, hw⟩ := step_tabToTab_inv hstep
  rw [hw, putRun_found, setPile_found]

/-- A pull of another suit leaves the `σ`-column alone. -/
theorem found_foundToTab_ne {st w : State} {c : Card} {b : Base}
    (hstep : State.step st (Move.foundToTab c b) = some w) {s : Suit} (hs : s ≠ c.suit) :
    w.found s = st.found s := by
  obtain ⟨c', -, hc', -, hw⟩ := step_foundToTab_inv hstep
  rw [hw, putCard_found]
  exact setFound_found_ne hs

/-- **A `σ`-free witness letter leaves the `σ`-column alone.** -/
theorem found_step_of_avoids {st w : State} {m : Move} {σ : Suit}
    (hstep : State.step st m = some w) (hrev : reversibleAtW st m)
    (h : AvoidsSuit σ m) : w.found σ = st.found σ := by
  cases m with
  | draw => rw [stepDraw_found hstep]
  | tabToTab c b => rw [found_tabToTab_eq hstep]
  | tabToFound c =>
      exact SafeTransport.found_tabToFound_ne hstep (fun hh => h hh.symm)
  | foundToTab c b =>
      exact found_foundToTab_ne hstep (fun hh => h hh.symm)
  | wasteToFound c => exact absurd hrev (wasteToFound_not_reversibleAtW st c)
  | wasteToTab c b => exact absurd hrev (wasteToTab_not_reversibleAtW st c b)

/-- **THE COLUMN-TRANSPORT.**  Along a witness play whose every letter avoids
`σ`, the `σ`-column of the foundation is unchanged. -/
theorem found_eq_of_avoids {u v : State} {ρ : List Move} {σ : Suit}
    (hplay : ShufflePlayW u ρ v) (h : ∀ m ∈ ρ, AvoidsSuit σ m) :
    v.found σ = u.found σ := by
  induction hplay with
  | nil st => rfl
  | @cons st s₁ W m ρ' hrev hstep hrest ih =>
      have hm : AvoidsSuit σ m := h m (List.mem_cons_self ..)
      have ht : ∀ m' ∈ ρ', AvoidsSuit σ m' :=
        fun m' hm' => h m' (List.mem_cons_of_mem m hm')
      rw [ih ht]
      exact found_step_of_avoids hstep hrev hm

/-- **THE TOP-TRANSPORT.**  Along a `σ`-free witness play the `σ`-foundation top
is unchanged. -/
theorem foundTop_eq_of_avoids {u v : State} {ρ : List Move} {σ : Suit}
    (hplay : ShufflePlayW u ρ v) (h : ∀ m ∈ ρ, AvoidsSuit σ m) :
    v.foundTop σ = u.foundTop σ := by
  unfold State.foundTop
  rw [found_eq_of_avoids hplay h]

/-- **THE FIRST `σ`-PULL PULLS THE `σ`-TOP.**  A play whose prefix avoids `σ`
and whose next letter is a `σ`-pull must pull exactly the `σ`-foundation top at
the origin. -/
theorem first_suit_pull_card {u v : State} {α β : List Move} {σ : Suit} {a e : Card}
    {b : Base}
    (hplay : ShufflePlayW u (α ++ Move.foundToTab e b :: β) v)
    (htop : u.foundTop σ = some a)
    (havoid : ∀ m ∈ α, AvoidsSuit σ m) (he : e.suit = σ) : e = a := by
  obtain ⟨A, hα, hrest⟩ := ValleyElim.ShufflePlayW_split hplay α _ rfl
  have hA : A.foundTop σ = some a := by
    rw [foundTop_eq_of_avoids hα havoid]; exact htop
  obtain ⟨T, -, hstep, -⟩ := Bubble.walk_cons_inv hrest
  obtain ⟨e', htop', he', -, -⟩ := step_foundToTab_inv hstep
  rw [he] at htop'
  have h1 : e' = a := Option.some.inj (htop'.symm.trans hA)
  exact he'.symm.trans h1

/-!
### §1.3 The lock, at a raise
-/

/-- **THE LOCK.**  After `raise c`, the first `σ`-pull (`σ = c.suit`) pulls `c`
itself.  Split form: if the interior `γ` is `c.suit`-free and the next `σ`-pull
follows it, that pull's card is `c`.

This is lever 1 of the brief, kernel-checked: **a raise LOCKS its suit** — the
only card the raised suit can give back while the column is untouched is the
raised card. -/
theorem lock_pull_eq_raised {u v : State} {pre γ tail : List Move} {c e : Card} {b : Base}
    (hplay : ShufflePlayW u
      (pre ++ Move.tabToFound c :: γ ++ Move.foundToTab e b :: tail) v)
    (havoid : ∀ m ∈ γ, AvoidsSuit c.suit m) (he : e.suit = c.suit) : e = c := by
  obtain ⟨A, -, hrest⟩ := ValleyElim.ShufflePlayW_split hplay pre
    (Move.tabToFound c :: γ ++ Move.foundToTab e b :: tail)
    (by simp only [List.append_assoc])
  obtain ⟨T, -, hstep, htail⟩ := Bubble.walk_cons_inv hrest
  obtain ⟨-, a, -, hs1⟩ := step_tabToFound_inv hstep
  have hT : T = raiseSt A c a := by rw [hs1]; rfl
  rw [hT] at htail
  exact first_suit_pull_card (u := raiseSt A c a) htail
    (BaseEn.foundTop_raiseSt_self A c a) havoid he

/-!
### §1.4 The ledger face of the lock
-/

/-- **A PULL-FREE COLUMN CLIMBS BY ITS RAISES.**  If the play contains no `σ`-pull
then the `σ`-rung at the endpoint is the origin's plus the number of `σ`-raises
(`LedgerKit.rungAt_ledger` with `pullsOf = 0`). -/
theorem rung_eq_add_raises_of_no_pull {u v : State} {ρ : List Move} {σ : Suit}
    (hplay : ShufflePlayW u ρ v) (hp : pullsOf ρ σ = 0) :
    rungAt v σ = rungAt u σ + raisesOf ρ σ := by
  have h := LedgerKit.rungAt_ledger (σ := σ) hplay
  omega

/-- **THE COLUMN NEVER FALLS WITHOUT A PULL.** -/
theorem rung_ge_of_no_pull {u v : State} {ρ : List Move} {σ : Suit}
    (hplay : ShufflePlayW u ρ v) (hp : pullsOf ρ σ = 0) :
    rungAt u σ ≤ rungAt v σ := by
  have h := rung_eq_add_raises_of_no_pull hplay hp
  omega

/-- **A LOCKED COLUMN STRICTLY RISES.**  A `σ`-raise in a `σ`-pull-free play
leaves the endpoint's `σ`-rung strictly above the origin's. -/
theorem rung_strict_of_raise_of_no_pull {u v : State} {ρ : List Move} {σ : Suit}
    (hplay : ShufflePlayW u ρ v) (hp : pullsOf ρ σ = 0) (hr : 0 < raisesOf ρ σ) :
    rungAt u σ < rungAt v σ := by
  have h := rung_eq_add_raises_of_no_pull hplay hp
  omega

/-!
## §2. The corridor normal form
-/

/-- **`CorridorClean γ c d`** — the corridor `γ` between a raise of `c` and a pull
of `d` carries no raise off suit `d.suit` and no pull off suit `c.suit`.  (Its
free letters are unconstrained.) -/
def CorridorClean (γ : List Move) (c d : Card) : Prop :=
  (∀ e : Card, Move.tabToFound e ∈ γ → e.suit = d.suit) ∧
    (∀ (e : Card) (b : Base), Move.foundToTab e b ∈ γ → e.suit = c.suit)

/-- **`PullFree γ`** — the corridor pulls nothing. -/
def PullFree (γ : List Move) : Prop :=
  ∀ (e : Card) (b : Base), Move.foundToTab e b ∈ γ → False

/-- **`CrossCorridor ρ`** — the play carries a raise-before-pull pair of two
different suits. -/
def CrossCorridor (ρ : List Move) : Prop :=
  ∃ (pre γ tail : List Move) (c d : Card) (b : Base),
    ρ = pre ++ Move.tabToFound c :: γ ++ Move.foundToTab d b :: tail ∧
      c.suit ≠ d.suit

/-- **`CleanCrossCorridor ρ`** — the same, with the corridor in normal form. -/
def CleanCrossCorridor (ρ : List Move) : Prop :=
  ∃ (pre γ tail : List Move) (c d : Card) (b : Base),
    ρ = pre ++ Move.tabToFound c :: γ ++ Move.foundToTab d b :: tail ∧
      c.suit ≠ d.suit ∧ CorridorClean γ c d

theorem crossCorridor_of_clean {ρ : List Move} (h : CleanCrossCorridor ρ) :
    CrossCorridor ρ := by
  obtain ⟨pre, γ, tail, c, d, b, heq, hne, -⟩ := h
  exact ⟨pre, γ, tail, c, d, b, heq, hne⟩

/-- A member of a list splits it. -/
theorem exists_split_of_mem {m : Move} : ∀ {l : List Move}, m ∈ l →
    ∃ a b : List Move, l = a ++ m :: b := by
  intro l
  induction l with
  | nil => intro h; exact absurd h (by simp)
  | cons z zs ih =>
      intro h
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨[], zs, rfl⟩
      · obtain ⟨a, b, hb⟩ := ih h
        exact ⟨z :: a, b, by rw [hb]; rfl⟩

/-- The corridor extends by an admissible head letter. -/
theorem corridorClean_cons {z : Move} {zs : List Move} {c d : Card}
    (hzs : CorridorClean zs c d)
    (hzd : ∀ e : Card, z = Move.tabToFound e → e.suit = d.suit)
    (hzc : ∀ (e : Card) (b : Base), z = Move.foundToTab e b → e.suit = c.suit) :
    CorridorClean (z :: zs) c d := by
  refine ⟨?_, ?_⟩
  · intro e' he'
    rcases List.mem_cons.mp he' with h | he'
    · exact hzd e' h.symm
    · exact hzs.1 e' he'
  · intro e' b' he'
    rcases List.mem_cons.mp he' with h | he'
    · exact hzc e' b' h.symm
    · exact hzs.2 e' b' he'

/-- **THE CORRIDOR DICHOTOMY (constructive).**  Every corridor is either clean,
or carries a raise off the pull's suit, or carries a pull off the raise's suit.
Proved by recursion on the list, with only `Suit` equality decided. -/
theorem corridor_clean_or_dirty (γ : List Move) (c d : Card) :
    CorridorClean γ c d ∨ (∃ e : Card, Move.tabToFound e ∈ γ ∧ e.suit ≠ d.suit) ∨
      (∃ (e : Card) (b : Base), Move.foundToTab e b ∈ γ ∧ e.suit ≠ c.suit) := by
  induction γ with
  | nil => exact Or.inl ⟨fun e he => absurd he (by simp), fun e b he => absurd he (by simp)⟩
  | cons z zs ih =>
      rcases ih with hcl | ⟨e, he, hse⟩ | ⟨e, b, he, hse⟩
      · cases z with
        | tabToFound e =>
            by_cases hsd : e.suit = d.suit
            · exact Or.inl (corridorClean_cons hcl
                (fun e' h => by cases h; exact hsd) (fun e' b' h => by cases h))
            · exact Or.inr (Or.inl ⟨e, by simp, hsd⟩)
        | foundToTab e b =>
            by_cases hsc : e.suit = c.suit
            · exact Or.inl (corridorClean_cons hcl
                (fun e' h => by cases h) (fun e' b' h => by cases h; exact hsc))
            · exact Or.inr (Or.inr ⟨e, b, by simp, hsc⟩)
        | draw =>
            exact Or.inl (corridorClean_cons hcl
              (fun e' h => by cases h) (fun e' b' h => by cases h))
        | tabToTab e b =>
            exact Or.inl (corridorClean_cons hcl
              (fun e' h => by cases h) (fun e' b' h => by cases h))
        | wasteToFound e =>
            exact Or.inl (corridorClean_cons hcl
              (fun e' h => by cases h) (fun e' b' h => by cases h))
        | wasteToTab e b =>
            exact Or.inl (corridorClean_cons hcl
              (fun e' h => by cases h) (fun e' b' h => by cases h))
      · exact Or.inr (Or.inl ⟨e, List.mem_cons_of_mem z he, hse⟩)
      · exact Or.inr (Or.inr ⟨e, b, List.mem_cons_of_mem z he, hse⟩)

/-- **THE CORRIDOR NORMAL FORM.**  If a play carries *any* cross-suit
raise-before-pull pair, it carries one whose corridor is clean: choose a pair of
minimal corridor length; a dirty letter inside the corridor would supply a
strictly shorter cross-suit pair.

This is the reduction that makes the residual *strictly weaker* than the theorem:
the theorem only has to be proved at the corridor shape. -/
theorem clean_of_cross {ρ : List Move} (h : CrossCorridor ρ) : CleanCrossCorridor ρ := by
  obtain ⟨pre₀, γ₀, tail₀, c₀, d₀, b₀, heq₀, hne₀⟩ := h
  have aux : ∀ (n : Nat) (pre : List Move) (γ : List Move) (c d : Card) (b : Base)
      (tail : List Move), γ.length = n → c.suit ≠ d.suit →
      CleanCrossCorridor (pre ++ Move.tabToFound c :: γ ++ Move.foundToTab d b :: tail) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro pre γ c d b tail hlen hne
      rcases corridor_clean_or_dirty γ c d with hclean | ⟨e, hmem, hne'⟩ | ⟨e, b', hmem, hne'⟩
      · exact ⟨pre, γ, tail, c, d, b, rfl, hne, hclean⟩
      · -- a raise off the pull's suit: move the pair's left end right
        obtain ⟨γ1, γ2, hγ⟩ := exists_split_of_mem hmem
        have hlen2 : γ2.length < n := by
          rw [hγ] at hlen
          simp only [List.length_append, List.length_cons] at hlen
          omega
        have hres := ih γ2.length hlen2 (pre ++ Move.tabToFound c :: γ1) γ2 e d b tail
          rfl hne'
        rw [hγ]
        simpa only [List.append_assoc, List.cons_append] using hres
      · -- a pull off the raise's suit: move the pair's right pull left
        obtain ⟨γ1, γ2, hγ⟩ := exists_split_of_mem hmem
        have hlen1 : γ1.length < n := by
          rw [hγ] at hlen
          simp only [List.length_append, List.length_cons] at hlen
          omega
        have hres := ih γ1.length hlen1 pre γ1 c e b'
          (γ2 ++ Move.foundToTab d b :: tail) rfl (fun hce => hne' hce.symm)
        rw [hγ]
        simpa only [List.append_assoc, List.cons_append] using hres
  rw [heq₀]
  exact aux γ₀.length pre₀ γ₀ c₀ d₀ b₀ tail₀ rfl hne₀

/-!
### §2.4 The corridor lock: a corridor that pulls at all pulls the raised card
-/

/-- **THE CORRIDOR'S FIRST PULL IS THE RAISED CARD.**  In a clean corridor, a
pull preceded by a pull-free stretch must pull `c` itself: the raised suit is
locked (§1.3). -/
theorem corridor_first_pull_eq {u v : State} {pre γ1 γ2 tail : List Move}
    {c e d : Card} {b b' : Base}
    (hplay : ShufflePlayW u
      (pre ++ Move.tabToFound c ::
        (γ1 ++ Move.foundToTab e b' :: γ2) ++ Move.foundToTab d b :: tail) v)
    (hclean : CorridorClean (γ1 ++ Move.foundToTab e b' :: γ2) c d)
    (hne : c.suit ≠ d.suit) (hnopull : PullFree γ1) : e = c := by
  have he : e.suit = c.suit := hclean.2 e b' (by simp)
  have hplay' : ShufflePlayW u
      (pre ++ Move.tabToFound c :: γ1 ++ Move.foundToTab e b' ::
        (γ2 ++ Move.foundToTab d b :: tail)) v := by
    simpa only [List.append_assoc, List.cons_append] using hplay
  refine lock_pull_eq_raised hplay' ?_ he
  intro m hm
  cases m with
  | draw => exact trivial
  | tabToTab x bb => exact trivial
  | wasteToFound x => exact trivial
  | wasteToTab x bb => exact trivial
  | tabToFound x =>
      have hx : x.suit = d.suit := hclean.1 x (List.mem_append_left _ hm)
      show x.suit ≠ c.suit
      rw [hx]
      exact fun hc => hne hc.symm
  | foundToTab x bb => exact absurd hm (hnopull x bb)

/-- **EVERY LIST EITHER PULLS BEHIND A PULL-FREE PREFIX, OR PULLS NOTHING.**
Constructive dichotomy (recursion on the list). -/
theorem pull_split_or_free : ∀ γ : List Move,
    (∃ (γ1 γ2 : List Move) (e : Card) (b : Base),
      γ = γ1 ++ Move.foundToTab e b :: γ2 ∧ PullFree γ1) ∨ PullFree γ
  | [] => Or.inr (fun e b h => absurd h (by simp))
  | Move.foundToTab e b :: zs =>
      Or.inl ⟨[], zs, e, b, rfl, fun x bb hx => absurd hx (by simp)⟩
  | Move.tabToFound x :: zs =>
      (pull_split_or_free zs).elim
        (fun ⟨γ1, γ2, e, b, hγ, hpf⟩ =>
          Or.inl ⟨Move.tabToFound x :: γ1, γ2, e, b, by rw [hγ]; rfl,
            fun y bb hy => by
              rcases List.mem_cons.mp hy with h | h
              · cases h
              · exact hpf y bb h⟩)
        (fun hpf => Or.inr (fun y bb hy => by
          rcases List.mem_cons.mp hy with h | h
          · cases h
          · exact hpf y bb h))
  | Move.draw :: zs =>
      (pull_split_or_free zs).elim
        (fun ⟨γ1, γ2, e, b, hγ, hpf⟩ =>
          Or.inl ⟨Move.draw :: γ1, γ2, e, b, by rw [hγ]; rfl,
            fun y bb hy => by
              rcases List.mem_cons.mp hy with h | h
              · cases h
              · exact hpf y bb h⟩)
        (fun hpf => Or.inr (fun y bb hy => by
          rcases List.mem_cons.mp hy with h | h
          · cases h
          · exact hpf y bb h))
  | Move.wasteToFound x :: zs =>
      (pull_split_or_free zs).elim
        (fun ⟨γ1, γ2, e, b, hγ, hpf⟩ =>
          Or.inl ⟨Move.wasteToFound x :: γ1, γ2, e, b, by rw [hγ]; rfl,
            fun y bb hy => by
              rcases List.mem_cons.mp hy with h | h
              · cases h
              · exact hpf y bb h⟩)
        (fun hpf => Or.inr (fun y bb hy => by
          rcases List.mem_cons.mp hy with h | h
          · cases h
          · exact hpf y bb h))
  | Move.wasteToTab x bb :: zs =>
      (pull_split_or_free zs).elim
        (fun ⟨γ1, γ2, e, b, hγ, hpf⟩ =>
          Or.inl ⟨Move.wasteToTab x bb :: γ1, γ2, e, b, by rw [hγ]; rfl,
            fun y bb' hy => by
              rcases List.mem_cons.mp hy with h | h
              · cases h
              · exact hpf y bb' h⟩)
        (fun hpf => Or.inr (fun y bb' hy => by
          rcases List.mem_cons.mp hy with h | h
          · cases h
          · exact hpf y bb' h))
  | Move.tabToTab x bb :: zs =>
      (pull_split_or_free zs).elim
        (fun ⟨γ1, γ2, e, b, hγ, hpf⟩ =>
          Or.inl ⟨Move.tabToTab x bb :: γ1, γ2, e, b, by rw [hγ]; rfl,
            fun y bb' hy => by
              rcases List.mem_cons.mp hy with h | h
              · cases h
              · exact hpf y bb' h⟩)
        (fun hpf => Or.inr (fun y bb' hy => by
          rcases List.mem_cons.mp hy with h | h
          · cases h
          · exact hpf y bb' h))

/-- **THE CORRIDOR LOCK, UNCONDITIONAL FORM.**  If a clean cross-suit corridor
contains any pull, then it contains the same-card continuation
`raise c ; (pull-free) ; pull c` — the pull is of the raised card itself. -/
theorem corridor_pull_is_c {u v : State} {pre γ tail : List Move} {c d : Card} {b : Base}
    (hplay : ShufflePlayW u (pre ++ Move.tabToFound c :: γ ++ Move.foundToTab d b :: tail) v)
    (hclean : CorridorClean γ c d) (hne : c.suit ≠ d.suit)
    (hpull : ∃ (e : Card) (b' : Base), Move.foundToTab e b' ∈ γ) :
    ∃ (γ1 γ2 : List Move) (b' : Base),
      γ = γ1 ++ Move.foundToTab c b' :: γ2 ∧ PullFree γ1 := by
  rcases pull_split_or_free γ with ⟨γ1, γ2, e, b', hγ, hpf⟩ | hpf
  · have hc : e = c := by
      have hplay' : ShufflePlayW u
          (pre ++ Move.tabToFound c :: (γ1 ++ Move.foundToTab e b' :: γ2) ++
            Move.foundToTab d b :: tail) v := by
        rw [← hγ]; exact hplay
      exact corridor_first_pull_eq hplay' (by rw [← hγ]; exact hclean) hne hpf
    subst e
    exact ⟨γ1, γ2, b', hγ, hpf⟩
  · obtain ⟨e, b', hm⟩ := hpull
    exact absurd hm (hpf e b')

/-!
## §3. The named residual, and the reduction
-/

/-- **REFUTED — KERNEL-CERTIFIED; DO NOT CITE AS A RESIDUAL.**  A minimal
witness play between `SSaturated` `WF` endpoints never carries a raise of `c`,
a corridor clean at `(c, d)`, and then a pull of `d` - for two different suits.
`Cert.not_crossSuitCorridorResidual` (`Archive/Cert/ForkCertMain.lean`) proves this is
FALSE, with a 17-letter shortest play whose clean corridor is
`raise QD ; raise KS ; slide KH→empty ; pull KS (inl 5)`. -/
def CrossSuitCorridorResidual : Prop :=
  ∀ (u v : State) (ρ pre γ tail : List Move) (c d : Card) (b : Base),
    u.WF → SSaturated u → SSaturated v → ShufflePlayW u ρ v →
    (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) →
    ρ = pre ++ Move.tabToFound c :: γ ++ Move.foundToTab d b :: tail →
    c.suit ≠ d.suit → CorridorClean γ c d → False

/-- **NO CROSS-SUIT PAIR AT THE CORRIDOR SHAPE.**  §2 gives a clean corridor from
any cross-suit pair, and the residual closes it. -/
theorem no_crossCorridor_of_residual (hres : CrossSuitCorridorResidual)
    {u v : State} {ρ : List Move}
    (huwf : u.WF) (hu : SSaturated u) (hv : SSaturated v)
    (hplay : ShufflePlayW u ρ v)
    (hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) :
    ¬ CrossCorridor ρ := by
  intro h
  obtain ⟨pre, γ, tail, c, d, b, heq, hne, hclean⟩ := clean_of_cross h
  exact hres u v ρ pre γ tail c d b huwf hu hv hplay hmin heq hne hclean

/-! ### §3.2 From index pairs to the corridor shape -/

/-- Membership at an index splits the list, with the prefix length pinned. -/
theorem exists_split_of_get? {l : List Move} {k : Nat} {m : Move}
    (h : l[k]? = some m) :
    ∃ a b : List Move, l = a ++ m :: b ∧ a.length = k := by
  induction k generalizing l with
  | zero =>
      cases l with
      | nil => simp at h
      | cons z zs =>
          rw [List.getElem?_cons_zero] at h
          have hz : z = m := Option.some.inj h
          exact ⟨[], zs, by simp [hz], by simp⟩
  | succ k ih =>
      cases l with
      | nil => simp at h
      | cons z zs =>
          simp only [List.getElem?_cons_succ, Nat.succ_eq_add_one] at h
          obtain ⟨a, b, hzs, hlen⟩ := ih h
          exact ⟨z :: a, b, by rw [hzs, List.cons_append], by simp [hlen]⟩

/-- **TWO INDEX HITS SPLIT THE PLAY AROUND THEM.**  `i < j` with `ρ[i]? = x` and
`ρ[j]? = y` gives `ρ = pre ++ x :: γ ++ y :: tail`. -/
theorem exists_double_split {ρ : List Move} {i j : Nat} {x y : Move}
    (hij : i < j) (hi : ρ[i]? = some x) (hj : ρ[j]? = some y) :
    ∃ pre γ tail, ρ = pre ++ x :: γ ++ y :: tail := by
  induction i generalizing ρ j with
  | zero =>
      obtain ⟨a, b, hρ, hlen⟩ := exists_split_of_get? hi
      cases a with
      | cons a1 as => simp at hlen
      | nil =>
          have hρ' : ρ = x :: b := by rw [hρ]; rfl
          have hjeq : j = (j - 1) + 1 := by omega
          have hjb : b[j - 1]? = some y := by
            have hh := hj
            rw [hρ', hjeq, List.getElem?_cons_succ] at hh
            exact hh
          obtain ⟨γ, tail, hb, -⟩ := exists_split_of_get? hjb
          exact ⟨[], γ, tail, by rw [hρ', hb]; simp⟩
  | succ i ih =>
      cases ρ with
      | nil => simp at hi
      | cons z zs =>
          have hi' : zs[i]? = some x := by
            have hh := hi
            simp only [List.getElem?_cons_succ, Nat.succ_eq_add_one] at hh
            exact hh
          have hj' : zs[j - 1]? = some y := by
            have hh := hj
            rw [show j = (j - 1) + 1 by omega, List.getElem?_cons_succ] at hh
            exact hh
          obtain ⟨pre, γ, tail, hzs⟩ := ih (j := j - 1) (by omega) hi' hj'
          exact ⟨z :: pre, γ, tail, by rw [hzs]; simp⟩

/-- **CROSS-SUIT VACUITY, FROM THE RESIDUAL.**  The target statement, in the
index form (`ρ[i]?`/`ρ[j]?` — the option-safe reading of `ρ[i]`; the `getElem`
form follows from `List.getElem?_eq_getElem`). -/
theorem crossSuitVacuity_of_residual (hres : CrossSuitCorridorResidual)
    {u v : State} (huwf : u.WF) (hu : SSaturated u) (hv : SSaturated v)
    {ρ : List Move} (hplay : ShufflePlayW u ρ v)
    (hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length)
    {i j : Nat} {c d : Card} {b : Base} (hij : i < j)
    (hi : ρ[i]? = some (Move.tabToFound c))
    (hj : ρ[j]? = some (Move.foundToTab d b)) (hsu : c.suit ≠ d.suit) : False := by
  obtain ⟨pre, γ, tail, heq⟩ := exists_double_split hij hi hj
  exact no_crossCorridor_of_residual hres huwf hu hv hplay hmin
    ⟨pre, γ, tail, c, d, b, heq, hsu⟩

/-!
## §4. The sharpened split: same-card interior + the pull-free corridor
-/

/-- **WITHDRAWN — FALSE.**  A same-card relocation with an arbitrary interior
does NOT shorten: the unit-shortest equal-rung witness contains
`raise 5C ; slide 5S ; pull 5C` with a free interior (`EqualRung.play`,
`EqualRung.witnessMinimality`; checked letter-by-letter in
`Temp/Pure_Report.md`).  This is `MtnPr.SameCardRelocation` with the
read-safety and seat-inertness side conditions dropped — and both that un-gated
form and this free form are false.  Consequently `pureResidual_of_sameCard` /
`crossSuitVacuity_of_split` are vacuous; use the same-card-free split
`CrossSuit.FreeCorridorResidual + CrossSuit.InnerRaiseResidual`
(`Orig2/ForkCrossSuitPure.lean`) instead. -/
def SameCardFreeInteriorShortens : Prop :=
  ∀ (u v : State) (ρ pre γ post : List Move) (c : Card) (b : Base),
    u.WF → ShufflePlayW u ρ v →
    ρ = pre ++ Move.tabToFound c :: γ ++ Move.foundToTab c b :: post →
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length

/-- **THE PULL-FREE CORRIDOR RESIDUAL.**  §3's residual restricted to corridors
that pull nothing: the only genuinely cross-suit configuration left. -/
def CrossSuitPureCorridorResidual : Prop :=
  ∀ (u v : State) (ρ pre γ tail : List Move) (c d : Card) (b : Base),
    u.WF → SSaturated u → SSaturated v → ShufflePlayW u ρ v →
    (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) →
    ρ = pre ++ Move.tabToFound c :: γ ++ Move.foundToTab d b :: tail →
    c.suit ≠ d.suit → CorridorClean γ c d → PullFree γ → False

/-- **THE SHARPENED REDUCTION.**  `SameCardFreeInteriorShortens` kills every
corridor that pulls — its first pull is the raised card (§2.4), so the play
shortens against minimality — leaving only the pull-free corridor. -/
theorem pureResidual_of_sameCard (hpur : CrossSuitPureCorridorResidual)
    (hsc : SameCardFreeInteriorShortens) : CrossSuitCorridorResidual := by
  intro u v ρ pre γ tail c d b huwf hu hv hplay hmin heq hne hclean
  rcases pull_split_or_free γ with ⟨γ1, γ2, e, b', hγ, hpf⟩ | hpf
  · -- the corridor pulls: its first pull is `c`
    have he : e = c := by
      have hplay' : ShufflePlayW u
          (pre ++ Move.tabToFound c :: (γ1 ++ Move.foundToTab e b' :: γ2) ++
            Move.foundToTab d b :: tail) v := by
        rw [← hγ, ← heq]
        exact hplay
      exact corridor_first_pull_eq hplay' (by rw [← hγ]; exact hclean) hne hpf
    subst e
    have heq' : ρ = pre ++ Move.tabToFound c :: γ1 ++ Move.foundToTab c b' ::
        (γ2 ++ Move.foundToTab d b :: tail) := by
      rw [heq, hγ]
      simp only [List.append_assoc, List.cons_append]
    obtain ⟨ρ', hρ', hlen'⟩ :=
      hsc u v ρ pre γ1 (γ2 ++ Move.foundToTab d b :: tail) c b' huwf hplay heq'
    exact absurd hlen' (Nat.not_lt.mpr (hmin ρ' hρ'))
  · exact hpur u v ρ pre γ tail c d b huwf hu hv hplay hmin heq hne hclean hpf

/-!
## §5. The target shape, named
-/

/-- **CROSS-SUIT VACUITY** - the brief's target, from the named corridor
residual.  **REFUTED — KERNEL-CERTIFIED** (`Cert.not_crossSuitVacuityTarget`,
`Archive/Cert/ForkCertMain.lean`): the counterexample play has `inv = 8`, so the
target proposition is false. -/
theorem crossSuitVacuity (hres : CrossSuitCorridorResidual)
    {u v : State} (huwf : u.WF) (hu : SSaturated u) (hv : SSaturated v)
    {ρ : List Move} (hplay : ShufflePlayW u ρ v)
    (hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length)
    {i j : Nat} {c d : Card} {b : Base} (hij : i < j)
    (hi : ρ[i]? = some (Move.tabToFound c))
    (hj : ρ[j]? = some (Move.foundToTab d b)) (hsu : c.suit ≠ d.suit) : False :=
  crossSuitVacuity_of_residual hres huwf hu hv hplay hmin hij hi hj hsu

/-- **CROSS-SUIT VACUITY, FROM THE SHARPENED PAIR.**  Same conclusion from the
same-card interior residual plus the pull-free corridor residual (§4). -/
theorem crossSuitVacuity_of_split (hpur : CrossSuitPureCorridorResidual)
    (hsc : SameCardFreeInteriorShortens)
    {u v : State} (huwf : u.WF) (hu : SSaturated u) (hv : SSaturated v)
    {ρ : List Move} (hplay : ShufflePlayW u ρ v)
    (hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length)
    {i j : Nat} {c d : Card} {b : Base} (hij : i < j)
    (hi : ρ[i]? = some (Move.tabToFound c))
    (hj : ρ[j]? = some (Move.foundToTab d b)) (hsu : c.suit ≠ d.suit) : False :=
  crossSuitVacuity_of_residual (pureResidual_of_sameCard hpur hsc)
    huwf hu hv hplay hmin hij hi hj hsu

/-- **NO CROSS-SUIT PAIR ANYWHERE.**  The whole-play form of the target: a
minimal witness play between `SSaturated` endpoints carries no cross-suit
raise-before-pull pair at all (any index, any split). -/
theorem noCrossCorridor (hres : CrossSuitCorridorResidual)
    {u v : State} (huwf : u.WF) (hu : SSaturated u) (hv : SSaturated v)
    {ρ : List Move} (hplay : ShufflePlayW u ρ v)
    (hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) :
    ¬ CrossCorridor ρ :=
  no_crossCorridor_of_residual hres huwf hu hv hplay hmin

end CrossSuit

/-! ## §6. Axiom battery -/

#print axioms CrossSuit.found_tabToTab_eq
#print axioms CrossSuit.found_foundToTab_ne
#print axioms CrossSuit.found_step_of_avoids
#print axioms CrossSuit.found_eq_of_avoids
#print axioms CrossSuit.foundTop_eq_of_avoids
#print axioms CrossSuit.first_suit_pull_card
#print axioms CrossSuit.lock_pull_eq_raised
#print axioms CrossSuit.rung_eq_add_raises_of_no_pull
#print axioms CrossSuit.rung_ge_of_no_pull
#print axioms CrossSuit.rung_strict_of_raise_of_no_pull
#print axioms CrossSuit.exists_split_of_mem
#print axioms CrossSuit.corridorClean_cons
#print axioms CrossSuit.corridor_clean_or_dirty
#print axioms CrossSuit.clean_of_cross
#print axioms CrossSuit.corridor_first_pull_eq
#print axioms CrossSuit.pull_split_or_free
#print axioms CrossSuit.corridor_pull_is_c
#print axioms CrossSuit.no_crossCorridor_of_residual
#print axioms CrossSuit.exists_split_of_get?
#print axioms CrossSuit.exists_double_split
#print axioms CrossSuit.crossSuitVacuity_of_residual
#print axioms CrossSuit.pureResidual_of_sameCard
#print axioms CrossSuit.crossSuitVacuity
#print axioms CrossSuit.crossSuitVacuity_of_split
#print axioms CrossSuit.noCrossCorridor

#check @CrossSuit.CrossSuitCorridorResidual
#check @CrossSuit.CrossSuitPureCorridorResidual
#check @CrossSuit.SameCardFreeInteriorShortens
#check @CrossSuit.CrossCorridor

