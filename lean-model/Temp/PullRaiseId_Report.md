# Temp/PullRaiseId — report

File: `Temp/PullRaiseId.lean`
Build: `cd B:\code\lonelybot\lean-model; lake env lean Temp/PullRaiseId.lean` → exit code **0**.

Import surface: `Orig2.Substrate.Classification` (which brings `Vocab`/`Kit`/`Integrity`).
No `Orig2/` or existing `Temp/*.lean` file was touched. Prerequisite oleans
(`Orig2/Substrate/{Vocab,Kit,Integrity,Classification}.olean`, `Temp/SatDiffer_config.olean`)
were already present and fresh; the new file does not import `Temp.SatDiffer_config`.

## 1. Exact statements proved

```lean
theorem pull_raise_id {s u s' : State} {c : Card} {b : Base}
    (hwf : s.WF)
    (hpull : State.step s (Move.foundToTab c b) = some u)
    (hcan : CanRaise u c)
    (hraise : State.step u (Move.tabToFound c) = some s') :
    s' = s

theorem pull_raise_id_rung {s u s' : State} {c : Card} {b : Base}
    (hwf : s.WF)
    (hpull : State.step s (Move.foundToTab c b) = some u)
    (hcan : CanRaise u c)
    (hraise : State.step u (Move.tabToFound c) = some s') :
    ∀ σ, rungAt s' σ = rungAt s σ

theorem pull_raise_id_components {s u s' : State} {c : Card} {b : Base}
    (hwf : s.WF)
    (hpull : State.step s (Move.foundToTab c b) = some u)
    (hcan : CanRaise u c)
    (hraise : State.step u (Move.tabToFound c) = some s') :
    s'.found = s.found ∧ s'.piles = s.piles ∧ s'.stock = s.stock ∧
      s'.waste = s.waste ∧ s'.drawStep = s.drawStep

theorem not_canRaise_after_pull_short {s u : State} {c : Card} {b : Base}
    (hpull : State.step s (Move.foundToTab c b) = some u)
    (h : ¬ CanRaise u c) :
    rungAt u c.suit = rungAt s c.suit - 1
```

The first three use the promoted round trip
`step_tabToFound_of_foundToTab : st.WF → step st (foundToTab c b) = some s₁ →
step s₁ (tabToFound c) = some st` (`Orig2/Substrate/Classification.lean:1011`),
read at `s₁ = u`; the raise equation `hraise` then forces `s' = s` by
`Option.some.inj`. `not_canRaise_after_pull_short` is proved directly from
`step_foundToTab_inv` and `lastOf_chop`, and is **unconditional** (the
hypothesis `h` is not used).

## 2. Axiom lines

```
'pull_raise_id' depends on axioms: [propext, Quot.sound]
'pull_raise_id_rung' depends on axioms: [propext, Quot.sound]
'pull_raise_id_components' depends on axioms: [propext, Quot.sound]
'not_canRaise_after_pull_short' depends on axioms: [propext, Quot.sound]
```

No `sorry`, no `Classical`, no `noncomputable`.

## 3. The `WF` premise is necessary (the literal statement is false)

The task statement omits `s.WF`. Without it the theorem is **false**: `State.step`
does not know card conservation, so two piles may carry the same card `c` on
top. `foundToTab` then writes `c` at the landing pile, but the raise's
`pileOfTop c` search (`firstWhere` over `Anchor.all`, first hit wins) may locate
the *other*, earlier copy; the raise then removes `c` from a pile the pull never
touched.

Concrete counterexample (all hypotheses of the literal statement hold, verified
by evaluation of `State.step`; `c = 2S`, `b = inr 3H`, `w = 2H`):

```lean
c  = ⟨.spade, .two⟩      -- rank index 1, so nextUp holds at the landing
w  = ⟨.heart, .two⟩
z  = ⟨.heart, .three⟩
s.found .spade = [AS, 2S]
s.piles .p0    = ⟨[], [2H, 2S]⟩     -- duplicate copy of c on top
s.piles .p1    = ⟨[], [3H]⟩
other piles empty

-- pull foundToTab 2S (inr 3H)
u.found .spade = [AS]
u.piles .p0    = ⟨[], [2H, 2S]⟩     -- untouched
u.piles .p1    = ⟨[], [3H, 2S]⟩     -- the pull's landing
u.nextUp 2S    = true
u.pileOfTop 2S = some .p0           -- the earlier duplicate copy
chop (u.piles .p0).faceUp = [2H] ≠ []   -- so CanRaise u 2S holds

-- raise tabToFound 2S removes the top 2S from p0
s'.found .spade = [AS, 2S]
s'.piles .p0    = ⟨[], [2H]⟩
s'.piles .p1    = ⟨[], [3H, 2S]⟩
```

`s' ≠ s` (`s.piles .p0` still had `[2H, 2S]`), while `hpull`, `hcan` and
`hraise` all hold. The `#eval` transcript used for this check was left out of
the final card (it would require `Repr Card`, so it printed `(Suit × Rank)`).
At `WF` states the conservation clause `∀ c, st.cardCount c = 1` rules out the
duplicate top and the proof goes through. So the correct side condition for the
main proof is `s.WF`; `hcan` alone is *not* enough.

Note: under `s.WF`, `hcan` is actually automatic at the pull's landing
(`SatDifferConfig.canRaise_after_pull`), and the stronger core statement is just
`step_tabToFound_of_foundToTab`. The `hcan` argument is retained in the
statements above so the signature matches the requested consumer shape.

## 4. Does the `chop = []` branch of `CanRaise` behave?

Yes, both branches restore, and the empty-chop branch need not be excluded:

* **Empty-chop branch** (`chop faceUp = [] ∧ hidden = [] ∧ c.rank = king`).
  At the pull's landing this is exactly the empty-seat pull `b = inl a`:
  `u.piles a = ⟨[], [c]⟩` (so `chop [c] = []`, `hidden = []`), and
  `canPlace c (inl a)` supplies `c.rank = king`. The raise's pile update is
  `Pile.afterRunRemoved ⟨[], [c]⟩ (chop [c]) = Pile.revealTop ⟨[], []⟩ = ⟨[], []⟩`,
  which is precisely the original empty pile. The foundation write
  `chop (found) ++ [c]` also cancels by `lastOf_chop`. So this branch restores
  the state exactly — no exclusion is needed.
* **Non-empty-chop branch.** For a card landing on a pile (`b = inr z`, landing
  anchor `k = pileOfTop z`), the target pile already has `z` face up, so after
  `putCard` its `faceUp` is `p.faceUp ++ [c]` with `p.faceUp ≠ []`; hence
  `chop (p.faceUp ++ [c]) = p.faceUp ≠ []` (left disjunct of `CanRaise`). The
  round trip is `putCard_inr_roundtrip`, i.e. `afterRunRemoved {p with faceUp :=
  p.faceUp ++ [c]} p.faceUp = p`.

Thus `CanRaise`'s disjunction covers exactly the two pull landings, and in both
the local pile update is the identity after the raise.

## 5. Totality under `hcan`

At `WF` states the cancellation is total under `hcan` — indeed `hcan` is
redundant there, because `canRaise_after_pull` derives it from the pull, and
`s' = s` holds exactly; without `WF`, `hcan` does not make the cancellation
total (the counterexample above satisfies `hcan` and still has `s' ≠ s`), so
`WF` — not `hcan` — is the real side condition.

## 6. Suggested main-proof consumption

```lean
have hid := pull_raise_id hwf hpull hcan hraise        -- s' = s
have hrung := pull_raise_id_rung hwf hpull hcan hraise -- ∀ σ, rungAt s' σ = rungAt s σ
have hcomp := pull_raise_id_components hwf hpull hcan hraise
```

If the main proof only needs the rung/field agreement, `pull_raise_id_components`
avoids rewriting the whole state.
