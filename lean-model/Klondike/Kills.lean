import Klondike.Theorems

/-!
# The closure-goal kills (the K-rules — the engine's `goal_dead`)

Cheap necessary conditions for an accommodation goal to open *anywhere*
in the reversible closure (the engine's macro-game BFS — see the
`ClosureCtx` doc in `src/macro_game.rs`, whose K1/K2/K4/K5/K6 rules the
search applies before walking).  A killed goal provably has no BFS
answer, so skipping it is pure search cost; the rules are stated here
as *closure invariants* over `safeAccommodates` (Theorems.lean).

Everything rides on one keystone, `vis_of_safeAccommodates`: shuffles
never deal, never reveal, and never stack a locked card, so a card
visible in the closure was root-visible or worried back from the root
foundation.  K4 (first-layer kings) and K5 (the saturated-board gate)
are not yet statable — the model has no first-layer predicate and no
path state; see FARM.md's wave-12 notes.

Status 2026-10-05 (the K1 farm session): the keystone, the frontier
witness spec, and the K1 climb kill are PROVEN (sorry-free; no WF
hypothesis anywhere, as the wave-12 plan hoped).  The K2 row keeps its
`sorry` and plan below.

Refute-first gate for the sorried rows: the Rust differential probe
(`macro_direct_matches_oracle` — a wrong kill counts as a missing
outcome) is the falsification instrument; there is no Lean-side
executable closure walk, do **not** hand-probe these with `#eval`.
-/

/-! ## The list kit — `find?` first-hit semantics over `Rank.all`

Core's `find?_eq_some_iff_append` names a found element together with
its no-earlier-hit prefix; the prefix law below is the one bespoke
separation step (core's `find?_append`/`or_eq_some_iff` do the rest),
and `Rank.all`'s toIdx-enumeration splits at any rank as a 13-way
`decide`.  These feed only `State.frontier_spec`. -/

/-- The `find?` prefix law: if the first hit of `p` in `A ++ b :: B`
is `b` itself and `b` is not in `A`, then nothing in `A` satisfies
`p`. -/
theorem find?_prefix_false {α : Type} (p : α → Bool) (A : List α) (b : α)
    (B : List α) (h : (A ++ b :: B).find? p = some b) (hb : b ∉ A) :
    ∀ x ∈ A, p x = false := by
  rw [List.find?_append] at h
  cases hA : A.find? p with
  | some z =>
      rw [hA] at h
      rw [Option.some_or, Option.some.injEq] at h
      subst h
      obtain ⟨-, as₂, bs₂, hs, -⟩ := List.find?_eq_some_iff_append.mp hA
      rw [hs] at hb
      exact absurd (by
        show z ∈ as₂ ++ z :: bs₂
        exact List.mem_append.mpr (Or.inr List.mem_cons_self)) hb
  | none =>
      rw [hA, Option.none_or] at h
      intro x hx
      have hnx := (List.find?_eq_none.mp hA) x hx
      cases hpx : p x with
      | false => rfl
      | true => exact absurd hpx hnx

/-- The rank enumeration splits at any rank into its toIdx-below
prefix and its toIdx-above suffix, with the rank in between (a
13-element closed identity per case). -/
theorem Rank.all_split_filter (b : Rank) :
    Rank.all = (Rank.all.filter fun r => decide (r.toIdx < b.toIdx))
      ++ b :: (Rank.all.filter fun r => decide (b.toIdx < r.toIdx)) := by
  cases b <;> decide

/-! ## The keystone — the closure's visibility bound -/

/-- `pileStack`'s one-step visibility law: the detach removes exactly
the stacked card from the image — what is still visible was visible. -/
theorem vis_of_pileStack {st st₁ : State} {x : Card}
    (hm : st.apply (Move.pileStack x) = some st₁) {c : Card}
    (hc : st₁.isVis c = true) : c ≠ x ∧ st.isVis c = true := by
  obtain ⟨-, bx, hbx, -, rfl⟩ := apply_pileStack_iff.mp hm
  have htb : st.board.topOf bx = some x := (Board.bottomOf_eq st.board x bx).mp hbx
  have hne : c ≠ x := by
    intro hcx; subst hcx
    have hx : (st.board.detach bx).bottomOf c = none :=
      Board.bottomOf_detach_self htb
    have hc' : (((st.board.detach bx).bottomOf c).isSome) = true := hc
    rw [hx] at hc'
    exact absurd hc' (by simp)
  refine ⟨hne, ?_⟩
  have hb := bottomOf_detach_ne htb hne
  show ((st.board.bottomOf c).isSome) = true
  have hc' : (((st.board.detach bx).bottomOf c).isSome) = true := hc
  rw [hb] at hc'
  exact hc'

/-- `stackPile`'s one-step visibility law: the attach adds exactly the
worry-back card; anything else visible was visible, and the worry-back
card itself is root-foundation (the un-stack guard puts it strictly
below the root height). -/
theorem vis_of_stackPile {st st₁ : State} {x : Card} {b : Base}
    (hm : st.apply (Move.stackPile x b) = some st₁) {c : Card}
    (hc : st₁.isVis c = true) :
    c ≠ x ∧ st.isVis c = true ∨ c.rank.toIdx < st.heights c.suit := by
  obtain ⟨hg, -, bd, hatt, rfl⟩ := apply_stackPile_iff.mp hm
  cases hcx : decide (c = x) with
  | true =>
      have hcxeq : c = x := of_decide_eq_true hcx
      subst hcxeq
      exact Or.inr (by omega)
  | false =>
      have hcxne : ¬(c = x) := by
        intro hcon
        rw [hcon] at hcx
        exact absurd hcx (by simp)
      have hbb := (lockedness_stackPile hm hcxne).2
      have hb : bd.bottomOf c = st.board.bottomOf c := hbb
      have hvis : st.isVis c = true := by
        have hc' : (((bd).bottomOf c).isSome) = true := hc
        show ((st.board.bottomOf c).isSome) = true
        rw [← hb]
        exact hc'
      exact Or.inl ⟨hcxne, hvis⟩

/-- The play induction behind the keystone: along an accommodation
play, every endpoint-visible and every endpoint-foundation card was
root-visible or root-foundation.  The two conjuncts are carried
together — one step's visibility claim consumes the successor state's
foundation-side shadow — and the play start is generalized, so the
induction composes the one-step transports through every intermediate
state. -/
theorem vis_shadow_play : ∀ (ι : State) (ms : List Move) (ρ : State),
    ι.run ms = some ρ → (∀ m ∈ ms, m.isAccommodation = true) →
    ((∀ c : Card, ρ.isVis c = true →
        ι.isVis c = true ∨ c.rank.toIdx < ι.heights c.suit) ∧
    (∀ c : Card, c.rank.toIdx < ρ.heights c.suit →
        ι.isVis c = true ∨ c.rank.toIdx < ι.heights c.suit)) := by
  intro ι ms
  induction ms generalizing ι with
  | nil =>
      intro ρ hrun _
      have hρ : ι = ρ := Option.some.inj hrun
      subst hρ
      exact ⟨fun _ h => Or.inl h, fun _ h => Or.inr h⟩
  | cons m rest ih =>
      intro ρ hrun hall
      have hacc := hall m (List.mem_cons_self)
      simp only [State.run] at hrun
      cases hap : ι.apply m with
      | none =>
          rw [hap] at hrun
          exact absurd hrun (by simp)
      | some σ =>
          rw [hap] at hrun
          have hrun' : σ.run rest = some ρ := hrun
          cases m with
          | pileStack x =>
              obtain ⟨htop, bx, hbx, hrk, hσlit⟩ := apply_pileStack_iff.mp hap
              have stepVis : ∀ c, σ.isVis c = true →
                  ι.isVis c = true ∨ c.rank.toIdx < ι.heights c.suit :=
                fun c hc => Or.inl (vis_of_pileStack hap hc).2
              have stepSh : ∀ c, c.rank.toIdx < σ.heights c.suit →
                  ι.isVis c = true ∨ c.rank.toIdx < ι.heights c.suit := by
                intro c hc
                cases hsc : decide (c.suit = x.suit) with
                | true =>
                    have hsc' : c.suit = x.suit := of_decide_eq_true hsc
                    have hob : σ.heights c.suit = ι.heights c.suit + 1 := by
                      rw [hσlit, hsc']
                      exact heights_bump_self
                    rw [hob] at hc
                    rcases Nat.lt_or_ge c.rank.toIdx (ι.heights c.suit) with hlt | hle
                    · exact Or.inr hlt
                    · have heq : c.rank.toIdx = ι.heights c.suit := by omega
                      have hceq : c = x := by
                        obtain ⟨s₁, r₁⟩ := c; obtain ⟨s₂, r₂⟩ := x
                        have hs : s₁ = s₂ := hsc'
                        have h1 : r₁.toIdx = ι.heights s₁ := heq
                        have h2 : r₂.toIdx = ι.heights s₂ := hrk
                        have hhe : ι.heights s₁ = ι.heights s₂ := by rw [hs]
                        rw [Card.mk.injEq]
                        exact ⟨hs, Rank.toIdx_inj (by omega)⟩
                      subst hceq
                      refine Or.inl ?_
                      show ((ι.board.bottomOf c).isSome) = true
                      rw [hbx]
                      rfl
                | false =>
                    have hsc' : ¬(c.suit = x.suit) := by
                      intro hcon
                      rw [hcon] at hsc
                      exact absurd hsc (by simp)
                    have hob : σ.heights c.suit = ι.heights c.suit := by
                      rw [hσlit]
                      exact heights_bump_ne hsc'
                    rw [hob] at hc
                    omega
              obtain ⟨PVis, PShadow⟩ := ih σ ρ hrun'
                (fun m' hm' => hall m' (List.mem_cons_of_mem _ hm'))
              refine ⟨fun c hc => ?_, fun c hc => ?_⟩
              · rcases PVis c hc with h | h
                · exact stepVis c h
                · exact stepSh c h
              · rcases PShadow c hc with h | h
                · exact stepVis c h
                · exact stepSh c h
          | stackPile x b =>
              obtain ⟨hg, -, bd, hatt, hσlit⟩ := apply_stackPile_iff.mp hap
              have stepVis : ∀ c, σ.isVis c = true →
                  ι.isVis c = true ∨ c.rank.toIdx < ι.heights c.suit := by
                intro c hc
                rcases vis_of_stackPile hap hc with ⟨-, h⟩ | h
                · exact Or.inl h
                · exact Or.inr h
              have stepSh : ∀ c, c.rank.toIdx < σ.heights c.suit →
                  ι.isVis c = true ∨ c.rank.toIdx < ι.heights c.suit := by
                intro c hc
                cases hsc : decide (c.suit = x.suit) with
                | true =>
                    have hsc' : c.suit = x.suit := of_decide_eq_true hsc
                    have hob : σ.heights c.suit = ι.heights c.suit - 1 := by
                      rw [hσlit, hsc']
                      exact heights_drop_self
                    rw [hob] at hc
                    omega
                | false =>
                    have hsc' : ¬(c.suit = x.suit) := by
                      intro hcon
                      rw [hcon] at hsc
                      exact absurd hsc (by simp)
                    have hob : σ.heights c.suit = ι.heights c.suit := by
                      rw [hσlit]
                      exact heights_drop_ne hsc'
                    rw [hob] at hc
                    omega
              obtain ⟨PVis, PShadow⟩ := ih σ ρ hrun'
                (fun m' hm' => hall m' (List.mem_cons_of_mem _ hm'))
              refine ⟨fun c hc => ?_, fun c hc => ?_⟩
              · rcases PVis c hc with h | h
                · exact stepVis c h
                · exact stepSh c h
              · rcases PShadow c hc with h | h
                · exact stepVis c h
                · exact stepSh c h
          | draw | reveal _ | deckPile _ _ | deckStack _ | pilePile _ _ =>
              simp only [Move.isAccommodation] at hacc
              exact absurd hacc (by simp)

/-- **The closure's visibility bound** (the K-rules' shared premise):
inside the safe accommodation closure, every visible card was
root-visible or sits below its suit's root foundation height (a
worry-back from the root foundation).  Deck and buried cards never
enter `vis`.

Proof: the play induction `vis_shadow_play` — each step's visibility
claim composes through the successor's foundation-side shadow.  The
`pileStack` step's new foundation card is the fired card itself
(root-visible by its apply guard); the `stackPile` step's new visible
card is root-foundation by the un-stack guard.  The play's safety
condition is not needed. -/
theorem vis_of_safeAccommodates {st st' : State} (h : safeAccommodates st st')
    (c : Card) (hvis : st'.isVis c = true) :
    st.isVis c = true ∨ c.rank.toIdx < st.heights c.suit := by
  obtain ⟨ms, hrun, hall, -⟩ := h
  exact (vis_shadow_play st ms st' hrun hall).1 c hvis

/-- The frontier's witness spec: below 13 the frontier is a real
missing rank — at or above the height, not visible-and-unlocked, with
every prefix rank below it visible and unlocked.

Proof: the found element of `find?` over the height-filtered
`Rank.all` is a witness in range and blocked (core's
`find?_eq_some_iff_append`); minimality runs the `find?` prefix law on
the `filter`/`append` reassembly of the filtered list around the
witness (`Rank.all_split_filter`), which places every shorter rank of
the range on the prefix side. -/
theorem State.frontier_spec (st : State) (s : Suit) (hlt : st.frontier s < 13) :
    ∃ r : Rank, st.frontier s = r.toIdx ∧ st.heights s ≤ r.toIdx ∧
      (st.isVis ⟨s, r⟩ = false ∨ st.isLocked ⟨s, r⟩ = true) ∧
      ∀ r' : Rank, st.heights s ≤ r'.toIdx → r'.toIdx < r.toIdx →
        st.isVis ⟨s, r'⟩ = true ∧ st.isLocked ⟨s, r'⟩ = false := by
  simp only [State.frontier] at hlt ⊢
  cases hff : (Rank.all.filter fun r => st.heights s ≤ r.toIdx).find?
      (fun r => !(st.isVis ⟨s, r⟩) || st.isLocked ⟨s, r⟩) with
  | none => rw [hff] at hlt; exact absurd hlt (by simp)
  | some rr =>
      obtain ⟨hprr, as_, bs_, hsplit, -⟩ := List.find?_eq_some_iff_append.mp hff
      have hrrL : rr ∈ Rank.all.filter (fun r => st.heights s ≤ r.toIdx) := by
        rw [hsplit]
        exact List.mem_append.mpr (Or.inr List.mem_cons_self)
      obtain ⟨-, hQrr⟩ := List.mem_filter.mp hrrL
      have hh0 : st.heights s ≤ rr.toIdx := of_decide_eq_true hQrr
      have hblocked : st.isVis ⟨s, rr⟩ = false ∨ st.isLocked ⟨s, rr⟩ = true := by
        cases hv : st.isVis ⟨s, rr⟩ with
        | false => exact Or.inl rfl
        | true =>
            rw [hv, Bool.not_true, Bool.false_or] at hprr
            exact Or.inr hprr
      refine ⟨rr, rfl, hh0, hblocked, ?_⟩
      intro r' hh0' hlt'
      have hsplit2 := Rank.all_split_filter rr
      -- the filtered list around the witness
      have hre : Rank.all.filter (fun r => decide (st.heights s ≤ r.toIdx)) =
          (Rank.all.filter fun r => decide (r.toIdx < rr.toIdx)).filter
            (fun r => decide (st.heights s ≤ r.toIdx)) ++ (rr ::
            (Rank.all.filter fun r => decide (rr.toIdx < r.toIdx))).filter
                (fun r => decide (st.heights s ≤ r.toIdx)) := by
        rw [← List.filter_append, ← hsplit2]
      have hcons : (rr :: Rank.all.filter
            (fun r => decide (rr.toIdx < r.toIdx))).filter
            (fun r => decide (st.heights s ≤ r.toIdx))
          = rr :: (Rank.all.filter fun r => decide (rr.toIdx < r.toIdx)).filter
                (fun r => decide (st.heights s ≤ r.toIdx)) :=
        List.filter_cons_of_pos hQrr
      have hQL : (((Rank.all.filter fun r => decide (r.toIdx < rr.toIdx)).filter
            (fun r => decide (st.heights s ≤ r.toIdx))) ++ rr ::
            (Rank.all.filter fun r => decide (rr.toIdx < r.toIdx)).filter
                (fun r => decide (st.heights s ≤ r.toIdx))).find?
            (fun r => !(st.isVis ⟨s, r⟩) || st.isLocked ⟨s, r⟩) = some rr := by
        rw [← hcons, ← hre]
        exact hff
      have hrrA : rr ∉ (Rank.all.filter fun r => decide (r.toIdx < rr.toIdx)).filter
            (fun r => decide (st.heights s ≤ r.toIdx)) := by
        intro hcon
        obtain ⟨h1, -⟩ := List.mem_filter.mp hcon
        obtain ⟨-, h2⟩ := List.mem_filter.mp h1
        have := of_decide_eq_true h2
        omega
      have hr'A : r' ∈ (Rank.all.filter fun r => decide (r.toIdx < rr.toIdx)).filter
            (fun r => decide (st.heights s ≤ r.toIdx)) := by
        refine List.mem_filter.mpr ⟨?_, decide_eq_true hh0'⟩
        exact List.mem_filter.mpr ⟨Rank.mem_all r', decide_eq_true hlt'⟩
      have hnext := find?_prefix_false _
        ((Rank.all.filter fun r => decide (r.toIdx < rr.toIdx)).filter
          (fun r => decide (st.heights s ≤ r.toIdx))) rr
        ((Rank.all.filter fun r => decide (rr.toIdx < r.toIdx)).filter
          (fun r => decide (st.heights s ≤ r.toIdx))) hQL hrrA r' hr'A
      cases hv : st.isVis ⟨s, r'⟩ with
      | false =>
          rw [hv] at hnext
          exact absurd hnext (by simp)
      | true =>
          cases hl : st.isLocked ⟨s, r'⟩ with
          | false => exact ⟨rfl, rfl⟩
          | true =>
              rw [hv, hl] at hnext
              exact absurd hnext (by simp)

/-! ## K1 — the climb kill -/

/-- **K1's first-passage firing**: on a safe accommodation play that
starts with suit `s`'s height at or below `k` and ends strictly above
`k`, the `k`-ranked card for `s` (`ccard`) fires as a `pileStack` at
some prefix state τ, where it is visible (the apply guard) and
unlocked (the play's safety); until that firing its seat and
lockedness were the play start's (it can never `stackPile` below its
own rank, and every other card's move leaves another card's seat
alone — the lockedness lemmas). -/
theorem climb_firstPassage {s : Suit} {k : Nat} (ccard : Card)
    (hcc : ccard.suit = s) (hk0 : ccard.rank.toIdx = k) :
    ∀ (ι : State) (ms : List Move) (ρ : State),
    ι.run ms = some ρ → (∀ m ∈ ms, m.isAccommodation = true) →
    playSafeAccomm ι ms → ι.heights s ≤ k → k < ρ.heights s →
    ∃ (τ : State) (ms₁ ms₂ : List Move),
      ms = ms₁ ++ Move.pileStack ccard :: ms₂ ∧
      ι.run ms₁ = some τ ∧ τ.isVis ccard = true ∧ τ.isLocked ccard = false ∧
      τ.board.bottomOf ccard = ι.board.bottomOf ccard ∧
      τ.isLocked ccard = ι.isLocked ccard := by
  intro ι ms
  induction ms generalizing ι with
  | nil =>
      intro ρ hrun _ _ hle hgt
      have hρ : ι = ρ := Option.some.inj hrun
      subst hρ
      omega
  | cons m rest ih =>
      intro ρ hrun hall hsafe hle hgt
      have hacc := hall m (List.mem_cons_self)
      simp only [State.run] at hrun
      cases hap : ι.apply m with
      | none =>
          rw [hap] at hrun
          exact absurd hrun (by simp)
      | some σ =>
          rw [hap] at hrun
          have hrun' : σ.run rest = some ρ := hrun
          have hsafepair : (∀ c, m = Move.pileStack c → ι.isLocked c = false) ∧
              playSafeAccomm ((ι.apply m).getD ι) rest := hsafe
          have hgs : (ι.apply m).getD ι = σ := by rw [hap]; rfl
          rw [hgs] at hsafepair
          obtain ⟨hlockm, hsafe'⟩ := hsafepair
          cases m with
          | pileStack x =>
              obtain ⟨htop, bx, hbx, hrkx, hσlit⟩ := apply_pileStack_iff.mp hap
              cases hxc : decide (x = ccard) with
              | true =>
                  have hcxeq : x = ccard := of_decide_eq_true hxc
                  rw [← hcxeq]
                  refine ⟨ι, [], rest, rfl, rfl, ?_, hlockm x rfl, rfl, rfl⟩
                  show ((ι.board.bottomOf x).isSome) = true
                  rw [hbx]
                  rfl
              | false =>
                  have hxcn : ¬(x = ccard) := by
                    intro hcon
                    rw [hcon] at hxc
                    exact absurd hxc (by simp)
                  have hσle : σ.heights s ≤ k := by
                    cases hxs : decide (x.suit = s) with
                    | true =>
                        have hxs' : x.suit = s := of_decide_eq_true hxs
                        have hob : σ.heights s = ι.heights s + 1 := by
                          rw [hσlit, ← hxs']
                          exact heights_bump_self
                        rcases Nat.lt_or_ge (ι.heights s) k with hltk | hgek
                        · omega
                        · have hks' : ι.heights s = k := by omega
                          exact absurd (by
                            obtain ⟨s₁, r₁⟩ := x; obtain ⟨s₂, r₂⟩ := ccard
                            have hs : s₁ = s₂ := hxs'.trans hcc.symm
                            have h1 : r₁.toIdx = ι.heights s₁ := hrkx
                            have h2 : r₂.toIdx = k := hk0
                            have hhe : ι.heights s₁ = ι.heights s₂ := by rw [hs]
                            have h3 : ι.heights s₂ = k := by
                              rw [show s₂ = s from hcc]; exact hks'
                            rw [Card.mk.injEq]
                            exact ⟨hs, Rank.toIdx_inj (by omega)⟩) hxcn
                    | false =>
                        have hxs' : ¬(x.suit = s) := by
                          intro hcon
                          rw [hcon] at hxs
                          exact absurd hxs (by simp)
                        have hob : σ.heights s = ι.heights s := by
                          rw [hσlit]
                          exact heights_bump_ne (fun hh => hxs' hh.symm)
                        omega
                  obtain ⟨hlockσ, hseatσ⟩ :=
                    lockedness_pileStack hap (fun hh => hxcn hh.symm)
                  obtain ⟨τ, ms₁, ms₂, hdecomp, hrun₁, hvis, hunl, hseat, hlockτ⟩ :=
                    ih σ ρ hrun'
                      (fun m' hm' => hall m' (List.mem_cons_of_mem _ hm'))
                      hsafe' hσle hgt
                  refine ⟨τ, Move.pileStack x :: ms₁, ms₂, by
                    rw [List.cons_append]; exact congrArg (fun l => Move.pileStack x :: l) hdecomp,
                    by simp only [State.run, hap]; exact hrun₁,
                    hvis, hunl,
                    by rw [hseat, hseatσ],
                    by rw [hlockτ, hlockσ]⟩
          | stackPile x b =>
              obtain ⟨hg, -, bd, hatt, hσlit⟩ := apply_stackPile_iff.mp hap
              have hccx : ccard ≠ x := by
                intro hcon
                rw [← hcon] at hg
                rw [hcc] at hg
                exact absurd hg (by omega)
              have hσle : σ.heights s ≤ k := by
                cases hxs : decide (x.suit = s) with
                | true =>
                    have hxs' : x.suit = s := of_decide_eq_true hxs
                    have hob : σ.heights s = ι.heights s - 1 := by
                      rw [hσlit, ← hxs']
                      exact heights_drop_self
                    omega
                | false =>
                    have hxs' : ¬(x.suit = s) := by
                      intro hcon
                      rw [hcon] at hxs
                      exact absurd hxs (by simp)
                    have hob : σ.heights s = ι.heights s := by
                      rw [hσlit]
                      exact heights_drop_ne (fun hh => hxs' hh.symm)
                    omega
              obtain ⟨hlockσ, hseatσ⟩ := lockedness_stackPile hap hccx
              obtain ⟨τ, ms₁, ms₂, hdecomp, hrun₁, hvis, hunl, hseat, hlockτ⟩ :=
                ih σ ρ hrun'
                  (fun m' hm' => hall m' (List.mem_cons_of_mem _ hm'))
                  hsafe' hσle hgt
              refine ⟨τ, Move.stackPile x b :: ms₁, ms₂, by
                rw [List.cons_append]; exact congrArg (fun l => Move.stackPile x b :: l) hdecomp,
                by simp only [State.run, hap]; exact hrun₁,
                hvis, hunl,
                by rw [hseat, hseatσ],
                by rw [hlockτ, hlockσ]⟩
          | draw | reveal _ | deckPile _ _ | deckStack _ | pilePile _ _ =>
              simp only [Move.isAccommodation] at hacc
              exact absurd hacc (by simp)

/-- **K1 (the climb kill, `goal_dead`'s Stack arm)**: with the suit's
frontier below the target rank, the suit never climbs to `X` anywhere
in the closure — i.e. `X` is never stacked.  (The climb from `h₀` to
`rank X` stacks each prefix card; the frontier card can never fire:
not root-visible by `frontier_spec` — worry-backs surface only ranks
below the root height — or locked — excluded by `playSafeAccomm`.)

Proof: suppose some closure state's height for the suit passed
`rank X`; then it passed the frontier's blocked rank `r₀`, so the
first-passage firing fired `⟨suit, r₀⟩` somewhere.  Its seat and
lockedness at the firing state are still the root's (the pre-passage
invariance carried by `climb_firstPassage`), so the firing's
visibility (the apply guard) gives `isVis`-at-root, and the play's
safety gives the firing unlockedness — `isLocked`-false-at-root.
Both contradict the frontier's blockedness disjunction for `r₀`. -/
theorem K1_stack_goal_dead {st : State} {X : Card}
    (hfront : st.frontier X.suit < X.rank.toIdx) :
    ∀ st' : State, safeAccommodates st st' → st'.heights X.suit ≤ X.rank.toIdx := by
  have hlt13 : st.frontier X.suit < 13 := by
    have := X.rank.toIdx_lt
    omega
  obtain ⟨rr, hfr, hh0, hblocked, -⟩ := State.frontier_spec st X.suit hlt13
  intro st' hacc
  obtain ⟨ms, hrun, hall, hsafe⟩ := hacc
  cases hc : decide (st'.heights X.suit ≤ X.rank.toIdx) with
  | true => exact of_decide_eq_true hc
  | false =>
      have hnle : ¬(st'.heights X.suit ≤ X.rank.toIdx) := by
        intro hcon
        have hdt : decide (st'.heights X.suit ≤ X.rank.toIdx) = true :=
          decide_eq_true hcon
        rw [hc] at hdt
        exact absurd hdt (by simp)
      have hgt : X.rank.toIdx < st'.heights X.suit := by omega
      obtain ⟨τ, ms₁, ms₂, hdecomp, hrun₁, hvis, hunl, hseat, hlockτ⟩ :=
        climb_firstPassage (ccard := ⟨X.suit, rr⟩) rfl rfl st ms st' hrun hall hsafe
          hh0 (by
            show rr.toIdx < st'.heights X.suit
            omega)
      have hrootvis : st.isVis ⟨X.suit, rr⟩ = true := by
        show ((st.board.bottomOf ⟨X.suit, rr⟩).isSome) = true
        rw [← hseat]
        exact hvis
      have hrootunl : st.isLocked ⟨X.suit, rr⟩ = false := by
        rw [← hlockτ]
        exact hunl
      rcases hblocked with hv | hl
      · rw [hv] at hrootvis
        exact absurd hrootvis (by simp)
      · rw [hl] at hrootunl
        exact absurd hrootunl (by simp)

/-- **K2 (the receiver kill, `goal_dead`'s Tableau arm for
non-kings)**: if neither receiver can ever surface in the closure
(not root-visible, and ranked at-or-above its suit's root height so
no worry-back can surface it — the keystone's second disjunct), `X`
has no legal tableau placement anywhere in the closure.

PROOF LANDED 2026-10-05 (the wave-12 K2 farm session; the row's own
`sorry` marker is discharged — but the proof is
keystone-tainted until `vis_of_safeAccommodates` lands:
`#print axioms` carries `sorryAx` through it): the staged route —
`canPlace X b = true` case-splits on `b`: the anchor arm
(`canPlace_inl_iff`) needs a king, killed by `hking`; the tableau arm
is `d` visible (`isVis_of_canPlace_inr`) with `X` fitting
(`canSitOn_of_canPlace_inr`), `Card.mem_receivers_iff` puts `d` in
the receiver set, and the keystone `vis_of_safeAccommodates`
contradicts `hrecv d` both ways (root-visible contra the first
conjunct; the worry-back range `rank < h₀` contra the second, which
bounds the receiver out of it by the root heights — the engine's
`dead` test `!root.vis ∧ !root-stacked`).  This is the §8.5
visibility door: the engine-side reading is the receiver *pair*
(`or_vis` on it, §8.1's first conjunct — `Card.orVis_of_movableOf`,
Klondike/Movability.lean); the model's `canPlace` reads the pair's
visible members directly, and both receivers being dead pins the
pair invisible at every closure word.

Kings are excluded (the empty-pile gate — K5's jurisdiction, not
K2's): the anchor arm is the *only* king opening, and it has no
receiver to kill. -/
theorem K2_tableau_goal_dead {st : State} {X : Card} (hking : X.rank ≠ Rank.king)
    (hrecv : ∀ r, r ∈ X.receivers →
      st.isVis r = false ∧ st.heights r.suit ≤ r.rank.toIdx) :
    ∀ st' : State, safeAccommodates st st' → ∀ b : Base, st'.canPlace X b = false := by
  intro st' hacc b
  rcases Bool.eq_false_or_eq_true (st'.canPlace X b) with h | h
  · exfalso
    cases b with
    | inl a => exact hking (king_of_canPlace_inl h)
    | inr d =>
        obtain ⟨-, hvis', hcs⟩ := canPlace_inr_iff.mp h
        obtain ⟨hvis0, hrk⟩ := hrecv d ((Card.mem_receivers_iff X d).mpr hcs)
        rcases vis_of_safeAccommodates hacc d hvis' with h1 | h2
        · rw [h1] at hvis0
          simp at hvis0
        · omega
  · exact h
