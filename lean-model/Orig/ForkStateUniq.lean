import Orig.MacroInternal

/-!
# Orig.ForkStateUniq — the ForkState Uniqueness Theorem

The last big mathematical content of the fork program: **if one
`weakForkState` exists in a macro class, then the only forkStates of that
macro class are the conjugate weakForkState, up to bare cargo exchange
(`CargoPath` connected)** — the two parts of the user's formulation:

* **Part 1 (non-king pairs)** — the mate face is the SLID STATE: the
  covering cargo's run, one direct reversible `tabToTab`, flips the
  license from one twin to the other (`forkState_slide_mate`); the
  raise–slide–pull composite of `conjugateForkState` is its
  DancePath-shaped detour, and the composite's endpoint RE-LICENSES
  the same witness it started from (`conjugate_endpoint_relic` —
  the composite never lands the mate; the mate is one cargo leg
  away, not three dance legs).
* **Part 2 (king pairs, the king shuffle)** — every bare-king vacate
  (king, whole pile face-up from the king, sliding to an EMPTY
  anchor) is ONE REVERSIBLE `tabToTab` whose undo is the mirror
  vacate back (`kingVacate_reversibleW`, riding Classify's
  `tabToTab_undo_bare` — the bare-king license cell of the
  `tabToTab` classification; `Orig.Vacate`'s `vacate_emptiesPile`
  is the NON-king vacate's computational meaning, its
  `vacateShape` bars kings by design, and this chapter supplies the
  king-side complement), so every king-vacate move is a `FlatStep`
  cargo leg and the WHOLE king shuffle orbit is `CargoPath`
  connected (`KingVacWalk`, `kingVacWalk_cargoPath`).

The main row `forkState_unique` assembles the two parts with step
(1)'s pair transport; its maximality-transport sub-step is THE GATE,
recorded below it as the explicitly-named BLOCKED residue with a
per-gate diagnosis.

The in-tree interface (`Orig.MacroInternal`) is mirrored, never
redefined: `weakForkState`, `conjugateForkState`, `CargoPath`,
`FaceShape`, `classOf` are consumed by their real names.  Several of
the battery rows the in-tree module keeps `private` (the rung
writers, the loop-closed `class_leg`, the snoc-nodup kit) are
re-landed here as private copies per the house dedup discipline —
each cites its public component rows.
-/

/-! ## §0. The private engine kit
(Farm-local copies of `Orig.MacroInternal`'s private battery — the
components they split into are all public.) -/

/-- The loop-closure engine: a play from `x` landing at `w`, spliced
with ANY play back from `w` to `x`, is a witness shuffle `x → w`
(The copy of `Orig.MacroInternal`'s private `shuffleW_of_round`; the
components `State.run_cons`, `run_split`, `run_one` are public.) -/
private theorem shuffleW_of_round : ∀ (σ : List Move) (x w : State),
    x.run σ = some w → ∀ ρ : List Move, w.run ρ = some x →
      ShufflePlayW x σ w := by
  intro σ
  induction σ with
  | nil =>
      intro x w hσ ρ hρ
      have hxw : some x = some w := hσ
      injection hxw with hx
      rw [hx]
      exact .nil w
  | cons p rest ih =>
      intro x w hσ ρ hρ
      obtain ⟨y, hp, hrest⟩ := State.run_cons hσ
      refine .cons ⟨y, rest ++ ρ, hp, run_split rest y w ρ x hrest hρ⟩ hp ?_
      exact ih y w hrest (ρ ++ [p]) (run_split ρ w x [p] y hρ (run_one hp))

/-- One reversible leg stays inside the macro class (the copy of the
in-tree private `class_leg`; the setoid's `r` runs reversed, so the
witness pair is fed with its arguments swapped). -/
private theorem class_leg {st s₁ : State} {m : Move}
    (hrev : reversibleAtW st m) (hstep : State.step st m = some s₁) :
    sameOrbitSetoid.r st s₁ := by
  obtain ⟨s₁', play, hstep', hrun⟩ := hrev
  have hs : s₁' = s₁ := Option.some.inj (hstep'.symm.trans hstep)
  rw [hs] at hrun
  show RevEqW s₁ st
  exact ⟨play, shuffleW_of_round play s₁ st hrun [m] (run_one hstep),
    [m], .cons ⟨s₁, play, hstep, hrun⟩ hstep (.nil s₁)⟩

/-- Class-membership transitivity through the setoid's own engine. -/
private theorem class_trans {a b c : State}
    (h₁ : sameOrbitSetoid.r a b) (h₂ : sameOrbitSetoid.r b c) :
    sameOrbitSetoid.r a c :=
  RevEqW_trans h₂ h₁

/-- A snoc-nodup membership bar: if appending `[d]` keeps the list
duplicate-free, `d` was not in the prefix (the copy of the in-tree
private row). -/
private theorem nodup_snoc_notmem :
    ∀ (bs : List Card) (d : Card) (_hnd : (bs ++ [d]).Nodup), d ∉ bs
  | [], _, _ =>
      by
        intro hcon
        simp at hcon
  | b :: t, d, hnd =>
      by
        intro hcon
        rcases List.mem_cons.mp hcon with hdb | hcon'
        · have hbmem : b ∈ t ++ [d] :=
              List.mem_append.mpr (Or.inr (List.mem_singleton.mpr hdb.symm))
          exact absurd hbmem (List.nodup_cons.mp hnd).1
        · exact nodup_snoc_notmem t d (List.nodup_cons.mp hnd).2 hcon'

/-- A `tabToTab` never writes any foundation (the found-equality
behind the rung-preservation; `putRun_found`, `setPile_found` are
public). -/
private theorem slide_foundEq {st st' : State} {c : Card} {b : Base}
    (hstep : State.step st (Move.tabToTab c b) = some st') :
    ∀ σ, st'.found σ = st.found σ := by
  obtain ⟨a, _, _, _, hs⟩ := step_tabToTab_inv hstep
  intro σ
  rw [hs, putRun_found, setPile_found]

/-- The bare vacate's computational meaning at the removal: an empty
prefix split and an empty hidden deck leave the bare empty pile (the
`Orig.Vacate` chapters' private kit, re-landed — its public
`vacate_emptiesPile` bars kings at `vacateShape`, so the king-side
needs its own copy of the list fact). -/
private theorem afterRunRemoved_bareEmpty {p : Pile} (h : p.hidden = []) :
    Pile.afterRunRemoved p ([] : List Card) = ⟨[], ([] : List Card)⟩ := by
  rcases p with ⟨hlist, flist⟩
  cases hlist with
  | nil => rfl
  | cons x xs => exact absurd h (by simp)

/-- A twin is never its own card (the suit moves under the twin). -/
private theorem card_twin_ne (c : Card) : c.twin ≠ c := by
  intro hcon
  exact Suit.twin_ne c.suit (congrArg Card.suit hcon)

/-! ## §1. Pin transport — the pair is one, the rungs stay pinned -/

/-- A forkState's witness raises — the iff's left-to-right existence
half, instantiated once. -/
theorem forkState_raiser {st : State} (h : weakForkState st) :
    ∃ x, CanRaise st x ∧ ∀ c, CanRaise st c → c = x := by
  obtain ⟨x, _, _, hiff⟩ := h
  exact ⟨x, (hiff x).2 rfl, fun c hc => (hiff c).1 hc⟩

/-- **The state-level pair exclusivity, color form** — two
weakForkState witnesses of one state never sit at different-color pairs
(the `forkPoint_exclusive` content at the new reads: the in-tree
sandwich carries the class-grade strand; at the state grade the
two iff's alone pinch — `finalFork_pairUnique` names the pair
uniquely, and a twin flip never changes the color family). -/
theorem forkPair_not_twoColors_state {st : State} {x y : Card}
    (hx : rungAt st x.suit = x.rank.toIdx ∧
      rungAt st x.twin.suit = x.rank.toIdx ∧ (∀ c, CanRaise st c ↔ c = x))
    (hy : rungAt st y.suit = y.rank.toIdx ∧
      rungAt st y.twin.suit = y.rank.toIdx ∧ (∀ c, CanRaise st c ↔ c = y))
    (hcol : ¬ twinSuit x.suit y.suit) : False := by
  have hcx : CanRaise st x := (hx.2.2 x).2 rfl
  have hxy : x = y := (hy.2.2 x).1 hcx
  rw [hxy] at hcol
  exact hcol (Or.inl rfl)

/-- **The state-level pair exclusivity, rank form** — the two
witnesses share the rank (the twin flip keeps it; a second pair at
another rank cannot coexist at one state). -/
theorem forkPair_not_twoRanks_state {st : State} {x y : Card}
    (hx : rungAt st x.suit = x.rank.toIdx ∧
      rungAt st x.twin.suit = x.rank.toIdx ∧ (∀ c, CanRaise st c ↔ c = x))
    (hy : rungAt st y.suit = y.rank.toIdx ∧
      rungAt st y.twin.suit = y.rank.toIdx ∧ (∀ c, CanRaise st c ↔ c = y))
    (hrank : x.rank ≠ y.rank) : False := by
  have hcx : CanRaise st x := (hx.2.2 x).2 rfl
  have hxy : x = y := (hy.2.2 x).1 hcx
  rw [hxy] at hrank
  exact hrank rfl

/-- One flat leg preserves `WF` (both letters are legal moves). -/
private theorem flatStep_wf {s z : State} (h : FlatStep s z) : s.WF → z.WF := by
  cases h with
  | cargo _ _ hfire _hrev => exact fun hwf => step_wf hwf hfire
  | draw hfire _hrev => exact fun hwf => step_wf hwf hfire

/-- A cargo walk preserves `WF`, leg by leg (the kind conjunct pins
every leg to the cargo letter). -/
private theorem cargoPath_wf : ∀ {st w : State}, CargoPath st w → st.WF → w.WF := by
  intro st w h
  induction h with
  | refl s => exact fun hx => hx
  | @cons s₀ z u₂ hstep hkind _t ih =>
      obtain ⟨c, b, hfire, hrev, _⟩ := hkind
      exact fun hwf => ih (flatStep_wf hstep hwf)

/-- Every `CargoPath` leg, stripped of its kind witness, is a
`FlatPath` leg (the cargo letter IS a `FlatStep` constructor shape,
`FlatStep.draw` never rides the `CargoPath` cons by its own
`∃`-kind conjunct). -/
theorem cargoPath_flatPath {w u : State} (h : CargoPath w u) :
    FlatPath w u := by
  induction h with
  | refl s => exact FlatPath.refl s
  | @cons w₀ z u₂ hstep hkind _t ih =>
      obtain ⟨c, b, hfire, hrev, _⟩ := hkind
      exact FlatPath.cons hstep ih

/-- **The pin transport** — a cargo walk never writes a foundation,
so the weakForkState rung pair stays pinned along it (the in-tree
`flat_heights` restated at the interface relation; the found-content
upgrade is `cargoPath_foundCongr` below). -/
theorem cargoPath_rungs {st w : State} (h : CargoPath st w) :
    ∀ s, rungAt w s = rungAt st s :=
  flat_heights (cargoPath_flatPath h)

/-- **The found-content upgrade** — at `WF`, cargo-connected states
read the foundations card for card (the pins plus the banked
`rung_found_congr`; `WF` travels along the legs). -/
theorem cargoPath_foundCongr {st w : State} (h : CargoPath st w)
    (hwf : st.WF) (s : Suit) : w.found s = st.found s :=
  rung_found_congr w st (cargoPath_wf h hwf) hwf s (cargoPath_rungs h s)

/-- **Cargo walks stay in class** — every cargo leg carries its own
`reversibleAtW`, so the loop-closure engine turns it into the
both-directions shuffle pair and the path composes through the
rev-closure's transitivity.  (The mechanical strand of the in-tree
`faceShape_rel`, landed here without its gate.) -/
theorem cargoPath_class {st w : State} (h : CargoPath st w) :
    sameOrbitSetoid.r st w := by
  induction h with
  | refl s => exact RevEqW_refl s
  | @cons st₀ z u₂ hstep hkind _t ih =>
      obtain ⟨c, b, hfire, hrev, _⟩ := hkind
      exact class_trans (class_leg hrev hfire) ih

/-! ## §2. The king shuffle — every king-vacate is one cargo leg -/
/-!
The user's Part 2, mechanical core: for a king pair the conjugate
orbit EXPANDS — each bare king may vacate to any empty anchor, and
every such vacate realizes as ONE reversible `tabToTab` (undo =
the mirror vacate back; the Classification chapter's bare-king cell
is the license).  The whole orbit is therefore generated by cargo
legs alone.
-/

/-- **The king vacate is reversible `tabToTab`** — a bare king `K`
(its whole pile face-up from `K`, no hidden cards below) firing
`tabToTab K (Sum.inl k)` onto the empty anchor `k` undoes by the
mirror move `tabToTab K (Sum.inl a)` — the king rides to `k`, the
seat `a` RE-SPRINGS bare-empty, and the return is one move.  Riding
`tabToTab_undo_bare` (the classification's bare-king license cell)
with the spell rows all WF-derived; the computational meaning
(the sprung seat) is returned with the witness. -/
theorem kingVacate_reversibleW {st s₁ : State} {K : Card} {a k : Anchor}
    (hwf : st.WF) (hking : K.rank = Rank.king)
    (hhold : st.pileHolding K = some a)
    (hbelow : below K (st.piles a).faceUp = [])
    (hhid : (st.piles a).hidden = [])
    (hstep : State.step st (Move.tabToTab K (Sum.inl k)) = some s₁) :
    reversibleAtW st (Move.tabToTab K (Sum.inl k)) ∧
      (s₁.piles a).isEmpty = true := by
  -- the step record
  obtain ⟨a₀, hh₀, hcp, _, hs₁⟩ := step_tabToTab_inv hstep
  have haa : a = a₀ := Option.some.inj (hhold.symm.trans hh₀)
  subst haa
  -- the pile shape: the face-up run starts at K and rides whole
  have hKmem : K ∈ (st.piles a).faceUp := pileHolding_mem hhold
  have hrun : fromCard K (st.piles a).faceUp = K :: aboveIn K ((st.piles a).faceUp) :=
    fromCard_eq_of_mem hKmem
  -- the landing anchor is empty and off the source, by the placement guard
  obtain ⟨hkempty, _⟩ := canPlace_inl hcp
  obtain ⟨_, hknilf⟩ := (Pile.isEmpty_eq _).mp hkempty
  have hkane : k ≠ a := by
    intro hcon
    rw [hcon] at hknilf
    rw [hknilf] at hKmem
    exact absurd hKmem (by simp)
  -- the source pile empties to the bare pair of lists
  have hbare : Pile.afterRunRemoved (st.piles a) (below K (st.piles a).faceUp)
      = ⟨[], ([] : List Card)⟩ := by
    rw [hbelow]
    exact afterRunRemoved_bareEmpty hhid
  rw [hbare] at hs₁
  -- the successor's pile profile
  have hs₁a : s₁.piles a = ⟨[], ([] : List Card)⟩ := by
    rw [hs₁, putRun_piles_inl_ne _ _ _ _ (Ne.symm hkane), setPile_piles_self]
  have hs₁k : s₁.piles k = ⟨[], K :: aboveIn K ((st.piles a).faceUp)⟩ := by
    rw [hs₁, putRun_eq_inl, setPile_piles_self, hrun]
  have hkeep : ∀ y, y ≠ a → y ≠ k → s₁.piles y = st.piles y := by
    intro y hya hyk
    rw [hs₁, putRun_eq_inl, setPile_piles_ne hyk, setPile_piles_ne hya]
  -- the successor holds the search pin for the king at the landing pile
  have hwf₁ : s₁.WF := step_wf hwf hstep
  have hhold₁ : s₁.pileHolding K = some k :=
    (pileHolding_eq_some_iff hwf₁).2 (by
      rw [hs₁k]
      exact List.mem_cons_self ..)
  have hcN : K ∉ (st.piles k).faceUp :=
    (mem_faceUp_unique hwf hKmem k hkane).1
  -- the license: the classification's bare-king undo cell
  exact ⟨tabToTab_undo_bare hstep hhold hbelow hhid hking hhold₁ (Or.inl rfl)
    hkeep hcN, by rw [hs₁a]; rfl⟩

/-- **The king vacate is one cargo leg** — the `CargoPath`
constructor's own kind conjunct is fed by the reversibility row
above; the walk from `st` to its vacated successor is one
`FlatStep.cargo`. -/
theorem kingVacate_cargoLeg {st s₁ : State} {K : Card} {a k : Anchor}
    (hwf : st.WF) (hking : K.rank = Rank.king)
    (hhold : st.pileHolding K = some a)
    (hbelow : below K (st.piles a).faceUp = [])
    (hhid : (st.piles a).hidden = [])
    (hstep : State.step st (Move.tabToTab K (Sum.inl k)) = some s₁) :
    CargoPath st s₁ :=
  CargoPath.cons
    (let h := (kingVacate_reversibleW hwf hking hhold hbelow hhid hstep).1
     FlatStep.cargo K (Sum.inl k) hstep h)
    (let h := (kingVacate_reversibleW hwf hking hhold hbelow hhid hstep).1
     ⟨K, (Sum.inl k), hstep, h, rfl⟩)
    (CargoPath.refl s₁)

/-- **The bare-king vacate walk** — the reflexive-transitive closure
of single king-vacate retainer moves, each leg carrying its own
shape premises at its own base (the base `WF` rides the constructor;
successor `WF` is never needed by the closure's consumers). -/
inductive KingVacWalk : State → State → Prop
  | refl (st : State) : KingVacWalk st st
  | step {st s₁ w : State} {K : Card} {a k : Anchor}
      (hwf : st.WF) (hking : K.rank = Rank.king)
      (hhold : st.pileHolding K = some a)
      (hbelow : below K (st.piles a).faceUp = [])
      (hhid : (st.piles a).hidden = [])
      (hstep : State.step st (Move.tabToTab K (Sum.inl k)) = some s₁)
      (t : KingVacWalk s₁ w) : KingVacWalk st w

/-- **The whole king shuffle orbit is cargo-connected** — every leg
of a `KingVacWalk` is one `FlatStep.cargo` by the vacate
reversibility, so the entire orbit (a king wandering across the
vacant anchors, and back) sits inside the `CargoPath` closure. -/
theorem kingVacWalk_cargoPath {st w : State} (h : KingVacWalk st w) :
    CargoPath st w := by
  induction h with
  | refl s => exact CargoPath.refl s
  | @step st₀ s₁ w₂ K a k hwf hking hhold hbelow hhid hstep _t ih =>
      exact CargoPath.cons
        (FlatStep.cargo K (Sum.inl k) hstep
          (kingVacate_reversibleW hwf hking hhold hbelow hhid hstep).1)
        ⟨K, (Sum.inl k), hstep,
          (kingVacate_reversibleW hwf hking hhold hbelow hhid hstep).1, rfl⟩
        ih

/-- The king shuffle never leaves the macro class (each leg is
reversible; `cargoPath_class` composes). -/
theorem kingVacWalk_class {st w : State} (h : KingVacWalk st w) :
    sameOrbitSetoid.r st w :=
  cargoPath_class (kingVacWalk_cargoPath h)

/-! ## §3. The slid mate — the conjugate's second face is ONE CARGO LEG

At a weakForkState whose witness twin is covered by a FITTING cargo
(the `forkPointC` witness shape, mirrored at the new reads), the
mate face is the SLID STATE: the cargo's run slides off the twin
onto the witness — one direct reversible `tabToTab` — and the
license flips from `x` to `x.twin`.  The full iff at the slid state
is carried by the weakForkState parcel itself (the pins ride the
found-nonwrite of a slide; the maximality rides the failure of every
OTHER card's license at `st`, the rung strand of the cargo, and the
burial of the witness) — the composite's three-step
raise–slide–pull detour is NOT needed for the mate connection (see
§4: the composite's endpoint even keeps the SAME witness).
-/

/-- The mate row: the three-clause `weakForkState` at `st` with its
witness `x` raising, its twin `x.twin` covered directly by a cargo
`d` that fits ON `x` (one rank below the pair, opposite color — the
`canSitOn` fit), and the seat package the exposed twin will need
(under-seat content, or the bare-king vacate shape of
`Orig/Vacate`'s channel) — then the one-move slide produces the
mate weakForkState at the pair, CargoPath-connected to `st` (the leg's
own reversibility is `tabToTab_undo_under`, the classification's
under-cell: undo = the slide back onto the exposed twin). -/
theorem forkState_slide_mate {st : State} {x d : Card} {q : Anchor} {bs : List Card}
    (hwf : st.WF)
    (hpin1 : rungAt st x.suit = x.rank.toIdx)
    (hpin2 : rungAt st x.twin.suit = x.rank.toIdx)
    (hiff : ∀ c, CanRaise st c ↔ c = x)
    (hshape : (st.piles q).faceUp = bs ++ [x.twin, d])
    (hfit : canSitOn d x = true)
    (hseat : bs ≠ [] ∨ ((st.piles q).hidden = [] ∧ x.twin.rank = Rank.king)) :
    ∃ s', st.step (Move.tabToTab d (Sum.inr x)) = some s' ∧
      weakForkState s' ∧ CargoPath st s' := by
  -- the license's own location of x
  obtain ⟨_, p, hpox, _⟩ := (hiff x).2 rfl
  -- the memberships and search pins at st
  have htwinmem : x.twin ∈ (st.piles q).faceUp := by
    rw [hshape]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
  have hdmem : d ∈ (st.piles q).faceUp := by
    rw [hshape]
    exact List.mem_append.mpr (Or.inr
      (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl))))
  have hdhold : st.pileHolding d = some q := (pileHolding_eq_some_iff hwf).2 hdmem
  have hassol : bs ++ [x.twin, d] = (bs ++ [x.twin]) ++ [d] :=
    (List.append_assoc bs [x.twin] [d]).symm
  have hdtopq : (st.piles q).top = some d := by
    show lastOf (st.piles q).faceUp = some d
    rw [hshape, hassol]
    exact lastOf_snoc
  have hpod : st.pileOfTop d = some q := (pileOfTop_eq_some_iff hwf).2 hdtopq
  -- the fit facts
  obtain ⟨hrank, hcolne⟩ := (canSitOn_eq d x).mp hfit
  have hdne : d ≠ x := by
    intro hcon
    rw [← hcon] at hrank
    omega
  have hdtne : d ≠ x.twin := by
    intro hcon
    rw [hcon, Card.twin_rank] at hrank
    omega
  -- the piles differ: the cargo tops q, the witness tops p
  have hpq : q ≠ p := by
    intro hcon
    have hLd : lastOf (st.piles p).faceUp = some d := by
      rw [← hcon]
      exact hdtopq
    exact hdne (Option.some.inj (((pileOfTop_top hpox).2).symm.trans hLd)).symm
  -- the cut shapes, through the run discipline's duplicate-freedom
  have hndq : ((bs ++ [x.twin]) ++ [d]).Nodup := by
    have h := runOK_nodup (hwf.runOK_of q)
    rw [hshape, hassol] at h
    exact h
  have hdnotmem : d ∉ bs ++ [x.twin] := nodup_snoc_notmem _ d hndq
  have hbel : below d ((st.piles q).faceUp) = bs ++ [x.twin] := by
    rw [hshape, hassol]
    exact below_append_stop hdnotmem
  have hfrom : fromCard d ((st.piles q).faceUp) = [d] := by
    rw [hshape, hassol]
    exact fromCard_append_stop hdnotmem
  have hpre : bs ++ [x.twin] ≠ [] := by
    cases bs with
    | nil => simp
    | cons w ws => simp
  -- FIRE the slide; the successor is the literal
  have hsteplit : st.step (Move.tabToTab d (Sum.inr x)) = some
      ((st.setPile q (Pile.afterRunRemoved (st.piles q) (bs ++ [x.twin]))).putRun
        [d] (Sum.inr x)) := by
    show (match st.pileHolding d with
      | none => none
      | some a₂ =>
          if st.canPlace d (Sum.inr x) then
            match fromCard d ((st.piles a₂).faceUp) with
            | [] => none
            | run => some ((st.setPile a₂
                (Pile.afterRunRemoved (st.piles a₂)
                  (below d ((st.piles a₂).faceUp)))).putRun run (Sum.inr x))
          else none) = _
    rw [hdhold]
    simp only [canPlace_inr_located hpox, hfit]
    rw [hfrom, hbel]
    rfl
  obtain ⟨s', hs'eq, hstep⟩ : ∃ s', s' =
      (st.setPile q (Pile.afterRunRemoved (st.piles q) (bs ++ [x.twin]))).putRun
        [d] (Sum.inr x) ∧
      st.step (Move.tabToTab d (Sum.inr x)) = some s' :=
    ⟨_, rfl, hsteplit⟩
  -- the mid-state pile q: the twin exposed, the hidden deck kept
  have hmidq : (st.setPile q (Pile.afterRunRemoved (st.piles q) (bs ++ [x.twin]))).piles q
      = ⟨(st.piles q).hidden, bs ++ [x.twin]⟩ := by
    rw [setPile_piles_self, afterRunRemoved_ne hpre]
  -- the mid-state search pin for x at p (WF-free: the profile of tops)
  have hxmem : x ∈ (st.piles p).faceUp :=
    Pile.mem_of_top (pileOfTop_top hpox).2
  have hnoTx : ∀ y : Anchor, y ≠ p → (st.piles y).top ≠ some x := by
    intro y hyp htop
    exact (mem_faceUp_unique hwf hxmem y hyp).1 (Pile.mem_of_top htop)
  have hmidx :
      (st.setPile q (Pile.afterRunRemoved (st.piles q) (bs ++ [x.twin]))).pileOfTop x
        = some p := by
    show (firstWhere (fun a₂ =>
        decide ((st.setPile q
          (Pile.afterRunRemoved (st.piles q) (bs ++ [x.twin]))).topOf a₂ = some x))
      Anchor.all) = some p
    refine firstWhere_find (Anchor.mem_all p) ?_ ?_
    · show decide (((st.setPile q
          (Pile.afterRunRemoved (st.piles q) (bs ++ [x.twin]))).topOf p) = some x) = true
      rw [setPile_topOf_ne (Ne.symm hpq)]
      exact decide_eq_true (pileOfTop_top hpox).2
    · intro y _hyp hyne
      show decide (((st.setPile q
          (Pile.afterRunRemoved (st.piles q) (bs ++ [x.twin]))).topOf y) = some x) = false
      by_cases hyq : y = q
      · have hpqmid : ((st.setPile q
            (Pile.afterRunRemoved (st.piles q) (bs ++ [x.twin]))).piles q).top ≠ some x := by
          rw [setPile_piles_self, afterRunRemoved_ne hpre]
          show lastOf (bs ++ [x.twin]) ≠ some x
          intro hcon
          exact card_twin_ne x (Option.some.inj (lastOf_snoc.symm.trans hcon))
        exact decide_false_of_not (by rw [hyq]; exact hpqmid)
      · rw [setPile_topOf_ne hyq]
        exact decide_false_of_not (fun hcon => hnoTx y hyne
          (show (st.piles y).top = some x from hcon))
  -- the successor's pile profile
  have hmidp : (st.setPile q
      (Pile.afterRunRemoved (st.piles q) (bs ++ [x.twin]))).piles p = st.piles p :=
    setPile_piles_ne (Ne.symm hpq)
  have hs'l : s' = (st.setPile q
      (Pile.afterRunRemoved (st.piles q) (bs ++ [x.twin]))).setPile p
    { (st.piles p) with faceUp := (st.piles p).faceUp ++ [d] } := by
    rw [hs'eq, putRun_inr_eq hmidx, hmidp]
  have hs'p : s'.piles p = ⟨(st.piles p).hidden, (st.piles p).faceUp ++ [d]⟩ := by
    rw [hs'l, setPile_piles_self]
  have hs'q : s'.piles q = ⟨(st.piles q).hidden, bs ++ [x.twin]⟩ := by
    rw [hs'l, setPile_piles_ne hpq, hmidq]
  have hs'others : ∀ y, y ≠ p → y ≠ q → s'.piles y = st.piles y := by
    intro y hyp hyq
    rw [hs'l, setPile_piles_ne hyp, setPile_piles_ne hyq]
  -- the founds and WF never leave the leg
  have hfounds : ∀ σ, s'.found σ = st.found σ := fun _ => slide_foundEq hstep _
  have hwfs' : s'.WF := step_wf hwf hstep
  have hL1 : (st.found x.suit).length = x.rank.toIdx := hpin1
  have hL2 : (st.found x.twin.suit).length = x.rank.toIdx := hpin2
  have hL1 : (st.found x.suit).length = x.rank.toIdx := hpin1
  have hL2 : (st.found x.twin.suit).length = x.rank.toIdx := hpin2
  -- the mate arm is live: x.twin exposes licensed at the slid state
  have hnexttwin : s'.nextUp x.twin = true := by
    show decide (x.twin.rank.toIdx = (s'.found x.twin.suit).length) = true
    rw [hfounds x.twin.suit, hL2, Card.twin_rank]
    exact decide_eq_true rfl
  have htopq' : (s'.piles q).top = some x.twin := by
    rw [hs'q]
    show lastOf (bs ++ [x.twin]) = some x.twin
    exact lastOf_snoc
  have hpodtwin : s'.pileOfTop x.twin = some q :=
    (pileOfTop_eq_some_iff hwfs').2 htopq'
  have hseattwin : chop (s'.piles q).faceUp ≠ [] ∨
      ((s'.piles q).hidden = [] ∧ x.twin.rank = Rank.king) := by
    rw [hs'q]
    rcases hseat with hbs | hhk
    · exact Or.inl (by rw [chop_snoc]; exact hbs)
    · exact Or.inr hhk
  have hlicensetwin : CanRaise s' x.twin :=
    ⟨hnexttwin, q, hpodtwin, hseattwin⟩
  -- the witness is buried by the landed run
  have hnox : ¬ CanRaise s' x := by
    rintro ⟨_, a₂, hpo₂, _⟩
    have hxmem' : x ∈ (s'.piles p).faceUp := by
      rw [hs'p]
      exact List.mem_append.mpr (Or.inl hxmem)
    have hmema₂ : x ∈ (s'.piles a₂).faceUp :=
      Pile.mem_of_top ((pileOfTop_eq_some_iff hwfs').mp hpo₂)
    have hap : a₂ = p :=
      pileHolding_inj ((pileHolding_eq_some_iff hwfs').2 hmema₂)
        ((pileHolding_eq_some_iff hwfs').2 hxmem')
    rw [hap] at hpo₂
    have htopp : (s'.piles p).top = some x := (pileOfTop_eq_some_iff hwfs').mp hpo₂
    rw [hs'p] at htopp
    have hlast : lastOf ((st.piles p).faceUp ++ [d]) = some x := htopp
    exact hdne (Option.some.inj (lastOf_snoc.symm.trans hlast))
  -- the cargo stays strand-barred: its own license would have fired at st
  have hnextdfalse : st.nextUp d = false := by
    cases hnu : st.nextUp d with
    | true =>
        exfalso
        have hchop : chop ((st.piles q).faceUp) ≠ [] := by
          rw [hshape, hassol, chop_snoc]
          exact hpre
        exact hdne ((hiff d).1 ⟨hnu, q, hpod, Or.inl hchop⟩)
    | false => rfl
  have hstrandd : ¬ CanRaise s' d := by
    rintro ⟨hnu2, _, _, _⟩
    have hcast : st.nextUp d = true := by
      show decide (d.rank.toIdx = (st.found d.suit).length) = true
      rw [← hfounds d.suit]
      exact hnu2
    rw [hcast] at hnextdfalse
    exact Bool.noConfusion hnextdfalse
  -- every other card stays unlicensed: the parcel transports
  have hiffc : ∀ c, c ≠ x.twin → c ≠ x → c ≠ d → ¬ CanRaise s' c := by
    intro c hct hcx hcxd
    rcases Decidable.em (st.nextUp c = true) with hnu | hnu
    · have hnc : ∀ a₂, st.pileOfTop c = some a₂ →
          ¬ (chop ((st.piles a₂).faceUp) ≠ [] ∨
            ((st.piles a₂).hidden = [] ∧ c.rank = Rank.king)) := by
        intro a₂ hpo hseat₂
        exact hcx ((hiff c).1 ⟨hnu, a₂, hpo, hseat₂⟩)
      intro hcr
      obtain ⟨_, a₃, hpo₃, hseat₃⟩ := hcr
      have hpne : a₃ ≠ p := by
        intro hcon
        rw [hcon] at hpo₃
        have htopp : (s'.piles p).top = some c := (pileOfTop_eq_some_iff hwfs').mp hpo₃
        rw [hs'p] at htopp
        have hlast : lastOf ((st.piles p).faceUp ++ [d]) = some c := htopp
        exact hcxd (Option.some.inj (lastOf_snoc.symm.trans hlast)).symm
      have hqne : a₃ ≠ q := by
        intro hcon
        rw [hcon] at hpo₃
        have htopq2 : (s'.piles q).top = some c := (pileOfTop_eq_some_iff hwfs').mp hpo₃
        rw [hs'q] at htopq2
        have hlastc : lastOf (bs ++ [x.twin]) = some c := htopq2
        exact hct (Option.some.inj (lastOf_snoc.symm.trans hlastc)).symm
      have hP3 : s'.piles a₃ = st.piles a₃ := hs'others a₃ hpne hqne
      have htop3 : (s'.piles a₃).top = some c := (pileOfTop_eq_some_iff hwfs').mp hpo₃
      rw [hP3] at htop3
      have hseat3s : chop ((st.piles a₃).faceUp) ≠ [] ∨
          (((st.piles a₃).hidden = []) ∧ c.rank = Rank.king) := by
        rw [← hP3]
        exact hseat₃
      exact hnc a₃ ((pileOfTop_eq_some_iff hwf).mpr htop3) hseat3s
    · intro hcr
      obtain ⟨hnu2, _, _, _⟩ := hcr
      have hcast : st.nextUp c = true := by
        show decide (c.rank.toIdx = (st.found c.suit).length) = true
        rw [← hfounds c.suit]
        exact hnu2
      rw [hcast] at hnu
      exact hnu rfl
  -- the mate weakForkState, and the one-leg CargoPath
  refine ⟨s', hstep, ⟨x.twin, ?_, ?_, ?_⟩, ?_⟩
  · show (s'.found x.twin.suit).length = x.twin.rank.toIdx
    rw [hfounds x.twin.suit, hL2, Card.twin_rank]
  · show (s'.found x.twin.twin.suit).length = x.twin.rank.toIdx
    rw [Card.twin_twin, hfounds x.suit, hL1, Card.twin_rank]
  · intro c
    constructor
    · intro hcr
      by_cases hct : c = x.twin
      · exact hct
      · by_cases hcx2 : c = x
        · rw [hcx2] at hcr
          exact absurd hcr hnox
        · by_cases hcd2 : c = d
          · rw [hcd2] at hcr
            exact absurd hcr hstrandd
          · exact absurd hcr (hiffc c hct hcx2 (fun h => hcd2 h))
    · intro hc
      rw [hc]
      exact hlicensetwin
  · -- the leg's reversibility: the classification's under-cell
    have hbell : lastOf (below d ((st.piles q).faceUp)) = some x.twin := by
      rw [hbel]
      exact lastOf_snoc
    have hrankT : d.rank.toIdx + 1 = x.twin.rank.toIdx := by
      rw [Card.twin_rank]
      exact hrank
    have hcolT : d.suit.color ≠ x.twin.suit.color := by
      rw [show x.twin.suit.color = x.suit.color from
          (Suit.color_twin x.suit)]
      exact hcolne
    have hsitT : canSitOn d x.twin = true :=
      (canSitOn_eq d x.twin).2 ⟨hrankT, hcolT⟩
    have hholdp' : s'.pileHolding d = some p :=
      (pileHolding_eq_some_iff hwfs').2 (by
        rw [hs'p]
        show d ∈ (st.piles p).faceUp ++ [d]
        exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))
    have hcn2 : d ∉ (st.piles p).faceUp := (mem_faceUp_unique hwf hdmem p (Ne.symm hpq)).1
    have hzonly : ∀ y, y ≠ q → (s'.piles y).top ≠ some x.twin := by
      intro y hyq htop
      by_cases hyp : y = p
      · rw [hyp] at htop
        rw [hs'p] at htop
        have hlast : lastOf ((st.piles p).faceUp ++ [d]) = some x.twin := htop
        exact hdtne (Option.some.inj (lastOf_snoc.symm.trans hlast))
      · have hP4 : s'.piles y = st.piles y := hs'others y hyp hyq
        rw [hP4] at htop
        exact (mem_faceUp_unique hwf htwinmem y hyq).1 (Pile.mem_of_top htop)
    have hzk : (st.piles p).top ≠ some x.twin :=
      fun htop => (mem_faceUp_unique hwf htwinmem p (Ne.symm hpq)).1 (Pile.mem_of_top htop)
    have hmidx2 : (st.setPile q
        (Pile.afterRunRemoved (st.piles q) (below d ((st.piles q).faceUp)))).pileOfTop x
          = some p := by
      rw [hbel]
      exact hmidx
    have hrev := tabToTab_undo_under hstep hdhold hbell hsitT hholdp'
      (Or.inr ⟨x, rfl, hmidx2⟩) (fun y hyq hyp => hs'others y hyp hyq) hcn2
      hzonly hzk
    exact CargoPath.cons (FlatStep.cargo d (Sum.inr x) hstep hrev)
      ⟨d, (Sum.inr x), hstep, hrev, rfl⟩ (CargoPath.refl s')

/-! ## §4. The composite's own anatomy — what the raise–slide–pull detour lands

The `conjugateForkState` composite's three legs are a dance: the
raise is a `DanceStep.raise`, the two `tabToTab` legs are cargo
letters when taken in the flat direction (each with its own
reversibility — the raise's undo is the pulled seat, the slide's
undo is the mirror slide, the pull's undo is the re-raise).  But
the composite is NET-FLAT on the foundations, and its endpoint
RE-LICENSES the very witness it started from: the pulled-back card
sits on a fresh seat with its pin restored, so the composite never
lands the mate face — the mate is the SLIDE of §3, one cargo leg,
not three dance legs.  These rows pin that anatomy down.
-/

/-- **The composite is net-flat on the foundations** — the raise
writes `+[x]`, the slide writes nothing, the pull chops it right
back; every foundation returns card for card.  Stated at the loose
three-step shape (the `weakForkState st` conjunct of
`conjugateForkState` is never read here, so the row is the
stronger one). -/
theorem conjugate_endpoint_netflat {st w : State} {x : Card}
    (hsteps : ∃ d ba bb st₁ st₂,
      st.step (Move.tabToFound x) = some st₁ ∧
      st₁.step (Move.tabToTab d ba) = some st₂ ∧
      st₂.step (Move.foundToTab x bb) = some w) :
    ∀ σ, w.found σ = st.found σ := by
  obtain ⟨d, ba, bb, st₁, st₂, h₁, h₂, h₃⟩ := hsteps
  obtain ⟨_, a, _, hs₁⟩ := step_tabToFound_inv h₁
  obtain ⟨_, _, _, _, hs₃⟩ := step_foundToTab_inv h₃
  intro σ
  have h₁self : st₁.found x.suit = st.found x.suit ++ [x] :=
    (tabToFound_found_trio (a := a) hs₁).1
  have h₁other : ∀ σ', σ' ≠ x.suit → st₁.found σ' = st.found σ' :=
    (tabToFound_found_trio (a := a) hs₁).2.1
  have h₂f : ∀ σ', st₂.found σ' = st₁.found σ' :=
    fun σ' => slide_foundEq h₂ σ'
  have hw : w.found σ =
      (st₂.setFound x.suit (chop (st₂.found x.suit))).found σ := by
    rw [hs₃]
    exact congrFun (putCard_keep (st := st₂.setFound x.suit (chop (st₂.found x.suit)))
      (c := x) (b := bb)).1 σ
  rw [hw]
  by_cases hσ : σ = x.suit
  · rw [hσ, setFound_found_self, h₂f, h₁self, chop_snoc]
  · rw [setFound_found_ne hσ, h₂f, h₁other σ hσ]

/-- **The composite's endpoint re-licenses its own witness** — the
pulled-back `x` lands as a pile top with a live seat (the fresh
base's chop, or the king-vacate shape of the empty-anchor landing),
its pin restored by the net-flat composite.  This is the row that
separates the composite from the mate: a weakForkState at the composite
endpoint must witness the SAME card the composite started with. -/
theorem conjugate_endpoint_relic {st w : State} {x : Card}
    (hwf : st.WF)
    (hconj : ∃ d ba bb st₁ st₂,
      st.step (Move.tabToFound x) = some st₁ ∧
      st₁.step (Move.tabToTab d ba) = some st₂ ∧
      st₂.step (Move.foundToTab x bb) = some w) :
    CanRaise w x ∧ rungAt w x.suit = x.rank.toIdx := by
  obtain ⟨d, ba, bb, st₁, st₂, h₁, h₂, h₃⟩ := hconj
  obtain ⟨hnextst, a, hpox, hs₁⟩ := step_tabToFound_inv h₁
  obtain ⟨-, htop₃, -, hcp₃, hs₃⟩ := step_foundToTab_inv h₃
  have hwfst₁ : st₁.WF := step_wf hwf h₁
  have hwfst₂ : st₂.WF := step_wf hwfst₁ h₂
  have hwfw : w.WF := step_wf hwfst₂ h₃
  have hnet : ∀ σ, w.found σ = st.found σ :=
    conjugate_endpoint_netflat ⟨d, ba, bb, st₁, st₂, h₁, h₂, h₃⟩
  -- the pin, read off the raise's own guard, rides the net-flat composite
  have hL : (st.found x.suit).length = x.rank.toIdx :=
    (of_decide_eq_true hnextst).symm
  have hpinw : rungAt w x.suit = x.rank.toIdx := by
    show (w.found x.suit).length = x.rank.toIdx
    rw [hnet x.suit]
    exact hL
  have hnextw : w.nextUp x = true := by
    show decide (x.rank.toIdx = (w.found x.suit).length) = true
    rw [hnet x.suit, hL]
    exact decide_eq_true rfl
  refine ⟨⟨hnextw, ?_⟩, hpinw⟩
  obtain ⟨k, hwtop, hseat⟩ :
      ∃ k, (w.piles k).top = some x ∧
        (chop (w.piles k).faceUp ≠ [] ∨
          ((w.piles k).hidden = [] ∧ x.rank = Rank.king)) := by
    cases bb with
    | inl k =>
        obtain ⟨_, hking⟩ := canPlace_inl hcp₃
        refine ⟨k, ?_, ?_⟩
        · rw [hs₃, putCard_eq_inl, setPile_piles_self]
          rfl
        · refine Or.inr ⟨by
            show (w.piles k).hidden = []
            rw [hs₃, putCard_eq_inl, setPile_piles_self], hking⟩
    | inr z =>
        obtain ⟨k, hk₂, _⟩ := canPlace_inr hcp₃
        have hkS : (st₂.setFound x.suit (chop (st₂.found x.suit))).pileOfTop z = some k :=
          hk₂
        refine ⟨k, ?_, ?_⟩
        · rw [hs₃, putCard_inr_eq hkS, setPile_piles_self]
          show lastOf (((st₂.setFound x.suit (chop (st₂.found x.suit))).piles k).faceUp
            ++ [x]) = some x
          exact lastOf_snoc
        · refine Or.inl ?_
          rw [hs₃, putCard_inr_eq hkS, setPile_piles_self]
          show chop (((st₂.setFound x.suit (chop (st₂.found x.suit))).piles k).faceUp
            ++ [x]) ≠ []
          rw [chop_snoc]
          have hne : ((st₂.setFound x.suit (chop (st₂.found x.suit))).piles k).faceUp ≠ [] := by
            show ((st₂.piles k).faceUp : List Card) ≠ []
            exact (pileOfTop_top hk₂).1
          exact hne
  exact ⟨k, (pileOfTop_eq_some_iff hwfw).2 hwtop, hseat⟩

/-- **THE ENDPOINT'S WITNESS IS THE SAME CARD** — if the composite's
endpoint carries a weakForkState at all, its iff names the composite's
own starting witness: the mate face never comes from the composite
(it comes from §3's one-leg slide). -/
theorem conjugate_endpoint_witness {st w : State} {x y : Card}
    (hwf : st.WF)
    (hconj : ∃ d ba bb st₁ st₂,
      st.step (Move.tabToFound x) = some st₁ ∧
      st₁.step (Move.tabToTab d ba) = some st₂ ∧
      st₂.step (Move.foundToTab x bb) = some w)
    (hyiff : ∀ c, CanRaise w c ↔ c = y) : y = x := by
  obtain ⟨hrel, _⟩ := conjugate_endpoint_relic hwf hconj
  exact ((hyiff x).1 hrel).symm

/-- The composite read as a dance path, given each leg's own
reversibility (the raise leg's undo is the pulled seat — the fork
license's own seat package; the slide leg's mirror; the pull leg's
re-raise).  The `tabToTab` classification's reversibility cells are
what the flat direction of the package supplies. -/
theorem conjugate_dancePath {st w : State} {x d : Card} {ba bb : Base}
    {st₁ st₂ : State}
    (h₁ : st.step (Move.tabToFound x) = some st₁)
    (h₂ : st₁.step (Move.tabToTab d ba) = some st₂)
    (h₃ : st₂.step (Move.foundToTab x bb) = some w)
    (hr₁ : reversibleAtW st (Move.tabToFound x))
    (hr₂ : reversibleAtW st₁ (Move.tabToTab d ba))
    (hr₃ : reversibleAtW st₂ (Move.foundToTab x bb)) :
    DancePath st w :=
  DancePath.cons (DanceStep.raise x h₁ hr₁)
    (DancePath.cons (DanceStep.cone (ConeStep.slide d ba h₂ hr₂))
      (DancePath.cons (DanceStep.cone (ConeStep.pull x bb h₃ hr₃))
        (DancePath.refl w)))

/-! ## §5. THE MAIN ROW — the ForkState Uniqueness Theorem, assembled and gated

The assembled statement, in the user's two parts (the non-king
conjugate half and the king-shuffle half), with everything the two
halves need mechanically having landed above:

* the mate face is ONE reversible cargo leg off the witness state
  (§3), and it is a weakForkState of the SAME CLASS (`cargoPath_sameClass`);
* every bare-king vacate is one reversible cargo leg (§2), so the
  whole king shuffle orbit — a king wandering the vacant anchors,
  swapping with its twin — sits inside the `CargoPath` closure
  (`kingVacWalk_cargoPath`), inside the same class
  (`kingVacWalk_class`);
* the composite detour never produces the mate (§4) — at a fork
  state the class's fork faces are the SLIDE orbit, and the dance-
  shaped composites re-license the same witness, so the two-face
  book is honest.

What remains beyond assembly is ONE gate — the maximality
transport — recorded under the main row with the precise
diagnosis.  Everything else in this file is sorry-free.
-/

/-- The class-membership corollary: a cargo walk's endpoint sits in
the same macro class as its start (the leg reversibility composes
through the setoid's engine; the quotient sound read at the class). -/
theorem cargoPath_sameClass {st w : State} {C : SameOrbit}
    (h : CargoPath st w) (hC : classOf C st) : classOf C w :=
  (Quotient.sound (cargoPath_class h)).symm.trans hC

/-- The mate face is a class-mate: §3's slid weakForkState enters the
same macro class as the state it slid off (`cargoPath_sameClass` at
the mate leg). -/
theorem forkState_mate_inClass {st : State} {C : SameOrbit}
    (hC : classOf C st)
    (hmate : ∃ s' d x, st.step (Move.tabToTab d (Sum.inr x)) = some s' ∧
      weakForkState s' ∧ CargoPath st s') : ∃ s', weakForkState s' ∧ classOf C s' ∧
      CargoPath st s' := by
  obtain ⟨s', d, x, hstep, hfs, hcp⟩ := hmate
  exact ⟨s', hfs, cargoPath_sameClass hcp hC, hcp⟩

/-- **THE FORKSTATE UNIQUENESS THEOREM** — IF one weakForkState exists
in a macro class, THEN the only forkStates of that macro class are
the conjugate weakForkState, UP TO BARE CARGO EXCHANGE (`CargoPath`
connected): in the non-king case the pair's two faces are the
witness state and its §3 slid mate; in the king case the orbit
expands across the vacant anchors by §2's king-vacate legs, all
cargo.

**STATUS (the 2026-10-12 reproof wave) — G2 DISSOLVED, the assembly
re-graded.**  At the strong premises the coverage gate is GONE: the
covered-twin-with-fitting-cover geometry is derivable from the def
(`Orig.ForkWeaker`'s witness rows), and the mate production is landed
at theorem grade (`Orig.SFlatTransfer.forkState_mate_S`, zero sorry)
with the conjugate production beside it (`Orig.SConjugate`
—assembled, two named census residues) — the production stack this
row's G2 case-split had priced.  The remaining honest gates:

* **G1 (pair transport, journey half)**: the census half LANDED
  (`Orig.SFlatTransfer.S_census_one_leg` — the flat invariance); the
  journey half rides the bracket machinery
  (`Orig.BracketDecomp.reversible_equaltuple_decompose`, one named
  nesting residue) and the conjugate census transport (the two named
  rows of `Orig.SConjugate`).
* **G3 (the saturated residue)**: unchanged — the
  `saturated_classification`/`canonFace_sameShape` tier.

* **(G1) PAIR-TRANSPORT** — the two witnesses must share the pair
  up to twin flip.  At the new reads the rung pins of one weakForkState
  do NOT exclude a second pair at the other color family: the two
  off-pair suits' rungs are free data, and the in-tree
  `forkPoint_exclusive` sandwich needs the `forkPointC` cargo
  strand (`¬ satStackable` at the witness's own cargo) — a
  CLASS-grade fact that the state-grade iff carries only at
  itself.  Transporting the strand across the reversible journey
  between `st₁` and `st₂` is the content the in-tree corpus gates
  behind the envelope (`envelope`) and the saturated residue
  (`saturated_classification`/`cononFace_sameShape` tier) —
  riding those sorry'd rows is exactly what this row may not do.
* **(G2) COVERAGE-DEGENERACY** — the mate production needs the
  covering-cargo parcel (the trial shape: the twin COVERED
  directly by a fitting `d`, and the exposed seat package).  A
  weakForkState whose twin is blocked otherwise (waste/stock, buried
  under non-fitting cargo, or the bare-bottom non-king twin — the
  (Q,J)-falsifier seat) realizes with NO slid mate, and for those
  classes the uniqueness claim degenerates to the cargo orbit of
  the one witness; the case-split itself is classification
  content.
* **(G3) THE SATURATED RESIDUE** — even sharing the pair and the
  coverage, two same-class forkStates may differ by EXTRA
  non-covering cargo (the class's other wiggle content); linking
  each into the {witness, mate} pair through reversible legs each
  keeping the fork geometry is the saturated-classification half
  the canon-face tier owns.

Given any one of the gates' closures (the classification card's
remaining work), the row assembles from this file's landed halves:
G1 pins the pair, G2 selects the slide-orbit, G3 normalizes the
residue; `forkState_slide_mate` and `kingVacWalk_cargoPath` are
the connectors.  The residue is intentionally a single `sorry`
carrying the whole named gate.

**THE S-GRADE RETARGETING** (the strong-grade resurrection, this
premises-level swap): the hypotheses now carry the maneuver-stable
detection, and the tuple lock `htup` bars the cascade ladder (two
same-class forks may sit at different pair-column rungs by raising
through the cone — the ladder is not FaceShape-flat, and the lock is
what the spectral analysis always said this row needed).  What the
strong grade buys here: **G2 DISSOLVES** — the covered-twin-with-
fitting-cover geometry is now derivable from the def alone (a twin
blocked otherwise — waste/stock, non-fitting cargo, the bare
(Q,J)-seat — is NOT S-live, failing the iff's pair-live half, so
those degenerate weak-grade shapes are not forkStates at this grade);
and the bridge `forkState → weakForkState` lets every banked weak-
grade connector fire under the strong hypotheses.  What remains:
G1's pair transport at the locked tuple (the census/freeze transfer
along the reversible journey — the cone-cards' machinery) and G3's
residue normalization. -/
theorem forkState_unique {C : SameOrbit} {st₁ st₂ : State}
    (hwf₁ : st₁.WF) (hwf₂ : st₂.WF)
    (h₁ : forkState st₁) (h₂ : forkState st₂)
    (hc₁ : classOf C st₁) (hc₂ : classOf C st₂)
    (htup : ∀ σ : Suit, rungAt st₁ σ = rungAt st₂ σ) :
    FaceShape st₁ st₂ := by
  sorry

/-! ## The audit battery
(`#print axioms` per fresh head — expected `[propext, Quot.sound]`
everywhere except the main row's named residue, which shows its
`sorryAx` exactly as the in-tree gated rows do
(`cone_pulls_congr_crossarm`'s precedent).  Zero `Classical.choice`
is expected across the whole chapter: every landed row is
constructive search-bookkeeping and step-record arithmetic.) -/

#print axioms forkState_raiser
#print axioms forkPair_not_twoColors_state
#print axioms forkPair_not_twoRanks_state
#print axioms cargoPath_flatPath
#print axioms cargoPath_rungs
#print axioms cargoPath_foundCongr
#print axioms cargoPath_class
#print axioms kingVacate_reversibleW
#print axioms kingVacate_cargoLeg
#print axioms kingVacWalk_cargoPath
#print axioms kingVacWalk_class
#print axioms forkState_slide_mate
#print axioms conjugate_endpoint_netflat
#print axioms conjugate_endpoint_relic
#print axioms conjugate_endpoint_witness
#print axioms conjugate_dancePath
#print axioms cargoPath_sameClass
#print axioms forkState_mate_inClass
#print axioms forkState_unique

/- APPEND-MARKER -/
