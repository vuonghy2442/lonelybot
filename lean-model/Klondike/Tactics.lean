import Klondike.Move
import Lean

/-!
# The tactic layer — the guard set + the two most-pasted idioms

Phase-0's ergonomics file (FARM.md R3): the guard-normal-form simp
bundle `guard_nf` and the two macros `run_step` / `move_cases`, which
kill the two most-pasted proof idioms in the library:

* the `Bool.and_eq_true_iff` decomposition chains behind every
  `canPlace` / `canMoveRun` hypothesis — the characterizations live in
  Move.lean, next to `apply_*_iff` (`apply_wf` itself consumes them;
  this file imports Move);
* the `State.run` cons-propagation dance (`simp only [State.run]` +
  the apply case-split + `Option.some.inj`), pasted verbatim through
  every induction proof;
* the seven-arm `cases m` + `rw [apply_X_iff] at h` + `obtain`
  dispatch on an `st.apply m = some st'` hypothesis.

The bundle is a `simp only [...]` expansion — no global simp set is
touched (a changed global set could break unrelated proofs; the
conservative named-set form was picked on purpose).  Both macros
elaborate to exactly the tactic sequences the library pastes by hand,
plus the `run_cons_*` lemmas they ride — proven here, sorry-free.
Nothing changes any statement.
-/

/-! ## The run lemmas (`run_step`'s engine) -/

/-- Producing a successful cons run: the move applies, the rest runs. -/
theorem run_cons_intro {st : State} {m : Move} {ms : List Move} {s' w : State}
    (hm : st.apply m = some s') (hrest : s'.run ms = some w) :
    st.run (m :: ms) = some w := by
  show (match st.apply m with
    | some x => x.run ms
    | none => none) = some w
  rw [hm]
  exact hrest

/-- Consuming a successful cons run: the move applies to some
successor that runs the rest.  (The `none` branch is absurd —
discharged once, here, for every consumer.) -/
theorem run_cons_elim {st : State} {m : Move} {ms : List Move} {w : State}
    (h : st.run (m :: ms) = some w) :
    ∃ s', st.apply m = some s' ∧ s'.run ms = some w := by
  simp only [State.run] at h
  cases hm : st.apply m with
  | none => rw [hm] at h; simp at h
  | some s' => rw [hm] at h; exact ⟨s', rfl, h⟩

/-- The nil step of a run: the end state is the start state. -/
theorem run_nil_elim {st w : State} (h : st.run [] = some w) : st = w := by
  simp only [State.run] at h
  exact Option.some.inj h

/-! ## `guard_nf` — the guard-normal-form bundle -/

/-- The guard normal form, one call: `guard_nf at h` (or `guard_nf`
for the goal) takes an `st.apply m = some st'` hypothesis — or any
`legal` / `canPlace` / `canMoveRun` fact — to its canonical flat
conjunction, the apply-guards chained all the way down (concrete
bases; at a variable base the base-shaped conjuncts correctly stay
folded).  A macro over `simp only`, deliberately: no global simp set
is touched. -/
syntax (name := guardNf) "guard_nf" ("at" ident)? : tactic

macro_rules
  | `(tactic| guard_nf at $h) =>
      `(tactic| simp only [canPlace_inl_iff, canPlace_inr_iff, canMoveRun_inl_iff,
        canMoveRun_inr_iff, legal_true_iff, apply_draw_iff, apply_reveal_iff,
        apply_deckPile_iff, apply_deckStack_iff, apply_pileStack_iff,
        apply_stackPile_iff, apply_pilePile_iff] at $h:ident)
  | `(tactic| guard_nf) =>
      `(tactic| simp only [canPlace_inl_iff, canPlace_inr_iff, canMoveRun_inl_iff,
        canMoveRun_inr_iff, legal_true_iff, apply_draw_iff, apply_reveal_iff,
        apply_deckPile_iff, apply_deckStack_iff, apply_pileStack_iff,
        apply_stackPile_iff, apply_pilePile_iff])

/-! ## `run_step` — the run cons-propagation dance -/

open Lean Elab Tactic Meta in
/-- `run_step h` — the `State.run` cons-propagation dance in one call,
by the shape of `h`:

* `h : st.run [] = some w` — the nil step: substitutes through
  `Option.some.inj`;
* `h : st.run (m :: ms) = some w` — the cons step: the case-split dance
  collapses to `hm : st.apply m = some s₂` and `hrest : s₂.run ms =
  some w` (via `run_cons_elim`; for custom binder names, use
  `obtain ⟨s₁, hap, hrest⟩ := run_cons_elim h` directly);
* `h : st.apply m = some s` with goal `st.run [m] = some w` — the
  singleton produce (`run_cons_intro h rfl`; for a longer tail use
  `run_cons_intro h hrest`). -/
elab "run_step" h:ident : tactic => do
  let hName := h.getId
  let goal ← getMainGoal
  let gdecl ← goal.getDecl
  let some decl := gdecl.lctx.findFromUserName? hName |
    throwError "run_step: unknown hypothesis '{hName}'"
  let type ← whnf decl.type
  unless type.isAppOf ``Eq do
    throwError "run_step: '{hName}' is not an equation"
  let lhs := type.appFn!.appArg!
  if lhs.isAppOf ``State.run then
    let play := lhs.appArg!
    if play.isAppOf ``List.nil then
      evalTactic <| ← `(tactic|
        simp only [State.run] at $h:ident; have heq := Option.some.inj $h; subst heq)
    else if play.isAppOf ``List.cons then
      evalTactic <| ← `(tactic|
        obtain ⟨s₂, hm, hrest⟩ := run_cons_elim $h)
    else
      throwError "run_step: '{hName}' runs an opaque play — expected a literal \
        `[]` or `m :: ms` (rewrite append-forms to cons first)"
  else if lhs.isAppOf ``State.apply then
    let goalType ← whnf gdecl.type
    unless goalType.isAppOf ``Eq do
      throwError "run_step: goal is not an equation"
    let glhs := goalType.appFn!.appArg!
    let ok := glhs.isAppOf ``State.run &&
      glhs.appArg!.isAppOf ``List.cons &&
      (glhs.appArg!.appArg!).isAppOf ``List.nil
    unless ok do
      throwError "run_step: produce-form needs goal `st.run [m] = some w`; \
        for a longer tail use `run_cons_intro h hrest`"
    evalTactic <| ← `(tactic| exact run_cons_intro $h rfl)
  else
    throwError "run_step: '{hName}' is neither a run nor an apply fact"

/-! ## `move_cases` — the apply-hypothesis dispatch -/

open Lean Elab Tactic Meta in
/-- The constructor name of a `cases`/`induction` alternative (the arm
`| ctor binders => …`); local copy of the unexported core helper. -/
private def mcAltName (alt : Syntax) : Option Name :=
  let head := alt[0][0][1]
  let ident := head[1]
  if ident.isOfKind identKind then some ident.getId.eraseMacroScopes else none

open Lean Elab Tactic Meta in
/-- Strip the hygiene scopes from every identifier in emitted syntax: the
tactic's expansions must elaborate exactly as if hand-written at the call
site (rcases's `rfl` pattern is name-matched, and the binder names are
the library's conventions, not hygiene-freshened ones). -/
private def mcDescoping (stx : Syntax) : Syntax :=
  match stx with
  | .node info k args => .node info k (args.map mcDescoping)
  | .ident info str n pre => .ident info str n.eraseMacroScopes pre
  | other => other

open Lean Elab Tactic Meta in
/-- `move_cases h` — destruct `h : st.apply m = some st'` and dispatch over
the seven move kinds in one call.  Write the per-move bodies as the
alternatives of `move_cases h with | ctor binders => …`; each arm runs
its `obtain … := apply_*_iff.mp h` first (the library's binder
conventions, with the successor substituted — `rfl`), then the given
body:

```
move_cases h with
| draw => …
| reveal c => …            -- htop r a bd hbot hpile hatt
| deckPile c b => …        -- hprev hcp bd hatt
| deckStack c => …         -- hprev hrk
| pileStack c => …         -- htop b hb hrk
| stackPile c b => …       -- hrk hcp bd hatt
| pilePile c b => …       -- b₀ hb hne hcmr bd hatt
```

The move is found from `h`'s type (it must be a named local).  The
arm bodies must close their goals (the tactic framework's rule for
`cases`-alternatives — this is why the bodies are arguments, not
follow-up `case`-lines).  The move-argument binders (`c`, `b`) shadow
— check for collisions.  The follow-on guard decomposition is
`guard_nf at hcp`'s territory. -/
elab "move_cases" h:ident
    alts:(Lean.Parser.Tactic.inductionAlts) : tactic => do
  let hName := h.getId
  let goal ← getMainGoal
  let gdecl ← goal.getDecl
  let some decl := gdecl.lctx.findFromUserName? hName |
    throwError "move_cases: unknown hypothesis '{hName}'"
  let type ← whnf decl.type
  unless type.isAppOf ``Eq do
    throwError "move_cases: '{hName}' is not an equation"
  let lhs := type.appFn!.appArg!
  unless lhs.isAppOf ``State.apply do
    throwError "move_cases: '{hName}' is not an `st.apply m = some st'` fact"
  -- `State.apply : Move → State → Option State` — the move is the first argument
  match lhs.appFn!.appArg! with
  | .fvar mv =>
      let mDecl := gdecl.lctx.getFVar! (.fvar mv)
      if mDecl.userName.hasMacroScopes then
        throwError "move_cases: the move's name is inaccessible (case manually)"
      let mIdent : TSyntax `ident := ⟨Lean.mkIdent mDecl.userName⟩
      -- collect the alternative nodes (kind `inductionAlt`), in tree order
      let mut found : Array Syntax := #[]
      let mut queue : Array Syntax := #[alts.raw]
      while h : queue.size > 0 do
        let stx := queue[0]!
        queue := queue.eraseIdx 0
        if stx.isOfKind ``Lean.Parser.Tactic.inductionAlt then
          found := found.push stx
        else
          queue := queue ++ stx.getArgs
      if found.isEmpty then
        throwError "move_cases: no alternatives found (use `move_cases h with | draw => …`)"
      -- rebuild each alternative with the obtain prepended to its body
      let mut rebuilt : Array Syntax := #[]
      for alt in found do
        -- hygiene off throughout: the `rfl` patterns must elaborate as if
        -- hand-written at the call site
        let newAlt ← withOptions (fun o => o.setBool `hygiene false) do
          let obt? : Option (TSyntax `tactic) ←
            match mcAltName alt with
            | some `draw => `(tactic| obtain rfl := apply_draw_iff.mp $h)
            | some `reveal => `(tactic|
                obtain ⟨htop, r, a, bd, hbot, hpile, hatt, rfl⟩ :=
                  apply_reveal_iff.mp $h)
            | some `deckPile => `(tactic|
                obtain ⟨hprev, hcp, bd, hatt, rfl⟩ := apply_deckPile_iff.mp $h)
            | some `deckStack => `(tactic|
                obtain ⟨hprev, hrk, rfl⟩ := apply_deckStack_iff.mp $h)
            | some `pileStack => `(tactic|
                obtain ⟨htop, b, hb, hrk, rfl⟩ := apply_pileStack_iff.mp $h)
            | some `stackPile => `(tactic|
                obtain ⟨hrk, hcp, bd, hatt, rfl⟩ := apply_stackPile_iff.mp $h)
            | some `pilePile => `(tactic|
                obtain ⟨b₀, hb, hne, hcmr, bd, hatt, rfl⟩ := apply_pilePile_iff.mp $h)
            | _ => pure none
          match obt? with
          | some obt =>
              let rhs' : TSyntax `tactic := ⟨alt[1][1]⟩
              let newRhs ← `(tactic| $obt; $rhs')
              pure (alt.setArg 1 (alt[1].setArg 1 (mcDescoping newRhs.raw)))
          | none => pure alt
        rebuilt := rebuilt.push newAlt
      -- splice the rebuilt alternatives back into the tree (same order)
      let rec visit (stx : Syntax) (idx : Nat) : Syntax × Nat :=
        match stx with
        | .node info k args =>
            if k == ``Lean.Parser.Tactic.inductionAlt then
              if idx < rebuilt.size then (rebuilt[idx]!, idx + 1)
              else (stx, idx)
            else
              let (args', idx') := Id.run do
                let mut i := idx
                let mut acc := #[]
                for a in args do
                  let (a', i') := visit a i
                  acc := acc.push a'
                  i := i'
                return (acc, i)
              (.node info k args', idx')
        | other => (other, idx)
      let (newAlts, _) := visit alts.raw 0
      let alts' : TSyntax `Lean.Parser.Tactic.inductionAlts := ⟨newAlts⟩
      -- hygiene off: the emitted arm binders and the `rfl` patterns must
      -- elaborate exactly as if hand-written at the call site
      let stx ← withOptions (fun o => o.setBool `hygiene false) <|
        `(tactic| cases ($mIdent : Move) $alts':inductionAlts)
      evalTactic stx
  | _ => throwError "move_cases: the move is not a local variable (case manually)"
