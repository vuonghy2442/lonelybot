# Rigor status — what is proved, what isn't, and the finish line

The per-claim index with tiers, dependencies, and closers is
[soundness_ledger.md](soundness_ledger.md); this document is the narrative
framing behind it.

Working assessment at the end of the 2026-09 documentation push
(method.md + no_pile_to_pile.md + last_draw_rules.md +
pruning_dominance_interaction.md + macro_formalization.md).

**The standard.** A claim is *rigorous* when every step is either
mechanically checkable from the definitions, or a stated lemma a competent
reader could discharge without inventing a new idea. Evidence and
instrumentation do not count as proof.

## Rigorous or near-rigorous

- **CyclePruner** — the splice identity (`m` then immediate undo is a
  no-op; delete both).
- **Hidden identities pinned within a game** — a pile's structure is a
  prefix of the deal, so counts determine identities
  (no_pile_to_pile.md §1). This also discharged macro doc O2.
- **The safe-stack formula** — proven, in the literature (Keller; Blake &
  Gent App. B.1, plus Thm 5 for the pair's mutual soundness), for the
  standard move set. Rigorous *modulo the port* to this engine's
  arrangement-free state (channels A/B are the port's shape).
- **no_pile_to_pile.md §3–§4** (realizability invariant, parity
  truthfulness, compression lemma) — the argument *form* is rigorous
  (per-move witnesses, original positions realizing the abstract states),
  but the mechanical case tables are not yet written out: the
  (present, placed) enumeration for the parity lemma, and the case-split
  exhaustiveness for the guards. A focused reader can fill these.
- **6.3's `{r, twin(r)}` exemption** — modulo L1/L2, which are
  formula-level claims not yet case-discharged.

## Not rigorous — the informality localizes to three cores

1. **The reshape lemma** (no_pile_to_pile.md §5). An existence statement
   with a strategy (the normal form) and a falsifier, not an argument.
   Blocker chains have never been analyzed mathematically; empirically,
   the one-relocation concretization in convert.rs has never been
   observed to fail.
2. **Rule 6.4** (last_draw_rules.md). D1–D3 give the clean half; R1/R2
   are named counterexample *shapes* (R1 already widened once — kept
   family reveals are themselves R1 constructors); Claim B is a mechanism
   hypothesis. A writeup that ends "unless these two shapes, conjecturally
   empty" is triangulated, not rigorous.
3. **The closure property for the composition** (interaction doc §2). A
   rewrite-system confluence claim — genuinely beyond hand proof at this
   rule count: Blake & Gent's own ceiling is pairwise compatibility
   (their Thm 5 covers two rules). The informal surrogate is
   drain-safes-first + stack-stack commutation + the R1/R2 discharge,
   written tight — still not confluence, but it covers every *known*
   collision shape.

## Two things not to mistake for rigor

- **The empirical floor.** Zero disagreements across the cross-checked
  corpora bounds only the *observed* rate: by the rule of three on the
  ~2M-game cross-version check, ≲1.5×10⁻⁶ per game at 95%. A hole that
  fires once in 10⁸ games coexists happily with that.
- **The falsifiers** (P1–P3, the relocation-depth counter) are a plan for
  knowing, not a state of knowing.

## The finish line (informal rigor, pre-Lean)

1. The four Lean obligations of no_pile_to_pile.md §9 written out as prose
   proofs — machine-checking is not required for rigor, only that each
   step be checkable.
2. **R1/R2 discharged or witnessed.** Note that a witness is not only a
   Lean target: a live R1/R2 hit on a winnable game is a pruner bug to
   fix — the rule's kept set or its rescue must be widened.
3. Real writeups for the least-stack cascade (5.6) and the `is_pure` deck
   dominance (5.3 at draw ≥ 2) — writing problems, not discovery
   problems.
4. The closure property proper stays on the Lean track (lean-verify/) —
   the one item hand-proof will not close.

Overall read: **referee-legible, not referee-proof.** As an informal
appendix to the numbers, the expected referee response is "the structure
is right; discharge the reshape lemma and the R1/R2 residues, then we'll
talk."
