# Temp/BlockHousing — report

**File:** `B:\code\lonelybot\lean-model\Temp\BlockHousing.lean`
**Status:** compiles, `lake env lean Temp\BlockHousing.lean` exits 0.
**House rules:** no `sorry`, no `Classical`, no `noncomputable`, no `native_decide`,
no new `Prop` predicate/`def`; only `theorem`s in `namespace OneColourClosure`.

## Prerequisites built first

Compiled (with `.olean` written to `.lake/build/lib/lean/Temp/`) before the new file:

| module | result |
|---|---|
| `Temp.PullRaiseId` | OK, axioms `[propext, Quot.sound]` |
| `Temp.RungMono` | OK, axioms `[propext, Quot.sound]` |
| `Temp.RaisesOrFork` | OK, axioms `[propext]` / `[propext, Quot.sound]` |

(The task's `lake build Temp.X` is not a valid target — `Temp` is not a
`lean_lib` in `lakefile.toml` — so the oleans were produced with
`lake env lean -o .lake/build/lib/lean/Temp/<M>.olean Temp/<M>.lean`.)

## Exact statements

Conventions: `RaiseSSeqLicensed` words are **reverse chronological**, and
`playWord P = P.reverse` is the word for the chronological play `P`
(`Orig2/Fork/Class/ForkRaiseReorderProof.lean`).  All names are in
`namespace OneColourClosure`.

### 1. Half 1 — suffix transport (word form, as requested)

```lean
theorem suffix_transport {u z : State} {c : Card} {high : List Card}
    (hu : u.WF)
    (hplay : RaiseSSeqLicensed u high z)
    (hc : CanRaiseS u c)
    (hr : ∀ d ∈ high, c.rank.toIdx < d.rank.toIdx) :
    ∃ z', RaiseSSeqLicensed u (c :: high) z'
```

Literal form asked for.  Proof: R1 (`RaiseSSeqLicensed.canRaiseS_persist_of_rank_ne`)
keeps `c` licensed through the word, then `exists_append_raise`
(`Temp/RaisesOrFork.lean`) appends the single raise.

### 2. Half 2 — chronological suffix insertion

```lean
theorem suffix_insert {u z : State} {c : Card} {H : List Card}
    (hu : u.WF)
    (hH : H.Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx))
    (hplay : RaiseSSeqLicensed u (playWord H) z)
    (hc : CanRaiseS u c)
    (hr : ∀ d ∈ H, c.rank.toIdx < d.rank.toIdx) :
    ∃ z', RaiseSSeqLicensed u (playWord (c :: H)) z'
```

Route (no state transport needed):

1. persist `c`'s licence to the endpoint of `H` (R1);
2. append `c` at the end (`exists_append_raise`), giving a play of
   `playWord (H ++ [c])`;
3. `sortable` re-sorts that play ascending;
4. because `c` is strictly below every letter of `H` and `H` is ascending,
   `c :: H` is an ascending list with the same multiset as
   `sortByRank (H ++ [c])`, so `tieFree` moves to `playWord (c :: H)`.

`raiseS_rankfront_L` was **not** needed for this; `sortable` + `tieFree` is the
same "hoist to the front" content at the word level.

### 3. Main theorem — split form (the form to consume)

```lean
theorem insert_at_block_end_split {s u z : State} {c : Card} {low high : List Card}
    (hs : s.WF)
    (hlowPlay : RaiseSSeqLicensed s (playWord low) u)
    (hplay : RaiseSSeqLicensed u (playWord high) z)
    (hlow : ∀ d ∈ low, d.rank.toIdx ≤ c.rank.toIdx)
    (hhigh : ∀ d ∈ high, c.rank.toIdx < d.rank.toIdx)
    (hhighAsc : high.Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx))
    (hc : CanRaiseS u c) :
    ∃ z', RaiseSSeqLicensed s (playWord (low ++ [c] ++ high)) z'
```

`u` is the caller's boundary state; `hlowPlay`, `hplay` are the two halves
obtained from `RaiseSSeqLicensed.split_chron` if the caller has the whole play.
`hlow` is part of the statement for fidelity but is not used by the proof.

### 4. Main theorem — from the whole play alone

```lean
theorem insert_at_block_end {s z : State} {c : Card} {low high : List Card}
    (hs : s.WF)
    (hplay : RaiseSSeqLicensed s (playWord (low ++ high)) z)
    (hlow : ∀ d ∈ low, d.rank.toIdx ≤ c.rank.toIdx)
    (hhigh : ∀ d ∈ high, c.rank.toIdx < d.rank.toIdx)
    (hhighAsc : high.Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx))
    (hc : ∀ u, RaiseSSeqLicensed s (playWord low) u →
      RaiseSSeqLicensed u (playWord high) z → CanRaiseS u c) :
    ∃ z', RaiseSSeqLicensed s (playWord (low ++ [c] ++ high)) z'
```

The boundary state is recovered with `split_chron`; `hc` is demanded at the
genuine boundary (endpoint of `low` **and** start of `high`).

### 5. Same, taking the brief's full rank-sortedness

```lean
theorem insert_at_block_end_sorted {s z : State} {c : Card} {low high : List Card}
    (hs : s.WF)
    (hplay : RaiseSSeqLicensed s (playWord (low ++ high)) z)
    (hlow : ∀ d ∈ low, d.rank.toIdx ≤ c.rank.toIdx)
    (hhigh : ∀ d ∈ high, c.rank.toIdx < d.rank.toIdx)
    (hsorted : (low ++ high).Pairwise
      (fun a b => a.rank.toIdx ≤ b.rank.toIdx))
    (hc : ∀ u, RaiseSSeqLicensed s (playWord low) u →
      RaiseSSeqLicensed u (playWord high) z → CanRaiseS u c) :
    ∃ z', RaiseSSeqLicensed s (playWord (low ++ [c] ++ high)) z'
```

with the helper

```lean
theorem pairwise_append_right {l m : List Card}
    (h : (l ++ m).Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx)) :
    m.Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx)
```

which extracts `hhighAsc` from `hsorted`.

### 6. Composition lemma — the tail after `raise c` starts at `s`

```lean
theorem cancel_prefix_is_play_from_source {s u : State} {c : Card} {b : Base}
    {ws : List Card} {v : State} (hs : s.WF)
    (hpull : State.step s (Move.foundToTab c b) = some u)
    (hcan : CanRaise u c)
    (hplay : RaiseSSeqLicensed u (playWord (c :: ws)) v) :
    ∃ v', RaiseSSeqLicensed s (playWord ws) v'
```

Note the orientation: under the library convention the usable hypothesis is
`playWord (c :: ws)` (chronology `raise c`, then `ws`), not the literal
`c :: ws` (which would mean "play `ws`, then raise `c`").  This is the
composition the main proof consumes.

Proof: `split_chron` at `[c]` gives the tail from the (existential) landing
`s'`.  The first letter's cargo path is non-canonical, so `s'` need not be `s`
syntactically.  We build the *canonical* one-letter play from `u` to `s`
(empty `CargoPath`, `step_tabToFound_of_foundToTab`), and transport the tail
from `s'` to `s` with `RaiseSSeqLicensed.tail_transport` (both one-letter words
are `playWord [c]`, so the permutation is `List.Perm.refl`).
**This lemma needed no new transport residual — it is fully proved.**

## Axiom lines (verbatim output)

```
'OneColourClosure.suffix_transport' depends on axioms: [propext, Quot.sound]
'OneColourClosure.suffix_insert' depends on axioms: [propext, Quot.sound]
'OneColourClosure.insert_at_block_end_split' depends on axioms: [propext, Quot.sound]
'OneColourClosure.insert_at_block_end' depends on axioms: [propext, Quot.sound]
'OneColourClosure.pairwise_append_right' does not depend on any axioms
'OneColourClosure.insert_at_block_end_sorted' depends on axioms: [propext, Quot.sound]
'OneColourClosure.cancel_prefix_is_play_from_source' depends on axioms: [propext, Quot.sound]
```

No `sorryAx`, no `Classical.choice`, no `Classical.em`.

## Deviation from the literal target, and the one residual

The literal target in the brief has no order hypothesis on `high`; it carries
only `hlow` and `hhigh`.  The prose, however, says "whose word is
**rank-sorted**", and the delivered theorems need exactly that order
information:

* `insert_at_block_end_sorted` takes the whole word `low ++ high` rank-ascending
  (matching the brief's prose);
* `insert_at_block_end` / `insert_at_block_end_split` take the equivalent tail
  hypothesis `hhighAsc : high.Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx)`.

Sortedness cannot simply be dropped: a permutation of a licensed play is not in
general licensed (e.g. two same-suit cards can be raised ascending but not
descending), and the sort/`tieFree` step genuinely produces the ascending order.

**Residual (only if the caller needs an unsorted `high`):** the following is
not proved here and is *not* implied by the delivered results:

```lean
/-- RESIDUAL — unsorted chronological suffix insertion. -/
theorem suffix_insert_unsorted {u z : State} {c : Card} {H : List Card}
    (hu : u.WF)
    (hplay : RaiseSSeqLicensed u (playWord H) z)
    (hc : CanRaiseS u c)
    (hr : ∀ d ∈ H, c.rank.toIdx < d.rank.toIdx) :
    ∃ z', RaiseSSeqLicensed u (playWord (c :: H)) z'
```

Name it `suffix_insert_unsorted` if it is ever needed; it requires a transport
that replays the *same* tail order from the post-`raise c` state (the obstacle
is that `RaiseSSeqLicensed`'s step hides its `CargoPath`, so the landing states
of `c ; d` and `d ; c` are not syntactically canonical).  Under the brief's
rank-sorted hypothesis this residual is unnecessary.

## Files touched

* **new** `Temp/BlockHousing.lean`
* **new** `Temp/BlockHousing_Report.md` (this file)

Nothing under `Orig2/` was modified; no existing `Temp/*.lean` was modified.
A temporary probe file `Temp/BH_probe.lean` was created for `#check`s and then
deleted.
