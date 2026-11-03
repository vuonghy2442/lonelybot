# RankFront_close — report

File: `Temp/RankFront_close.lean` (compiles clean with `lake env lean`; no
`sorry`, no `Classical`, no `noncomputable`, no `native_decide`).
Report: this file.

Build (prerequisite olean already needed because `Temp.RankFront_licensed` had
none in `.lake`):

```
cd lean-model
lake env lean -o .lake/build/lib/lean/Temp/RankFront_licensed.olean Temp/RankFront_licensed.lean
lake env lean Temp/RankFront_close.lean
```

## Headline

**`(S)` is TRUE and is now PROVED** — kernel-checked, axiom-clean:

```lean
theorem canRaiseS_of_raise_perm {s u v : State} {P Q : List Card} {d : Card}
    (hs : s.WF) (hP : RaiseSSeqL s P u) (hQ : RaiseSSeqL s Q v) (hperm : P.Perm Q) :
    CanRaiseS u d ↔ CanRaiseS v d
```

Two licensed plays from the same state that raise the same multiset of cards do
end in states with the same licences.

Two more results land with it: the **sorted play exists whenever a licensed play
does** (`sortable` — the `sorted` census row as a theorem), and the parent's
`SortedPrefixLicence` is **refuted** as stated.

However, two things the parent's plan assumed are **not** true as stated:

1. `SortedPrefixLicence` (`Temp/RankFront_licensed.lean:790`) is **FALSE** —
   kernel refutation `sortedPrefixLicence_false` below. It is missing the
   hypothesis `x ∉ R`; with it added the repaired statement survives 2836
   probe instances (§5).
2. `(S)` does **not** by itself carry the end-to-end induction. The residual is
   a *different* statement — `TailExists` (§6) — and its hard part is the
   front/tie passage, for which the state-level tie step the plan leans on
   (`twin_raise_square`) is insufficient in general (§7).

So: the lane is **not** closed; it is reduced to one kernel-checked `Prop`
(`TailExists`), and the previously-named bridge `(S)` is discharged.

## Axiom profile

Every declaration in `Temp/RankFront_close.lean` is `[propext]` or
`[propext, Quot.sound]`:

```
'OneColourClosure.canRaise_tabToFoundR'              [propext]
'OneColourClosure.canRaise_reversibleAtW'            [propext, Quot.sound]
'OneColourClosure.cargoLeg_rungAt'                   [propext, Quot.sound]
'OneColourClosure.cargoPath_rungAt'                  [propext, Quot.sound]
'OneColourClosure.RaiseSSeqL.rungAt_eq'              [propext, Quot.sound]
'OneColourClosure.rungAt_eq_of_perm'                 [propext, Quot.sound]
'OneColourClosure.RaiseSSeqL.revEqW'                 [propext, Quot.sound]
'OneColourClosure.revEqW_of_raise_plays'             [propext, Quot.sound]
'OneColourClosure.canRaiseS_of_raise_perm'           [propext, Quot.sound]
'OneColourClosure.canRaiseS_of_raise_perm''          [propext, Quot.sound]
'OneColourClosure.RaiseSSeqL.split_head'             [propext]
'OneColourClosure.RaiseSSeqL.tail_transport'         [propext, Quot.sound]
'OneColourClosure.perm_two_reverse_aux'              [propext]
'OneColourClosure.perm_reverse'                      [propext]
'OneColourClosure.RaiseSSeqL.split_chron'            [propext]
'OneColourClosure.swap_inversion'                    [propext, Quot.sound]
'OneColourClosure.t6a_not_canRaiseS_KD'              [propext, Quot.sound]
'OneColourClosure.sortedPrefixLicence_false'         [propext, Quot.sound]
'OneColourClosure.insRank_push'                      [propext, Quot.sound]
'OneColourClosure.sortable'                          [propext, Quot.sound]
'OneColourClosure.raiseS_sorted_of_licensed'         [propext, Quot.sound]
'OneColourClosure.raiseS_rankfront_L_of_tail'        [propext]
```

No `sorryAx`, no `Classical.choice`.

## `(S)` — the proof, and why the cargo-class route was the wrong one

`Temp/RankFront_licensed.lean` had analysed `(S)` as a *cargo/slide
identification*: `freeCardS` reads only `d`'s pile, that pile's `hidden`, and
`pileOfTop d.twin`, so it looked as if one had to show that same-multiset plays
end in the same **cargo class**. That is the wrong quotient. A raise is not a
cargo move, and two licensed plays of the same word can genuinely end in
different cargo classes.

The right quotient is the **orbit** (`RevEqW` / `sameOrbitSetoid`), and the
route is three lines of existing machinery once one notices the licence is
exactly undoability:

1. `CanRaise z c` is literally `tabToFoundR z c = true` (both are
   `nextUp ∧ pileOfTop = some a ∧ (chop faceUp ≠ [] ∨ (hidden = [] ∧ king))`):
   `canRaise_tabToFoundR`.
2. Hence, at `WF`, a licensed raise is a reversible move:
   `canRaise_reversibleAtW` from `tabToFoundR_iff_reversibleAtW`. A cargo leg is
   reversible by definition, so **every** licensed play is a witness shuffle
   (`cargoPath_shuffle` + `Walk.cons`), therefore
   `RaiseSSeqL.revEqW : RaiseSSeqL s ws z → s.WF → RevEqW s z`.
   `RevEqW` is an equivalence, so *any* two licensed endpoints from the same
   start are orbit-mates — whatever their words:
   `revEqW_of_raise_plays`.
3. Rungs: a raise of `c` moves exactly the rung of `c`'s suit by one
   (`rungAt_tabToFound`), a cargo leg moves none (`cargoPath_rungAt`), so the
   rung ledger of a word is its multiset (`RaiseSSeqL.rungAt_eq`,
   `rungAt_eq_of_perm`).
4. At equal rungs the S-licence is an orbit invariant — the existing
   `canRaiseS_orbit_rung` (`Orig2/Fiber/FreeOrbit.lean:1431`,
   `[propext, Quot.sound]`).

That is the whole proof. The load-bearing ingredient is the **licence itself**:
with the weak `RaiseSSeq` step the raise need not be reversible (`t4a_fires` +
`t4a_not_canRaise`), the endpoints are not orbit-mates, and this route dies —
consistent with the earlier finding that `(P)` is false for weak steps. `(S)` is
a theorem about the *licensed* grade, exactly as the parent suspected.

Supporting toolkit also proved here (all reusable):

| theorem | what it gives |
|---|---|
| `RaiseSSeqL.split_head` | split a word `ws ++ [c]` at its first chronological raise |
| `RaiseSSeqL.split_chron` | split a play at an arbitrary chronological prefix |
| `RaiseSSeqL.tail_transport` | replay a tail from the endpoint of **any** play of the same multiset prefix (this is how `(S)` is consumed) |
| `swap_inversion` | swap an adjacent inversion `x, y` (`y.rank < x.rank`) anywhere in a play |
| `perm_reverse` | `List.Perm.reverse` (absent from this core) |
| `insRank_push` | push a card rightward into ascending place (`insRank`) |
| **`sortable`** | **the sorted play exists whenever a licensed play exists** |
| **`raiseS_sorted_of_licensed`** | word form: a realisable word's rank-sorted word is realisable |

`swap_inversion` is the bubble-sort primitive: `y`'s licence at the prefix
endpoint is recovered from its post-`x` licence by `canRaiseS_unraise_word`
(inertness), then the tail is replayed by `tail_transport`. It is the concrete
sense in which `(S)` makes the sorted replay work.

`sortable` is the **`sorted` census row (91/91) as a theorem**, and it is *tie-free*:
the induction splits off the first card `a`, sorts the tail by IH, and then pushes
`a` rightward with `insRank_push`; `insRank` decides between "already in place"
(`a.rank ≤ b.rank`, no move) and "swap past `b`" (`b.rank < a.rank`, a strict
inversion, so `swap_inversion` applies). No equal-rank swap is ever needed.
This is the piece of the end-to-end induction that *does* follow from `(S)`.

## §5. The parent's `SortedPrefixLicence` is FALSE

```lean
def SortedPrefixLicence : Prop :=        -- Temp/RankFront_licensed.lean:790
  ∀ {s z u : State} {R P : List Card} {x : Card},
    s.WF →
    R.Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx) →
    (∀ r ∈ R, r ∈ P) →
    (∀ p ∈ P, p.rank.toIdx < x.rank.toIdx → p ∈ R) →
    RaiseSSeqL s R.reverse u →
    RaiseSSeqL s P.reverse z →
    x ∈ P →
    CanRaiseS u x
```

There is no `x ∉ R`. If `x ∈ R` then the sorted prefix has *already raised* `x`;
at its endpoint the suit's rung is past `x.rank`, so `nextUp x` is false and
`CanRaiseS u x` cannot hold.

Kernel refutation `sortedPrefixLicence_false` at `t6` (three bare kings,
`Temp/RankFront_census.lean`), `R = P = [K♦]`, `x = K♦`:

* `t6_canRaise_KD : CanRaise t6 K♦` (next-up, bare-king seat) — `by decide`;
* `t6_raiseSSeqL_KD : RaiseSSeqL t6 [K♦] t6a` (`t6_step_KD`);
* `t6a_not_nextUp_KD : t6a.nextUp K♦ = false` — `by decide`;
* `t6a_not_canRaiseS_KD : ¬ CanRaiseS t6a K♦`.

All the other hypotheses hold (`R` is ascending, `R ⊆ P`, the "lower cards"
condition is vacuous, `x ∈ P`), so `¬ SortedPrefixLicence`.

Repair, stated in the file as `SortedPrefixLicenceFixed`: add `x ∉ R`. That is
the honest form of the sorted-prefix bridge.

**Census of the repaired statement** (`Temp/RankFront_close_probe11.py`,
`SPL'` = SPL with `x ∉ R`, all plays of length ≤ 3):

| probe | `(P,R,x,endpoint)` instances checked | violations |
|---|---|---|
| T1 | 641 | 0 |
| T2 | 10 | 0 |
| T3 | 1 | 0 |
| T4 | 1 | 0 |
| T5 | 8 | 0 |
| T6 | 2175 | 0 |
| **total** | **2836** | **0** |

So the repaired residual is non-vacuous and not refuted.

## §6. The exact residual: `TailExists`

`(S)` transfers a licence between endpoints of plays of the *same* multiset.
The end-to-end induction needs something else: after raising the front card `c`,
the **rest of the multiset must still be playable** at all. `(S)` does not say
that (it compares endpoints of equal-multiset plays, not the endpoint of `[c]`
with the interior state of a longer play). That is the residual, and it is
stated in the file as

```lean
def TailExists : Prop :=
  ∀ {s z : State} {ws : List Card} {c : Card},
    s.WF → CanRaiseS s c → RaiseSSeqL s ws z → c ∈ ws →
      ∃ s₁, RaiseSSeqL s [c] s₁ ∧
        ∃ z', RaiseSSeqL s₁ (playWord (sortRank (ws.erase c))) z'
```

and it is *exactly* the target: `raiseS_rankfront_L_of_tail` proves

```lean
theorem raiseS_rankfront_L_of_tail (H : TailExists) :
    ∀ {s z : State} {c : Card} {ws : List Card},
      s.WF → CanRaiseS s c → RaiseSSeqL s ws z → c ∈ ws →
        ∃ z', RaiseSSeqL s (rankFront c ws) z'
```

(one `RaiseSSeqL.append`). So the lane is now: **`(S)` closed, the whole
rank-front theorem reduced to the single `Prop` `TailExists`.**

The `RaiseSSeq` corollary (*every step licensed* → `RaiseSSeq`) is `toSeq`
(`Temp/RankFront_licensed.lean` §1); it is unaffected by this work.

## §7. What is genuinely left in `TailExists`, and why it is not `(S)`

Two sub-obligations, the first of which is now **proved** in this file.

1. **Ascending sort — DONE.** `sortable` proves that from *any* licensed play of
   a multiset the ascending play exists (and `raiseS_sorted_of_licensed` is the
   word form). It is tie-free: split off the head `a`, sort the tail by IH, push
   `a` rightward with `insRank_push`, and every swap is a *strict* inversion
   (`swap_inversion`).

2. **The front/tie passage — the real obstruction, and the one the parent's plan
   underestimates.** To obtain `c :: ascending (ws \ {c})` from the ascending
   play, `c` must move to the front across the cards of rank `< c.rank`,
   across the cards of rank `> c.rank` (both fine — `swap_inversion` handles
   the higher ones, and across strictly lower ones an "anti-inversion" swap is
   available because `c` is licensed at `s` and R1 keeps it licensed through
   lower-rank raises) and, crucially, across the cards of rank **equal** to
   `c.rank`. Equal-rank adjacent transpositions are **not** inversion swaps, and
   the state-level tie step

   > if `d.rank = e.rank` and both are `CanRaiseS` at `u`, then either order of
   > `(d, e)` is playable

   is **FALSE**. Probe witness `RankFront_close_probe10.py`:
   `p0 = [7♣, 6♦]`, `p1 = [7♠, 6♥, 5♠]`, rungs `♠ = 3, ♥ = 5, ♦ = 5, ♣ = 0`.
   Then `live = {6♦, 6♥}` (equal rank), both licensed, and **neither** order is
   realisable; after `6♦` alone the live set is empty. So `twin_raise_square`
   covers only the sub-case where both same-rank cards are *simultaneously
   vanilla-raisable*; the general tie move needs the extra hypothesis that the
   pair is playable inside the full play (which is what `TailExists` supplies
   circularly).

   This is the honest reason `(S)` cannot be the last step: the missing
   information is not a licence at a comparable state, it is the *existence of
   a continuation*. In the sorted replay the ties are rescued by the intervening
   lower-rank raises (in T1, `K♦` first destroys `K♥`'s twin-seat, but the sorted
   order inserts `Q♠` between them, and raising `Q♠` exposes `K♥`). Reproducing
   that needs the full-play induction of `TailExists`, not a state-level lemma.

Consequently the honest residual is `TailExists` as a whole (with its tie
sub-case), not a licence-equality statement. `(S)` is strictly weaker than
`TailExists` and is now available for free in whatever proof of `TailExists`
comes next.

## §8. Code census of `(S)`

`Temp/RankFront_close_probe.py` (T1–T6, all licensed plays of length ≤ 3): for
every pair of plays with the same multiset, every pair of endpoints was compared
pointwise — **0 violations** for all six probes; the weaker `CargoPath` form
(Q2) also showed 0. `Temp/RankFront_close_probe3.py`: 1600 random states, all
1- and 2-card plays, endpoints of same-multiset plays compared for cargo
relatedness — 0 class splits. (The stronger cargo-class statement is not needed
now that `(S)` is proved via the orbit.)

## Bottom line (blunt)

* `(S)`: **proved**, axiom-clean. This was the parent's named "whole remaining
  gap" and it is now closed — but the parent's claim that it closes the
  induction is **wrong**: the front/tie passage is not a licence-equality
  statement.
* The **sorted play** (`sorted` census row) is now a **theorem** (`sortable`),
  tie-free, from `(S)`.
* The parent's `SortedPrefixLicence`: **FALSE** as stated (kernel refutation);
  the repair is `x ∉ R` and the repaired form survives 2836 probe instances.
* The general rank-front theorem is **NOT proved, NOT refuted**; it is now
  reduced to one kernel-checked statement, `TailExists`
  (`raiseS_rankfront_L_of_tail`), whose only hard sub-case is moving the front
  card across same-rank cards, and the state-level tie step is false (probe
  witness), so the next round must exploit the *existence of the full play*, not
  a state-level tie lemma.
