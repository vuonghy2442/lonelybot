# The twin-exchange evidence probes

The #eval-validated miniatures cited by the route notes in
`Klondike/TwinQuotient.lean`, `Klondike/TwinBridge.lean`, and
`Klondike/TwinReplay.lean`.  Each is a standalone script over the model:
run with `lake env lean probes/<file>.lean` from `lean-model/`.  They are
evidence, not theorems — nothing here is imported by the library.

| file | what it establishes |
|---|---|
| `w15merge.lean` | The original merge witness: a licensed, non-WF state where the 3-move win goes through the merge while the exchanged state is frozen — refutes the premiseless exchange theorem (the `+hwf` repair's justification). |
| `w15wfmerge.lean` | The WF-candidate gate probe (fired empty: the w15merge blockade family is structurally dead at WF — `founds_gone` forces live blockers) and the crafted 3-cycle showing WF does NOT exclude board cycles. |
| `rhoreplay.lean` | The growing-ρ replay validation: the source play with a twin-suit stacking INSIDE the mid (non-ortho) vs the flip-translated mirror play from the twin-swapped state — both win, the catch-up rung-sorted. |
| `rhoreplay2.lean` | The growth / mid-episode worry-back / two-overlapping-growths / deckStack validation probes (the crossed-pair exhibition). |
| `fithole.lean` | The fit hole is LIVE at WF: a licensed WF state whose deep merge is on the winning line with a deal-adjacent non-fitting first rider; both 2b ply moves dead in the exchanged state; the rider-detour repair validated (winning plays for source-original, source-reordered, and the exchanged mirror). |
| `fithole2.lean` | The fitting-rider control: with `canSitOn r₁ z = true` the two-ply lands at exactly the 2a ply's conclusion. |
| `detour.lean` | The non-king detach-blockade witness: r₁'s both candidate tops occupied by live riders, the free anchor king-locked — no detach base exists (`ExchangeDeepNorm`'s plain form is FALSE at WF); the iterated-detach repair wins both sides. |
| `detour2.lean` | The king detach-blockade witness: all seven anchors legally occupied — no detach exists; the iterated repair wins both sides. |
| `detour3.lean` | The detour's structural harmlessness: it cannot land inside c's run (the run's only bare card is z, excluded by the hole hypothesis), empties z′'s stack, preserves the self-landing guard; the license/merge-premise survival checks. |
| `dblclear.lean` | The double-clear probe: the both-bare regime's trivial discharge, the verbatim-replay check field-by-field, the failure-mode search (the circular construction dissolves at the solvability hypothesis). |
| `dblclear2.lean` | The constructive schedule probe: the raiser (`deckStack ♥9`) + blocker stack + detour + merge + climbs wins on both sides; the mixed-prefix replay holds board-per-seat. |
| `rootedprobe2.lean` | The `CleanAt` clearing-prefix validation (the witnesses' `pileStack ♥10` is off both protected zones). |
| `rootedprobe3.lean` | The twin-pair correspondence REFUTATION: the exchange swaps seat contents without relabeling card identities (`TwinCorr (swapTwin t) t.suit st (st.exchangeTwinCargo t)` fails at licensed states) — the corrected correspondence is at the cargo pair, both cargo seats bare. |
| `eqheights.lean` | The sufficiency probe: at the both-bare witness's equalized regime the adjacent-head play wins and its `playWindow'` value is TRUE. |
