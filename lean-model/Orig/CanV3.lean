import Orig.Canonical
import Orig.FoundKit

/-!
# Orig.CanV3 — the class-anchored canonical representative (landing 4)

The REDEFINED canonV3 (the coordinator's landing-4 call and its
upgrades): not a new run machine — the landing-1 verdict stands
(`TwinContended` is EMPTY at WF; the retired scaffold stays
retired) — but a MEMBER SELECTOR over the class: `canonV3` names
the canonIdx-maximal member of the class's SATURATED member set
(the saturated faces of the class), so a class gets ONE literal
representative.

## The composite index (height-first, per the user's proposal)

`canonIdx w` = lex (htup w, positionKey w, formalKey w):

* `canonHtup` — the foundation-height tuple in the FIXED suit
  order (spade, heart, diamond, club — the house decSt order):
  the FOUNDED CONTENT leads, and the fixed-order lex IS the arm
  choice — the fork wings are INCOMPARABLE componentwise
  (13/12 vs 12/13), so the conjugate-arm price, already accepted
  at the section level, is paid here on a meaningful quantity;
* `canonPosKey` — per-anchor position quantities (face-up run
  lengths, hidden depths, anchor order), the CONJUGATION-INVARIANT
  reader that breaks the WIGGLE ties: the residue-exhibit pair
  shares its height tuple — heights UNDER-determine the class
  (positions are not height data);
* `canonFormalKey` — the house decSt 14-field lexicographic read,
  card-index-encoded: the LAST FORMALITY — with the 2026-10-10
  SETOID FLIP (sameOrbitSetoid is the RevEqW closure; conjugate
  mates live in DISTINCT classes) the formal level never hides a
  symmetry violation; equal formal keys imply equal states.

The selector `canonV3Arg` is a fold over a bounded member LIST —
canonV3 is COMPUTABLE BY CONSTRUCTION.  The machine face of the
member set (the FINAL members of the orbit through the
decompression card's cone rows — `mem_macro_iff`, pulls + slides +
draws) is NOT importable at this base (branch
`orig-canon-decompress`, commit `8a0e121`, unmerged): until the
merge the selector consumes an explicit member list, the probe
battery (probes/CanonV3Probe.lean, landing 4) decides the evidence
at every census family and both wings of every fork instance, and
the post-merge targets are the named residues ledgered in
FUTURES-ORIG.md §11-L4 (the canus bridge `canus_class_inv` paid by
`mem_macro_iff`; the full literal section iff through the
exhausted member set; the canus conj-closure; the selector's
canonIdx-maximality through the transitivity packet).

## The Q-CARGO LAW and FORK EXCLUSIVITY (the user's theorem)

A standing fork's cover must be a QUEEN of the opposite color
(only queens sit on kings, `v3CoverIsQueen`), and a PILED queen is
unfounded (conservation), pinning its suit's foundation weakly
below the queen rung — with strictness exactly when the fork
STANDS: a rung-ready queen (the equality case) raises away and the
cascade MERGES the fork (the landing-3 row, decided at
probes/CanonV3Probe.lean's merge cell).  The twin kings'
stackability requires their suits at the king rung.  So a fork
forces exactly ONE opposite-color suit below the queen rung,
unfounding the very card the other pair's fork would need —
AT MOST ONE COLOR PAIR CAN FORK PER CLASS.  Consequences: the arm
space is ≤ 2 per class; the saturated-tuple orbit is the
SINGLE-PAIR flip of whichever pair forks (pair-dependent Z/2,
trivial for benign classes; the (Z/2)² product reading was
REFUTED by this law); one neck, one bottleneck, one unionability
obstruction per class.  The rank arithmetic is decided at the
battery's refutation-witness cells.
-/

/-! ## The composite index -/


/-- The foundation-height tuple, fixed suit order (spade, heart,
diamond, club — the decSt field order). -/
def canonHtup (st : State) : List Nat :=
  [(st.found .spade).length, (st.found .heart).length,
    (st.found .diamond).length, (st.found .club).length]

/-- The per-anchor position key: face-up run lengths then hidden
depths, anchor order — conjugation-invariant (twinMap relabels
piles in place, never moves anchors). -/
def canonPosKey (st : State) : List Nat :=
  Anchor.all.map (fun a => (st.piles a).faceUp.length) ++
  Anchor.all.map (fun a => (st.piles a).hidden.length)

/-- The suit ordinal: the decSt field order. -/
private def v3SuitOrd (s : Suit) : Nat :=
  match s with
  | .spade => 0
  | .heart => 1
  | .diamond => 2
  | .club => 3

/-- The card's position in the decSt card order. -/
def canonCardIdx (c : Card) : Nat :=
  v3SuitOrd c.suit * 13 + c.rank.toIdx

/-- The formal (decSt-shaped) key: the fourteen fields,
card-index-encoded, drawStep last. -/
def canonFormalKey (st : State) : List Nat :=
  Suit.all.flatMap fun s => (st.found s).map canonCardIdx
  ++ Anchor.all.flatMap fun a =>
      ((st.piles a).hidden ++ (st.piles a).faceUp).map canonCardIdx
  ++ st.stock.map canonCardIdx ++ st.waste.map canonCardIdx ++ [st.drawStep]

/-- Strict lexicographic order on Nat lists (the prefix loses). -/
def v3NatListLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys =>
      if x < y then true else if y < x then false else v3NatListLt xs ys

/-- Self-contained Bool equality on Nat lists (decides the
composite's equality guards without BEq-instance surface). -/
def v3NatListEq : List Nat → List Nat → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | x :: xs, y :: ys => if x = y then v3NatListEq xs ys else false

theorem v3NatListEq_self : ∀ l : List Nat, v3NatListEq l l = true
  | [] => rfl
  | x :: t => by
      show (if x = x then v3NatListEq t t else false) = true
      rw [if_pos rfl, v3NatListEq_self t]

/-- THE COMPOSITE: canonIdx-strict-less — heights lead; positions
break the wiggle ties; the formal key is the last formality. -/
def canonIdxLt (a b : State) : Bool :=
  v3NatListLt (canonHtup a) (canonHtup b) ||
  (v3NatListEq (canonHtup a) (canonHtup b) &&
    (v3NatListLt (canonPosKey a) (canonPosKey b) ||
      (v3NatListEq (canonPosKey a) (canonPosKey b) &&
        v3NatListLt (canonFormalKey a) (canonFormalKey b))))

/-! ## The organizing vocabulary (the final grades; computation-side engines riding the banked `canon`)

The CLASS grades live at the ∃-spec level (MacroInternal's
`atRungInClass` / `satStackable` / `strandedInClass` /
`pendingForever` / `surelyStackable` — one existential over
classOf, no carrier, trivially class-invariant).  THIS chapter
carries the STATE-LEVEL ENGINES those grades compute through,
with the final vocabulary — note the DISAMBIGUATION the
finalization enforces: the fork CARGO is STRANDED (below every
ceiling the class reaches — pinned by RANK, the pin row
`v3RungAt st d.suit < d.rank.toIdx` is its state-level witness
reading); the covered Final TWIN and the buried stranded kings
are PENDING-FOREVER (at-rung but never founded — blocked by
POSITION, not by rank).  The old one-word "parked" merged the
two; the engines below name their grade explicitly.  -/


/-- The saturation ceiling of `s` from `st` — the maximal stackable
rank from `st`: canon's founded content, read as a height.  RIDES
the banked V2 canon (computable, zero new machinery).  The
computation-side engine of the class ceiling `classRung`. -/
def satRung (st : State) (s : Suit) : Nat :=
  ((canon st).found s).length

/-- The at-or-above-ceiling population (internal engine name —
not a class grade): cards whose rank sits weakly at or above
the state's canonical ceiling.  The final skeleton vocabulary
keeps ONLY the three existential class grades (satStackable /
atRungInClass / strandedInClass / pendingForever — grade_partition
PROVED there, founded_implies_atRung the remaining stub); the
ceiling arithmetic below is this chapter's computation-side
engine, never a spec-side definition. -/
def aboveCeiling (st : State) (c : Card) : Bool :=
  decide (c.rank.toIdx ≥ satRung st c.suit)

/-- The stranded-at-state read: the card sits strictly above the
state's own canonical ceiling — the RANK-pinned grade (the fork
cargo's obstruction; the pin row's computation-side witness
shape). -/
def strandedAt (st : State) (c : Card) : Bool :=
  decide (satRung st c.suit < c.rank.toIdx)

/-- The pending-forever-at-state read: the card is AT ITS OWN
rung at the state's CANONICAL CEILING yet was not founded by the
saturation — the POSITION-blocked grade (the covered Final twin;
the buried stranded kings' obverse: at-rung, blocked by cargo
above). -/
def pendingForeverAt (st : State) (c : Card) : Bool :=
  decide (satRung st c.suit = c.rank.toIdx ∧
    ¬ (c ∈ (canon st).found c.suit))

/-- The parking map: the seated never-founded population with
their anchors (the residue profile's seating read — the stranded
and the pending-forever are two seatings of one never-founded
population; the class-level profile derives as the grades at
canonV3 after arm selection). -/
def parkingMap (st : State) : List (Card × Anchor) :=
  Card.universe.filter (aboveCeiling st) |>.filterMap
    (fun c => match st.pileHolding c with
      | some a => some (c, a)
      | none => none)

/-! ## The selector -/


/-- THE SELECTOR: the canonIdx-maximal member of the class's
saturated member list (deterministic fold; bounded input; there
are no ties beyond canonIdx — the formal key separates states). -/
def canonV3Arg : List State → Option State
  | [] => none
  | s :: rest =>
      match canonV3Arg rest with
      | none => some s
      | some b => if canonIdxLt b s then some s else some b

/-! ## The argmax rows -/

/-- A map congruence (core-only). -/
private theorem v3MapCong {α β : Type} {f g : α → β} : ∀ (l : List α),
    (∀ x, f x = g x) → l.map f = l.map g
  | [], _ => rfl
  | a :: t, h => by
      rw [List.map_cons, List.map_cons, h a, v3MapCong t h]

/-- The lex order is irreflexive. -/
theorem v3NatListLt_irrefl : ∀ l : List Nat, v3NatListLt l l = false
  | [] => rfl
  | x :: xs => by
      show (if x < x then true else if x < x then false else v3NatListLt xs xs) = false
      rw [if_neg (Nat.lt_irrefl x), if_neg (Nat.lt_irrefl x)]
      exact v3NatListLt_irrefl xs

/-- The composite order is irreflexive. -/
theorem canonIdxLt_irrefl (st : State) : canonIdxLt st st = false := by
  have e1 : v3NatListEq (canonHtup st) (canonHtup st) = true :=
    v3NatListEq_self (canonHtup st)
  have e2 : v3NatListEq (canonPosKey st) (canonPosKey st) = true :=
    v3NatListEq_self (canonPosKey st)
  show (v3NatListLt (canonHtup st) (canonHtup st) || (v3NatListEq (canonHtup st) (canonHtup st) &&
      (v3NatListLt (canonPosKey st) (canonPosKey st) ||
        (v3NatListEq (canonPosKey st) (canonPosKey st) &&
          v3NatListLt (canonFormalKey st) (canonFormalKey st))))) = false
  rw [v3NatListLt_irrefl, v3NatListLt_irrefl, v3NatListLt_irrefl, e1, e2]
  rfl

/-- The selector's output is a member of the list. -/
theorem canonV3Arg_mem : ∀ {l : List State} {s : State},
    canonV3Arg l = some s → s ∈ l
  | [], _, h => by
      simp only [canonV3Arg] at h
      exact absurd h (by simp)
  | w :: rest, s, h => by
      simp only [canonV3Arg] at h
      cases hr : canonV3Arg rest with
      | none =>
          rw [hr] at h
          have h2 : some w = some s := h
          injection h2 with hs
          subst hs
          exact List.mem_cons.2 (Or.inl rfl)
      | some b =>
          rw [hr] at h
          have hlt : (if canonIdxLt b w then some w else some b) = some s := h
          cases hb : canonIdxLt b w with
          | true =>
              rw [hb] at hlt
              simp only [ite_true] at hlt
              injection hlt with hs
              subst hs
              exact List.mem_cons.2 (Or.inl rfl)
          | false =>
              rw [hb] at hlt
              simp only [Bool.false_eq_true, ite_false] at hlt
              injection hlt with hs
              subst hs
              have hbin : b ∈ rest := canonV3Arg_mem hr
              exact List.mem_cons_of_mem w hbin

/-- SATURATED-GATED (well-behavedness row 4 of five): if every
member of the list is Final, so is the selection — the
residue-profile dividends hold at the output BY CONSTRUCTION. -/
theorem canonV3Arg_final_of_all : ∀ {l : List State},
    (∀ w ∈ l, Final w) → ∀ s, canonV3Arg l = some s → Final s
  | [], _, _, h => by
      simp only [canonV3Arg] at h
      exact absurd h (by simp)
  | w :: rest, hall, s, h => by
      have hrest : ∀ x ∈ rest, Final x := fun x hx => hall x (List.mem_cons_of_mem _ hx)
      simp only [canonV3Arg] at h
      cases hr : canonV3Arg rest with
      | none =>
          rw [hr] at h
          have h2 : some w = some s := h
          injection h2 with hs
          subst hs
          exact hall w (List.mem_cons.2 (Or.inl rfl))
      | some b =>
          rw [hr] at h
          have hlt : (if canonIdxLt b w then some w else some b) = some s := h
          cases hb : canonIdxLt b w with
          | true =>
              rw [hb] at hlt
              simp only [ite_true] at hlt
              injection hlt with hs
              subst hs
              exact hall w (List.mem_cons.2 (Or.inl rfl))
          | false =>
              rw [hb] at hlt
              simp only [Bool.false_eq_true, ite_false] at hlt
              injection hlt with hs
              subst hs
              exact canonV3Arg_final_of_all hrest _ hr

/-! ## The conjugation rows (the keys' invariances) -/


/-- The height tuple conjugates by the PAIR SWAP (spade club,
heart diamond) — the permutation that makes the fixed-order lex
the arm price at the height level. -/
theorem canonHtup_twinMap (st : State) :
    canonHtup st.twinMap =
      [((st.found .club).length), ((st.found .diamond).length),
        ((st.found .heart).length), ((st.found .spade).length)] := by
  have h0 : st.twinMap.found .spade = (st.found .club).map Card.twin := by
    rw [State.twinMap_found]; rfl
  have h1 : st.twinMap.found .heart = (st.found .diamond).map Card.twin := by
    rw [State.twinMap_found]; rfl
  have h2 : st.twinMap.found .diamond = (st.found .heart).map Card.twin := by
    rw [State.twinMap_found]; rfl
  have h3 : st.twinMap.found .club = (st.found .spade).map Card.twin := by
    rw [State.twinMap_found]; rfl
  rw [canonHtup, h0, h1, h2, h3]
  simp only [List.length_map]

/-- The position key is conjugation-INVARIANT: twinMap relabels
piles in place, never moves anchors — the wiggle layer of the
index is conj-safe by construction (why every suit-flavored
tie-break was doomed and this one is not). -/
theorem canonPosKey_twinMap (st : State) :
    canonPosKey st.twinMap = canonPosKey st := by
  have hf : ∀ a, ((st.twinMap.piles a).faceUp).length = ((st.piles a).faceUp).length := by
    intro a
    rw [show st.twinMap.piles a = (st.piles a).twinMap from rfl, Pile.twinMap_faceUp,
      List.length_map]
  have hh : ∀ a, ((st.twinMap.piles a).hidden).length = ((st.piles a).hidden).length := by
    intro a
    rw [show st.twinMap.piles a = (st.piles a).twinMap from rfl, Pile.twinMap_hidden,
      List.length_map]
  rw [canonPosKey, canonPosKey, v3MapCong _ hf, v3MapCong _ hh]

/-! ## The Q-cargo law (the arithmetic) -/


/-- Only queens sit on kings — the exchlaw falsifier's cargo class
is the WHOLE cover class of a king. -/
theorem v3CoverIsQueen {z c : Card} (hs : canSitOn z c = true)
    (hk : c.rank = Rank.king) : z.rank = Rank.queen := by
  rw [canSitOn_eq] at hs
  have hk12 : (Rank.king).toIdx = 12 := rfl
  have hq11 : (Rank.queen).toIdx = 11 := rfl
  rw [hk, hk12] at hs
  exact Rank.toIdx_inj (by omega)

/-! ## FORK EXCLUSIVITY — the deductive three-lemma chain (the
user's proof sketch, landed as arithmetic): (A) rank exactness —
a PILED card's suit rung sits weakly below the card's own rank
(a higher rung would mean the card is already founded, and
conservation forbids a card in two zones); (B) fork pins — a
standing fork pins BOTH twin suits exactly at the twin rank
(the twins' stackability) and pins the cargo's suit STRICTLY
below its own rank (the parked cover, never rung-ready); (C) the
SANDWICH — two forks contradict: each fork's cargo-pin collides
with the other fork's twin-pin, and the two strict inequalities
chase each other around the color square.  Full law: AT MOST
ONE FORK PER CLASS, at any ranks, in any color — same-color
double forks die at step (B) alone (the second fork demands the
already-pinned rungs at a different rank), and the crafted
double-fork cell becomes the negative-control exhibit attached
to the deductive proof at the probe battery.  The §3.1
sharpening: the worried bit is a PER-CLASS SINGLETON BY
ARITHMETIC — the ≤2 arm calibration's last soft spot now
rigid.  -/

/-- An element at position `i` belongs to the first `n` of the
list when `i < n` (the position-to-membership row). -/
private theorem v3GetInTake : ∀ {α : Type} (l : List α) (n i : Nat)
    (hl : i < l.length) (hn : i < n), l.get ⟨i, hl⟩ ∈ l.take n := by
  intro α l n i hl hn
  induction n generalizing l i hl with
  | zero => exact absurd hn (by omega)
  | succ n ih =>
      cases l with
      | nil => exact absurd hl (by simp)
      | cons a t =>
          cases i with
          | zero =>
              show a ∈ a :: t.take n
              exact List.mem_cons.2 (Or.inl rfl)
          | succ i' =>
              simp only [List.length_cons] at hl
              refine List.mem_cons_of_mem a (ih t i' (by omega) (by omega))

/-- The founded build order is position-true: the card at rank
`r`'s own build index is `r` itself. -/
private theorem v3RankGet : ∀ (r : Rank) (h : r.toIdx < Rank.all.length),
    Rank.all.get ⟨r.toIdx, h⟩ = r := by
  intro r h
  cases r <;> rfl

/-- CARD-LEVEL position: a card sits at its own build index. -/
private theorem v3UpGet : ∀ (z : Card) (h : z.rank.toIdx < z.suit.upCards.length),
    z.suit.upCards.get ⟨z.rank.toIdx, h⟩ = z := by
  intro z h
  obtain ⟨zs, zr⟩ := z
  cases zr <;> rfl

/-- (A) RANK EXACTNESS, the piled leg: a face-up card's suit rung
sits weakly below the card's own rank index — a higher rung
would have founded it, and conservation forbids a card in two
zones. -/
theorem v3PiledRung {st : State} {z : Card} {a : Anchor} (hwf : st.WF)
    (hmem : z ∈ (st.piles a).faceUp) :
    st.foundHeight z.suit ≤ z.rank.toIdx := by
  rcases Nat.lt_trichotomy (st.foundHeight z.suit) (z.rank.toIdx) with hlt | heq | hgt
  · exact Nat.le_of_lt hlt
  · exact Nat.le_of_eq heq
  · -- the taller rung would have founded z; conservation forbids it
    have hnotin : z ∉ st.found z.suit := (mem_faceUp_only hwf hmem).2.2.2.2 z.suit
    have h13 : z.suit.upCards.length = 13 := Suit.upCards_length z.suit
    obtain ⟨n, hn⟩ := hwf.found_prefix z.suit
    have hlen : (z.suit.upCards.take n).length = min n (z.suit.upCards.length) :=
      List.length_take
    have hfl2 : st.foundHeight z.suit = min n (z.suit.upCards.length) := by
      rw [show st.foundHeight z.suit = (st.found z.suit).length from rfl, hn, hlen]
    have htn : z.rank.toIdx < n := by omega
    have hget : z.suit.upCards.get ⟨z.rank.toIdx, by
        rw [h13]; exact Rank.toIdx_lt z.rank⟩ = z :=
      v3UpGet z (by rw [h13]; exact Rank.toIdx_lt z.rank)
    have zin : z ∈ z.suit.upCards.take n := by
      have hmem2 := v3GetInTake z.suit.upCards n z.rank.toIdx
        (by rw [h13]; exact Rank.toIdx_lt z.rank) htn
      rw [hget] at hmem2
      exact hmem2
    have hin : z ∈ st.found z.suit := by
      rw [hn]
      exact zin
    exact absurd hin hnotin

/-- (B) FORK PINS: a standing fork pins the licensed twin's suit
EXACTLY at the twin rank and the piled parked cover's suit
STRICTLY below the cover rank. -/
theorem v3ForkPins {st : State} {t q : Card} {a : Anchor} (hwf : st.WF)
    (htop : st.nextUp t = true)
    (hmem : q ∈ (st.piles a).faceUp)
    (hparked : st.nextUp q = false) :
    st.foundHeight t.suit = t.rank.toIdx ∧
      st.foundHeight q.suit < q.rank.toIdx := by
  refine ⟨by
      have h := htop
      simp only [State.nextUp, decide_eq_true_eq] at h
      exact h.symm, ?_⟩
  have hle := v3PiledRung hwf hmem
  have hne : st.foundHeight q.suit ≠ q.rank.toIdx := by
    intro heq
    rw [State.nextUp] at hparked
    simp [heq] at hparked
  omega

/-- (C) THE SANDWICH: two standing forks in both colors contradict.
Each fork pins both suits of its own color at its twin rank and
pins a suit of the opposite color strictly below; the black
fork's twin-pin demands the very rung the red fork's cargo-pin
denies, and vice versa — the two strict inequalities chase each
other around the color square. -/
theorem v3ForkExclusivity {st : State} {r1 r2 qR b1 b2 qB : Card}
    (hRrank : r1.rank.toIdx = r2.rank.toIdx)
    (hBrank : b1.rank.toIdx = b2.rank.toIdx)
    (hB1 : st.foundHeight b1.suit = b1.rank.toIdx)
    (hB2 : st.foundHeight b2.suit = b2.rank.toIdx)
    (hR1 : st.foundHeight r1.suit = r1.rank.toIdx)
    (hR2 : st.foundHeight r2.suit = r2.rank.toIdx)
    (hQRrank : qR.rank.toIdx + 1 = r1.rank.toIdx)
    (hQRbelow : st.foundHeight qR.suit < qR.rank.toIdx)
    (hQBrank : qB.rank.toIdx + 1 = b1.rank.toIdx)
    (hQBbelow : st.foundHeight qB.suit < qB.rank.toIdx)
    (hQRsuit : qR.suit = b1.suit ∨ qR.suit = b2.suit)
    (hQBsuit : qB.suit = r1.suit ∨ qB.suit = r2.suit) :
    False := by
  rcases hQRsuit with hS | hS
  · rcases hQBsuit with hT | hT
    · rw [hS, hB1] at hQRbelow
      rw [hT, hR1] at hQBbelow
      omega
    · rw [hS, hB1] at hQRbelow
      rw [hT, hR2] at hQBbelow
      omega
  · rcases hQBsuit with hT | hT
    · rw [hS, hB2] at hQRbelow
      rw [hT, hR1] at hQBbelow
      omega
    · rw [hS, hB2] at hQRbelow
      rw [hT, hR2] at hQBbelow
      omega

/-! ## The swap-grade license (the second signature correction, MacroInternal-aligned) -/


/-- THE SWAP-AWARE LICENSE (the skeleton's shape, mirrored
exactly): the vanilla license closes under licensed REVERSIBLE
SLIDES — 'now': the vanilla grade; 'via': a reversible tabToTab
slide then the swap-grade license at the landed state.  This is
the {slide·raise}-cascade license: the cascade-fixpoint mechanism
the census families probe operationally.  The VANILLA grade
(`CanRaise`) has NO swap disjunct, and the census's
`TwinContended`-emptiness was won AT THE VANILLA GRADE and stands
untouched — the fork is contention at the CanRaiseS grade (see
the battery's gap-form rows and FUTURES-ORIG.md §11-L4.2). -/
inductive CanRaiseS : State → Card → Prop
  | now {st : State} (c : Card) (h : CanRaise st c) : CanRaiseS st c
  | via {st st' : State} (c : Card)
      (hl : ∃ d b, st.step (Move.tabToTab d b) = some st' ∧
        reversibleAtW st (Move.tabToTab d b))
      (h : CanRaiseS st' c) : CanRaiseS st c

/-- The cargo reading (the skeleton's shape): `d` TOPS the twin's
pile — the twin sits beneath it, covered by construction. -/
def v3CargoTop (st : State) (d c : Card) : Prop :=
  ∃ a, st.pileOfTop d = some a ∧ st.pileHolding c = some a

/-- The vanilla escape row: every vanilla lift is a swap-grade
lift (the now-clause, named for the audit trail). -/
theorem canRaiseS_of_canRaise {st : State} {c : Card} (h : CanRaise st c) :
    CanRaiseS st c := CanRaiseS.now c h

/-! ## The floor sweep (MacroInternal mirror, tiers 0/1 + 2 — proofs-in-progress on this branch)

The skeleton (`Orig/MacroInternal.lean`, the user's file in the
main tree) is the name reference; this section mirrors the floor
into THIS branch with real proofs where the bank suffices, named
residues with documented routes where the assembly remains.  At
merge, the sorry-carrying skeleton rows with the same names swap
for these shapes (deltas ledgered in FUTURES-ORIG.md §11-L4.5).  -/


/-- The current founded count of a suit — the skeleton's rung
(mirrored name). -/
def rungAt (w : State) (s : Suit) : Nat := (w.found s).length

/-! ### Tier 0: the calibration and monotone rows -/


/-- STACKABLE-NOW, the forward half (the rank-encoding
calibration): a licensed lift sits EXACTLY at its rung.

The biconditional's OTHER direction is FALSE as literally stated
at covered seats — decided at the merge cell (probes/
CanonV3Probe.lean: `canRaiseB pnCasForkMerge v3DK` is FALSE while
`rungAt pnCasForkMerge .diamond = v3DK.rank.toIdx` — the covered
twin at its rung under cargo).  The load-bearing halves are this
direction plus `v3PiledRung` (a piled card's rung sits weakly
below its index — the "not-above" hedge, proven above).  The
skeleton row should take this shape or add the seat premise. -/
theorem stackable_now_rungexact {st : State} {c : Card}
    (h : CanRaise st c) : rungAt st c.suit = c.rank.toIdx := by
  obtain ⟨hn, a, hp, hseat⟩ := h
  simp only [State.nextUp, decide_eq_true_eq] at hn
  exact hn.symm

/-- The saturator step never lowers a rung (the per-step half of
the monotone row). -/
private theorem satStep_rung_mono (s : Suit) (w : State) :
    rungAt w s ≤ rungAt (satStep w) s := by
  by_cases hp : pick w = none
  · rw [satStep_none hp]
    exact Nat.le_refl _
  · have hsome : ∃ c, pick w = some c := by
      cases hp' : pick w with
      | none => exact absurd hp' hp
      | some c => exact ⟨c, rfl⟩
    obtain ⟨c, hp'⟩ := hsome
    have hsat : satStep w = (raise w c).getD w := by
      simp only [satStep, hp']
    rw [hsat]
    cases hr : raise w c with
    | none => exact Nat.le_refl _
    | some s' =>
        have hF := (raise_foundTransport hr).2 s
        show (w.found s).length ≤ (s'.found s).length
        rw [hF]
        by_cases hsc : s = c.suit
        · subst hsc
          rw [if_pos rfl, List.length_append]
          simp only [List.length_cons, List.length_nil]
          omega
        · rw [ite_eq_right hsc]
          exact Nat.le_refl _

/-- Saturation only raises: the canonical form dominates the
rungs, per suit.  (canon_rung_mono, the skeleton's name.) -/
theorem canon_rung_mono (st : State) (s : Suit) :
    rungAt st s ≤ rungAt (canon st) s := by
  have key : ∀ (N : Nat) (w : State),
      rungAt w s ≤ rungAt (canonAux N w) s := by
    intro N
    induction N with
    | zero => intro w; exact Nat.le_refl _
    | succ n ih =>
        intro w
        exact Nat.le_trans (satStep_rung_mono s w) (ih (satStep w))
  change rungAt st s ≤ rungAt (canonAux 53 st) s
  exact key 53 st

/-! ### Tier 2: PULL-MULTISET DETERMINISM (the fresh lemma) -/


/-- Builds-past-length take is the whole list. -/
private theorem v3TakeGe : ∀ (l : List Card) (n : Nat),
    l.length ≤ n → l.take n = l
  | [], 0, _ => rfl
  | [], n + 1, _ => rfl
  | a :: t, 0, h => by
      simp at h
  | a :: t, n + 1, h => by
      show a :: t.take n = a :: t
      refine congrArg (fun l => a :: l) (v3TakeGe t n ?_)
      have hlen : (a :: t).length = t.length + 1 := rfl
      omega

/-- The top-forced pull segment: the pops a descent from rung `r`
to target `t` removes from one suit's foundation — read on the
fixed build order, so determined by the tuple delta alone. -/
def pullSegment (s : Suit) (r t : Nat) : List Card :=
  s.upCards.take r |>.drop t

/-- A member's own descent segment IS the build segment (the
founded prefix is the build prefix at its height). -/
theorem found_pullSegment (st : State) (hwf : st.WF) (s : Suit) (t : Nat)
    (ht : t ≤ rungAt st s) :
    (st.found s).drop t = pullSegment s (rungAt st s) t := by
  obtain ⟨n, hn⟩ := hwf.found_prefix s
  have h13 : s.upCards.length = 13 := Suit.upCards_length s
  have hL : (s.upCards.take n).length = min n (s.upCards.length) :=
    List.length_take
  have hr : min n 13 = rungAt st s := by
    show min n 13 = (st.found s).length
    rw [hn, hL, h13]
  have htake : st.found s = s.upCards.take (rungAt st s) := by
    rcases Nat.lt_or_ge (rungAt st s) 13 with hlt | hge
    · have hn_eq : n = rungAt st s := by omega
      rw [hn, hn_eq]
    · have hall : s.upCards.take n = s.upCards := v3TakeGe s.upCards n (by omega)
      rw [hn, hall, v3TakeGe s.upCards (rungAt st s) (by omega)]
  rw [htake]
  rfl

/-- PULL-MULTISET DETERMINISM, the sweep statement: same class
fiber (equal per-suit rungs — within one arm; the arm split is
the twin pair's tuple swap, decided at the wing cells) ⇒ the
descent pops to any lower target coincide card-for-card. -/
theorem pull_multiset_determinism (u v : State) (hu : u.WF) (hv : v.WF)
    (h : ∀ s, (u.found s).length = (v.found s).length)
    (t : Suit → Nat) :
    ∀ s, (u.found s).drop (t s) = (v.found s).drop (t s) := by
  intro s
  have hf := FoundKit.found_congr u v hu hv s (h s)
  rw [hf]

/-! ## The audit: the floor sweep's opening rows

`\#print axioms` for every head this chapter adds: all audit
`[propext]` — ZERO sorry, ZERO native_decide, ZERO Classical.choice.
The post-merge targets (the canus bridge, the saturated-tuple
orbit, the full section iff, the selector's transitivity packet)
are the named residues LEDGERED in FUTURES-ORIG.md §11-L4, not
stubbed here: their payers (mem_macro_iff and the cone rows) are
unmerged imports, and the probe battery carries their decided
evidence.  The fork-exclusivity chain (v3PiledRung, v3ForkPins,
v3ForkExclusivity) lands DEDUCTIVELY above — zero sorry.  -/

#print axioms CanRaiseS
#print axioms v3CargoTop
#print axioms canRaiseS_of_canRaise
#print axioms canonHtup
#print axioms canonPosKey
#print axioms canonCardIdx
#print axioms canonFormalKey
#print axioms v3NatListLt
#print axioms canonIdxLt
#print axioms satRung
#print axioms aboveCeiling
#print axioms strandedAt
#print axioms pendingForeverAt
#print axioms parkingMap
#print axioms canonV3Arg
#print axioms v3NatListLt_irrefl
#print axioms canonIdxLt_irrefl
#print axioms canonV3Arg_mem
#print axioms canonV3Arg_final_of_all
#print axioms canonHtup_twinMap
#print axioms canonPosKey_twinMap
#print axioms v3CoverIsQueen
#print axioms v3PiledRung
#print axioms v3ForkPins
#print axioms v3ForkExclusivity
#print axioms rungAt
#print axioms stackable_now_rungexact
#print axioms satStep_rung_mono
#print axioms canon_rung_mono
#print axioms v3TakeGe
#print axioms pullSegment
#print axioms found_pullSegment
#print axioms pull_multiset_determinism
