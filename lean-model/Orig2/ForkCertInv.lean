import Orig2.ForkCertMain

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Cert_CrossSuit_Inv - the cross-suit pair count of the 17-letter play

READ-ONLY scratch card (`Temp/`).  Zero `sorry`, zero `Classical.choice`,
zero `nativeDecide`.

`Temp/Search_Report.md` §2/§4 records that the play `ρ` carries **8** cross-suit
raise-before-pull pairs, i.e. `Canon.inv ρ = 8`.  This card certifies that
count in the kernel (`inv_rho`), together with the exhibited pair
`i = 6 (raise QD), j = 9 (pull KS)` already used for the refutation.

NOT certified here: the report's stronger claim that EVERY shortest play of
`(u,v)` has `inv = 8` (25 plays).  That needs an enumeration of the shortest
plays, not just the distance table; see `Temp/Cert_Report.md` §4.
-/

namespace Cert

/-- The suit of a raise letter (if the letter is a raise). -/
def raiseSuitOf : Move → Option Suit
  | Move.tabToFound c => some c.suit
  | _ => none

/-- The suit of a pull letter (if the letter is a pull). -/
def pullSuitOf : Move → Option Suit
  | Move.foundToTab c _ => some c.suit
  | _ => none

/-- `crossCount acc ρ` - the number of `(raise, strictly later pull)` pairs of
DIFFERENT suits in `ρ`, given the suits of the raises already seen (`acc`,
newest first).  This is `Canon.inv` (`Temp/Search_verify_hit.py: inv_of`). -/
def crossCount : List Move → List Suit → Nat
  | [], _ => 0
  | m :: t, acc =>
      (match pullSuitOf m with
       | some s => (acc.filter (fun s' => decide (s' ≠ s))).length
       | none => 0)
      + (match raiseSuitOf m with
         | some s => crossCount t (s :: acc)
         | none => crossCount t acc)

/-- **`Canon.inv` OF THE PLAY.** -/
def inv (ρ : List Move) : Nat := crossCount ρ []

/-- **THE PLAY CARRIES EIGHT CROSS-SUIT RAISE-BEFORE-PULL PAIRS.** -/
theorem inv_rho : inv rho = 8 := by decide

/-! ## The table size (the component) -/

/-- **THE TABLE IS EXACTLY THE 2308-STATE COMPONENT** (80 rung-vector buckets). -/
theorem distTab_size : (distTab.flatMap (fun b => b.2)).length = 2308 := by decide

theorem distTab_buckets : distTab.length = 80 := by decide

/-! ## The equal-rung endpoints -/

theorem rung_u_heart : rungAt u .heart = 11 := rfl
theorem rung_u_diamond : rungAt u .diamond = 10 := rfl
theorem rung_u_spade : rungAt u .spade = 12 := rfl
theorem rung_u_club : rungAt u .club = 0 := rfl
theorem rung_v_heart : rungAt v .heart = 11 := rfl
theorem rung_v_diamond : rungAt v .diamond = 10 := rfl
theorem rung_v_spade : rungAt v .spade = 12 := rfl
theorem rung_v_club : rungAt v .club = 0 := rfl

/-- **THE ENDPOINTS HAVE THE SAME RUNG VECTOR `(11,10,12,0)`.** -/
theorem rung_eq (σ : Suit) : rungAt u σ = rungAt v σ := by
  cases σ <;> rfl

/-- The endpoints are different states (`p5`/`p6` are exchanged). -/
theorem u_ne_v : u ≠ v := by
  intro h
  have h1 : (u.piles .p5).faceUp = (v.piles .p5).faceUp := by rw [h]
  have h2 : (u.piles .p5).faceUp = [crd .heart .king] := rfl
  have h3 : (v.piles .p5).faceUp = [crd .spade .king, crd .diamond .queen] := rfl
  rw [h2, h3] at h1
  exact absurd h1 (by decide)

end Cert

#print axioms Cert.inv_rho
#print axioms Cert.distTab_size
#print axioms Cert.rung_eq
#print axioms Cert.u_ne_v
