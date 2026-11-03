import Temp.SpecShift_sem
import Orig2.Fork.Split.ForkDrainInduction

set_option autoImplicit false

/-!
# The drain's transport row is `specShift_sem_fwd`

`RaiseTransport x` (`Orig2/Fork/Split/ForkDrainInduction.lean:556`) names three
inputs for the raise-only drain phase; the first is

```
CanRaiseS_preserved : u.WF → DrainInvariant u x → DrainRaisable u x →
  CanRaise u c → c ≠ x → c ≠ x.twin → reversibleAtW u (tabToFound c) →
  State.step u (tabToFound c) = some u' → CanRaiseS u' x.twin
```

That is exactly the lane's forward licence shift (`specShift_sem_fwd`) at
`d = x.twin`: its two side conditions are literally `c ≠ x.twin` and `c ≠ x`,
and the input licence is the `DrainInvariant`'s `CanRaiseS u x.twin` conjunct.
So the first transport row needs no new mathematics — it is already proved.
-/

namespace OneColourClosure

/-- **The `CanRaiseS` transport row.**  A reversible raise of a non-twin card
keeps `x.twin` S-live. -/
theorem drain_transport_canRaiseS {u u' : State} {x c : Card}
    (hwf : u.WF) (h : Drain.DrainInvariant u x)
    (hx : c ≠ x) (hxt : c ≠ x.twin)
    (hstep : State.step u (Move.tabToFound c) = some u') :
    CanRaiseS u' x.twin := by
  have hstepS : RaiseStepS u u' c := ⟨u, Steps.refl u, hstep⟩
  have hd : x.twin ≠ c := fun hcon => hxt hcon.symm
  have hdt : x.twin ≠ c.twin := by
    intro hcon
    have hxc : x = c := by
      simpa [card_twin_twin] using congrArg Card.twin hcon
    exact hx hxc.symm
  exact specShift_sem_fwd hwf hstepS hd hdt h.2.1

end OneColourClosure

#print axioms OneColourClosure.drain_transport_canRaiseS
