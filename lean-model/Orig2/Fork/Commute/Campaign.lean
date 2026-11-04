import Orig2.Fork.Class.CeilingBridge
import Orig2.Fork.Commute.PullCommute

set_option autoImplicit false

/-!
# Orig2.Fork.Commute.Campaign — the unconditional forkless campaign theorem

`Orig2/Fork/Class/CeilingBridge.lean` reduces the campaign theorem to the
residue `SatDifferForkWF`.  `Orig2/Fork/Commute/PullCommute.lean` proves that
residue (`satDifferForkWF_proved`), so the campaign theorem is unconditional.

The statements below are the residue-free versions of
`forkless_rungs_agree_wf` and `forkless_found_unique_wf`.
-/

/-- **UNCONDITIONAL RUNG AGREEMENT.**  In a forkless class, two saturated
`WF` class-mates have equal rungs. -/
theorem forkless_rungs_agree_proved {s s' : State}
    (hwf : s.WF) (hclass : sameOrbitSetoid.r s s')
    (hfrk : ∀ u, sameOrbitSetoid.r s u → ¬ forkState u)
    (hsat : SSaturated s) (hsat' : SSaturated s') :
    ∀ σ : Suit, rungAt s σ = rungAt s' σ :=
  forkless_rungs_agree_wf OneColourClosure.satDifferForkWF_proved
    hwf hclass hfrk hsat hsat'

/-- **THE UNCONDITIONAL CAMPAIGN THEOREM.**  In a forkless macro class, two
saturated endpoints share their foundations verbatim. -/
theorem forkless_found_unique_proved {s s' : State}
    (hwf : s.WF) (hwf' : s'.WF)
    (hclass : sameOrbitSetoid.r s s')
    (hfrk : ∀ u, sameOrbitSetoid.r s u → ¬ forkState u)
    (hsat : SSaturated s) (hsat' : SSaturated s') :
    s.found = s'.found :=
  forkless_found_unique_wf OneColourClosure.satDifferForkWF_proved
    hwf hwf' hclass hfrk hsat hsat'

#print axioms forkless_rungs_agree_proved
#print axioms forkless_found_unique_proved
