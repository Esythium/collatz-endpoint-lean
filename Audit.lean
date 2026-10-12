import CollatzEndpoint

/-! Public, concrete statements followed by their transitive axiom dependencies. -/
open CollatzEndpoint

#print alpha
#print beta
#print gamma
#print step
#print CollisionFree
#print Divergent
#print EventuallyPeriodic
#print successiveOddOrbit
#print collatzDrift

#check alpha_unique
#check parityWord_bijective
#check dyadic_translation
#check block_card_le_layerSum
#check layerSum_le
#check uniform_window_bound
#check divergent_prefixMax_lower
#check divergent_odd_prefixMax_lower
#check divergent_not_isBigO
#check divergent_odd_not_isBigO
#check eventuallyPeriodic_of_critical_power
#check eventuallyPeriodic_of_odd_critical_power
#check divergent_reciprocal_summable
#check divergent_odd_reciprocal_summable
#check collatz_product_identity
#check divergent_correctionProduct_converges
#check divergent_not_drift_upper
#check divergent_drift_frequently_gt
#check divergent_drift_limsup

#print axioms alpha_unique
#print axioms parityWord_bijective
#print axioms dyadic_translation
#print axioms block_card_le_layerSum
#print axioms layerSum_le
#print axioms uniform_window_bound
#print axioms divergent_iff_injective_orbit
#print axioms successiveOddOrbit_eq_orbit
#print axioms divergent_prefixMax_lower
#print axioms divergent_odd_prefixMax_lower
#print axioms divergent_not_isBigO
#print axioms divergent_odd_not_isBigO
#print axioms eventuallyPeriodic_of_critical_power
#print axioms eventuallyPeriodic_of_odd_critical_power
#print axioms divergent_reciprocal_summable
#print axioms divergent_odd_reciprocal_summable
#print axioms collatz_product_identity
#print axioms divergent_correctionProduct_converges
#print axioms divergent_not_drift_upper
#print axioms divergent_drift_frequently_gt
#print axioms divergent_drift_limsup
