import CollatzEndpoint.Windows
import CollatzEndpoint.Reciprocal
import CollatzEndpoint.Dynamics
import CollatzEndpoint.Drift

/-!
# Concrete Collatz endpoint theorems

This module discharges the abstract counting and dynamical hypotheses of the
growth and drift lemmas using the proved window theorem and the actual Collatz
maps.  No analytic bound is assumed in the final trajectory theorems.
-/

namespace CollatzEndpoint

open Filter
open scoped Topology

theorem initial_counting_bound {A : Set ℕ} (hfree : CollisionFree A) :
    InitialCountingBound A
      (fun X => 400 * (X : ℝ) ^ beta / (Real.logb 2 X) ^ gamma) := by
  classical
  intro X hX s hs hbounds
  have hsub : s ⊆ windowSet A 1 X := by
    intro x hx
    exact mem_windowSet.mpr ⟨(hbounds x hx).1, by have := (hbounds x hx).2; omega, hs x hx⟩
  exact (show (s.card : ℝ) ≤ ((windowSet A 1 X).card : ℝ) by
    exact_mod_cast Finset.card_le_card hsub).trans (uniform_window_bound hfree 1 hX)

theorem initial_power_counting_bound {A : Set ℕ} (hfree : CollisionFree A) :
    InitialCountingBound A (fun X => 400 * (X : ℝ) ^ beta) := by
  intro X hX s hs hb
  apply (initial_counting_bound hfree X hX s hs hb).trans
  exact div_le_self (by positivity)
    (Real.one_le_rpow (one_le_logb_nat hX) gamma_pos.le)

theorem collisionFree_prefixMax_lower {A : Set ℕ} {z : ℕ → ℕ}
    (hfree : CollisionFree A) (hinj : Function.Injective z)
    (hpos : ∀ n, 0 < z n) (hA : ∀ n, z n ∈ A) {N : ℕ} (hN : 2 ≤ N) :
    (400 : ℝ) ^ (-1 / beta) * (N : ℝ) ^ (1 / beta) *
      (Real.logb 2 N) ^ (gamma / beta) ≤ (prefixMax z N : ℝ) :=
  prefixMax_lower_bound hinj hpos hA (by norm_num) beta_pos gamma_pos.le
    (initial_counting_bound hfree) hN

theorem collisionFree_not_isBigO {A : Set ℕ} {z : ℕ → ℕ} {c : ℝ}
    (hfree : CollisionFree A) (hinj : Function.Injective z)
    (hpos : ∀ n, 0 < z n) (hA : ∀ n, z n ∈ A) (hc : c < gamma / beta) :
    ¬ Asymptotics.IsBigO atTop (fun n => (z n : ℝ)) (powerLogScale (1 / beta) c) := by
  apply not_isBigO_of_prefixMax_lower (K := (400 : ℝ) ^ (-1 / beta))
    (Real.rpow_pos_of_pos (by norm_num) _) (div_nonneg (by norm_num) beta_pos.le)
    (div_pos gamma_pos beta_pos) hc
  intro N hN
  simpa only [powerLogScale, mul_assoc] using
    collisionFree_prefixMax_lower hfree hinj hpos hA hN

theorem collisionFree_reciprocal_summable {A : Set ℕ} {z : ℕ → ℕ}
    (hfree : CollisionFree A) (hinj : Function.Injective z)
    (hpos : ∀ n, 0 < z n) (hA : ∀ n, z n ∈ A) :
    Summable (fun n => 1 / (z n : ℝ)) :=
  reciprocal_summable_of_power_count (by norm_num) beta_lt_one hinj hpos hA
    (initial_power_counting_bound hfree)

/-- Corollary 5.1, shortcut trajectory, with explicit constant. -/
theorem divergent_prefixMax_lower {start : ℕ} (hstart : 0 < start)
    (hdiv : Divergent start) {N : ℕ} (hN : 2 ≤ N) :
    (400 : ℝ) ^ (-1 / beta) * (N : ℝ) ^ (1 / beta) *
      (Real.logb 2 N) ^ (gamma / beta) ≤ (prefixMax (orbit start) N : ℝ) :=
  collisionFree_prefixMax_lower (collisionFree_of_divergent hdiv)
    (injective_orbit_of_divergent hdiv) (orbit_pos hstart)
    (fun n => ⟨n, rfl⟩) hN

theorem divergent_not_isBigO {start : ℕ} {c : ℝ} (hstart : 0 < start)
    (hdiv : Divergent start) (hc : c < gamma / beta) :
    ¬ Asymptotics.IsBigO atTop (fun n => (orbit start n : ℝ))
      (powerLogScale (1 / beta) c) :=
  collisionFree_not_isBigO (collisionFree_of_divergent hdiv)
    (injective_orbit_of_divergent hdiv) (orbit_pos hstart) (fun n => ⟨n, rfl⟩) hc

theorem divergent_reciprocal_summable {start : ℕ} (hstart : 0 < start)
    (hdiv : Divergent start) : Summable (fun n => 1 / (orbit start n : ℝ)) :=
  collisionFree_reciprocal_summable (collisionFree_of_divergent hdiv)
    (injective_orbit_of_divergent hdiv) (orbit_pos hstart) (fun n => ⟨n, rfl⟩)

theorem eventuallyPeriodic_of_isBigO {start : ℕ} {c : ℝ}
    (hstart : 0 < start) (hc : c < gamma / beta)
    (hO : Asymptotics.IsBigO atTop (fun n => (orbit start n : ℝ))
      (powerLogScale (1 / beta) c)) : EventuallyPeriodic start := by
  apply eventuallyPeriodic_of_not_divergent
  intro hdiv
  exact divergent_not_isBigO hstart hdiv hc hO

/-- The critical pure-power endpoint implies eventual periodicity. -/
theorem eventuallyPeriodic_of_critical_power {start : ℕ} (hstart : 0 < start)
    (hO : Asymptotics.IsBigO atTop (fun n => (orbit start n : ℝ))
      (fun n => (n : ℝ) ^ (1 / beta))) : EventuallyPeriodic start := by
  apply eventuallyPeriodic_of_isBigO hstart (c := 0) (div_pos gamma_pos beta_pos)
  have heq : powerLogScale (1 / beta) 0 = (fun n : ℕ => (n : ℝ) ^ (1 / beta)) := by
    funext n
    simp [powerLogScale]
  rwa [heq]

/-- Corollary 5.1 for successive odd iterates, including an even initial seed. -/
theorem divergent_odd_prefixMax_lower {start : ℕ} (hstart : 0 < start)
    (hdiv : Divergent start) {N : ℕ} (hN : 2 ≤ N) :
    (400 : ℝ) ^ (-1 / beta) * (N : ℝ) ^ (1 / beta) *
      (Real.logb 2 N) ^ (gamma / beta) ≤
      (prefixMax (successiveOddOrbit start) N : ℝ) :=
  collisionFree_prefixMax_lower (collisionFree_of_divergent hdiv)
    (successiveOddOrbit_injective hstart (injective_orbit_of_divergent hdiv))
    (successiveOddOrbit_pos hstart) (successiveOddOrbit_mem_range hstart) hN

theorem divergent_odd_not_isBigO {start : ℕ} {c : ℝ} (hstart : 0 < start)
    (hdiv : Divergent start) (hc : c < gamma / beta) :
    ¬ Asymptotics.IsBigO atTop (fun n => (successiveOddOrbit start n : ℝ))
      (powerLogScale (1 / beta) c) :=
  collisionFree_not_isBigO (collisionFree_of_divergent hdiv)
    (successiveOddOrbit_injective hstart (injective_orbit_of_divergent hdiv))
    (successiveOddOrbit_pos hstart) (successiveOddOrbit_mem_range hstart) hc

theorem divergent_odd_reciprocal_summable {start : ℕ} (hstart : 0 < start)
    (hdiv : Divergent start) : Summable (fun n => 1 / (successiveOddOrbit start n : ℝ)) :=
  collisionFree_reciprocal_summable (collisionFree_of_divergent hdiv)
    (successiveOddOrbit_injective hstart (injective_orbit_of_divergent hdiv))
    (successiveOddOrbit_pos hstart) (successiveOddOrbit_mem_range hstart)

theorem eventuallyPeriodic_of_odd_isBigO {start : ℕ} {c : ℝ}
    (hstart : 0 < start) (hc : c < gamma / beta)
    (hO : Asymptotics.IsBigO atTop (fun n => (successiveOddOrbit start n : ℝ))
      (powerLogScale (1 / beta) c)) : EventuallyPeriodic start := by
  apply eventuallyPeriodic_of_not_divergent
  intro hdiv
  exact divergent_odd_not_isBigO hstart hdiv hc hO

theorem eventuallyPeriodic_of_odd_critical_power {start : ℕ} (hstart : 0 < start)
    (hO : Asymptotics.IsBigO atTop (fun n => (successiveOddOrbit start n : ℝ))
      (fun n => (n : ℝ) ^ (1 / beta))) : EventuallyPeriodic start := by
  apply eventuallyPeriodic_of_odd_isBigO hstart (c := 0) (div_pos gamma_pos beta_pos)
  have heq : powerLogScale (1 / beta) 0 = (fun n : ℕ => (n : ℝ) ^ (1 / beta)) := by
    funext n
    simp [powerLogScale]
  rwa [heq]

theorem divergent_odd_correction_summable {start : ℕ} (hstart : 0 < start)
    (hdiv : Divergent start) :
    Summable (fun n => 1 / (3 * (successiveOddOrbit start n : ℝ))) := by
  convert (divergent_odd_reciprocal_summable hstart hdiv).mul_left (1 / 3 : ℝ) using 1
  ext n
  ring

/-- The exact dyadic drift of the actual successive odd iterates. -/
noncomputable def collatzDrift (start n : ℕ) : ℝ :=
  driftSequence (fun j => oddValuation (successiveOddOrbit start j)) n

theorem collatz_product_identity {start : ℕ} (hstart : 0 < start) (n : ℕ) :
    (successiveOddOrbit start n : ℝ) = (successiveOddOrbit start 0 : ℝ) *
      (2 : ℝ) ^ collatzDrift start n * correctionProduct (successiveOddOrbit start) n :=
  odd_recurrence_drift_identity (successiveOddOrbit_pos hstart)
    (successiveOddOrbit_recurrence start) n

theorem divergent_correctionProduct_converges {start : ℕ} (hstart : 0 < start)
    (hdiv : Divergent start) :
    ∃ Q : ℝ, 1 ≤ Q ∧
      Q ≤ Real.exp (∑' j, 1 / (3 * (successiveOddOrbit start j : ℝ))) ∧
      Tendsto (correctionProduct (successiveOddOrbit start)) atTop (𝓝 Q) :=
  correctionProduct_converges _ (divergent_odd_correction_summable hstart hdiv)

/-- Corollary 5.2: excludes every eventual upper envelope with c < gamma/beta. -/
theorem divergent_not_drift_upper {start : ℕ} {c B : ℝ} (hstart : 0 < start)
    (hdiv : Divergent start) (hc : c < gamma / beta) :
    ¬ (∀ᶠ n in atTop, collatzDrift start n ≤
      (1 / beta) * Real.logb 2 n + c * Real.logb 2 (Real.logb 2 n) + B) := by
  apply not_drift_upper_of_prefixMax_lower
    (successiveOddOrbit_pos hstart) (successiveOddOrbit_recurrence start)
    (divergent_odd_correction_summable hstart hdiv)
    (K := (400 : ℝ) ^ (-1 / beta))
    (Real.rpow_pos_of_pos (by norm_num) _) (div_nonneg (by norm_num) beta_pos.le)
    (div_pos gamma_pos beta_pos) hc
  intro N hN
  simpa only [powerLogScale, mul_assoc] using divergent_odd_prefixMax_lower hstart hdiv hN

theorem divergent_drift_frequently_gt {start : ℕ} {c : ℝ} (hstart : 0 < start)
    (hdiv : Divergent start) (hc : c < gamma / beta) :
    ∃ᶠ n in atTop, c <
      (collatzDrift start n - (1 / beta) * Real.logb 2 n) /
        Real.logb 2 (Real.logb 2 n) := by
  apply frequently_lt_normalizedDrift
    (successiveOddOrbit_pos hstart) (successiveOddOrbit_recurrence start)
    (divergent_odd_correction_summable hstart hdiv)
    (K := (400 : ℝ) ^ (-1 / beta))
    (Real.rpow_pos_of_pos (by norm_num) _) (div_nonneg (by norm_num) beta_pos.le)
    (div_pos gamma_pos beta_pos) hc
  intro N hN
  simpa only [powerLogScale, mul_assoc] using divergent_odd_prefixMax_lower hstart hdiv hN

/-- The limsup is taken in the extended reals, so an unbounded normalized
drift is included without a hidden boundedness hypothesis. -/
theorem divergent_drift_limsup {start : ℕ} (hstart : 0 < start)
    (hdiv : Divergent start) :
    (gamma / beta : EReal) ≤ Filter.limsup
      (fun n => (((collatzDrift start n - (1 / beta) * Real.logb 2 n) /
        Real.logb 2 (Real.logb 2 n) : ℝ) : EReal)) atTop := by
  apply le_limsup_normalizedDrift
    (successiveOddOrbit_pos hstart) (successiveOddOrbit_recurrence start)
    (divergent_odd_correction_summable hstart hdiv)
    (K := (400 : ℝ) ^ (-1 / beta))
    (Real.rpow_pos_of_pos (by norm_num) _) (div_nonneg (by norm_num) beta_pos.le)
    (div_pos gamma_pos beta_pos)
  intro N hN
  simpa only [powerLogScale, mul_assoc] using divergent_odd_prefixMax_lower hstart hdiv hN

end CollatzEndpoint
