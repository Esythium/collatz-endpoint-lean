import CollatzEndpoint.WindowCover
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace CollatzEndpoint

/-- Numerical passage from a dyadic layer estimate to a window estimate.
The input exponents are explicit parameters so this algebraic lemma can be
checked independently of the entropy-crossing construction. -/
theorem dyadic_bound_to_window {β γ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hγ : 0 ≤ γ) {X k : ℕ} (hX : 2 ≤ X)
    (hlo : X ≤ 2 ^ k) (hhi : 2 ^ k < 2 * X) :
    200 * (2 : ℝ) ^ (β * (k : ℝ)) * (k : ℝ) ^ (-γ) ≤
      400 * (X : ℝ) ^ β / (Real.logb 2 (X : ℝ)) ^ γ := by
  have hXp : (0 : ℝ) < X := by positivity
  have hlogp : 0 < Real.logb 2 (X : ℝ) :=
    Real.logb_pos (by norm_num) (by exact_mod_cast (show 1 < X by omega))
  have hlog : Real.logb 2 (X : ℝ) ≤ (k : ℝ) := by
    apply (Real.logb_le_iff_le_rpow (by norm_num) hXp).2
    simpa only [Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat] using
      (show (X : ℝ) ≤ (2 ^ k : ℕ) by exact_mod_cast hlo)
  have hpow : (2 : ℝ) ^ (β * (k : ℝ)) ≤ 2 * (X : ℝ) ^ β := by
    calc
      (2 : ℝ) ^ (β * (k : ℝ)) = ((2 : ℝ) ^ k) ^ β := by
        rw [mul_comm β, Real.rpow_natCast_mul (by norm_num)]
      _ ≤ (2 * (X : ℝ)) ^ β := by
        apply Real.rpow_le_rpow (by positivity) _ hβ0
        exact_mod_cast hhi.le
      _ = (2 : ℝ) ^ β * (X : ℝ) ^ β := Real.mul_rpow (by norm_num) hXp.le
      _ ≤ 2 * (X : ℝ) ^ β := by
        have htwo : (2 : ℝ) ^ β ≤ 2 := by
          simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hβ1
        exact mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hXp.le β)
  have hdec : (k : ℝ) ^ (-γ) ≤ (Real.logb 2 (X : ℝ)) ^ (-γ) :=
    Real.rpow_le_rpow_of_nonpos hlogp hlog (by linarith)
  calc
    _ ≤ 200 * (2 * (X : ℝ) ^ β) * (Real.logb 2 (X : ℝ)) ^ (-γ) := by
      gcongr
    _ = 400 * (X : ℝ) ^ β / (Real.logb 2 (X : ℝ)) ^ γ := by
      rw [Real.rpow_neg hlogp.le]
      ring

end CollatzEndpoint
