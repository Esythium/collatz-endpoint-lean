import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The entropy crossing and the Collatz endpoint exponents

All entropy calculations use natural logarithms.  Dividing by `Real.log 2`
recovers exactly the base-two definitions in the accompanying manuscript.
-/

namespace CollatzEndpoint

open Set

noncomputable def entropyDifference (p : ℝ) : ℝ :=
  Real.binEntropy p - p * Real.log 3

lemma log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

lemma log_three_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)

lemma entropyDifference_continuous : Continuous entropyDifference := by
  exact Real.binEntropy_continuous.sub (continuous_id.mul_const _)

lemma binEntropy_three_fifths :
    Real.binEntropy ((3 : ℝ) / 5) =
      Real.log 5 - (3 / 5 : ℝ) * Real.log 3 - (2 / 5 : ℝ) * Real.log 2 := by
  rw [Real.binEntropy, show (1 : ℝ) - 3 / 5 = 2 / 5 by norm_num]
  simp only [Real.log_inv]
  rw [Real.log_div (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (5 : ℝ) ≠ 0),
    Real.log_div (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (5 : ℝ) ≠ 0)]
  ring

lemma binEntropy_five_eighths :
    Real.binEntropy ((5 : ℝ) / 8) =
      3 * Real.log 2 - (5 / 8 : ℝ) * Real.log 5 - (3 / 8 : ℝ) * Real.log 3 := by
  rw [Real.binEntropy, show (1 : ℝ) - 5 / 8 = 3 / 8 by norm_num]
  simp only [Real.log_inv]
  rw [Real.log_div (by norm_num : (5 : ℝ) ≠ 0) (by norm_num : (8 : ℝ) ≠ 0),
    Real.log_div (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (8 : ℝ) ≠ 0)]
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    convert (Real.log_pow (2 : ℝ) 3) using 1; norm_num
  rw [h8]
  ring

lemma entropyDifference_three_fifths_pos :
    0 < entropyDifference ((3 : ℝ) / 5) := by
  have h : Real.log ((3 : ℝ) ^ 6 * 2 ^ 2) < Real.log ((5 : ℝ) ^ 5) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow,
    Real.log_pow] at h
  rw [entropyDifference, binEntropy_three_fifths]
  norm_num at h ⊢
  linarith

lemma entropyDifference_five_eighths_neg :
    entropyDifference ((5 : ℝ) / 8) < 0 := by
  have h : Real.log ((2 : ℝ) ^ 24) < Real.log ((5 : ℝ) ^ 5 * 3 ^ 8) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow,
    Real.log_pow] at h
  rw [entropyDifference, binEntropy_five_eighths]
  norm_num at h ⊢
  linarith

lemma entropyDifference_strictAntiOn :
    StrictAntiOn entropyDifference (Icc (1 / 2 : ℝ) 1) := by
  intro x hx y hy hxy
  have he : Real.binEntropy y < Real.binEntropy x :=
    Real.binEntropy_strictAntiOn (by simpa using hx) (by simpa using hy) hxy
  have hl : x * Real.log 3 < y * Real.log 3 :=
    mul_lt_mul_of_pos_right hxy log_three_pos
  dsimp [entropyDifference]
  linarith

lemma entropy_root_exists :
    ∃ p : ℝ, p ∈ Ioo (3 / 5 : ℝ) (5 / 8 : ℝ) ∧ entropyDifference p = 0 := by
  have h0 : (0 : ℝ) ∈ Ioo (entropyDifference (5 / 8))
      (entropyDifference (3 / 5)) :=
    ⟨entropyDifference_five_eighths_neg, entropyDifference_three_fifths_pos⟩
  obtain ⟨p, hp, he⟩ := intermediate_value_Ioo' (by norm_num : (3 / 5 : ℝ) ≤ 5 / 8)
    entropyDifference_continuous.continuousOn h0
  exact ⟨p, hp, he⟩

noncomputable def alpha : ℝ := Classical.choose entropy_root_exists

lemma alpha_mem : alpha ∈ Ioo (3 / 5 : ℝ) (5 / 8 : ℝ) :=
  (Classical.choose_spec entropy_root_exists).1

lemma alpha_gt_three_fifths : (3 / 5 : ℝ) < alpha := alpha_mem.1

lemma alpha_lt_five_eighths : alpha < (5 / 8 : ℝ) := alpha_mem.2

lemma alpha_pos : 0 < alpha := by linarith [alpha_gt_three_fifths]

lemma alpha_lt_one : alpha < 1 := by linarith [alpha_lt_five_eighths]

lemma alpha_gt_half : (1 / 2 : ℝ) < alpha := by linarith [alpha_gt_three_fifths]

lemma alpha_equation : Real.binEntropy alpha = alpha * Real.log 3 := by
  have h := (Classical.choose_spec entropy_root_exists).2
  change entropyDifference alpha = 0 at h
  dsimp [entropyDifference] at h
  linarith

lemma alpha_unique {p : ℝ} (hp : p ∈ Icc (1 / 2 : ℝ) 1)
    (he : Real.binEntropy p = p * Real.log 3) : p = alpha := by
  have ha : alpha ∈ Icc (1 / 2 : ℝ) 1 := ⟨alpha_gt_half.le, alpha_lt_one.le⟩
  apply entropyDifference_strictAntiOn.injOn hp ha
  simp only [entropyDifference, he, alpha_equation, sub_self]

noncomputable def beta : ℝ := alpha * Real.log 3 / Real.log 2

noncomputable def entropySlope : ℝ := Real.log (1 - alpha) - Real.log alpha

noncomputable def entropyGap : ℝ := Real.log 3 - entropySlope

noncomputable def gamma : ℝ := Real.log 3 / (2 * entropyGap)

lemma beta_pos : 0 < beta := div_pos (mul_pos alpha_pos log_three_pos) log_two_pos

lemma beta_lt_one : beta < 1 := by
  rw [beta, div_lt_one log_two_pos, ← alpha_equation]
  apply Real.binEntropy_lt_log_two.mpr
  have h := alpha_gt_half
  norm_num at h ⊢
  linarith

lemma log_three_gt_nineteen_twelfths :
    (19 / 12 : ℝ) * Real.log 2 < Real.log 3 := by
  have h : Real.log ((2 : ℝ) ^ 19) < Real.log ((3 : ℝ) ^ 12) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  norm_num at h
  linarith

lemma beta_gt_nineteen_twentieths : (19 / 20 : ℝ) < beta := by
  rw [beta, lt_div_iff₀ log_two_pos]
  have h1 := mul_lt_mul_of_pos_right alpha_gt_three_fifths log_three_pos
  have h2 := log_three_gt_nineteen_twelfths
  nlinarith

lemma entropySlope_neg : entropySlope < 0 := by
  dsimp [entropySlope]
  apply sub_neg.mpr
  apply Real.log_lt_log (by linarith [alpha_lt_one])
  linarith [alpha_gt_half]

lemma entropyGap_pos : 0 < entropyGap := by
  dsimp [entropyGap]
  linarith [log_three_pos, entropySlope_neg]

lemma gamma_pos : 0 < gamma :=
  div_pos log_three_pos (mul_pos (by norm_num) entropyGap_pos)

lemma gamma_lt_half : gamma < (1 / 2 : ℝ) := by
  rw [gamma, div_lt_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) entropyGap_pos)]
  dsimp [entropyGap]
  linarith [entropySlope_neg]

lemma entropyGap_gt_two_log_two : 2 * Real.log 2 < entropyGap := by
  have ha : 0 < 1 - alpha := sub_pos.mpr alpha_lt_one
  have hq : (4 : ℝ) < 3 * alpha / (1 - alpha) := by
    apply (lt_div_iff₀ ha).mpr
    linarith [alpha_gt_three_fifths]
  have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 4) hq
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    convert (Real.log_pow (2 : ℝ) 2) using 1; norm_num
  rw [h4, Real.log_div (mul_ne_zero (by norm_num) (ne_of_gt alpha_pos)) (ne_of_gt ha),
    Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (ne_of_gt alpha_pos)] at h
  dsimp [entropyGap, entropySlope]
  linarith

lemma exp_neg_entropySlope_lt_five_thirds :
    Real.exp (-entropySlope) < (5 / 3 : ℝ) := by
  have ha : 0 < 1 - alpha := sub_pos.mpr alpha_lt_one
  rw [entropySlope, neg_sub, Real.exp_sub, Real.exp_log alpha_pos,
    Real.exp_log ha]
  apply (div_lt_iff₀ ha).mpr
  linarith [alpha_lt_five_eighths]

/-- A supporting-line bound, proved directly from `log x ≤ x - 1`. -/
lemma binEntropy_le_tangent {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q) (hq1 : q < 1) :
    Real.binEntropy p ≤ Real.binEntropy q +
      (Real.log (1 - q) - Real.log q) * (p - q) := by
  have hpa : 0 < 1 - p := sub_pos.mpr hp1
  have hqa : 0 < 1 - q := sub_pos.mpr hq1
  have h1 := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hq hp)) hp.le
  have h2 := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hqa hpa)) hpa.le
  rw [Real.log_div (ne_of_gt hq) (ne_of_gt hp)] at h1
  rw [Real.log_div (ne_of_gt hqa) (ne_of_gt hpa)] at h2
  have hc1 : p * (q / p - 1) = q - p := by
    field_simp [ne_of_gt hp]
  have hc2 : (1 - p) * ((1 - q) / (1 - p) - 1) = p - q := by
    field_simp [ne_of_gt hpa]
    ring
  rw [hc1] at h1
  rw [hc2] at h2
  simp only [Real.binEntropy, Real.log_inv]
  nlinarith

lemma binEntropy_le_alpha_tangent {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Real.binEntropy p ≤ alpha * Real.log 3 + entropySlope * (p - alpha) := by
  simpa only [alpha_equation, entropySlope] using
    (binEntropy_le_tangent hp hp1 alpha_pos alpha_lt_one)

lemma gamma_balance :
    -(1 / 2 : ℝ) - entropySlope / (2 * entropyGap) = -gamma := by
  have hd : entropyGap ≠ 0 := ne_of_gt entropyGap_pos
  rw [gamma]
  field_simp [hd]
  dsimp [entropyGap]
  ring

end CollatzEndpoint
