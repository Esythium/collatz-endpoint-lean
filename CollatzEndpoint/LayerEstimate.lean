import CollatzEndpoint.Entropy
import CollatzEndpoint.Counting
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum

/-!
# Analytic estimates for the Collatz layer sum

The factorial correction estimates below deliberately use only the global
Stirling bounds already in mathlib, rather than an unformalized version of
Robbins' remainder formula.
-/

namespace CollatzEndpoint

open scoped BigOperators
open Finset

noncomputable def factorialCorrection (n : ℕ) : ℝ :=
  Real.log (n.factorial : ℝ) - ((n : ℝ) + 1 / 2) * Real.log n + n

lemma factorialCorrection_eq {n : ℕ} (hn : n ≠ 0) :
    factorialCorrection n = Real.log (Stirling.stirlingSeq n) + Real.log 2 / 2 := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h := Stirling.log_stirlingSeq_formula n
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnR,
    Real.log_div hnR (ne_of_gt (Real.exp_pos 1)), Real.log_exp] at h
  dsimp [factorialCorrection]
  linarith

lemma factorialCorrection_le_one {n : ℕ} (hn : n ≠ 0) :
    factorialCorrection n ≤ 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hm := Stirling.stirlingSeq'_antitone (Nat.zero_le m)
  change Stirling.stirlingSeq (m + 1) ≤ Stirling.stirlingSeq 1 at hm
  have hl := Real.log_le_log (Stirling.stirlingSeq'_pos m) hm
  rw [Stirling.stirlingSeq_one, Real.log_div (ne_of_gt (Real.exp_pos 1))
    (by positivity), Real.log_exp, Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hl
  rw [factorialCorrection_eq (by omega)]
  linarith

lemma log_two_le_factorialCorrection {n : ℕ} (hn : n ≠ 0) :
    Real.log 2 ≤ factorialCorrection n := by
  have h := Stirling.le_log_factorial_stirling hn
  have hpi : Real.log 4 ≤ Real.log (2 * Real.pi) := by
    apply Real.log_le_log (by norm_num)
    nlinarith [Real.two_le_pi]
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    convert (Real.log_pow (2 : ℝ) 2) using 1; norm_num
  rw [h4] at hpi
  dsimp [factorialCorrection]
  linarith

lemma log_choose_eq_factorialCorrection {k t : ℕ} (ht : t ≤ k) :
    Real.log (k.choose t : ℝ) =
      factorialCorrection k - factorialCorrection t - factorialCorrection (k - t) +
      ((k : ℝ) + 1 / 2) * Real.log k -
      ((t : ℝ) + 1 / 2) * Real.log t -
      ((k - t : ℕ) + 1 / 2 : ℝ) * Real.log (k - t : ℕ) := by
  rw [Nat.cast_choose ℝ ht, Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)]
  dsimp [factorialCorrection]
  rw [Nat.cast_sub ht]
  ring

/-- A coarse global logarithmic bound with no numerical approximation. -/
lemma log_choose_le_stirling {k t : ℕ} (ht0 : 0 < t) (htk : t < k) :
    Real.log (k.choose t : ℝ) ≤
      1 - 2 * Real.log 2 +
      ((k : ℝ) + 1 / 2) * Real.log k -
      ((t : ℝ) + 1 / 2) * Real.log t -
      ((k - t : ℕ) + 1 / 2 : ℝ) * Real.log (k - t : ℕ) := by
  rw [log_choose_eq_factorialCorrection htk.le]
  have hk := factorialCorrection_le_one (show k ≠ 0 by omega)
  have ht := log_two_le_factorialCorrection (show t ≠ 0 by omega)
  have hkt := log_two_le_factorialCorrection (show k - t ≠ 0 by omega)
  linarith

lemma mul_binEntropy_div {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    y * Real.binEntropy (x / y) =
      y * Real.log y - x * Real.log x - (y - x) * Real.log (y - x) := by
  have hy : 0 < y := lt_trans hx hxy
  have hyx : 0 < y - x := sub_pos.mpr hxy
  have hc : 1 - x / y = (y - x) / y := by field_simp [ne_of_gt hy]
  rw [Real.binEntropy, hc]
  simp only [Real.log_inv]
  rw [Real.log_div (ne_of_gt hx) (ne_of_gt hy),
    Real.log_div (ne_of_gt hyx) (ne_of_gt hy)]
  field_simp [ne_of_gt hy]
  ring

lemma log_choose_le_entropy {k t : ℕ} (ht0 : 0 < t) (htk : t < k) :
    Real.log (k.choose t : ℝ) ≤
      (k : ℝ) * Real.binEntropy ((t : ℝ) / k) - Real.log k / 2 +
      (1 - 2 * Real.log 2 -
        Real.log (((t : ℝ) / k) * (1 - (t : ℝ) / k)) / 2) := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht0
  have htkR : (t : ℝ) < k := by exact_mod_cast htk
  have hkR : (0 : ℝ) < k := lt_trans htR htkR
  have hktR : (0 : ℝ) < (k : ℝ) - t := sub_pos.mpr htkR
  have hp : 0 < (t : ℝ) / k := div_pos htR hkR
  have hpa : 0 < 1 - (t : ℝ) / k := by
    apply sub_pos.mpr
    exact (div_lt_one hkR).mpr htkR
  have hc : 1 - (t : ℝ) / k = ((k : ℝ) - t) / k := by
    field_simp [ne_of_gt hkR]
  have h := log_choose_le_stirling ht0 htk
  rw [mul_binEntropy_div htR htkR,
    Real.log_mul (ne_of_gt hp) (ne_of_gt hpa), hc,
    Real.log_div (ne_of_gt htR) (ne_of_gt hkR),
    Real.log_div (ne_of_gt hktR) (ne_of_gt hkR)]
  rw [Nat.cast_sub htk.le] at h
  linarith

lemma entropy_prefactor_le_log_two {p : ℝ}
    (hp : (11 / 20 : ℝ) ≤ p) (hp' : p ≤ (5 / 8 : ℝ)) :
    1 - 2 * Real.log 2 - Real.log (p * (1 - p)) / 2 ≤ Real.log 2 := by
  have hprod : (1 / 5 : ℝ) ≤ p * (1 - p) := by
    have h := mul_nonneg (show 0 ≤ p - 3 / 8 by linarith)
      (show 0 ≤ 5 / 8 - p by linarith)
    nlinarith
  have hlprod := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 5) hprod
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (5 : ℝ) ≠ 0),
    Real.log_one, zero_sub] at hlprod
  have he := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
  rw [Real.log_exp] at he
  have hnum : Real.log ((3 : ℝ) ^ 2 * 5) < Real.log ((2 : ℝ) ^ 6) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow] at hnum
  norm_num at hnum
  linarith

lemma log_choose_le_entropy_uniform {k t : ℕ} (ht0 : 0 < t) (htk : t < k)
    (hp : (11 / 20 : ℝ) ≤ (t : ℝ) / k)
    (hp' : (t : ℝ) / k ≤ (5 / 8 : ℝ)) :
    Real.log (k.choose t : ℝ) ≤
      Real.log 2 - Real.log k / 2 + (k : ℝ) * Real.binEntropy ((t : ℝ) / k) := by
  have h := log_choose_le_entropy ht0 htk
  have hc := entropy_prefactor_le_log_two hp hp'
  linarith

noncomputable def cutoffDisplacement (k : ℕ) : ℝ :=
  Real.log k / (2 * entropyGap)

noncomputable def layerCutoff (k : ℕ) : ℕ :=
  ⌊alpha * k - cutoffDisplacement k⌋₊

lemma log_le_linear_of_ge_sixty_four {x : ℝ} (hx : 64 ≤ x) :
    Real.log x ≤ (3 / 32 : ℝ) * Real.log 2 * x := by
  have hx0 : 0 < x := by linarith
  have h64 : Real.log 64 = 6 * Real.log 2 := by
    convert (Real.log_pow (2 : ℝ) 6) using 1; norm_num
  have hlog64 : 1 < 6 * Real.log 2 := by
    have h := Real.log_lt_log (Real.exp_pos 1)
      (show Real.exp 1 < 64 by linarith [Real.exp_one_lt_three])
    rw [Real.log_exp, h64] at h
    exact h
  have h := Real.log_le_sub_one_of_pos (div_pos hx0 (by norm_num : (0 : ℝ) < 64))
  rw [Real.log_div (ne_of_gt hx0) (by norm_num : (64 : ℝ) ≠ 0), h64] at h
  have hm := mul_nonneg (show 0 ≤ x / 64 - 1 by linarith)
    (show 0 ≤ 6 * Real.log 2 - 1 by linarith)
  nlinarith

lemma cutoffDisplacement_nonneg {k : ℕ} (hk : 1 ≤ k) :
    0 ≤ cutoffDisplacement k := by
  apply div_nonneg
  · exact Real.log_nonneg (by exact_mod_cast hk)
  · exact (mul_pos (by norm_num) entropyGap_pos).le

lemma cutoffDisplacement_le {k : ℕ} (hk : 64 ≤ k) :
    cutoffDisplacement k ≤ (3 / 128 : ℝ) * k := by
  have hkR : (64 : ℝ) ≤ k := by exact_mod_cast hk
  have hlog := log_le_linear_of_ge_sixty_four hkR
  have hg := mul_le_mul_of_nonneg_left entropyGap_gt_two_log_two.le
    (show (0 : ℝ) ≤ (3 / 64 : ℝ) * k by positivity)
  rw [cutoffDisplacement, div_le_iff₀
    (mul_pos (by norm_num : (0 : ℝ) < 2) entropyGap_pos)]
  nlinarith

lemma cutoff_argument_pos {k : ℕ} (hk : 64 ≤ k) :
    0 < alpha * k - cutoffDisplacement k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have ha := mul_lt_mul_of_pos_right alpha_gt_three_fifths hk0
  have hd := cutoffDisplacement_le hk
  nlinarith

lemma layerCutoff_le_argument {k : ℕ} (hk : 64 ≤ k) :
    (layerCutoff k : ℝ) ≤ alpha * k - cutoffDisplacement k :=
  Nat.floor_le (cutoff_argument_pos hk).le

lemma argument_sub_one_lt_layerCutoff (k : ℕ) :
    alpha * k - cutoffDisplacement k - 1 < (layerCutoff k : ℝ) :=
  Nat.sub_one_lt_floor _

lemma layerCutoff_ratio_gt {k : ℕ} (hk : 64 ≤ k) :
    (11 / 20 : ℝ) < (layerCutoff k : ℝ) / k := by
  have hkR : (64 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have ha := mul_lt_mul_of_pos_right alpha_gt_three_fifths hk0
  have hd := cutoffDisplacement_le hk
  have ht := argument_sub_one_lt_layerCutoff k
  apply (lt_div_iff₀ hk0).mpr
  nlinarith

lemma layerCutoff_ratio_lt {k : ℕ} (hk : 64 ≤ k) :
    (layerCutoff k : ℝ) / k < (5 / 8 : ℝ) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have ha := mul_lt_mul_of_pos_right alpha_lt_five_eighths hk0
  have hd := cutoffDisplacement_nonneg (show 1 ≤ k by omega)
  have ht := layerCutoff_le_argument hk
  apply (div_lt_iff₀ hk0).mpr
  linarith

lemma layerCutoff_pos {k : ℕ} (hk : 64 ≤ k) : 0 < layerCutoff k := by
  have h := layerCutoff_ratio_gt hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hpos : (0 : ℝ) < layerCutoff k := by
    have h' := (lt_div_iff₀ hk0).mp h
    nlinarith
  exact_mod_cast hpos

lemma layerCutoff_lt {k : ℕ} (hk : 64 ≤ k) : layerCutoff k < k := by
  have h := layerCutoff_ratio_lt hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlt : (layerCutoff k : ℝ) < k := by
    have h' := (div_lt_iff₀ hk0).mp h
    linarith
  exact_mod_cast hlt

noncomputable def endpointScale (k : ℕ) : ℝ :=
  Real.exp (alpha * Real.log 3 * k - gamma * Real.log k)

lemma endpointScale_pos (k : ℕ) : 0 < endpointScale k := Real.exp_pos _

lemma endpointScale_eq {k : ℕ} (hk : 0 < k) :
    endpointScale k = (2 : ℝ) ^ (beta * k) * (k : ℝ) ^ (-gamma) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos hkR, ← Real.exp_add]
  unfold endpointScale
  congr 1
  dsimp [beta]
  field_simp [ne_of_gt log_two_pos]
  ring

lemma cutoffDisplacement_mul_log_three (k : ℕ) :
    cutoffDisplacement k * Real.log 3 = gamma * Real.log k := by
  dsimp [cutoffDisplacement, gamma]
  ring

lemma three_pow_layerCutoff_le {k : ℕ} (hk : 64 ≤ k) :
    (3 : ℝ) ^ layerCutoff k ≤ endpointScale k := by
  have h := mul_le_mul_of_nonneg_right (layerCutoff_le_argument hk) log_three_pos.le
  have he : (layerCutoff k : ℝ) * Real.log 3 ≤
      alpha * Real.log 3 * k - gamma * Real.log k := by
    rw [← cutoffDisplacement_mul_log_three k]
    nlinarith
  have hlog : Real.log ((3 : ℝ) ^ layerCutoff k) ≤
      alpha * Real.log 3 * k - gamma * Real.log k := by
    simpa only [Real.log_pow] using he
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (by positivity)] at hexp
  exact hexp

lemma log_choose_layerCutoff_le {k : ℕ} (hk : 64 ≤ k) :
    Real.log (k.choose (layerCutoff k) : ℝ) ≤
      Real.log 2 - entropySlope + alpha * Real.log 3 * k - gamma * Real.log k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hp0 : 0 < (layerCutoff k : ℝ) / k :=
    div_pos (by exact_mod_cast layerCutoff_pos hk) hkR
  have hp1 : (layerCutoff k : ℝ) / k < 1 := by
    linarith [layerCutoff_ratio_lt hk]
  have hb := log_choose_le_entropy_uniform (layerCutoff_pos hk) (layerCutoff_lt hk)
    (layerCutoff_ratio_gt hk).le (layerCutoff_ratio_lt hk).le
  have he := mul_le_mul_of_nonneg_left (binEntropy_le_alpha_tangent hp0 hp1) hkR.le
  have hcancel : (k : ℝ) * (alpha * Real.log 3 +
      entropySlope * ((layerCutoff k : ℝ) / k - alpha)) =
      alpha * Real.log 3 * k + entropySlope * ((layerCutoff k : ℝ) - alpha * k) := by
    field_simp [ne_of_gt hkR]
  rw [hcancel] at he
  have hf := mul_le_mul_of_nonpos_left
    (argument_sub_one_lt_layerCutoff k).le entropySlope_neg.le
  have hg : -(Real.log k / 2) - entropySlope * cutoffDisplacement k =
      -gamma * Real.log k := by
    calc
      _ = (-(1 / 2 : ℝ) - entropySlope / (2 * entropyGap)) * Real.log k := by
        dsimp [cutoffDisplacement]
        ring
      _ = _ := by rw [gamma_balance]
  nlinarith

lemma choose_layerCutoff_le {k : ℕ} (hk : 64 ≤ k) :
    (k.choose (layerCutoff k) : ℝ) ≤ (10 / 3 : ℝ) * endpointScale k := by
  have hchoose : (0 : ℝ) < k.choose (layerCutoff k) := by
    exact_mod_cast Nat.choose_pos (layerCutoff_lt hk).le
  have h := Real.exp_le_exp.mpr (log_choose_layerCutoff_le hk)
  rw [Real.exp_log hchoose] at h
  have he : Real.exp (Real.log 2 - entropySlope + alpha * Real.log 3 * k -
      gamma * Real.log k) = 2 * Real.exp (-entropySlope) * endpointScale k := by
    rw [show Real.log 2 - entropySlope + alpha * Real.log 3 * k - gamma * Real.log k =
      (Real.log 2 + -entropySlope) +
        (alpha * Real.log 3 * k - gamma * Real.log k) by ring,
      Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    rfl
  rw [he] at h
  have hc := mul_le_mul_of_nonneg_right exp_neg_entropySlope_lt_five_thirds.le
    (endpointScale_pos k).le
  nlinarith

lemma choose_succ_le_nine_elevenths {k j : ℕ}
    (hj : (11 / 20 : ℝ) * k ≤ j) :
    (k.choose (j + 1) : ℝ) ≤ (9 / 11 : ℝ) * (k.choose j : ℝ) := by
  by_cases hjk : j ≤ k
  · have hrec := Nat.choose_succ_right_eq k j
    have hrecR : (k.choose (j + 1) : ℝ) * ((j : ℝ) + 1) =
        (k.choose j : ℝ) * ((k : ℝ) - j) := by
      have h := congrArg (fun n : ℕ => (n : ℝ)) hrec
      push_cast [Nat.cast_sub hjk] at h
      exact h
    have hr : (k : ℝ) - j ≤ (9 / 11 : ℝ) * ((j : ℝ) + 1) := by linarith
    have hm := mul_le_mul_of_nonneg_left hr (show (0 : ℝ) ≤ k.choose j by positivity)
    have hjpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    apply (mul_le_mul_iff_left₀ hjpos).mp
    nlinarith
  · have hjk' : k < j := Nat.lt_of_not_ge hjk
    simp only [Nat.choose_eq_zero_of_lt hjk',
      Nat.choose_eq_zero_of_lt (show k < j + 1 by omega), Nat.cast_zero, mul_zero, le_refl]

lemma sum_tail_le_eleven_halves (f : ℕ → ℝ) (t : ℕ)
    (hpos : ∀ j, 0 ≤ f j)
    (hr : ∀ j, t ≤ j → f (j + 1) ≤ (9 / 11 : ℝ) * f j)
    (a n : ℕ) (ha : t ≤ a) :
    (∑ i ∈ range n, f (a + i)) ≤ (11 / 2 : ℝ) * f a := by
  induction n generalizing a with
  | zero =>
      simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 11 / 2) (hpos a)
  | succ n ih =>
      rw [sum_range_succ']
      simp only [Nat.add_zero]
      have hi := ih (a + 1) (show t ≤ a + 1 by omega)
      have hi' : (∑ i ∈ range n, f (a + (i + 1))) ≤ (11 / 2 : ℝ) * f (a + 1) := by
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hi
      have h := hr a ha
      linarith

lemma choose_tail_layerCutoff_le {k : ℕ} (hk : 64 ≤ k) (n : ℕ) :
    (∑ i ∈ range n, (k.choose (layerCutoff k + i) : ℝ)) ≤
      (11 / 2 : ℝ) * (k.choose (layerCutoff k) : ℝ) := by
  refine sum_tail_le_eleven_halves (fun j => (k.choose j : ℝ)) (layerCutoff k)
    (by intro j; positivity) ?_ (layerCutoff k) n le_rfl
  intro j hj
  apply choose_succ_le_nine_elevenths
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have ht := (lt_div_iff₀ hkR).mp (layerCutoff_ratio_gt hk)
  have hjR : (layerCutoff k : ℝ) ≤ j := by exact_mod_cast hj
  linarith

lemma sum_two_mul_three_pow (t : ℕ) :
    (∑ s ∈ range t, (2 : ℝ) * 3 ^ s) = 3 ^ t - 1 := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [sum_range_succ, ih, pow_succ]
      ring

lemma layerSum_le_two_pow (k : ℕ) : layerSum k ≤ 2 ^ k := by
  unfold layerSum
  calc
    _ ≤ ∑ s ∈ range (k + 1), k.choose s := by
      apply sum_le_sum
      intro s hs
      exact min_le_left _ _
    _ = 2 ^ k := Nat.sum_range_choose k

lemma layerSum_le_twenty_endpointScale {k : ℕ} (hk : 64 ≤ k) :
    (layerSum k : ℝ) ≤ 20 * endpointScale k := by
  let t := layerCutoff k
  let f : ℕ → ℝ := fun s => (min (k.choose s) (2 * 3 ^ s) : ℕ)
  have htk : t ≤ k + 1 := by dsimp [t]; have := layerCutoff_lt hk; omega
  have hs : (layerSum k : ℝ) =
      (∑ s ∈ range t, f s) + ∑ i ∈ range (k + 1 - t), f (t + i) := by
    have hh := sum_range_add (fun s => min (k.choose s) (2 * 3 ^ s)) t (k + 1 - t)
    rw [Nat.add_sub_of_le htk] at hh
    dsimp [layerSum, f]
    exact_mod_cast hh
  have hlo : (∑ s ∈ range t, f s) ≤ (3 : ℝ) ^ t - 1 := by
    rw [← sum_two_mul_three_pow]
    apply sum_le_sum
    intro s hs
    dsimp [f]
    exact_mod_cast min_le_right (k.choose s) (2 * 3 ^ s)
  have hhi : (∑ i ∈ range (k + 1 - t), f (t + i)) ≤
      (11 / 2 : ℝ) * (k.choose t : ℝ) := by
    calc
      _ ≤ ∑ i ∈ range (k + 1 - t), (k.choose (t + i) : ℝ) := by
        apply sum_le_sum
        intro i hi
        dsimp [f]
        exact_mod_cast min_le_left (k.choose (t + i)) (2 * 3 ^ (t + i))
      _ ≤ _ := choose_tail_layerCutoff_le hk _
  have hpow := three_pow_layerCutoff_le hk
  have hchoose := choose_layerCutoff_le hk
  have hscale := (endpointScale_pos k).le
  dsimp [t] at hs hlo hhi
  rw [hs]
  nlinarith

lemma two_pow_le_hundred_endpointScale {k : ℕ} (hk0 : 1 ≤ k) (hk : k ≤ 63) :
    (2 : ℝ) ^ k ≤ 100 * endpointScale k := by
  have hk0R : (1 : ℝ) ≤ k := by exact_mod_cast hk0
  have hkR : (k : ℝ) ≤ 63 := by exact_mod_cast hk
  have hlog0 : 0 ≤ Real.log k := Real.log_nonneg hk0R
  have hlog : Real.log k ≤ 6 * Real.log 2 := by
    have h := Real.log_le_log (by linarith : (0 : ℝ) < k)
      (show (k : ℝ) ≤ 64 by linarith)
    have h64 : Real.log 64 = 6 * Real.log 2 := by
      convert (Real.log_pow (2 : ℝ) 6) using 1; norm_num
    simpa only [h64] using h
  have hb : (19 / 20 : ℝ) * Real.log 2 < alpha * Real.log 3 := by
    exact (lt_div_iff₀ log_two_pos).mp beta_gt_nineteen_twentieths
  have hbk := mul_le_mul_of_nonneg_right hb.le (show (0 : ℝ) ≤ k by positivity)
  have hkk := mul_le_mul_of_nonneg_right hkR log_two_pos.le
  have hg := mul_le_mul_of_nonneg_right gamma_lt_half.le hlog0
  have hc : 13 * Real.log 2 < 2 * Real.log 100 := by
    have h : Real.log ((2 : ℝ) ^ 13) < Real.log ((100 : ℝ) ^ 2) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hle : (k : ℝ) * Real.log 2 ≤
      Real.log 100 + (alpha * Real.log 3 * k - gamma * Real.log k) := by
    nlinarith [log_two_pos]
  apply (Real.log_le_log_iff (by positivity)
    (mul_pos (by norm_num : (0 : ℝ) < 100) (endpointScale_pos k))).mp
  rw [Real.log_pow, Real.log_mul (by norm_num : (100 : ℝ) ≠ 0)
    (ne_of_gt (endpointScale_pos k)), endpointScale, Real.log_exp]
  exact hle

/-- The endpoint layer estimate, including the explicit constant in the paper. -/
theorem layerSum_le {k : ℕ} (hk : 1 ≤ k) :
    (layerSum k : ℝ) ≤ 100 * (2 : ℝ) ^ (beta * k) * (k : ℝ) ^ (-gamma) := by
  have h : (layerSum k : ℝ) ≤ 100 * endpointScale k := by
    by_cases hk64 : 64 ≤ k
    · have hh := layerSum_le_twenty_endpointScale hk64
      nlinarith [endpointScale_pos k]
    · have hh : (layerSum k : ℝ) ≤ (2 : ℝ) ^ k := by
        exact_mod_cast layerSum_le_two_pow k
      exact hh.trans (two_pow_le_hundred_endpointScale hk (by omega))
  rw [endpointScale_eq (by omega : 0 < k)] at h
  simpa only [mul_assoc] using h

end CollatzEndpoint
