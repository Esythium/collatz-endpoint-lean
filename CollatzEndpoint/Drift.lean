import CollatzEndpoint.OrbitGrowth
import CollatzEndpoint.Parity
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.Order.LiminfLimsup

/-!
# Exact multiplicative drift identities

These identities apply to any positive integer sequence satisfying the odd
Collatz recurrence.  The generic results take summability as an explicit
hypothesis; the main results supply it from the orbit counting bound.
-/

namespace CollatzEndpoint

open Finset Filter
open scoped BigOperators Topology

def valuationSum (a : ℕ → ℕ) (n : ℕ) : ℕ := ∑ j ∈ range n, a j

noncomputable def driftSequence (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (n : ℝ) * Real.logb 2 3 - valuationSum a n

noncomputable def correctionProduct (y : ℕ → ℕ) (n : ℕ) : ℝ :=
  ∏ j ∈ range n, (1 + 1 / (3 * (y j : ℝ)))

@[simp] theorem valuationSum_zero (a : ℕ → ℕ) : valuationSum a 0 = 0 := by
  simp [valuationSum]

@[simp] theorem valuationSum_succ (a : ℕ → ℕ) (n : ℕ) :
    valuationSum a (n + 1) = valuationSum a n + a n := by
  simp [valuationSum, Finset.sum_range_succ]

@[simp] theorem correctionProduct_zero (y : ℕ → ℕ) : correctionProduct y 0 = 1 := by
  simp [correctionProduct]

theorem correctionProduct_succ (y : ℕ → ℕ) (n : ℕ) :
    correctionProduct y (n + 1) =
      correctionProduct y n * (1 + 1 / (3 * (y n : ℝ))) := by
  simp [correctionProduct, Finset.prod_range_succ]

theorem one_le_correctionProduct (y : ℕ → ℕ) (n : ℕ) :
    1 ≤ correctionProduct y n := by
  apply Finset.one_le_prod₀
  intro j _
  have h : (0 : ℝ) ≤ 1 / (3 * (y j : ℝ)) := by positivity
  linarith

theorem correctionProduct_le_exp_tsum (y : ℕ → ℕ)
    (hsum : Summable (fun j => 1 / (3 * (y j : ℝ)))) (n : ℕ) :
    correctionProduct y n ≤ Real.exp (∑' j, 1 / (3 * (y j : ℝ))) := by
  have hnonneg : ∀ j, (0 : ℝ) ≤ 1 / (3 * (y j : ℝ)) := by
    intro j
    positivity
  calc
    correctionProduct y n ≤ Real.exp (∑ j ∈ range n, 1 / (3 * (y j : ℝ))) :=
      Real.prod_one_add_le_exp_sum (range n) hnonneg
    _ ≤ Real.exp (∑' j, 1 / (3 * (y j : ℝ))) :=
      Real.exp_le_exp.mpr (Summable.sum_le_tsum (range n) (fun j _ => hnonneg j) hsum)

theorem correctionProduct_mono (y : ℕ → ℕ) : Monotone (correctionProduct y) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [correctionProduct_succ]
  have hQ : 0 ≤ correctionProduct y n := (by norm_num : (0 : ℝ) ≤ 1).trans
    (one_le_correctionProduct y n)
  have hfactor : 1 ≤ 1 + 1 / (3 * (y n : ℝ)) := by
    have : (0 : ℝ) ≤ 1 / (3 * (y n : ℝ)) := by positivity
    linarith
  exact le_mul_of_one_le_right hQ hfactor

theorem correctionProduct_converges (y : ℕ → ℕ)
    (hsum : Summable (fun j => 1 / (3 * (y j : ℝ)))) :
    ∃ Q : ℝ, 1 ≤ Q ∧ Q ≤ Real.exp (∑' j, 1 / (3 * (y j : ℝ))) ∧
      Tendsto (correctionProduct y) atTop (𝓝 Q) := by
  have hbdd : BddAbove (Set.range (correctionProduct y)) :=
    ⟨Real.exp (∑' j, 1 / (3 * (y j : ℝ))), by
      rintro _ ⟨n, rfl⟩
      exact correctionProduct_le_exp_tsum y hsum n⟩
  refine ⟨⨆ n, correctionProduct y n, ?_, ?_, ?_⟩
  · simpa only [correctionProduct_zero] using (le_ciSup hbdd 0)
  · exact ciSup_le (correctionProduct_le_exp_tsum y hsum)
  · exact tendsto_atTop_ciSup (correctionProduct_mono y) hbdd

theorem odd_recurrence_product_identity {y a : ℕ → ℕ}
    (hpos : ∀ n, 0 < y n)
    (hrec : ∀ n, (y (n + 1) : ℝ) = (3 * (y n : ℝ) + 1) / (2 : ℝ) ^ a n)
    (n : ℕ) :
    (y n : ℝ) = (y 0 : ℝ) * (3 : ℝ) ^ n / (2 : ℝ) ^ valuationSum a n *
      correctionProduct y n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hyn : (y n : ℝ) ≠ 0 := by exact_mod_cast (hpos n).ne'
    have htwo : (2 : ℝ) ^ a n ≠ 0 := pow_ne_zero _ (by norm_num)
    have hsumtwo : (2 : ℝ) ^ valuationSum a n ≠ 0 := pow_ne_zero _ (by norm_num)
    calc
      (y (n + 1) : ℝ) =
          (y n : ℝ) * (3 / (2 : ℝ) ^ a n) * (1 + 1 / (3 * (y n : ℝ))) := by
        rw [hrec n]
        field_simp
      _ = ((y 0 : ℝ) * (3 : ℝ) ^ n / (2 : ℝ) ^ valuationSum a n *
          correctionProduct y n) * (3 / (2 : ℝ) ^ a n) *
          (1 + 1 / (3 * (y n : ℝ))) := by rw [ih]
      _ = (y 0 : ℝ) * (3 : ℝ) ^ (n + 1) / (2 : ℝ) ^ valuationSum a (n + 1) *
          correctionProduct y (n + 1) := by
        rw [valuationSum_succ, correctionProduct_succ, pow_succ, pow_add]
        field_simp

theorem two_rpow_driftSequence (a : ℕ → ℕ) (n : ℕ) :
    (2 : ℝ) ^ driftSequence a n = (3 : ℝ) ^ n / (2 : ℝ) ^ valuationSum a n := by
  unfold driftSequence
  rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2),
    mul_comm (n : ℝ) (Real.logb 2 3), Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
      (by norm_num : (0 : ℝ) < 3), Real.rpow_natCast, Real.rpow_natCast]

theorem odd_recurrence_drift_identity {y a : ℕ → ℕ}
    (hpos : ∀ n, 0 < y n)
    (hrec : ∀ n, (y (n + 1) : ℝ) = (3 * (y n : ℝ) + 1) / (2 : ℝ) ^ a n)
    (n : ℕ) :
    (y n : ℝ) = (y 0 : ℝ) * (2 : ℝ) ^ driftSequence a n * correctionProduct y n := by
  rw [two_rpow_driftSequence]
  simpa only [mul_div_assoc] using odd_recurrence_product_identity hpos hrec n

theorem odd_recurrence_le_drift {y a : ℕ → ℕ}
    (hpos : ∀ n, 0 < y n)
    (hrec : ∀ n, (y (n + 1) : ℝ) = (3 * (y n : ℝ) + 1) / (2 : ℝ) ^ a n)
    (hsum : Summable (fun j => 1 / (3 * (y j : ℝ)))) (n : ℕ) :
    (y n : ℝ) ≤ ((y 0 : ℝ) * Real.exp (∑' j, 1 / (3 * (y j : ℝ)))) *
      (2 : ℝ) ^ driftSequence a n := by
  calc
    (y n : ℝ) = (y 0 : ℝ) * (2 : ℝ) ^ driftSequence a n * correctionProduct y n :=
      odd_recurrence_drift_identity hpos hrec n
    _ ≤ (y 0 : ℝ) * (2 : ℝ) ^ driftSequence a n *
        Real.exp (∑' j, 1 / (3 * (y j : ℝ))) :=
      mul_le_mul_of_nonneg_left (correctionProduct_le_exp_tsum y hsum n) (by positivity)
    _ = _ := by ring

theorem two_rpow_log_scale (p c B : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    (2 : ℝ) ^ (p * Real.logb 2 n + c * Real.logb 2 (Real.logb 2 n) + B) =
      powerLogScale p c n * (2 : ℝ) ^ B := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlpos : 0 < Real.logb 2 n := zero_lt_one.trans_le (one_le_logb_nat hn)
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have hp : (2 : ℝ) ^ (p * Real.logb 2 n) = (n : ℝ) ^ p := by
    rw [mul_comm p, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_logb (by norm_num) (by norm_num) hnpos]
  have hc : (2 : ℝ) ^ (c * Real.logb 2 (Real.logb 2 n)) = (Real.logb 2 n) ^ c := by
    rw [mul_comm c, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_logb (by norm_num) (by norm_num) hlpos]
  rw [hp, hc]
  rfl

/-- An upper drift envelope gives the corresponding power-log orbit envelope. -/
theorem isBigO_of_drift_upper {y a : ℕ → ℕ} {p c B : ℝ}
    (hpos : ∀ n, 0 < y n)
    (hrec : ∀ n, (y (n + 1) : ℝ) = (3 * (y n : ℝ) + 1) / (2 : ℝ) ^ a n)
    (hsum : Summable (fun j => 1 / (3 * (y j : ℝ))))
    (hupper : ∀ᶠ n in atTop, driftSequence a n ≤
      p * Real.logb 2 n + c * Real.logb 2 (Real.logb 2 n) + B) :
    Asymptotics.IsBigO atTop (fun n => (y n : ℝ)) (powerLogScale p c) := by
  let Q := Real.exp (∑' j, 1 / (3 * (y j : ℝ)))
  let C := (y 0 : ℝ) * Q * (2 : ℝ) ^ B
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [hupper, eventually_ge_atTop 2] with n hn hn2
  have hpow : (2 : ℝ) ^ driftSequence a n ≤ powerLogScale p c n * (2 : ℝ) ^ B := by
    rw [← two_rpow_log_scale p c B hn2]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hn
  have hresult : (y n : ℝ) ≤ C * powerLogScale p c n := by
    calc
      (y n : ℝ) ≤ ((y 0 : ℝ) * Q) * (2 : ℝ) ^ driftSequence a n :=
        odd_recurrence_le_drift hpos hrec hsum n
      _ ≤ ((y 0 : ℝ) * Q) * (powerLogScale p c n * (2 : ℝ) ^ B) :=
        mul_le_mul_of_nonneg_left hpow (by dsimp [Q]; positivity)
      _ = C * powerLogScale p c n := by dsimp [C]; ring
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (show (0 : ℝ) ≤ (y n : ℝ) from Nat.cast_nonneg _),
    abs_of_nonneg (powerLogScale_nonneg p c hn2)] using hresult

theorem not_drift_upper_of_prefixMax_lower {y a : ℕ → ℕ} {K p r c B : ℝ}
    (hpos : ∀ n, 0 < y n)
    (hrec : ∀ n, (y (n + 1) : ℝ) = (3 * (y n : ℝ) + 1) / (2 : ℝ) ^ a n)
    (hsum : Summable (fun j => 1 / (3 * (y j : ℝ))))
    (hK : 0 < K) (hp : 0 ≤ p) (hr : 0 < r) (hc : c < r)
    (hlower : ∀ N, 2 ≤ N → K * powerLogScale p r N ≤ (prefixMax y N : ℝ)) :
    ¬ (∀ᶠ n in atTop, driftSequence a n ≤
      p * Real.logb 2 n + c * Real.logb 2 (Real.logb 2 n) + B) := by
  intro hupper
  exact not_isBigO_of_prefixMax_lower hK hp hr hc hlower
    (isBigO_of_drift_upper hpos hrec hsum hupper)

noncomputable def normalizedDrift (a : ℕ → ℕ) (p : ℝ) (n : ℕ) : ℝ :=
  (driftSequence a n - p * Real.logb 2 n) / Real.logb 2 (Real.logb 2 n)

theorem frequently_lt_normalizedDrift {y a : ℕ → ℕ} {K p r c : ℝ}
    (hpos : ∀ n, 0 < y n)
    (hrec : ∀ n, (y (n + 1) : ℝ) = (3 * (y n : ℝ) + 1) / (2 : ℝ) ^ a n)
    (hsum : Summable (fun j => 1 / (3 * (y j : ℝ))))
    (hK : 0 < K) (hp : 0 ≤ p) (hr : 0 < r) (hc : c < r)
    (hlower : ∀ N, 2 ≤ N → K * powerLogScale p r N ≤ (prefixMax y N : ℝ)) :
    ∃ᶠ n in atTop, c < normalizedDrift a p n := by
  by_contra hfreq
  have hsmall := Filter.not_frequently.mp hfreq
  apply not_drift_upper_of_prefixMax_lower hpos hrec hsum hK hp hr hc hlower (B := 0)
  filter_upwards [hsmall, eventually_ge_atTop 3] with n hn hn3
  have hn2 : (2 : ℝ) < n := by exact_mod_cast (show 2 < n by omega)
  have hlog : 1 < Real.logb 2 n := by
    have h := Real.logb_lt_logb (b := (2 : ℝ)) (by norm_num)
      (by norm_num : (0 : ℝ) < 2) hn2
    simpa using h
  have hloglog : 0 < Real.logb 2 (Real.logb 2 n) := Real.logb_pos (by norm_num) hlog
  have hratio := (div_le_iff₀ hloglog).mp (not_lt.mp hn)
  change driftSequence a n - p * Real.logb 2 n ≤
    c * Real.logb 2 (Real.logb 2 n) at hratio
  linarith

/-- The extended-real formulation remains correct even when the limsup is infinite. -/
theorem le_limsup_normalizedDrift {y a : ℕ → ℕ} {K p r : ℝ}
    (hpos : ∀ n, 0 < y n)
    (hrec : ∀ n, (y (n + 1) : ℝ) = (3 * (y n : ℝ) + 1) / (2 : ℝ) ^ a n)
    (hsum : Summable (fun j => 1 / (3 * (y j : ℝ))))
    (hK : 0 < K) (hp : 0 ≤ p) (hr : 0 < r)
    (hlower : ∀ N, 2 ≤ N → K * powerLogScale p r N ≤ (prefixMax y N : ℝ)) :
    (r : EReal) ≤ Filter.limsup (fun n => (normalizedDrift a p n : EReal)) atTop := by
  by_contra hle
  obtain ⟨c, hcL, hcr⟩ := EReal.exists_between_coe_real (lt_of_not_ge hle)
  have hc : c < r := by exact_mod_cast hcr
  have hfreq := frequently_lt_normalizedDrift hpos hrec hsum hK hp hr hc hlower
  have hfreq' : ∃ᶠ n in atTop, (c : EReal) ≤ (normalizedDrift a p n : EReal) :=
    hfreq.mono (fun n hn => by exact_mod_cast hn.le)
  exact (not_le_of_gt hcL) (Filter.le_limsup_of_frequently_le hfreq')

/-- The exact number of powers of two removed in an odd Collatz transition. -/
def oddValuation (n : ℕ) : ℕ := padicValNat 2 (3 * n + 1)

def oddStep (n : ℕ) : ℕ := (3 * n + 1) / 2 ^ oddValuation n

def oddOrbit (n k : ℕ) : ℕ := oddStep^[k] n

@[simp] theorem oddOrbit_zero (n : ℕ) : oddOrbit n 0 = n := rfl

theorem oddOrbit_succ (n k : ℕ) : oddOrbit n (k + 1) = oddStep (oddOrbit n k) := by
  exact Function.iterate_succ_apply' oddStep k n

theorem oddStep_pow_identity (n : ℕ) : 2 ^ oddValuation n * oddStep n = 3 * n + 1 := by
  exact Nat.mul_div_cancel' pow_padicValNat_dvd

theorem oddStep_pos (n : ℕ) : 0 < oddStep n := by
  have h := oddStep_pow_identity n
  by_contra hn
  have hz : oddStep n = 0 := by omega
  rw [hz, mul_zero] at h
  omega

theorem oddStep_mod_two (n : ℕ) : oddStep n % 2 = 1 := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnot : ¬ 2 ∣ oddStep n := by
    intro hdiv
    obtain ⟨k, hk⟩ := hdiv
    apply pow_succ_padicValNat_not_dvd (p := 2) (n := 3 * n + 1) (by omega)
    refine ⟨k, ?_⟩
    calc
      3 * n + 1 = 2 ^ oddValuation n * oddStep n := (oddStep_pow_identity n).symm
      _ = 2 ^ (padicValNat 2 (3 * n + 1) + 1) * k := by
        rw [hk, pow_succ]
        dsimp [oddValuation]
        ring
  have hrem := Nat.mod_lt (oddStep n) (by omega : 0 < 2)
  have hne : oddStep n % 2 ≠ 0 := fun h => hnot (Nat.dvd_iff_mod_eq_zero.mpr h)
  omega

theorem oddValuation_pos {n : ℕ} (hn : n % 2 = 1) : 0 < oddValuation n := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply one_le_padicValNat_of_dvd (by omega : 3 * n + 1 ≠ 0)
  apply Nat.dvd_iff_mod_eq_zero.mpr
  omega

theorem step_double (n : ℕ) : step (2 * n) = n := by
  simp [step, Nat.mul_comm]

theorem orbit_two_pow_mul (k n : ℕ) : orbit (2 ^ k * n) k = n := by
  induction k with
  | zero => simp
  | succ k ih =>
    have heq : 2 ^ (k + 1) * n = 2 * (2 ^ k * n) := by rw [pow_succ]; ring
    rw [heq, orbit_succ, step_double]
    exact ih

theorem oddStep_eq_orbit {n : ℕ} (hn : n % 2 = 1) :
    orbit n (oddValuation n) = oddStep n := by
  have ha : 1 ≤ oddValuation n := oddValuation_pos hn
  have hp : 2 * step n = 3 * n + 1 := step_odd_identity (by omega)
  have hfactor : 3 * n + 1 = 2 * (2 ^ (oddValuation n - 1) * oddStep n) := by
    calc
      3 * n + 1 = 2 ^ oddValuation n * oddStep n := (oddStep_pow_identity n).symm
      _ = 2 ^ ((oddValuation n - 1) + 1) * oddStep n := by rw [Nat.sub_add_cancel ha]
      _ = 2 * (2 ^ (oddValuation n - 1) * oddStep n) := by rw [pow_succ]; ring
  have hs : step n = 2 ^ (oddValuation n - 1) * oddStep n := by omega
  calc
    orbit n (oddValuation n) = orbit n ((oddValuation n - 1) + 1) := by
      rw [Nat.sub_add_cancel ha]
    _ = orbit (step n) (oddValuation n - 1) := orbit_succ n _
    _ = oddStep n := by rw [hs, orbit_two_pow_mul]

theorem oddOrbit_pos {n : ℕ} (hn : 0 < n) (k : ℕ) : 0 < oddOrbit n k := by
  cases k with
  | zero => simpa using hn
  | succ k => rw [oddOrbit_succ]; exact oddStep_pos _

theorem oddOrbit_mod_two {n : ℕ} (hn : n % 2 = 1) (k : ℕ) : oddOrbit n k % 2 = 1 := by
  cases k with
  | zero => simpa using hn
  | succ k => rw [oddOrbit_succ]; exact oddStep_mod_two _

def oddTimes (n k : ℕ) : ℕ := valuationSum (fun j => oddValuation (oddOrbit n j)) k

theorem oddTimes_strictMono {n : ℕ} (hn : n % 2 = 1) : StrictMono (oddTimes n) := by
  apply strictMono_nat_of_lt_succ
  intro k
  change valuationSum _ k < valuationSum _ (k + 1)
  rw [valuationSum_succ]
  exact Nat.lt_add_of_pos_right (oddValuation_pos (oddOrbit_mod_two hn k))

theorem oddOrbit_eq_orbit {n : ℕ} (hn : n % 2 = 1) (k : ℕ) :
    oddOrbit n k = orbit n (oddTimes n k) := by
  induction k with
  | zero => simp [oddTimes]
  | succ k ih =>
    have htime : oddTimes n (k + 1) = oddTimes n k + oddValuation (oddOrbit n k) := by
      exact valuationSum_succ _ k
    rw [htime, add_comm (oddTimes n k), orbit, Function.iterate_add_apply]
    change oddOrbit n (k + 1) = orbit (orbit n (oddTimes n k)) (oddValuation (oddOrbit n k))
    rw [← ih, oddStep_eq_orbit (oddOrbit_mod_two hn k), oddOrbit_succ]

theorem oddOrbit_mem_range {n : ℕ} (hn : n % 2 = 1) (k : ℕ) :
    oddOrbit n k ∈ Set.range (orbit n) :=
  ⟨oddTimes n k, (oddOrbit_eq_orbit hn k).symm⟩

theorem oddOrbit_injective {n : ℕ} (hn : n % 2 = 1)
    (hinj : Function.Injective (orbit n)) : Function.Injective (oddOrbit n) := by
  intro i j hij
  apply (oddTimes_strictMono hn).injective
  apply hinj
  simpa only [← oddOrbit_eq_orbit hn] using hij

theorem oddOrbit_recurrence (n k : ℕ) :
    (oddOrbit n (k + 1) : ℝ) =
      (3 * (oddOrbit n k : ℝ) + 1) / (2 : ℝ) ^ oddValuation (oddOrbit n k) := by
  rw [oddOrbit_succ]
  apply (eq_div_iff (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))).mpr
  have h := oddStep_pow_identity (oddOrbit n k)
  exact_mod_cast (by simpa only [mul_comm] using h)

/-- Remove the initial even segment before starting the successive odd iterates. -/
def firstOdd (n : ℕ) : ℕ := n / 2 ^ padicValNat 2 n

theorem firstOdd_pow_identity (n : ℕ) : 2 ^ padicValNat 2 n * firstOdd n = n := by
  exact Nat.mul_div_cancel' pow_padicValNat_dvd

theorem firstOdd_eq_orbit (n : ℕ) : firstOdd n = orbit n (padicValNat 2 n) := by
  calc
    firstOdd n = orbit (2 ^ padicValNat 2 n * firstOdd n) (padicValNat 2 n) :=
      (orbit_two_pow_mul _ _).symm
    _ = orbit n (padicValNat 2 n) := by rw [firstOdd_pow_identity]

theorem firstOdd_pos {n : ℕ} (hn : 0 < n) : 0 < firstOdd n := by
  rw [firstOdd_eq_orbit]
  exact orbit_pos hn _

theorem firstOdd_mod_two {n : ℕ} (hn : 0 < n) : firstOdd n % 2 = 1 := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnot : ¬ 2 ∣ firstOdd n := by
    rintro ⟨k, hk⟩
    apply pow_succ_padicValNat_not_dvd (p := 2) hn.ne'
    refine ⟨k, ?_⟩
    calc
      n = 2 ^ padicValNat 2 n * firstOdd n := (firstOdd_pow_identity n).symm
      _ = 2 ^ (padicValNat 2 n + 1) * k := by rw [hk, pow_succ]; ring
  have hrem := Nat.mod_lt (firstOdd n) (by omega : 0 < 2)
  have hne : firstOdd n % 2 ≠ 0 := fun h => hnot (Nat.dvd_iff_mod_eq_zero.mpr h)
  omega

def successiveOddOrbit (n k : ℕ) : ℕ := oddOrbit (firstOdd n) k

def successiveOddTimes (n k : ℕ) : ℕ := padicValNat 2 n + oddTimes (firstOdd n) k

theorem successiveOddOrbit_pos {n : ℕ} (hn : 0 < n) (k : ℕ) :
    0 < successiveOddOrbit n k := oddOrbit_pos (firstOdd_pos hn) k

theorem successiveOddOrbit_mod_two {n : ℕ} (hn : 0 < n) (k : ℕ) :
    successiveOddOrbit n k % 2 = 1 := oddOrbit_mod_two (firstOdd_mod_two hn) k

theorem successiveOddTimes_strictMono {n : ℕ} (hn : 0 < n) :
    StrictMono (successiveOddTimes n) := by
  intro i j hij
  exact Nat.add_lt_add_left (oddTimes_strictMono (firstOdd_mod_two hn) hij) _

theorem successiveOddOrbit_eq_orbit {n : ℕ} (hn : 0 < n) (k : ℕ) :
    successiveOddOrbit n k = orbit n (successiveOddTimes n k) := by
  calc
    successiveOddOrbit n k = orbit (firstOdd n) (oddTimes (firstOdd n) k) :=
      oddOrbit_eq_orbit (firstOdd_mod_two hn) k
    _ = orbit (orbit n (padicValNat 2 n)) (oddTimes (firstOdd n) k) := by
      congr 1
      exact firstOdd_eq_orbit n
    _ = orbit n (successiveOddTimes n k) := by
      unfold orbit successiveOddTimes
      rw [add_comm, Function.iterate_add_apply]

theorem successiveOddOrbit_mem_range {n : ℕ} (hn : 0 < n) (k : ℕ) :
    successiveOddOrbit n k ∈ Set.range (orbit n) :=
  ⟨successiveOddTimes n k, (successiveOddOrbit_eq_orbit hn k).symm⟩

theorem successiveOddOrbit_injective {n : ℕ} (hn : 0 < n)
    (hinj : Function.Injective (orbit n)) : Function.Injective (successiveOddOrbit n) := by
  intro i j hij
  apply (successiveOddTimes_strictMono hn).injective
  apply hinj
  simpa only [← successiveOddOrbit_eq_orbit hn] using hij

theorem successiveOddOrbit_recurrence (n k : ℕ) :
    (successiveOddOrbit n (k + 1) : ℝ) =
      (3 * (successiveOddOrbit n k : ℝ) + 1) /
        (2 : ℝ) ^ oddValuation (successiveOddOrbit n k) :=
  oddOrbit_recurrence (firstOdd n) k

end CollatzEndpoint
