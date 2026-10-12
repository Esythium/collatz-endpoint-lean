import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Growth consequences of an initial-interval counting bound

The lemmas in this file first isolate facts about arbitrary injective positive
integer sequences.  The counting hypothesis remains explicit until the proved
Collatz window theorem is substituted by the integration module.
-/

namespace CollatzEndpoint

open Finset Filter
open scoped Topology

def prefixValues (z : ℕ → ℕ) (N : ℕ) : Finset ℕ := (range N).image z

def prefixMax (z : ℕ → ℕ) (N : ℕ) : ℕ := (range N).sup z

theorem mem_prefixValues {z : ℕ → ℕ} {N x : ℕ} :
    x ∈ prefixValues z N ↔ ∃ n < N, z n = x := by
  simp [prefixValues]

theorem card_prefixValues {z : ℕ → ℕ} (hz : Function.Injective z) (N : ℕ) :
    (prefixValues z N).card = N := by
  simp only [prefixValues, Finset.card_image_of_injective _ hz, Finset.card_range]

theorem le_prefixMax {z : ℕ → ℕ} {n N : ℕ} (hn : n < N) :
    z n ≤ prefixMax z N :=
  Finset.le_sup (Finset.mem_range.mpr hn)

theorem prefixMax_le_iff {z : ℕ → ℕ} {N M : ℕ} :
    prefixMax z N ≤ M ↔ ∀ n < N, z n ≤ M := by
  simp [prefixMax, Finset.sup_le_iff]

theorem prefixMax_mono (z : ℕ → ℕ) : Monotone (prefixMax z) := by
  intro N M hNM
  apply prefixMax_le_iff.mpr
  intro n hn
  exact le_prefixMax (lt_of_lt_of_le hn hNM)

theorem prefixMax_eq_term (z : ℕ → ℕ) {N : ℕ} (hN : 0 < N) :
    ∃ n < N, prefixMax z N = z n := by
  obtain ⟨n, hn, heq⟩ := Finset.exists_mem_eq_sup (range N)
    ⟨0, Finset.mem_range.mpr hN⟩ z
  exact ⟨n, Finset.mem_range.mp hn, heq⟩

/-- A pointwise eventual bound transfers to prefix maxima for an eventually
monotone comparison function bounded below by one. -/
theorem prefixMax_bound_of_eventual_bound {z : ℕ → ℕ} {F : ℕ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hone : ∀ n, 2 ≤ n → 1 ≤ F n)
    (hmono : ∀ i j, 2 ≤ i → i ≤ j → F i ≤ F j)
    (hbound : ∀ᶠ n in atTop, (z n : ℝ) ≤ C * F n) :
    ∃ D > 0, ∀ N, 2 ≤ N → (prefixMax z N : ℝ) ≤ D * F N := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp hbound
  let M := max K 2
  let D : ℝ := (prefixMax z M : ℝ) + C + 1
  have hMnonneg : (0 : ℝ) ≤ prefixMax z M := Nat.cast_nonneg _
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro N hN
  obtain ⟨n, hn, heq⟩ := prefixMax_eq_term z (by omega : 0 < N)
  rw [heq]
  by_cases hsmall : n < M
  · have hzle : (z n : ℝ) ≤ (prefixMax z M : ℝ) := by
      exact_mod_cast le_prefixMax hsmall
    have hMD : (prefixMax z M : ℝ) ≤ D := by dsimp [D]; linarith
    exact hzle.trans (hMD.trans (le_mul_of_one_le_right hD.le (hone N hN)))
  · have hnK : K ≤ n := le_trans (le_max_left _ _) (Nat.le_of_not_gt hsmall)
    have hn2 : 2 ≤ n := le_trans (le_max_right _ _) (Nat.le_of_not_gt hsmall)
    have hCD : C ≤ D := by dsimp [D]; linarith
    calc
      (z n : ℝ) ≤ C * F n := hK n hnK
      _ ≤ C * F N := mul_le_mul_of_nonneg_left (hmono n N hn2 hn.le) hC
      _ ≤ D * F N := mul_le_mul_of_nonneg_right hCD (zero_le_one.trans (hone N hN))

theorem prefixValues_subset_Icc {z : ℕ → ℕ} (hz : ∀ n, 0 < z n) (N : ℕ) :
    prefixValues z N ⊆ Icc 1 (prefixMax z N) := by
  intro x hx
  obtain ⟨n, hn, rfl⟩ := mem_prefixValues.mp hx
  exact Finset.mem_Icc.mpr ⟨hz n, le_prefixMax hn⟩

theorem length_le_prefixMax {z : ℕ → ℕ} (hinj : Function.Injective z)
    (hpos : ∀ n, 0 < z n) (N : ℕ) : N ≤ prefixMax z N := by
  have h := Finset.card_le_card (prefixValues_subset_Icc hpos N)
  simpa only [card_prefixValues hinj, Nat.card_Icc, Nat.add_sub_cancel] using h

/-- A finite-subset formulation of an initial-interval counting estimate. -/
def InitialCountingBound (A : Set ℕ) (F : ℕ → ℝ) : Prop :=
  ∀ X, 2 ≤ X → ∀ s : Finset ℕ,
    (∀ x ∈ s, x ∈ A) → (∀ x ∈ s, 1 ≤ x ∧ x ≤ X) → (s.card : ℝ) ≤ F X

theorem prefix_bound_of_initialCountingBound {z : ℕ → ℕ} {A : Set ℕ}
    {F : ℕ → ℝ} (hinj : Function.Injective z) (hpos : ∀ n, 0 < z n)
    (hA : ∀ n, z n ∈ A) (hcount : InitialCountingBound A F)
    {N : ℕ} (hN : 2 ≤ N) : (N : ℝ) ≤ F (prefixMax z N) := by
  have hM := length_le_prefixMax hinj hpos N
  have h := hcount (prefixMax z N) (hN.trans hM) (prefixValues z N)
    (by
      intro x hx
      obtain ⟨n, _, rfl⟩ := mem_prefixValues.mp hx
      exact hA n)
    (by
      intro x hx
      exact Finset.mem_Icc.mp (prefixValues_subset_Icc hpos N hx))
  simpa only [card_prefixValues hinj] using h

/-- The algebraic inversion used for the sharp logarithmic prefix bound. -/
theorem lower_bound_of_counting {C β γ N M : ℝ}
    (hC : 0 < C) (hβ : 0 < β) (hγ : 0 ≤ γ) (hN : 2 ≤ N)
    (hNM : N ≤ M)
    (hcount : N ≤ C * M ^ β / (Real.logb 2 M) ^ γ) :
    C ^ (-1 / β) * N ^ (1 / β) * (Real.logb 2 N) ^ (γ / β) ≤ M := by
  have hNpos : 0 < N := by linarith
  have hMpos : 0 < M := hNpos.trans_le hNM
  have hLN : 0 < Real.logb 2 N := Real.logb_pos (by norm_num) (by linarith)
  have hLM : 0 < Real.logb 2 M := Real.logb_pos (by norm_num) (by linarith)
  have hlog : (Real.logb 2 N) ^ γ ≤ (Real.logb 2 M) ^ γ :=
    Real.rpow_le_rpow hLN.le
      (Real.logb_le_logb_of_le (by norm_num) hNpos hNM) hγ
  have hmul : N * (Real.logb 2 N) ^ γ ≤ C * M ^ β :=
    (mul_le_mul_of_nonneg_left hlog hNpos.le).trans
      ((le_div_iff₀ (Real.rpow_pos_of_pos hLM γ)).mp hcount)
  have hdiv : N * (Real.logb 2 N) ^ γ / C ≤ M ^ β := by
    apply (div_le_iff₀ hC).mpr
    simpa only [mul_comm C] using hmul
  have hroot : (N * (Real.logb 2 N) ^ γ / C) ^ β⁻¹ ≤ M := by
    have h := Real.rpow_le_rpow
      (div_nonneg (mul_nonneg hNpos.le (Real.rpow_nonneg hLN.le _)) hC.le)
      hdiv (inv_nonneg.mpr hβ.le)
    simpa only [Real.rpow_rpow_inv hMpos.le hβ.ne'] using h
  have hrewrite : (N * (Real.logb 2 N) ^ γ / C) ^ β⁻¹ =
      C ^ (-1 / β) * N ^ (1 / β) * (Real.logb 2 N) ^ (γ / β) := by
    rw [Real.div_rpow (mul_nonneg hNpos.le (Real.rpow_nonneg hLN.le _)) hC.le,
      Real.mul_rpow hNpos.le (Real.rpow_nonneg hLN.le _),
      ← Real.rpow_mul hLN.le]
    rw [show (-1 : ℝ) / β = -β⁻¹ by ring, Real.rpow_neg hC.le]
    simp only [div_eq_mul_inv]
    ring_nf
  rwa [hrewrite] at hroot

theorem prefixMax_lower_bound {z : ℕ → ℕ} {A : Set ℕ} {C β γ : ℝ}
    (hinj : Function.Injective z) (hpos : ∀ n, 0 < z n) (hA : ∀ n, z n ∈ A)
    (hC : 0 < C) (hβ : 0 < β) (hγ : 0 ≤ γ)
    (hcount : InitialCountingBound A
      (fun X => C * (X : ℝ) ^ β / (Real.logb 2 X) ^ γ))
    {N : ℕ} (hN : 2 ≤ N) :
    C ^ (-1 / β) * (N : ℝ) ^ (1 / β) * (Real.logb 2 N) ^ (γ / β) ≤
      (prefixMax z N : ℝ) := by
  apply lower_bound_of_counting hC hβ hγ (by exact_mod_cast hN)
    (by exact_mod_cast length_le_prefixMax hinj hpos N)
  exact prefix_bound_of_initialCountingBound hinj hpos hA hcount hN

noncomputable def powerLogScale (a c : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ a * (Real.logb 2 n) ^ c

theorem one_le_logb_nat {n : ℕ} (hn : 2 ≤ n) : 1 ≤ Real.logb 2 n := by
  have h := Real.logb_le_logb_of_le (b := (2 : ℝ)) (by norm_num)
    (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ n by exact_mod_cast hn)
  simpa using h

theorem powerLogScale_nonneg (a c : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ powerLogScale a c n :=
  mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) a)
    (Real.rpow_nonneg (zero_le_one.trans (one_le_logb_nat hn)) c)

theorem one_le_powerLogScale {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    {n : ℕ} (hn : 2 ≤ n) : 1 ≤ powerLogScale a c n := by
  apply one_le_mul_of_one_le_of_one_le
  · apply Real.one_le_rpow _ ha
    exact_mod_cast (show 1 ≤ n by omega)
  · exact Real.one_le_rpow (one_le_logb_nat hn) hc

theorem powerLogScale_mono {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    {i j : ℕ} (hi : 2 ≤ i) (hij : i ≤ j) : powerLogScale a c i ≤ powerLogScale a c j := by
  apply mul_le_mul
  · exact Real.rpow_le_rpow (Nat.cast_nonneg i) (by exact_mod_cast hij) ha
  · apply Real.rpow_le_rpow (zero_le_one.trans (one_le_logb_nat hi)) _ hc
    exact Real.logb_le_logb_of_le (by norm_num)
      (by exact_mod_cast (show 0 < i by omega)) (by exact_mod_cast hij)
  · exact Real.rpow_nonneg (zero_le_one.trans (one_le_logb_nat hi)) _
  · exact Real.rpow_nonneg (Nat.cast_nonneg j) _

/-- A logarithmic improvement in the prefix maximum excludes every smaller
logarithmic exponent, including negative exponents. -/
theorem not_isBigO_of_prefixMax_lower {z : ℕ → ℕ} {K a r c : ℝ}
    (hK : 0 < K) (ha : 0 ≤ a) (hr : 0 < r) (hc : c < r)
    (hlower : ∀ N, 2 ≤ N → K * powerLogScale a r N ≤ (prefixMax z N : ℝ)) :
    ¬ Asymptotics.IsBigO atTop (fun n => (z n : ℝ)) (powerLogScale a c) := by
  intro hO
  obtain ⟨C, hC, hCb⟩ := Asymptotics.isBigO_iff'.mp hO
  let d := max c 0
  have hd : 0 ≤ d := le_max_right _ _
  have hcd : c ≤ d := le_max_left _ _
  have hdr : d < r := max_lt hc hr
  have hbound : ∀ᶠ n in atTop, (z n : ℝ) ≤ C * powerLogScale a d n := by
    filter_upwards [hCb, eventually_ge_atTop 2] with n hn hn2
    have hsc : powerLogScale a c n ≤ powerLogScale a d n := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (one_le_logb_nat hn2) hcd)
        (Real.rpow_nonneg (Nat.cast_nonneg n) a)
    have hn' : (z n : ℝ) ≤ C * powerLogScale a c n := by
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (show (0 : ℝ) ≤ (z n : ℝ) from Nat.cast_nonneg _),
        abs_of_nonneg (powerLogScale_nonneg a c hn2)] using hn
    exact hn'.trans (mul_le_mul_of_nonneg_left hsc hC.le)
  obtain ⟨D, hD, hupper⟩ := prefixMax_bound_of_eventual_bound hC.le
    (fun n hn => one_le_powerLogScale ha hd hn)
    (fun i j hi hij => powerLogScale_mono ha hd hi hij) hbound
  have hlim : Tendsto (fun n : ℕ => (Real.logb 2 n) ^ (r - d)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hdr)).comp
      ((Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp
        tendsto_natCast_atTop_atTop)
  obtain ⟨N, hN, hlarge⟩ := ((eventually_ge_atTop 2).and
    (hlim.eventually (eventually_gt_atTop (D / K)))).exists
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLpos : 0 < Real.logb 2 N := zero_lt_one.trans_le (one_le_logb_nat hN)
  have hp : 0 < (N : ℝ) ^ a := Real.rpow_pos_of_pos hNpos a
  have hbase : K * (Real.logb 2 N) ^ r ≤ D * (Real.logb 2 N) ^ d := by
    apply (mul_le_mul_iff_right₀ hp).mp
    have h := (hlower N hN).trans (hupper N hN)
    dsimp [powerLogScale] at h
    convert h using 1 <;> ring
  have hle : (Real.logb 2 N) ^ (r - d) ≤ D / K := by
    apply (le_div_iff₀ hK).mpr
    calc
      (Real.logb 2 N) ^ (r - d) * K =
          (K * (Real.logb 2 N) ^ r) / (Real.logb 2 N) ^ d := by
        rw [Real.rpow_sub hLpos]
        ring
      _ ≤ D := (div_le_iff₀ (Real.rpow_pos_of_pos hLpos d)).mpr hbase
  exact (not_le_of_gt hlarge) hle

/-- Repetition of an iterate confines the entire forward trajectory to a finite prefix. -/
theorem iterate_mem_prefix_of_collision (f : ℕ → ℕ) (x : ℕ) {i j : ℕ}
    (hij : i < j) (hrep : f^[i] x = f^[j] x) (n : ℕ) :
    f^[n] x ∈ prefixValues (fun k => f^[k] x) j := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < j
    · exact mem_prefixValues.mpr ⟨n, hn, rfl⟩
    · have hsmall : n - j + i < n := by omega
      have heq : f^[n] x = f^[n - j + i] x := by
        calc
          f^[n] x = f^[n - j + j] x := by congr 1; omega
          _ = f^[n - j] (f^[j] x) := Function.iterate_add_apply f _ _ x
          _ = f^[n - j] (f^[i] x) := by rw [hrep]
          _ = f^[n - j + i] x := (Function.iterate_add_apply f _ _ x).symm
      rw [heq]
      exact ih _ hsmall

theorem finite_range_iterate_of_collision (f : ℕ → ℕ) (x : ℕ) {i j : ℕ}
    (hij : i < j) (hrep : f^[i] x = f^[j] x) :
    (Set.range (fun n => f^[n] x)).Finite := by
  apply (prefixValues (fun n => f^[n] x) j).finite_toSet.subset
  rintro y ⟨n, rfl⟩
  exact iterate_mem_prefix_of_collision f x hij hrep n

theorem injective_iterates_of_infinite_range (f : ℕ → ℕ) (x : ℕ)
    (hinf : (Set.range (fun n => f^[n] x)).Infinite) :
    Function.Injective (fun n => f^[n] x) := by
  intro i j heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact hinf (finite_range_iterate_of_collision f x hij heq)
  · exact hinf (finite_range_iterate_of_collision f x hji heq.symm)

end CollatzEndpoint
