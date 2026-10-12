import CollatzEndpoint.OrbitGrowth
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace CollatzEndpoint

open Finset
open scoped BigOperators

/-- The geometric form of the contribution of one dyadic shell. -/
lemma dyadic_shell_factor (β : ℝ) (r : ℕ) :
    ((2 : ℝ) ^ (r + 1)) ^ β / (2 : ℝ) ^ r =
      (2 : ℝ) ^ β * ((2 : ℝ) ^ (β - 1)) ^ r := by
  rw [← Real.rpow_natCast_mul (by norm_num)]
  rw [← Real.rpow_mul_natCast (by norm_num)]
  rw [← Real.rpow_add (by norm_num)]
  rw [← Real.rpow_natCast (2 : ℝ) r, ← Real.rpow_sub (by norm_num)]
  congr 1
  push_cast
  ring

/-- A power-saving counting estimate implies summability along any injective
positive enumeration. This lemma does not assume a monotone enumeration. -/
theorem reciprocal_summable_of_power_count {A : Set ℕ} {z : ℕ → ℕ} {C β : ℝ}
    (hC : 0 ≤ C) (hβ : β < 1) (hinj : Function.Injective z)
    (hpos : ∀ n, 0 < z n) (hA : ∀ n, z n ∈ A)
    (hcount : InitialCountingBound A (fun X => C * (X : ℝ) ^ β)) :
    Summable (fun n => 1 / (z n : ℝ)) := by
  let G : ℕ → ℝ := fun r => C * (2 : ℝ) ^ β * ((2 : ℝ) ^ (β - 1)) ^ r
  have hratio0 : 0 ≤ (2 : ℝ) ^ (β - 1) := Real.rpow_nonneg (by norm_num) _
  have hratio1 : (2 : ℝ) ^ (β - 1) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hG : Summable G := (summable_geometric_of_lt_one hratio0 hratio1).mul_left _
  have hG0 : ∀ r, 0 ≤ G r := by intro r; dsimp [G]; positivity
  apply summable_of_sum_le (c := ∑' r, G r) (by intro n; positivity)
  intro u
  let shell : ℕ → ℕ := fun n => Nat.log 2 (z n)
  have hfiber : ∀ r, ∑ n ∈ u.filter (fun n => shell n = r), 1 / (z n : ℝ) ≤ G r := by
    intro r
    let v := u.filter (fun n => shell n = r)
    have hlower : ∀ n ∈ v, 2 ^ r ≤ z n := by
      intro n hn
      have hs : Nat.log 2 (z n) = r := (Finset.mem_filter.mp hn).2
      rw [← hs]
      exact Nat.pow_log_le_self 2 (ne_of_gt (hpos n))
    have hupper : ∀ n ∈ v, z n ≤ 2 ^ (r + 1) := by
      intro n hn
      have hs : Nat.log 2 (z n) = r := (Finset.mem_filter.mp hn).2
      have := Nat.lt_pow_succ_log_self (b := 2) (by omega) (z n)
      simpa [hs] using this.le
    have htwo : 2 ≤ 2 ^ (r + 1) := by
      simpa using (Nat.pow_le_pow_right (by omega : 0 < 2) (show 1 ≤ r + 1 by omega))
    have hcard : (v.card : ℝ) ≤ C * ((2 : ℝ) ^ (r + 1)) ^ β := by
      have hc := hcount (2 ^ (r + 1)) htwo (v.image z)
        (by
          intro x hx
          obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hx
          exact hA n)
        (by
          intro x hx
          obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
          exact ⟨hpos n, hupper n hn⟩)
      simpa [Finset.card_image_of_injective v hinj] using hc
    calc
      ∑ n ∈ v, 1 / (z n : ℝ) ≤ ∑ _n ∈ v, 1 / ((2 : ℝ) ^ r) := by
        apply Finset.sum_le_sum
        intro n hn
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast hlower n hn
      _ = (v.card : ℝ) / ((2 : ℝ) ^ r) := by simp [div_eq_mul_inv]
      _ ≤ (C * ((2 : ℝ) ^ (r + 1)) ^ β) / ((2 : ℝ) ^ r) :=
        div_le_div_of_nonneg_right hcard (by positivity)
      _ = G r := by
        dsimp [G]
        rw [mul_div_assoc, dyadic_shell_factor]
        ring
  calc
    ∑ n ∈ u, 1 / (z n : ℝ) =
        ∑ r ∈ u.image shell, ∑ n ∈ u.filter (fun n => shell n = r), 1 / (z n : ℝ) := by
      exact (Finset.sum_fiberwise_of_maps_to (fun n hn => Finset.mem_image_of_mem shell hn)
        (fun n => 1 / (z n : ℝ))).symm
    _ ≤ ∑ r ∈ u.image shell, G r := Finset.sum_le_sum (fun r _ => hfiber r)
    _ ≤ ∑' r, G r := hG.sum_le_tsum _ (fun r _ => hG0 r)

end CollatzEndpoint
