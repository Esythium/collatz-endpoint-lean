import CollatzEndpoint.LayerEstimate
import CollatzEndpoint.WindowEstimate

namespace CollatzEndpoint

/-- The actual finite intersection of a set with an integer window. -/
noncomputable def windowSet (A : Set ℕ) (a X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico a (a + X)).filter (fun n => n ∈ A)

@[simp] theorem mem_windowSet {A : Set ℕ} {a X n : ℕ} :
    n ∈ windowSet A a X ↔ a ≤ n ∧ n < a + X ∧ n ∈ A := by
  classical
  simp [windowSet, and_assoc]

/-- The uniform window estimate with the manuscript's explicit constant 400.
In fact the half-open block argument also permits a = 0. -/
theorem uniform_window_bound {A : Set ℕ} (hfree : CollisionFree A)
    (a : ℕ) {X : ℕ} (hX : 2 ≤ X) :
    ((windowSet A a X).card : ℝ) ≤
      400 * (X : ℝ) ^ beta / (Real.logb 2 (X : ℝ)) ^ gamma := by
  classical
  let k := Nat.clog 2 X
  obtain ⟨hk, hlo, hhi⟩ := dyadic_scale hX
  have hblocks : ∀ q, ((alignedBlock (2 ^ k) q).filter (fun n => n ∈ A)).card ≤
      layerSum k := by
    intro q
    apply block_card_le_layerSum _ q k
    · intro j n hn m hm he
      exact hfree j (Finset.mem_filter.mp hn).2 (Finset.mem_filter.mp hm).2 he
    · intro n hn
      exact Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1
  have hfinite : (windowSet A a X).card ≤ 2 * layerSum k := by
    exact window_card_le_two (fun n => n ∈ A) (by positivity) hlo hblocks
  calc
    ((windowSet A a X).card : ℝ) ≤ 2 * (layerSum k : ℝ) := by exact_mod_cast hfinite
    _ ≤ 2 * (100 * (2 : ℝ) ^ (beta * (k : ℝ)) * (k : ℝ) ^ (-gamma)) :=
      mul_le_mul_of_nonneg_left (layerSum_le hk) (by norm_num)
    _ = 200 * (2 : ℝ) ^ (beta * (k : ℝ)) * (k : ℝ) ^ (-gamma) := by ring
    _ ≤ _ := dyadic_bound_to_window beta_pos.le beta_lt_one.le gamma_pos.le hX hlo hhi

end CollatzEndpoint
