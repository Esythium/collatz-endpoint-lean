import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace CollatzEndpoint

/-- Aligned half-open blocks of natural numbers. -/
def alignedBlock (B q : ℕ) : Finset ℕ :=
  Finset.Ico (q * B) ((q + 1) * B)

/-- A positive window no longer than a block meets at most two successive blocks. -/
theorem window_subset_two_blocks {a X B : ℕ} (hB : 0 < B)
    (hX : X ≤ B) :
    Finset.Ico a (a + X) ⊆
      alignedBlock B (a / B) ∪ alignedBlock B (a / B + 1) := by
  intro n hn
  have hn' := Finset.mem_Ico.mp hn
  have hmod := Nat.mod_lt a hB
  have hdiv := Nat.mod_add_div a B
  have hlow : a / B * B ≤ a := by
    have := Nat.div_mul_le_self a B
    omega
  have hupp : a < (a / B + 1) * B := by
    nlinarith
  apply Finset.mem_union.mpr
  by_cases h : n < (a / B + 1) * B
  · exact Or.inl (Finset.mem_Ico.mpr ⟨hlow.trans hn'.1, h⟩)
  · apply Or.inr
    apply Finset.mem_Ico.mpr
    constructor
    · omega
    · nlinarith

/-- The finite counting consequence of the two-block covering lemma. -/
theorem window_card_le_two (P : ℕ → Prop) [DecidablePred P]
    {a X B S : ℕ} (hB : 0 < B) (hX : X ≤ B)
    (hblock : ∀ q, ((alignedBlock B q).filter P).card ≤ S) :
    ((Finset.Ico a (a + X)).filter P).card ≤ 2 * S := by
  have hsub : (Finset.Ico a (a + X)).filter P ⊆
      (alignedBlock B (a / B)).filter P ∪
        (alignedBlock B (a / B + 1)).filter P := by
    intro n hn
    obtain ⟨hn, hp⟩ := Finset.mem_filter.mp hn
    have hc := window_subset_two_blocks hB hX hn
    rcases Finset.mem_union.mp hc with hc | hc
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hc, hp⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hc, hp⟩))
  calc
    _ ≤ ((alignedBlock B (a / B)).filter P ∪
        (alignedBlock B (a / B + 1)).filter P).card := Finset.card_le_card hsub
    _ ≤ ((alignedBlock B (a / B)).filter P).card +
        ((alignedBlock B (a / B + 1)).filter P).card := Finset.card_union_le _ _
    _ ≤ S + S := Nat.add_le_add (hblock _) (hblock _)
    _ = 2 * S := by omega

/-- An exact integer choice of dyadic scale avoids rounding real logarithms. -/
theorem dyadic_scale {X : ℕ} (hX : 2 ≤ X) :
    1 ≤ Nat.clog 2 X ∧ X ≤ 2 ^ Nat.clog 2 X ∧ 2 ^ Nat.clog 2 X < 2 * X := by
  have hk : 0 < Nat.clog 2 X := Nat.clog_pos (by omega) (by omega)
  refine ⟨hk, Nat.le_pow_clog (by omega) X, ?_⟩
  have hprev := Nat.pow_pred_clog_lt_self (b := 2) (by omega) (x := X) (by omega)
  have hk' : (Nat.clog 2 X).pred + 1 = Nat.clog 2 X := Nat.succ_pred_eq_of_pos hk
  calc
    2 ^ Nat.clog 2 X = 2 ^ (Nat.clog 2 X).pred * 2 := by
      rw [← pow_succ, hk']
    _ < 2 * X := by omega

end CollatzEndpoint
