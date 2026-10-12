import CollatzEndpoint.Parity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat

open scoped BigOperators

namespace CollatzEndpoint

/-- Distinct elements never coalesce at the same iterate. -/
def CollisionFree (A : Set ℕ) : Prop :=
  ∀ k, Set.InjOn (fun n => orbit n k) A

/-- A single odd-count layer of a finite set. -/
def layer (A : Finset ℕ) (k s : ℕ) : Finset ℕ :=
  A.filter (fun n => oddCount n k = s)

@[simp] theorem mem_layer {A : Finset ℕ} {n k s : ℕ} :
    n ∈ layer A k s ↔ n ∈ A ∧ oddCount n k = s := by
  simp [layer]

/-- The exact combinatorial capacity summed over all odd-count layers. -/
def layerSum (k : ℕ) : ℕ :=
  ∑ s ∈ Finset.range (k + 1), min (k.choose s) (2 * 3 ^ s)

theorem layer_card_le_choose (A : Finset ℕ) (q k s : ℕ)
    (hblock : ∀ n ∈ A, q * 2 ^ k ≤ n ∧ n < (q + 1) * 2 ^ k) :
    (layer A k s).card ≤ k.choose s := by
  have hinj : Set.InjOn (fun n => oddPositions n k) (↑(layer A k s) : Set ℕ) := by
    intro n hn m hm he
    exact oddPositions_injective_on_block q k
      (hblock n (mem_layer.mp hn).1) (hblock m (mem_layer.mp hm).1) he
  calc
    (layer A k s).card = ((layer A k s).image (fun n => oddPositions n k)).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ ((Finset.range k).powersetCard s).card := by
      apply Finset.card_le_card
      intro word hword
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hword
      apply Finset.mem_powersetCard.mpr
      constructor
      · intro j hj
        exact Finset.mem_range.mpr (mem_oddPositions_lt hj)
      · rw [card_oddPositions]
        exact (mem_layer.mp hn).2
    _ = k.choose s := by simp

theorem orbit_mem_layer_interval {n q k s : ℕ}
    (hblock : q * 2 ^ k ≤ n ∧ n < (q + 1) * 2 ^ k)
    (hc : oddCount n k = s) :
    q * 3 ^ s ≤ orbit n k ∧ orbit n k < (q + 2) * 3 ^ s := by
  have hsplit : n = (n - q * 2 ^ k) + q * 2 ^ k := by omega
  have hedge : (q + 1) * 2 ^ k = q * 2 ^ k + 2 ^ k := by ring
  have hr : n - q * 2 ^ k < 2 ^ k := by rw [hedge] at hblock; omega
  have hcount : oddCount (n - q * 2 ^ k) k = s := by
    conv at hc => lhs; rw [hsplit]
    rw [oddCount_add_pow] at hc
    exact hc
  have hiter := orbit_add_pow (n - q * 2 ^ k) k q
  rw [← hsplit, hcount] at hiter
  have hsmall := representative_orbit_lt (Nat.le_of_lt hr)
  rw [hcount] at hsmall
  rw [hiter]
  constructor
  · omega
  · calc
      orbit (n - q * 2 ^ k) k + q * 3 ^ s < 2 * 3 ^ s + q * 3 ^ s := by omega
      _ = (q + 2) * 3 ^ s := by ring

theorem layer_card_le_capacity (A : Finset ℕ) (q k s : ℕ)
    (hfree : CollisionFree (↑A : Set ℕ))
    (hblock : ∀ n ∈ A, q * 2 ^ k ≤ n ∧ n < (q + 1) * 2 ^ k) :
    (layer A k s).card ≤ 2 * 3 ^ s := by
  have hinj : Set.InjOn (fun n => orbit n k) (↑(layer A k s) : Set ℕ) := by
    intro n hn m hm he
    exact hfree k (mem_layer.mp hn).1 (mem_layer.mp hm).1 he
  calc
    (layer A k s).card = ((layer A k s).image (fun n => orbit n k)).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.Ico (q * 3 ^ s) ((q + 2) * 3 ^ s)).card := by
      apply Finset.card_le_card
      intro value hvalue
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hvalue
      exact Finset.mem_Ico.mpr
        (orbit_mem_layer_interval (hblock n (mem_layer.mp hn).1) (mem_layer.mp hn).2)
    _ = 2 * 3 ^ s := by
      rw [Nat.card_Ico]
      have : (q + 2) * 3 ^ s = q * 3 ^ s + 2 * 3 ^ s := by ring
      rw [this, Nat.add_sub_cancel_left]

theorem layer_card_le_min (A : Finset ℕ) (q k s : ℕ)
    (hfree : CollisionFree (↑A : Set ℕ))
    (hblock : ∀ n ∈ A, q * 2 ^ k ≤ n ∧ n < (q + 1) * 2 ^ k) :
    (layer A k s).card ≤ min (k.choose s) (2 * 3 ^ s) :=
  le_min (layer_card_le_choose A q k s hblock)
    (layer_card_le_capacity A q k s hfree hblock)

/-- The all-depth, finite combinatorial master bound on an aligned block. -/
theorem block_card_le_layerSum (A : Finset ℕ) (q k : ℕ)
    (hfree : CollisionFree (↑A : Set ℕ))
    (hblock : ∀ n ∈ A, q * 2 ^ k ≤ n ∧ n < (q + 1) * 2 ^ k) :
    A.card ≤ layerSum k := by
  have hsum : A.card = ∑ s ∈ Finset.range (k + 1), (layer A k s).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro n hn
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (oddCount_le n k))
  rw [hsum, layerSum]
  apply Finset.sum_le_sum
  intro s hs
  exact layer_card_le_min A q k s hfree hblock

end CollatzEndpoint
