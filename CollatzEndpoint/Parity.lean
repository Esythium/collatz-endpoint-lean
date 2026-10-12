import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset

namespace CollatzEndpoint

/-- The shortcut Collatz map. -/
def step (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- The value after `k` shortcut steps. -/
def orbit (n k : ℕ) : ℕ := step^[k] n

/-- The number of odd inputs in the first `k` shortcut steps. -/
def oddCount : ℕ → ℕ → ℕ
  | _, 0 => 0
  | n, k + 1 => n % 2 + oddCount (step n) k

@[simp] theorem orbit_zero (n : ℕ) : orbit n 0 = n := rfl

@[simp] theorem orbit_succ (n k : ℕ) : orbit n (k + 1) = orbit (step n) k := by
  simp [orbit, Function.iterate_succ_apply]

@[simp] theorem oddCount_zero (n : ℕ) : oddCount n 0 = 0 := rfl

@[simp] theorem oddCount_succ (n k : ℕ) :
    oddCount n (k + 1) = n % 2 + oddCount (step n) k := rfl

theorem oddCount_le (n k : ℕ) : oddCount n k ≤ k := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    simp only [oddCount_succ]
    have := ih (step n)
    have := Nat.mod_lt n (by omega : 0 < 2)
    omega

theorem step_pos {n : ℕ} (hn : 0 < n) : 0 < step n := by
  unfold step
  split_ifs <;> omega

theorem orbit_pos {n : ℕ} (hn : 0 < n) (k : ℕ) : 0 < orbit n k := by
  induction k generalizing n with
  | zero => simpa using hn
  | succ k ih => simpa only [orbit_succ] using ih (step_pos hn)

/-- Adding an even integer preserves the next parity and changes the next
value by the corresponding linear multiplier. -/
theorem step_add_two_mul (n m : ℕ) :
    step (n + 2 * m) = step n + (if n % 2 = 0 then m else 3 * m) := by
  unfold step
  split_ifs <;> omega

theorem step_even_identity {n : ℕ} (hn : n % 2 = 0) : 2 * step n = n := by
  simp only [step, hn, ite_true]
  omega

theorem step_odd_identity {n : ℕ} (hn : n % 2 ≠ 0) : 2 * step n = 3 * n + 1 := by
  simp only [step, hn, ite_false]
  omega

/-- Both the odd-step count and the iterate transform exactly under a dyadic
translation.  The two assertions are proved together by induction. -/
theorem dyadic_translation (n k q : ℕ) :
    oddCount (n + q * 2 ^ k) k = oddCount n k ∧
    orbit (n + q * 2 ^ k) k = orbit n k + q * 3 ^ oddCount n k := by
  induction k generalizing n q with
  | zero => simp
  | succ k ih =>
    have harg : n + q * 2 ^ (k + 1) = n + 2 * (q * 2 ^ k) := by
      rw [pow_succ]
      ring
    have hpar : (n + q * 2 ^ (k + 1)) % 2 = n % 2 := by
      rw [harg]
      omega
    by_cases hn : n % 2 = 0
    · have hstep : step (n + q * 2 ^ (k + 1)) = step n + q * 2 ^ k := by
        rw [harg, step_add_two_mul, ite_eq_left hn]
      obtain ⟨hc, ho⟩ := ih (step n) q
      constructor
      · simp only [oddCount_succ, hpar, hstep, hc]
      · simp only [orbit_succ, hstep, ho, oddCount_succ, hn, zero_add]
    · have hn1 : n % 2 = 1 := by omega
      have hstep : step (n + q * 2 ^ (k + 1)) = step n + (3 * q) * 2 ^ k := by
        rw [harg, step_add_two_mul, ite_eq_right hn]
        ring
      obtain ⟨hc, ho⟩ := ih (step n) (3 * q)
      constructor
      · simp only [oddCount_succ, hpar, hstep, hc]
      · rw [orbit_succ, hstep, ho]
        simp only [orbit_succ, oddCount_succ, hn1, pow_add, pow_one]
        ring

theorem oddCount_add_pow (n k q : ℕ) :
    oddCount (n + q * 2 ^ k) k = oddCount n k :=
  (dyadic_translation n k q).1

theorem orbit_add_pow (n k q : ℕ) :
    orbit (n + q * 2 ^ k) k = orbit n k + q * 3 ^ oddCount n k :=
  (dyadic_translation n k q).2

/-- A strict affine estimate, expressed without division. -/
theorem scaled_orbit_lt (n k : ℕ) :
    2 ^ k * orbit n k < 3 ^ oddCount n k * (n + 2 ^ k) := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    have hi := ih (step n)
    have hp : 0 < 3 ^ oddCount (step n) k := by positivity
    have htwo : 0 < (2 : ℕ) ^ k := by positivity
    by_cases hn : n % 2 = 0
    · have he := step_even_identity hn
      have he' := congrArg (fun z : ℕ => 3 ^ oddCount (step n) k * z) he
      simp only [orbit_succ, oddCount_succ, hn, zero_add, pow_succ]
      nlinarith
    · have hn1 : n % 2 = 1 := by omega
      have ho := step_odd_identity hn
      have ho' := congrArg (fun z : ℕ => 3 ^ oddCount (step n) k * z) ho
      have hprod := Nat.mul_le_mul_left (3 ^ oddCount (step n) k)
        (show 1 ≤ (2 : ℕ) ^ k by omega)
      simp only [orbit_succ, oddCount_succ, hn1, pow_add, pow_succ]
      nlinarith

/-- The endpoint bound for a representative in a complete positive dyadic
block. -/
theorem representative_orbit_lt {n k : ℕ} (hn : n ≤ 2 ^ k) :
    orbit n k < 2 * 3 ^ oddCount n k := by
  have hi := scaled_orbit_lt n k
  have hupper : 2 ^ k * orbit n k < 2 ^ k * (2 * 3 ^ oddCount n k) := by
    calc
      2 ^ k * orbit n k < 3 ^ oddCount n k * (n + 2 ^ k) := hi
      _ ≤ 3 ^ oddCount n k * (2 ^ k + 2 ^ k) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add_right hn _)
      _ = 2 ^ k * (2 * 3 ^ oddCount n k) := by ring
  by_contra hnot
  have hle : 2 * 3 ^ oddCount n k ≤ orbit n k := by omega
  have hmul := Nat.mul_le_mul_left (2 ^ k) hle
  omega

/-- The finite set of positions of the odd inputs in a parity prefix. -/
def oddPositions : ℕ → ℕ → Finset ℕ
  | _, 0 => ∅
  | n, k + 1 =>
      if n % 2 = 0 then (oddPositions (step n) k).image Nat.succ
      else insert 0 ((oddPositions (step n) k).image Nat.succ)

@[simp] theorem oddPositions_zero (n : ℕ) : oddPositions n 0 = ∅ := rfl

@[simp] theorem zero_mem_oddPositions_succ (n k : ℕ) :
    0 ∈ oddPositions n (k + 1) ↔ n % 2 ≠ 0 := by
  by_cases hn : n % 2 = 0 <;> simp [oddPositions, hn]

@[simp] theorem succ_mem_oddPositions_succ (n k j : ℕ) :
    j + 1 ∈ oddPositions n (k + 1) ↔ j ∈ oddPositions (step n) k := by
  by_cases hn : n % 2 = 0 <;> simp [oddPositions, hn]

theorem mem_oddPositions_lt {n k j : ℕ} (hj : j ∈ oddPositions n k) : j < k := by
  induction k generalizing n j with
  | zero => simp at hj
  | succ k ih =>
    cases j with
    | zero => omega
    | succ j =>
      have ht : j ∈ oddPositions (step n) k := by simpa using hj
      have := ih ht
      omega

theorem card_oddPositions (n k : ℕ) : (oddPositions n k).card = oddCount n k := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    have hnot : 0 ∉ (oddPositions (step n) k).image Nat.succ := by simp
    have hcard := Finset.card_image_of_injective (oddPositions (step n) k) Nat.succ_injective
    by_cases hn : n % 2 = 0
    · simp [oddPositions, oddCount_succ, hn, hcard, ih]
    · have hn1 : n % 2 = 1 := by omega
      simp [oddPositions, oddCount_succ, hn1, hnot,
        hcard, ih, Nat.add_comm]

theorem oddPositions_add_pow (n k q : ℕ) :
    oddPositions (n + q * 2 ^ k) k = oddPositions n k := by
  induction k generalizing n q with
  | zero => simp
  | succ k ih =>
    have harg : n + q * 2 ^ (k + 1) = n + 2 * (q * 2 ^ k) := by
      rw [pow_succ]
      ring
    have hpar : (n + q * 2 ^ (k + 1)) % 2 = n % 2 := by
      rw [harg]
      omega
    by_cases hn : n % 2 = 0
    · have hstep : step (n + q * 2 ^ (k + 1)) = step n + q * 2 ^ k := by
        rw [harg, step_add_two_mul, ite_eq_left hn]
      simp [oddPositions, hpar, hn, hstep, ih]
    · have hstep : step (n + q * 2 ^ (k + 1)) = step n + (3 * q) * 2 ^ k := by
        rw [harg, step_add_two_mul, ite_eq_right hn]
        ring
      simp [oddPositions, hpar, hn, hstep, ih]

theorem oddPositions_mod (n k : ℕ) :
    oddPositions (n % 2 ^ k) k = oddPositions n k := by
  have hsplit : n % 2 ^ k + (n / 2 ^ k) * 2 ^ k = n := by
    simpa [Nat.mul_comm] using Nat.mod_add_div n (2 ^ k)
  calc
    oddPositions (n % 2 ^ k) k =
        oddPositions (n % 2 ^ k + (n / 2 ^ k) * 2 ^ k) k :=
      (oddPositions_add_pow (n % 2 ^ k) k (n / 2 ^ k)).symm
    _ = oddPositions n k := by rw [hsplit]

/-- Equal parity words determine the initial value modulo the dyadic block
length. This is the injective half of the classical parity bijection. -/
theorem modEq_of_oddPositions_eq {n m k : ℕ}
    (h : oddPositions n k = oddPositions m k) : Nat.ModEq (2 ^ k) n m := by
  induction k generalizing n m with
  | zero => simp only [pow_zero, Nat.ModEq]; omega
  | succ k ih =>
    have hhead : (n % 2 ≠ 0) ↔ (m % 2 ≠ 0) := by
      have hh : (0 ∈ oddPositions n (k + 1)) ↔ (0 ∈ oddPositions m (k + 1)) := by rw [h]
      simpa using hh
    have htail : oddPositions (step n) k = oddPositions (step m) k := by
      ext j
      have hh : (j + 1 ∈ oddPositions n (k + 1)) ↔
          (j + 1 ∈ oddPositions m (k + 1)) := by rw [h]
      simpa using hh
    have hi := (ih htail).mul_left' 2
    by_cases hn : n % 2 = 0
    · have hm : m % 2 = 0 := by
        by_contra hm
        exact (hhead.mpr hm) hn
      simpa only [step_even_identity hn, step_even_identity hm,
        pow_succ, Nat.mul_comm] using hi
    · have hm : m % 2 ≠ 0 := hhead.mp hn
      have hscaled : Nat.ModEq (2 ^ (k + 1)) (3 * n + 1) (3 * m + 1) := by
        simpa only [step_odd_identity hn, step_odd_identity hm,
          pow_succ, Nat.mul_comm] using hi
      have hthree : Nat.ModEq (2 ^ (k + 1)) (3 * n) (3 * m) :=
        hscaled.add_right_cancel' 1
      exact Nat.ModEq.cancel_left_of_coprime (by
        have hc : Nat.Coprime 2 3 := by decide
        exact (hc.pow_left (k + 1))) hthree

theorem oddPositions_eq_iff_modEq (n m k : ℕ) :
    oddPositions n k = oddPositions m k ↔ Nat.ModEq (2 ^ k) n m := by
  constructor
  · exact modEq_of_oddPositions_eq
  · intro h
    change n % 2 ^ k = m % 2 ^ k at h
    rw [← oddPositions_mod n k, ← oddPositions_mod m k, h]

theorem oddPositions_injective_on_block (q k : ℕ) :
    Set.InjOn (fun n => oddPositions n k)
      {n | q * 2 ^ k ≤ n ∧ n < (q + 1) * 2 ^ k} := by
  intro n hn m hm h
  change q * 2 ^ k ≤ n ∧ n < (q + 1) * 2 ^ k at hn
  change q * 2 ^ k ≤ m ∧ m < (q + 1) * 2 ^ k at hm
  have hmod := modEq_of_oddPositions_eq h
  have he : (q + 1) * 2 ^ k = q * 2 ^ k + 2 ^ k := by ring
  exact Nat.le_antisymm (hmod.le_of_lt_add (by rw [he] at hn hm; omega))
    (hmod.symm.le_of_lt_add (by rw [he] at hn hm; omega))

/-- Every binary parity word of length `k`, encoded by its odd positions,
occurs exactly once among the standard representatives modulo `2^k`. -/
theorem parityWord_bijective (k : ℕ) :
    Set.BijOn (fun n => oddPositions n k)
      (↑(Finset.range (2 ^ k)) : Set ℕ)
      (↑((Finset.range k).powerset) : Set (Finset ℕ)) := by
  have hmap : Set.MapsTo (fun n => oddPositions n k)
      (↑(Finset.range (2 ^ k)) : Set ℕ)
      (↑((Finset.range k).powerset) : Set (Finset ℕ)) := by
    intro n hn
    apply Finset.mem_powerset.mpr
    intro j hj
    exact Finset.mem_range.mpr (mem_oddPositions_lt hj)
  have hinj : Set.InjOn (fun n => oddPositions n k)
      (↑(Finset.range (2 ^ k)) : Set ℕ) := by
    intro n hn m hm he
    apply oddPositions_injective_on_block 0 k _ _ he
    · simpa using Finset.mem_range.mp hn
    · simpa using Finset.mem_range.mp hm
  exact ⟨hmap, hinj,
    Finset.surjOn_of_injOn_of_card_le _ hmap hinj (by simp)⟩

end CollatzEndpoint
