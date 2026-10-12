import CollatzEndpoint.Counting
import Mathlib.Order.Filter.Cofinite

/-!
# Repetition, eventual periodicity and divergence

These results connect the finite collision-free counting argument with actual
forward Collatz trajectories.  Divergence means convergence to infinity in
the usual filter sense; eventual periodicity includes a positive period and
allows a finite preperiod.  No exclusion of nontrivial cycles is asserted.
-/

namespace CollatzEndpoint

/-- A forward orbit is eventually periodic if a positive period works at every
time after some finite initial segment. -/
def EventuallyPeriodic (start : ℕ) : Prop :=
  ∃ i p : ℕ, 0 < p ∧ ∀ n : ℕ, i ≤ n → orbit start (n + p) = orbit start n

/-- Divergence to infinity, rather than just unboundedness. -/
def Divergent (start : ℕ) : Prop :=
  Filter.Tendsto (orbit start) Filter.atTop Filter.atTop

theorem orbit_add (start i k : ℕ) :
    orbit start (i + k) = orbit (orbit start i) k := by
  simp only [orbit, Nat.add_comm i k, Function.iterate_add_apply]

/-- An injective forward trajectory has no same-time coalescence between any
two of its values. -/
theorem injective_orbit_collisionFree {start : ℕ}
    (hinj : Function.Injective (orbit start)) :
    CollisionFree (Set.range (orbit start)) := by
  intro k x hx y hy hxy
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨j, rfl⟩ := hy
  have hij : i + k = j + k := by
    apply hinj
    simpa only [orbit_add] using hxy
  have heq : i = j := by omega
  rw [heq]

/-- A single repetition propagates to a genuine positive-period tail. -/
theorem eventuallyPeriodic_of_orbit_eq {start i j : ℕ} (hij : i < j)
    (hrep : orbit start i = orbit start j) : EventuallyPeriodic start := by
  refine ⟨i, j - i, by omega, ?_⟩
  intro n hn
  have hprop : orbit start (j + (n - i)) = orbit start (i + (n - i)) := by
    rw [orbit_add, orbit_add, hrep]
  have hleft : j + (n - i) = n + (j - i) := by omega
  have hright : i + (n - i) = n := by omega
  simpa only [hleft, hright] using hprop

theorem injective_orbit_of_not_eventuallyPeriodic {start : ℕ}
    (h : ¬ EventuallyPeriodic start) : Function.Injective (orbit start) := by
  intro i j heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact h (eventuallyPeriodic_of_orbit_eq hij heq)
  · exact h (eventuallyPeriodic_of_orbit_eq hji heq.symm)

theorem not_eventuallyPeriodic_of_injective_orbit {start : ℕ}
    (hinj : Function.Injective (orbit start)) : ¬ EventuallyPeriodic start := by
  rintro ⟨i, p, hp, hperiod⟩
  have heq := hinj (hperiod i (le_refl i))
  omega

theorem not_eventuallyPeriodic_iff_injective_orbit (start : ℕ) :
    ¬ EventuallyPeriodic start ↔ Function.Injective (orbit start) :=
  ⟨injective_orbit_of_not_eventuallyPeriodic, not_eventuallyPeriodic_of_injective_orbit⟩

theorem eventuallyPeriodic_of_not_injective_orbit {start : ℕ}
    (h : ¬ Function.Injective (orbit start)) : EventuallyPeriodic start := by
  by_contra hperiod
  exact h (injective_orbit_of_not_eventuallyPeriodic hperiod)

/-- An injective sequence of natural numbers eventually leaves every bounded
set, so a nonperiodic natural-number orbit actually tends to infinity. -/
theorem tendsto_orbit_atTop_of_not_eventuallyPeriodic {start : ℕ}
    (h : ¬ EventuallyPeriodic start) :
    Filter.Tendsto (orbit start) Filter.atTop Filter.atTop :=
  (injective_orbit_of_not_eventuallyPeriodic h).nat_tendsto_atTop

theorem orbit_period_mul {start i p : ℕ}
    (hperiod : ∀ n : ℕ, i ≤ n → orbit start (n + p) = orbit start n)
    (m : ℕ) : orbit start (i + m * p) = orbit start i := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hidx : i + (m + 1) * p = (i + m * p) + p := by ring
    rw [hidx, hperiod (i + m * p) (by omega), ih]

theorem not_divergent_of_eventuallyPeriodic {start : ℕ}
    (h : EventuallyPeriodic start) : ¬ Divergent start := by
  rintro hdiv
  obtain ⟨i, p, hp, hperiod⟩ := h
  have hevent := Filter.tendsto_atTop.mp hdiv (orbit start i + 1)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hevent
  have hNp : N ≤ N * p := by
    have hm := Nat.mul_le_mul_left N (show 1 ≤ p by omega)
    simpa using hm
  have hlarge := hN (i + N * p) (by omega)
  rw [orbit_period_mul hperiod N] at hlarge
  omega

theorem divergent_iff_not_eventuallyPeriodic (start : ℕ) :
    Divergent start ↔ ¬ EventuallyPeriodic start := by
  constructor
  · intro hd hp
    exact not_divergent_of_eventuallyPeriodic hp hd
  · exact tendsto_orbit_atTop_of_not_eventuallyPeriodic

theorem divergent_iff_injective_orbit (start : ℕ) :
    Divergent start ↔ Function.Injective (orbit start) :=
  (divergent_iff_not_eventuallyPeriodic start).trans
    (not_eventuallyPeriodic_iff_injective_orbit start)

theorem injective_orbit_of_divergent {start : ℕ} (h : Divergent start) :
    Function.Injective (orbit start) :=
  (divergent_iff_injective_orbit start).mp h

theorem collisionFree_of_divergent {start : ℕ} (h : Divergent start) :
    CollisionFree (Set.range (orbit start)) :=
  injective_orbit_collisionFree (injective_orbit_of_divergent h)

theorem eventuallyPeriodic_of_not_divergent {start : ℕ} (h : ¬ Divergent start) :
    EventuallyPeriodic start := by
  by_contra hp
  exact h ((divergent_iff_not_eventuallyPeriodic start).mpr hp)

theorem eventuallyPeriodic_or_divergent (start : ℕ) :
    EventuallyPeriodic start ∨ Divergent start := by
  by_cases hp : EventuallyPeriodic start
  · exact Or.inl hp
  · exact Or.inr ((divergent_iff_not_eventuallyPeriodic start).mpr hp)

end CollatzEndpoint
