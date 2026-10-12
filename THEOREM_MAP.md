# Paper-to-Lean theorem map

Reference: **A Logarithmic Endpoint Refinement of Collatz Orbit Sparsity**, Esm, 12 October 2026. The numbering below refers to that six-page manuscript. Every declaration named here has namespace prefix `CollatzEndpoint.`. Import `CollatzEndpoint.MainResults` to obtain the complete result chain.

## Definitions and conventions

| Paper notation | Lean definition | Meaning |
| --- | --- | --- |
| `T` | `step` in `Parity.lean` | `n / 2` for even `n`, `(3*n+1)/2` for odd `n`, on `ℕ`. |
| `T^k(n)` | `orbit n k` | Exactly `step^[k] n`. |
| Number of odd inputs among the first `k` steps | `oddCount n k` | Counts the inputs at positions `0,...,k-1`. |
| Parity word | `oddPositions n k` | Finite set of the odd-input positions, a subset of `Finset.range k`. |
| Same-time collision-free set | `CollisionFree A` in `Counting.lean` | For every `k`, the map `n ↦ orbit n k` is injective on `A`. Different-time meetings are not forbidden by this definition. |
| `A ∩ [a,a+X)` | `windowSet A a X` in `Windows.lean` | The finite interval `Finset.Ico a (a+X)`, filtered by membership in the arbitrary set `A`. |
| Divergent shortcut orbit | `Divergent start` in `Dynamics.lean` | `Filter.Tendsto (orbit start) atTop atTop`. |
| Eventually periodic orbit | `EventuallyPeriodic start` | There are `i,p : ℕ` with `p>0` such that `orbit start (n+p)=orbit start n` for every `n>=i`. |
| First `N` values' maximum | `prefixMax z N` in `OrbitGrowth.lean` | Maximum over `0 <= n < N`, not the value at time `N`. |
| Successive odd iterates `y_n` | `successiveOddOrbit start n` in `Drift.lean` | Iterates of `oddStep` beginning at `firstOdd start`; an initial even seed is reduced by its initial power of 2. |
| Valuation drift `g_n` | `collatzDrift start n` in `MainResults.lean` | `n*log_2(3) - Σ_{j<n} v_2(3*y_j+1)`, for the actual successive odd iterates. |

The extension to `0 : ℕ` is used for convenient interval representatives. All trajectory consequences in `MainResults.lean` explicitly assume `0 < start`. Positivity is proved by `step_pos`, `orbit_pos`, and `successiveOddOrbit_pos`.

## Exact entropy constants

In `Entropy.lean`, `entropy_root_exists` proves existence and `alpha_unique` proves uniqueness on `[1/2,1]` of the root selected by `alpha`. Its defining equation is

```text
Real.binEntropy alpha = alpha * Real.log 3
```

Mathlib's `Real.binEntropy` uses natural logarithms. Dividing this equality by `ln 2` gives precisely the paper's `H_2(alpha)=alpha*log_2(3)`. The source defines

```text
beta         = alpha * ln(3) / ln(2)
entropySlope = ln(1-alpha) - ln(alpha)
entropyGap   = ln(3) - entropySlope
gamma        = ln(3) / (2*entropyGap)
```

These are the paper's exact `beta` and `gamma`; the natural-log factors cancel in the latter formula. `alpha_mem`, `beta_pos`, `beta_lt_one`, `gamma_pos`, and `gamma_lt_half` supply the required ranges. Decimal approximations are not definitions or assumptions.

## Theorem 2.2: uniform endpoint bound

**Final declaration:** `uniform_window_bound` in `Windows.lean`.

For every `A : Set ℕ` satisfying `CollisionFree A`, every `a : ℕ`, and every `X : ℕ` with `2 <= X`, it proves

```text
(windowSet A a X).card <= 400 * X^beta / (log_2 X)^gamma
```

with the cardinality and `X` cast to `ℝ` on the analytic side. No finiteness hypothesis is imposed on `A`. The theorem permits `a=0`, so it includes every positive starting point required by the paper. The constant is uniform in `A`, `a`, and `X`.

The supporting declarations are `dyadic_scale` and `window_card_le_two` in `WindowCover.lean`, `dyadic_bound_to_window` in `WindowEstimate.lean`, and `layerSum_le` in `LayerEstimate.lean`. The final theorem supplies the analytic layer bound itself; it does not retain it as an input hypothesis.

## Lemmas 3.1 and 3.2: finite parity and layer capacity

| Paper component | Declaration | Scope |
| --- | --- | --- |
| Parity words correspond to residues modulo `2^k` | `parityWord_bijective` and `oddPositions_eq_iff_modEq` in `Parity.lean` | Every natural depth `k`, including `k=0`. |
| Exact dyadic translation | `dyadic_translation`, `oddCount_add_pow`, `orbit_add_pow` | `orbit (n+q*2^k) k = orbit n k + q*3^(oddCount n k)`; the odd count is preserved. |
| Representative endpoint bound | `representative_orbit_lt` and `orbit_pos` | The upper bound `orbit n k < 2*3^(oddCount n k)` holds for `n <= 2^k`; the lower bound holds for positive `n`. |
| At most `choose(k,s)` members in a layer | `layer_card_le_choose` in `Counting.lean` | Parity-word injectivity inside any aligned block. |
| At most `2*3^s` members in a layer | `layer_card_le_capacity` | Uses same-time collision freedom and the translated endpoint interval. |
| Layerwise minimum and total capacity | `layer_card_le_min`, `block_card_le_layerSum` | An arbitrary finite subset of an aligned block, all `q,k : ℕ`. |

`layerSum k` is exactly

```text
Σ_{s=0}^k min(choose(k,s), 2*3^s).
```

The formal aligned blocks are `[q*2^k,(q+1)*2^k)`. The paper uses `q*2^k+{1,...,2^k}`. This change of complete residue representatives preserves the bound; the formal translated endpoint interval is `[q*3^s,(q+2)*3^s)`, containing exactly `2*3^s` integers.

## Lemma 4.1: the logarithmic layer estimate

**Final declaration:** `layerSum_le` in `LayerEstimate.lean`.

For every `k : ℕ` with `1 <= k`, it proves

```text
(layerSum k : ℝ) <= 100 * 2^(beta*k) * k^(-gamma).
```

The large-depth proof uses `layerCutoff`, `choose_layerCutoff_le`, `choose_tail_layerCutoff_le`, and `layerSum_le_twenty_endpointScale`. The small-depth estimate is `two_pow_le_hundred_endpointScale`, together with `layerSum_le_two_pow`. These cover all `k>=1`; the assertion is not inferred from a finite numerical scan.

The formal proof obtains a sufficient binomial prefactor from mathlib's global Stirling inequalities. It does not import Robbins' sharper remainder formula as an unproved premise. This is a proof-route difference from the paper, with the same final exponents and constants.

## Corollary 5.1: trajectory growth and critical endpoint

The concrete declarations below are in `MainResults.lean` and assume a positive initial integer. The bounds for divergent trajectories use `Divergent start`, whose equivalence with injectivity is proved in `Dynamics.lean`.

| Declaration | Concrete conclusion |
| --- | --- |
| `divergent_prefixMax_lower` | For `N>=2`, `max_{n<N} T^n(start) >= 400^(-1/beta) * N^(1/beta) * (log_2 N)^(gamma/beta)`. |
| `divergent_odd_prefixMax_lower` | The identical bound for successive odd iterates. |
| `divergent_not_isBigO` | No divergent shortcut trajectory is `O(n^(1/beta)*(log_2 n)^c)` when `c < gamma/beta`. |
| `divergent_odd_not_isBigO` | The same exclusion for successive odd iterates. |
| `eventuallyPeriodic_of_isBigO`, `eventuallyPeriodic_of_odd_isBigO` | The corresponding slow-growth hypothesis implies eventual periodicity. |
| `eventuallyPeriodic_of_critical_power`, `eventuallyPeriodic_of_odd_critical_power` | Explicit pure-power endpoint `O(n^(1/beta))`, obtained by setting `c=0`. |

`Asymptotics.IsBigO atTop` expresses an eventual bound with an arbitrary constant. In particular, the formal result permits finite exceptional initial segments. The cutoff is strict in the logarithmic exponent `c`; no exclusion at `c=gamma/beta` is claimed.

The general growth lemmas in `OrbitGrowth.lean` have counting hypotheses. The concrete `MainResults.lean` theorems discharge those hypotheses using `uniform_window_bound`. The dynamics connection is supplied by `eventuallyPeriodic_of_orbit_eq`, `divergent_iff_injective_orbit`, and `collisionFree_of_divergent`. Eventual periodicity is not identified with arrival at 1.

## Corollary 5.2: reciprocal sum, drift and limsup

The odd map is defined from `padicValNat 2 (3*n+1)`. `successiveOddOrbit_eq_orbit`, `successiveOddTimes_strictMono`, and `successiveOddOrbit_recurrence` in `Drift.lean` prove that it is the actual strictly indexed odd subsequence of the shortcut trajectory, including an even initial seed.

| Declaration in `MainResults.lean` | Concrete conclusion |
| --- | --- |
| `divergent_reciprocal_summable` | `Σ_n 1/T^n(start)` converges for a divergent positive shortcut orbit. |
| `divergent_odd_reciprocal_summable` | `Σ_n 1/y_n` converges for its successive odd iterates. |
| `collatz_product_identity` | The actual iterates satisfy `y_n = y_0 * 2^(g_n) * Q_n`, where `Q_n = product_{j<n}(1+1/(3*y_j))`. |
| `divergent_correctionProduct_converges` | `Q_n` converges to a finite real `Q` with `1 <= Q <= exp(Σ_j 1/(3*y_j))`. |
| `divergent_not_drift_upper` | For every real `B` and every `c < gamma/beta`, the eventual inequality `g_n <= beta^(-1)*log_2 n + c*log_2(log_2 n) + B` is impossible. |
| `divergent_drift_frequently_gt` | Every `c < gamma/beta` is exceeded infinitely often by the normalized drift. |
| `divergent_drift_limsup` | The limsup of `(g_n-beta^(-1)*log_2 n)/log_2(log_2 n)` is at least `gamma/beta`. |

The last declaration uses `EReal` for the limsup, so it includes an infinite upper limit without assuming bounded normalized drift. The finite set of small indices at which the logarithmic denominator is nonpositive has no effect on the `atTop` conclusions.

The generic product identity and its bounded correction factor are proved in `Drift.lean`, through `odd_recurrence_drift_identity`, `correctionProduct_le_exp_tsum`, and `correctionProduct_converges`. The concrete declarations `collatz_product_identity` and `divergent_correctionProduct_converges` in `MainResults.lean` supply the actual orbit's recurrence and summability, as appropriate. The product identity itself does not require divergence.

## Verification boundary

`lake build` checks the project source against the pinned environment, and `lake env lean Audit.lean` reports the selected final declarations' axiom closures. Standard Lean axioms may occur; admitted proofs or project-specific unproved axioms must not occur. See [README.md](README.md) for reproduction commands.

This correspondence documents the mathematical statements encoded in Lean. It does not prove the literature search exhaustive, certify originality, or turn the result into a proof of the full Collatz conjecture. The conjectural existence of a fast divergent orbit and the existence of nontrivial cycles remain outside the conclusions proved here.
