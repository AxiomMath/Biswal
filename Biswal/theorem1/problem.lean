import Mathlib

/-
# Problem: Positivity of Coefficients of a Partition Generating Function

We consider the sequence of polynomials
$p_0(x) = p_1(x) = 1$, $p_{n+1}(x) = p_n(x) - x \cdot p_{n-1}(x)$ for $n \ge 1$.

For an integer partition $\xi = (\xi_1 \ge \xi_2 \ge \cdots \ge \xi_\ell > 0)$, define
$p_\xi(x) := \prod_{i=1}^{\ell} p_{\xi_i}(x)$.

Fix $m \ge 1$, let $n \ge 0$, write $n = n_1 m + n_0$ with $0 \le n_0 < m$, and define
$F(x) = \frac{p_{m - n_0 - 1}(x) \cdot p_\xi(x)}{p_m(x)^{n_1 + 1}} = \sum_{r \ge 0} a_r x^r$.

Let $t := \#\{i : \xi_i = m\}$.

Theorem:
1. If $m = 1$, then $F(x) = 1$.
2. If $m \ge 2$:
   (a) If $t \ge n_1 + 1$, then $F(x)$ is a polynomial.
   (b) If $t \le n_1$, then $a_r > 0$ for all sufficiently large $r$.
-/

-- Main Definition: Polynomial sequence $p_n(x)$ defined by recurrence
-- $p_0(x) = 1$, $p_1(x) = 1$, $p_{n+1}(x) = p_n(x) - x \cdot p_{n-1}(x)$ for $n \ge 1$
noncomputable def polyP (R : Type*) [CommRing R] : ℕ → Polynomial R
  | 0 => 1
  | 1 => 1
  | (n + 2) => polyP R (n + 1) - Polynomial.X * polyP R n

-- Correctness: polyP satisfies the recurrence
theorem polyP_zero (R : Type*) [CommRing R] : polyP R 0 = 1 := by rfl
theorem polyP_one (R : Type*) [CommRing R] : polyP R 1 = 1 := by rfl
theorem polyP_succ_succ (R : Type*) [CommRing R] (n : ℕ) :
    polyP R (n + 2) = polyP R (n + 1) - Polynomial.X * polyP R n := by rfl

-- Partition polynomial: product of $p_{\xi_i}(x)$ over all parts of $\xi$
-- Here $\xi$ is a partition of some number $s$, represented as `Nat.Partition s`
noncomputable def partitionPoly (R : Type*) [CommRing R] {s : ℕ}
    (ξ : Nat.Partition s) : Polynomial R :=
  (ξ.parts.map (polyP R)).prod

-- Count of parts equal to $m$ in partition $\xi$
def countMaxParts (m : ℕ) {s : ℕ} (ξ : Nat.Partition s) : ℕ :=
  Multiset.count m ξ.parts

-- The generating function $F(x)$ as a formal power series over a field
-- $F(x) = p_{m - n_0 - 1}(x) \cdot p_\xi(x) / p_m(x)^{n_1 + 1}$
-- where $n_1 = n / m$ and $n_0 = n \% m$
noncomputable def genFun (K : Type*) [Field K] (m n : ℕ) {s : ℕ}
    (ξ : Nat.Partition s) : PowerSeries K :=
  let n₁ := n / m
  let n₀ := n % m
  (↑(polyP K (m - n₀ - 1) * partitionPoly K ξ) : PowerSeries K) *
    ((↑(polyP K m) : PowerSeries K) ^ (n₁ + 1))⁻¹

-- Coefficient of the generating function
noncomputable def genFunCoeff (K : Type*) [Field K] (m n r : ℕ) {s : ℕ}
    (ξ : Nat.Partition s) : K :=
  (PowerSeries.coeff r) (genFun K m n ξ)

-- Main Statement 1: If $m = 1$, then $F(x) = 1$
theorem genFun_eq_one_of_m_eq_one (K : Type*) [Field K]
    (n : ℕ) {s : ℕ} (ξ : Nat.Partition s)
    (h_parts : ∀ i ∈ ξ.parts, i ≤ 1) :
    genFun K 1 n ξ = 1 := by
  sorry

-- Main Statement 2(a): If $m \ge 2$ and $t \ge n_1 + 1$, then $F(x)$ is a polynomial
-- (i.e., $a_r = 0$ for all sufficiently large $r$)
theorem genFun_is_polynomial (K : Type*) [Field K]
    (m n : ℕ) {s : ℕ} (ξ : Nat.Partition s)
    (hm : 2 ≤ m)
    (h_parts : ∀ i ∈ ξ.parts, i ≤ m)
    (h_t : n / m + 1 ≤ countMaxParts m ξ) :
    ∃ N, ∀ r, N < r → genFunCoeff K m n r ξ = 0 := by
  sorry

-- Main Statement 2(b): If $m \ge 2$ and $t \le n_1$, then $a_r > 0$ for all sufficiently large $r$
-- We state this over $\mathbb{Q}$ since the coefficients are rational
-- and $\mathbb{Q}$ is a linearly ordered field.
theorem genFun_coeff_eventually_pos
    (m n : ℕ) {s : ℕ} (ξ : Nat.Partition s)
    (hm : 2 ≤ m)
    (h_parts : ∀ i ∈ ξ.parts, i ≤ m)
    (h_t : countMaxParts m ξ ≤ n / m) :
    ∃ N, ∀ r, N < r → 0 < genFunCoeff ℚ m n r ξ := by
  sorry
