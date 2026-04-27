import Mathlib

/-
# Problem: Combinatorial formula and Dyck path identity for Chebyshev partition generating functions

## Background
Define Chebyshev-type polynomials $p_n(x)$ by the recurrence
  $p_0 = 1$, $p_1 = 1$, $p_{n+2} = p_{n+1} - x \, p_n$.

For a partition $\xi$ of $s$, the partition polynomial is
  $p_\xi(x) = \prod_i p_{\xi_i}(x)$.

The generating function is
  $F_{\xi,m,\mu}(x) = p_{m-\mu_0-1}(x) \, p_\xi(x) / p_m(x)^{\mu_1+1}$,
where $\mu = \mu_1 m + \mu_0$ with $0 \le \mu_0 < m$.

Setting $t = \#\{i : \xi_i = m\}$ and $k = \mu_1 + 1 - t$,
$\alpha_0 = m - \mu_0 - 1$, and $\alpha_1, \ldots, \alpha_L$ the parts of $\xi$
strictly less than $m$, we have:
  $F = \prod_{i=0}^L p_{\alpha_i}(x) / p_m(x)^k$.

## Definitions
- $B_m(u) = [x^u](1/p_m(x))$  (Definition 6)
- $D_m(a,b;u) = [x^u](p_a(x) p_b(x) / p_m(x))$  (Definition 7)

## Theorem 2 (Combinatorial formula)
For every $r \ge 0$:
$a_r = \sum_{j_0+\cdots+j_L+u_1+\cdots+u_k=r}
  (-1)^{j_0+\cdots+j_L} \prod_{i=0}^L \binom{\alpha_i - j_i}{j_i}
  \prod_{\nu=1}^k B_m(u_\nu).$

## Theorem 3 (Dyck path identity / manifestly nonneg formula)
If $\prod_{i=0}^L p_{\alpha_i}(x) = \prod_{\nu=1}^k p_{a_\nu}(x) p_{b_\nu}(x)$
with $0 \le a_\nu, b_\nu \le m-1$ and $a_\nu + b_\nu \le m-1$,
then:
(i)   $F = \prod_{\nu=1}^k \sum_{u \ge 0} D_m(a_\nu, b_\nu; u) x^u$
(ii)  $D_m(a_\nu, b_\nu; u) \ge 0$
(iii) All $a_r \ge 0$
-/

/-! ## Definition 1: Chebyshev-type polynomials -/

/-- Chebyshev-type polynomials defined by the recurrence
$p_0 = 1$, $p_1 = 1$, $p_{n+2} = p_{n+1} - x \, p_n$. -/
noncomputable def polyP (R : Type*) [CommRing R] : ℕ → Polynomial R
  | 0 => 1
  | 1 => 1
  | (n + 2) => polyP R (n + 1) - Polynomial.X * polyP R n

theorem polyP_zero (R : Type*) [CommRing R] : polyP R 0 = 1 := rfl
theorem polyP_one (R : Type*) [CommRing R] : polyP R 1 = 1 := rfl
theorem polyP_succ_succ (R : Type*) [CommRing R] (n : ℕ) :
    polyP R (n + 2) = polyP R (n + 1) - Polynomial.X * polyP R n := rfl

/-! ## Definition 2: Partition polynomial -/

/-- $p_\xi(x) = \prod_{i} p_{\xi_i}(x)$ for a partition $\xi$. -/
noncomputable def partitionPoly (R : Type*) [CommRing R] {s : ℕ}
    (ξ : Nat.Partition s) : Polynomial R :=
  (ξ.parts.map (polyP R)).prod

/-! ## Definition 3: Generating function -/

/-- The generating function $F_{\xi,m,\mu}(x) = p_{m-\mu_0-1}(x) p_\xi(x) / p_m(x)^{\mu_1+1}$
where $\mu = \mu_1 m + \mu_0$ with $0 \le \mu_0 < m$. -/
noncomputable def genFun (K : Type*) [Field K] (m μ : ℕ) {s : ℕ}
    (ξ : Nat.Partition s) : PowerSeries K :=
  let μ₁ := μ / m
  let μ₀ := μ % m
  (↑(polyP K (m - μ₀ - 1) * partitionPoly K ξ) : PowerSeries K) *
    ((↑(polyP K m) : PowerSeries K) ^ (μ₁ + 1))⁻¹

/-- The $r$-th coefficient of the generating function. -/
noncomputable def genFunCoeff (K : Type*) [Field K] (m μ r : ℕ) {s : ℕ}
    (ξ : Nat.Partition s) : K :=
  (PowerSeries.coeff r) (genFun K m μ ξ)

/-! ## Definition 4: Count of maximal parts -/

/-- $t = \#\{i : \xi_i = m\}$, the count of parts equal to $m$. -/
def countMaxParts (m : ℕ) {s : ℕ} (ξ : Nat.Partition s) : ℕ :=
  Multiset.count m ξ.parts

/-! ## Definition 5: Reduced parameters -/

/-- The multiset of parts of $\xi$ strictly less than $m$. -/
def nonMaxParts (m : ℕ) {s : ℕ} (ξ : Nat.Partition s) : Multiset ℕ :=
  ξ.parts.filter (· < m)

/-- The polynomial formed by the parts of $\xi$ that are strictly less than $m$. -/
noncomputable def nonMaxPartsPoly (K : Type*) [CommRing K] (m : ℕ) {s : ℕ}
    (ξ : Nat.Partition s) : Polynomial K :=
  ((nonMaxParts m ξ).map (polyP K)).prod

/-- The multiset $(\alpha_0, \alpha_1, \ldots, \alpha_L)$ from Definition 5,
    where $\alpha_0 = m - \mu_0 - 1$ and $\alpha_1, \ldots, \alpha_L$ are the
    parts of $\xi$ strictly less than $m$. -/
def alphaMultiset (m μ : ℕ) {s : ℕ} (ξ : Nat.Partition s) : Multiset ℕ :=
  (m - μ % m - 1) ::ₘ nonMaxParts m ξ

/-- The reduced exponent $k = \mu_1 + 1 - t$ where $\mu_1 = \mu / m$ and $t$ counts max parts. -/
def reducedK (m μ : ℕ) {s : ℕ} (ξ : Nat.Partition s) : ℕ :=
  μ / m + 1 - countMaxParts m ξ

/-- The number of $\alpha$-values: $L + 1$ is the cardinality of the alpha multiset. -/
def alphaCount (m μ : ℕ) {s : ℕ} (ξ : Nat.Partition s) : ℕ :=
  Multiset.card (alphaMultiset m μ ξ)

/-- The numerator polynomial $\prod_{i=0}^{L} p_{\alpha_i}(x)$ in the reduced form. -/
noncomputable def alphaProd (K : Type*) [CommRing K] (m μ : ℕ) {s : ℕ}
    (ξ : Nat.Partition s) : Polynomial K :=
  ((alphaMultiset m μ ξ).map (polyP K)).prod

/-- The alpha values as a list (choosing a representative ordering via `Multiset.toList`). -/
noncomputable def alphaValues (m μ : ℕ) {s : ℕ} (ξ : Nat.Partition s) : List ℕ :=
  (alphaMultiset m μ ξ).toList

/-! ## Basic properties of polyP -/

lemma polyP_constantCoeff (R : Type*) [CommRing R] (n : ℕ) :
    (polyP R n).coeff 0 = 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 | 1 => simp [polyP]
    | n + 2 =>
      simp [polyP] at ih ⊢
      simp_all

lemma polyP_coe_constantCoeff_ne_zero (K : Type*) [Field K] (m : ℕ) :
    PowerSeries.constantCoeff (↑(polyP K m) : PowerSeries K) ≠ 0 := by
  simp [polyP_constantCoeff]

lemma polyP_coe_pow_constantCoeff_ne_zero (K : Type*) [Field K] (m k : ℕ) :
    PowerSeries.constantCoeff ((↑(polyP K m) : PowerSeries K) ^ k) ≠ 0 := by
  rw [map_pow]
  exact pow_ne_zero _ (polyP_coe_constantCoeff_ne_zero K m)

/-! ## Correctness: the reduced form equals the original generating function -/

/-- When $k = \mu_1 + 1 - t \ge 0$, the generating function equals
    $\prod_{i=0}^L p_{\alpha_i}(x) / p_m(x)^k$. -/
theorem genFun_eq_reduced (K : Type*) [Field K] (m μ : ℕ) {s : ℕ}
    (ξ : Nat.Partition s) (hm : 2 ≤ m) (h_parts : ∀ i ∈ ξ.parts, i ≤ m)
    (hk : countMaxParts m ξ ≤ μ / m + 1) :
    genFun K m μ ξ =
      (↑(alphaProd K m μ ξ) : PowerSeries K) *
        ((↑(polyP K m) : PowerSeries K) ^ reducedK m μ ξ)⁻¹ := by
  sorry

/-! ## Definition 6: Coefficients of $1/p_m(x)$ -/

/-- $B_m(u) = [x^u](1/p_m(x))$, the $u$-th coefficient of the power series $1/p_m(x)$.
    Well-defined since $p_m(0) = 1 \ne 0$. -/
noncomputable def B_coeff (K : Type*) [Field K] (m u : ℕ) : K :=
  (PowerSeries.coeff u) ((↑(polyP K m) : PowerSeries K)⁻¹)

/-! ## Definition 7: Coefficients of $p_a \cdot p_b / p_m$ -/

/-- $D_m(a,b;u) = [x^u](p_a(x) \cdot p_b(x) / p_m(x))$. -/
noncomputable def D_coeff (K : Type*) [Field K] (m a b u : ℕ) : K :=
  (PowerSeries.coeff u)
    ((↑(polyP K a * polyP K b) : PowerSeries K) *
      ((↑(polyP K m) : PowerSeries K))⁻¹)

/-- The power series $p_a p_b / p_m$ can be written as `PowerSeries.mk (D_coeff K m a b)`. -/
theorem D_coeff_mk (K : Type*) [Field K] (m a b : ℕ) :
    (↑(polyP K a * polyP K b) : PowerSeries K) * ((↑(polyP K m) : PowerSeries K))⁻¹ =
      PowerSeries.mk (D_coeff K m a b) := by
  sorry

/-! ## Coefficient formula for polyP -/

/-- The coefficient formula $[x^j] p_n(x) = (-1)^j \binom{n-j}{j}$
    (where $\binom{n-j}{j} = 0$ when $j > n - j$). -/
theorem polyP_coeff (R : Type*) [CommRing R] (n j : ℕ) :
    (polyP R n).coeff j = (-1 : R) ^ j * (Nat.choose (n - j) j : ℕ) := by
  sorry

/-! ## Theorem 2: Combinatorial formula (thm:comb)

For every $r \ge 0$:
$$a_r = \sum_{\substack{j_0, \ldots, j_L \ge 0 \\ u_1, \ldots, u_k \ge 0 \\
    j_0 + \cdots + j_L + u_1 + \cdots + u_k = r}}
  (-1)^{j_0 + \cdots + j_L}
  \prod_{i=0}^L \binom{\alpha_i - j_i}{j_i}
  \prod_{\nu=1}^k B_m(u_\nu).$$

We formalize this in two parts:
(a) The Cauchy product form: $a_r = [x^r](\prod p_{\alpha_i}) \cdot (1/p_m)^k$.
(b) The explicit combinatorial sum using `Finset.Nat.antidiagonalTuple`.
-/

/-- **Theorem 2, Cauchy product form.** The generating function coefficient $a_r$ equals
    the $r$-th coefficient of the product
    $\left(\prod_{i=0}^L p_{\alpha_i}(x)\right) \cdot (1/p_m(x))^k$. -/
theorem thm_comb_cauchy (K : Type*) [Field K] (m μ : ℕ) {s : ℕ}
    (ξ : Nat.Partition s) (hm : 2 ≤ m) (h_parts : ∀ i ∈ ξ.parts, i ≤ m)
    (hk : countMaxParts m ξ ≤ μ / m + 1) (r : ℕ) :
    genFunCoeff K m μ r ξ =
      (PowerSeries.coeff r)
        ((↑(alphaProd K m μ ξ) : PowerSeries K) *
          ((↑(polyP K m) : PowerSeries K)⁻¹) ^ reducedK m μ ξ) := by
  sorry

/-- **Theorem 2, explicit summation formula.**
    Let $\alpha_0, \ldots, \alpha_L$ be given by `alphaValues` and let $k$ be the reduced exponent.
    The coefficient $a_r$ of the generating function is:
    $$a_r = \sum_{f \in \mathrm{antidiagonalTuple}(L+1+k, r)}
      \left(\prod_{i < L+1} (-1)^{f(i)} \binom{\alpha_i - f(i)}{f(i)}\right)
      \cdot \left(\prod_{\nu < k} B_m(f(L+1+\nu))\right).$$

    Here `f : Fin (L1 + k) → ℕ` ranges over tuples summing to $r$.
    The first $L+1$ components are the $j_i$ indices (polynomial part),
    the last $k$ components are the $u_\nu$ indices ($1/p_m$ part).

    We use `List.getD` for safe access to the alpha values list. -/
theorem thm_comb (m μ : ℕ) {s : ℕ}
    (ξ : Nat.Partition s) (hm : 2 ≤ m) (h_parts : ∀ i ∈ ξ.parts, i ≤ m)
    (hk : countMaxParts m ξ ≤ μ / m + 1) (r : ℕ) :
    let αs := alphaValues m μ ξ
    let L1 := αs.length  -- this is L + 1
    let k := reducedK m μ ξ
    genFunCoeff ℚ m μ r ξ =
      ∑ f ∈ Finset.Nat.antidiagonalTuple (L1 + k) r,
        (∏ i : Fin L1,
          ((-1 : ℚ) ^ (f (Fin.castAdd k i)) *
            ↑(Nat.choose (αs.getD i.val 0 - f (Fin.castAdd k i))
                          (f (Fin.castAdd k i))))) *
        (∏ ν : Fin k,
          B_coeff ℚ m (f (Fin.natAdd L1 ν))) := by
  sorry

/-! ## Theorem 3: Dyck path identity / manifestly nonneg formula (thm:manifest) -/

/-- **Theorem 3, Part (i): Factorization as a product of power series with $D$-coefficients.**
    If the numerator polynomial factors as $\prod_{\nu=1}^k p_{a_\nu} p_{b_\nu}$
    (with $0 \le a_\nu, b_\nu \le m-1$ and $a_\nu + b_\nu \le m-1$),
    then $F = \prod_{\nu=1}^k \sum_{u \ge 0} D_m(a_\nu, b_\nu; u) x^u$,
    i.e. $F$ factors into a product of power series whose coefficients are $D_m(a_\nu, b_\nu; u)$.

    Here `pairs : Fin k → ℕ × ℕ` represents the pairs $(a_\nu, b_\nu)$ (0-indexed). -/
theorem thm_manifest_factorization (m μ : ℕ) {s : ℕ}
    (ξ : Nat.Partition s) (hm : 2 ≤ m) (h_parts : ∀ i ∈ ξ.parts, i ≤ m)
    (hk_nonneg : countMaxParts m ξ ≤ μ / m + 1)
    (k : ℕ) (hk_eq : k = reducedK m μ ξ)
    (pairs : Fin k → ℕ × ℕ)
    (h_bound : ∀ ν, (pairs ν).1 ≤ m - 1 ∧ (pairs ν).2 ≤ m - 1 ∧
                     (pairs ν).1 + (pairs ν).2 ≤ m - 1)
    (h_factor : alphaProd ℚ m μ ξ =
      ∏ ν : Fin k, (polyP ℚ (pairs ν).1 * polyP ℚ (pairs ν).2)) :
    genFun ℚ m μ ξ =
      ∏ ν : Fin k,
        PowerSeries.mk (D_coeff ℚ m (pairs ν).1 (pairs ν).2) := by
  sorry

/-- **Theorem 3, Part (i), coefficient form.**
    Under the same hypotheses, the coefficient $a_r$ of the generating function
    is the Cauchy product of the $D_m(a_\nu, b_\nu; \cdot)$ sequences:
    $$a_r = \sum_{u_1 + \cdots + u_k = r} \prod_{\nu=1}^k D_m(a_\nu, b_\nu; u_\nu).$$ -/
theorem thm_manifest_coeff_formula (m μ : ℕ) {s : ℕ}
    (ξ : Nat.Partition s) (hm : 2 ≤ m) (h_parts : ∀ i ∈ ξ.parts, i ≤ m)
    (hk_nonneg : countMaxParts m ξ ≤ μ / m + 1)
    (k : ℕ) (hk_eq : k = reducedK m μ ξ)
    (pairs : Fin k → ℕ × ℕ)
    (h_bound : ∀ ν, (pairs ν).1 ≤ m - 1 ∧ (pairs ν).2 ≤ m - 1 ∧
                     (pairs ν).1 + (pairs ν).2 ≤ m - 1)
    (h_factor : alphaProd ℚ m μ ξ =
      ∏ ν : Fin k, (polyP ℚ (pairs ν).1 * polyP ℚ (pairs ν).2))
    (r : ℕ) :
    genFunCoeff ℚ m μ r ξ =
      ∑ f ∈ Finset.Nat.antidiagonalTuple k r,
        ∏ ν : Fin k, D_coeff ℚ m (pairs ν).1 (pairs ν).2 (f ν) := by
  sorry

/-- **Theorem 3, Part (ii): Nonnegativity of $D_m(a,b;u)$.**
    For $0 \le a, b \le m-1$ with $a + b \le m-1$ and $m \ge 2$,
    all coefficients $D_m(a,b;u) \ge 0$. -/
theorem thm_manifest_D_nonneg (m a b u : ℕ) (hm : 2 ≤ m)
    (ha : a ≤ m - 1) (hb : b ≤ m - 1) (hab : a + b ≤ m - 1) :
    (0 : ℚ) ≤ D_coeff ℚ m a b u := by
  sorry

/-- **Theorem 3, Part (iii): Nonnegativity of all coefficients $a_r$.**
    Under the factorization hypotheses, all coefficients of the generating function
    are nonneg. -/
theorem thm_manifest_coeff_nonneg (m μ : ℕ) {s : ℕ}
    (ξ : Nat.Partition s) (hm : 2 ≤ m) (h_parts : ∀ i ∈ ξ.parts, i ≤ m)
    (hk_nonneg : countMaxParts m ξ ≤ μ / m + 1)
    (k : ℕ) (hk_eq : k = reducedK m μ ξ)
    (pairs : Fin k → ℕ × ℕ)
    (h_bound : ∀ ν, (pairs ν).1 ≤ m - 1 ∧ (pairs ν).2 ≤ m - 1 ∧
                     (pairs ν).1 + (pairs ν).2 ≤ m - 1)
    (h_factor : alphaProd ℚ m μ ξ =
      ∏ ν : Fin k, (polyP ℚ (pairs ν).1 * polyP ℚ (pairs ν).2))
    (r : ℕ) :
    (0 : ℚ) ≤ genFunCoeff ℚ m μ r ξ := by
  sorry
