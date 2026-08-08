/-
Circle–hyperbola structure of the Pascal slices — the g=2 gudermannian anchor.

The mod-2 multisection of `(1+u)^N` (the even/odd binomial sums) is hyperbolic on
the nose: the even slice is `½[(1+u)^N + (1−u)^N] = G·cosh r` and the odd slice is
`½[(1+u)^N − (1−u)^N] = G·sinh r`, where `r = N·artanh u` is the rapidity and
`G = (1−u²)^{N/2}` the geometric mean. Hence the slice ratio is exactly `tanh r`,
and `gd(r) = arcsin(ratio)` is its circular image. This is `gd₂`, the flat base of
the `gd_g` ladder of circle↔hyperbola bridges (higher `g` lift off the real axis).

`binomEven/binomOdd` are the direct multisections `∑_{i≡k (2)} C(N,i) u^i`; the
repository's compressed `ResidueSlices.slice 2 k N` uses `x^(i/2)` instead, and
relates by `binomSlice_{2,k}(u) = u^k · slice 2 k N (u²)` — kept separate here so
the hyperbolic identity stays clean.

Proof routes (keep every statement verbatim; minor lemma-name changes ok):
- binomEven_closed / binomOdd_closed: expand `(1+u)^N` and `(1−u)^N` by the
  binomial theorem (`add_pow`), so `(1±u)^N = ∑ i, C(N,i) (±u)^i`. Then
  `((1+u)^N ± (1−u)^N)/2 = ∑ i, C(N,i) u^i · (1 ± (−1)^i)/2`, and
  `(1+(−1)^i)/2 = if i even then 1 else 0`, `(1−(−1)^i)/2 = if i odd then 1 else 0`
  (case on `Nat.even_or_odd i` / `Int.neg_one_pow_eq_one_iff_even`); `Finset.sum_congr`.
- binomSlice_ratio_tanh: with `|u| < 1` we have `1−u > 0`, `1+u > 0`, so
  `binomEven N u = ((1+u)^N+(1−u)^N)/2 > 0`. Rewrite both slices by the closed
  forms; the ratio is `((1+u)^N−(1−u)^N)/((1+u)^N+(1−u)^N)`. On the other side,
  `artanh u = ½·log((1+u)/(1−u))` (`Real.artanh_eq_log`), so
  `2·(N·artanh u) = log(((1+u)/(1−u))^N)` and `exp(2·N·artanh u) = ((1+u)/(1−u))^N`.
  Using `tanh x = (exp(2x)−1)/(exp(2x)+1)` (from `Real.tanh_eq_sinh_div_cosh` / the
  `exp` form), substitute `W = ((1+u)/(1−u))^N` and clear denominators by
  `(1−u)^N > 0` to match `(W−1)/(W+1) = ((1+u)^N−(1−u)^N)/((1+u)^N+(1−u)^N)`.
Certification: if a target cannot close, omit it and report its exact name; do not
weaken a statement.
-/
import Mathlib

open scoped BigOperators

namespace SliceHyperbolic

/-- Even-index binomial multisection — the (uncompressed) mod-2 Pascal slice `k=0`. -/
noncomputable def binomEven (N : ℕ) (u : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (N + 1), if i % 2 = 0 then (N.choose i : ℝ) * u ^ i else 0

/-- Odd-index binomial multisection — the mod-2 Pascal slice `k=1`. -/
noncomputable def binomOdd (N : ℕ) (u : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (N + 1), if i % 2 = 1 then (N.choose i : ℝ) * u ^ i else 0

/-- Binomial expansion of `(1 + u)^N` with the binomial coefficient in front. -/
private lemma one_add_pow_eq_sum (N : ℕ) (u : ℝ) :
    (1 + u) ^ N = ∑ i ∈ Finset.range (N + 1), (N.choose i : ℝ) * u ^ i := by
  rw [add_comm, add_pow]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Binomial expansion of `(1 - u)^N`, i.e. the alternating expansion. -/
private lemma one_sub_pow_eq_sum (N : ℕ) (u : ℝ) :
    (1 - u) ^ N = ∑ i ∈ Finset.range (N + 1), (N.choose i : ℝ) * (-u) ^ i := by
  have h : (1 : ℝ) - u = -u + 1 := by ring
  rw [h, add_pow]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The even slice is a hyperbolic cosine in disguise: `½[(1+u)^N + (1−u)^N]`. -/
theorem binomEven_closed (N : ℕ) (u : ℝ) :
    binomEven N u = ((1 + u) ^ N + (1 - u) ^ N) / 2 := by
  rw [one_add_pow_eq_sum, one_sub_pow_eq_sum, ← Finset.sum_add_distrib, Finset.sum_div,
    binomEven]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases Nat.even_or_odd i with he | ho
  · rw [he.neg_pow, if_pos (Nat.even_iff.mp he)]
    ring
  · rw [ho.neg_pow, if_neg (by simp [Nat.odd_iff.mp ho])]
    ring

/-- The odd slice is a hyperbolic sine in disguise: `½[(1+u)^N − (1−u)^N]`. -/
theorem binomOdd_closed (N : ℕ) (u : ℝ) :
    binomOdd N u = ((1 + u) ^ N - (1 - u) ^ N) / 2 := by
  rw [one_add_pow_eq_sum, one_sub_pow_eq_sum, ← Finset.sum_sub_distrib, Finset.sum_div,
    binomOdd]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases Nat.even_or_odd i with he | ho
  · rw [he.neg_pow, if_neg (by simp [Nat.even_iff.mp he])]
    ring
  · rw [ho.neg_pow, if_pos (Nat.odd_iff.mp ho)]
    ring

/-- `exp (N · artanh u)` squares to `((1+u)/(1-u))^N` when `|u| < 1`. -/
private lemma exp_rapidity_sq (N : ℕ) {u : ℝ} (hu : |u| < 1) :
    Real.exp ((N : ℝ) * Real.artanh u) ^ 2 = ((1 + u) / (1 - u)) ^ N := by
  obtain ⟨hu1, hu2⟩ := abs_lt.mp hu
  have hq : (0 : ℝ) ≤ (1 + u) / (1 - u) := by
    apply div_nonneg <;> linarith
  rw [Real.exp_nat_mul, Real.exp_artanh (Set.mem_Ioo.mpr ⟨hu1, hu2⟩), ← pow_mul,
    mul_comm N 2, pow_mul, Real.sq_sqrt hq]

/-- **The g=2 gudermannian anchor.** The mod-2 Pascal-slice ratio is exactly the
hyperbolic tangent of the rapidity `r = N · artanh u`. -/
theorem binomSlice_ratio_tanh (N : ℕ) {u : ℝ} (hu : |u| < 1) :
    binomOdd N u / binomEven N u = Real.tanh (N * Real.artanh u) := by
  obtain ⟨hu1, hu2⟩ := abs_lt.mp hu
  have hA : (0 : ℝ) < (1 + u) ^ N := pow_pos (by linarith) N
  have hB : (0 : ℝ) < (1 - u) ^ N := pow_pos (by linarith) N
  set E := Real.exp ((N : ℝ) * Real.artanh u) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hEsq : E ^ 2 = (1 + u) ^ N / (1 - u) ^ N := by
    rw [hE, exp_rapidity_sq N hu, div_pow]
  have hinv : Real.exp (-((N : ℝ) * Real.artanh u)) = E⁻¹ := by
    rw [Real.exp_neg, hE]
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, ← hE, hinv,
    binomOdd_closed, binomEven_closed]
  rw [div_div_div_cancel_right₀ (two_ne_zero), div_div_div_cancel_right₀ (two_ne_zero)]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  have hEB : E ^ 2 * (1 - u) ^ N = (1 + u) ^ N := by
    rw [hEsq]; field_simp
  field_simp
  nlinarith [hEB, hEpos, sq_nonneg E]

end SliceHyperbolic
