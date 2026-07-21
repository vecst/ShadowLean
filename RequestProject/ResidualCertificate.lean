/-
Algebraic residual certificates for positive fractional powers.

A "certificate" for the positive real `T` is the pair `(a, b)` with
`x^a * T^b = 1`, i.e. `T = x^(-a/b)`.  Everything here is stated with
natural-number powers only (no `Real.rpow`), so any generator — binomial
slices, Poisson kernels, or otherwise — that produces bracketing values
`L, U` with `x^a L^b ≤ 1 ≤ x^a U^b` can use the same certification
interface.  The final example certifies `√10` numerically.

This module is deliberately independent of the residue-slice development.
-/
import Mathlib

open scoped BigOperators

namespace ResidualCertificate

/-- Lower order certificate: if `A` undershoots the unit residual, then
`A ≤ T`. -/
theorem residual_order_lower {x A T : ℝ} {a b : ℕ}
    (hx : 0 < x) (_hA : 0 < A) (hT : 0 < T) (hb : 0 < b)
    (hT1 : x ^ a * T ^ b = 1) (hA1 : x ^ a * A ^ b ≤ 1) :
    A ≤ T := by
  have hxa : 0 < x ^ a := pow_pos hx a
  have hle : x ^ a * A ^ b ≤ x ^ a * T ^ b := by rw [hT1]; exact hA1
  have hAT : A ^ b ≤ T ^ b := le_of_mul_le_mul_left hle hxa
  exact le_of_pow_le_pow_left₀ hb.ne' hT.le hAT

/-- Upper order certificate: if `A` overshoots the unit residual, then
`T ≤ A`. -/
theorem residual_order_upper {x A T : ℝ} {a b : ℕ}
    (hx : 0 < x) (hA : 0 < A) (_hT : 0 < T) (hb : 0 < b)
    (hT1 : x ^ a * T ^ b = 1) (hA1 : 1 ≤ x ^ a * A ^ b) :
    T ≤ A := by
  have hxa : 0 < x ^ a := pow_pos hx a
  have hle : x ^ a * T ^ b ≤ x ^ a * A ^ b := by rw [hT1]; exact hA1
  have hTA : T ^ b ≤ A ^ b := le_of_mul_le_mul_left hle hxa
  exact le_of_pow_le_pow_left₀ hb.ne' hA.le hTA

/-- A two-sided bracket certificate: undershoot below, overshoot above. -/
theorem residual_bracket {x L U T : ℝ} {a b : ℕ}
    (hx : 0 < x) (hL : 0 < L) (hU : 0 < U) (hT : 0 < T) (hb : 0 < b)
    (hT1 : x ^ a * T ^ b = 1)
    (hLb : x ^ a * L ^ b ≤ 1) (hUb : 1 ≤ x ^ a * U ^ b) :
    L ≤ T ∧ T ≤ U :=
  ⟨residual_order_lower hx hL hT hb hT1 hLb,
   residual_order_upper hx hU hT hb hT1 hUb⟩

/-- Intersecting two bracketing intervals sharpens both bounds. -/
theorem residual_pair_intersection {T L₁ U₁ L₂ U₂ : ℝ}
    (h1 : L₁ ≤ T ∧ T ≤ U₁) (h2 : L₂ ≤ T ∧ T ≤ U₂) :
    max L₁ L₂ ≤ T ∧ T ≤ min U₁ U₂ :=
  ⟨max_le h1.1 h2.1, le_min h1.2 h2.2⟩

/-- Intersecting a nonempty finite family of bracketing intervals.  The
`Finset.Nonempty` hypothesis rules out the empty collection, for which no
`sup'`/`inf'` is defined. -/
theorem residual_finset_intersection {ι : Type*} {T : ℝ} {L U : ι → ℝ}
    {s : Finset ι} (hs : s.Nonempty)
    (hlo : ∀ i ∈ s, L i ≤ T) (hhi : ∀ i ∈ s, T ≤ U i) :
    s.sup' hs L ≤ T ∧ T ≤ s.inf' hs U :=
  ⟨Finset.sup'_le hs L hlo, Finset.le_inf' hs U hhi⟩

/-- Exact rational certificate for `√10`: `(79/25)^2 ≤ 10 ≤ (16/5)^2`, hence
`79/25 ≤ √10 ≤ 16/5`. -/
theorem sqrt_ten_certificate :
    ((79 : ℝ) / 25) ^ 2 ≤ 10 ∧ (10 : ℝ) ≤ ((16 : ℝ) / 5) ^ 2 ∧
      (79 : ℝ) / 25 ≤ Real.sqrt 10 ∧ Real.sqrt 10 ≤ (16 : ℝ) / 5 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (79 : ℝ) / 25 = Real.sqrt ((79 / 25) ^ 2) from
      (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  · rw [show (16 : ℝ) / 5 = Real.sqrt ((16 / 5) ^ 2) from
      (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)

/-!
## Quantitative residual bounds

The certificates above are order-only.  We now add relative-error control:
a small residual `|x^a A^b − 1| ≤ η` forces `A` close to the true root `T`,
with an explicit algebraic (non-`rpow`, non-calculus) modulus.
-/

/-
**Relative bound for a `b`-th power residual.**  If `r^b` is within `η`
of `1` (with `0 ≤ η < 1`), then `r` is within `η / (b(1−η))` of `1`.
The factorization `r^b − 1 = (r−1)·∑_{j<b} r^j` and a lower bound on the
geometric sum (`≥ b` when `r ≥ 1`, `≥ b·r^b ≥ b(1−η)` when `r ≤ 1`) give
the result.
-/
theorem pow_residual_relative_bound {r η : ℝ} {b : ℕ}
    (hr : 0 < r) (hb : 0 < b)
    (hη0 : 0 ≤ η)
    (hres : |r ^ b - 1| ≤ η)
    (hη1 : η < 1) :
    |r - 1| ≤ η / ((b : ℝ) * (1 - η)) := by
      rw [ le_div_iff₀ ( mul_pos ( by positivity ) ( by linarith ) ) ];
      -- We'll use the fact that $|r^b - 1| = |r - 1| \cdot |r^{b-1} + r^{b-2} + \cdots + r + 1|$.
      have h_factor : |r ^ b - 1| = |r - 1| * |∑ i ∈ Finset.range b, r ^ i| := by
        rw [ ← abs_mul, mul_comm, geom_sum_mul ];
      -- We'll use the fact that $|∑ i ∈ Finset.range b, r ^ i| ≥ b * (1 - η)$.
      have h_sum_bound : |∑ i ∈ Finset.range b, r ^ i| ≥ b * (1 - η) := by
        rw [ abs_of_nonneg ( Finset.sum_nonneg fun _ _ => pow_nonneg hr.le _ ) ];
        by_cases hr1 : r ≥ 1;
        · exact le_trans ( by norm_num; nlinarith ) ( Finset.sum_le_sum fun _ _ => one_le_pow₀ hr1 );
        · -- Since $r < 1$, we have $r^b \geq 1 - \eta$.
          have h_rb_ge : r ^ b ≥ 1 - η := by
            linarith [ abs_le.mp hres ];
          exact le_trans ( by norm_num ) ( Finset.sum_le_sum fun i hi => pow_le_pow_of_le_one hr.le ( le_of_not_ge hr1 ) ( Finset.mem_range_le hi ) ) |> le_trans ( mul_le_mul_of_nonneg_left h_rb_ge <| Nat.cast_nonneg _ );
      exact le_trans ( mul_le_mul_of_nonneg_left h_sum_bound ( abs_nonneg _ ) ) ( by linarith )

/-
**Generator-facing relative bound.**  For a unit certificate
`x^a T^b = 1` and a candidate `A` with residual `|x^a A^b − 1| ≤ η`, the
relative deviation `|A/T − 1|` is bounded by `η / (b(1−η))`.  Reduces to
`pow_residual_relative_bound` at `r = A/T`, since `x^a = T^{−b}` gives
`x^a A^b = (A/T)^b`.
-/
theorem fractional_residual_relative_bound
    {x A T η : ℝ} {a b : ℕ}
    (hx : 0 < x) (hA : 0 < A) (hT : 0 < T) (hb : 0 < b)
    (hunit : x ^ a * T ^ b = 1)
    (hη0 : 0 ≤ η)
    (hres : |x ^ a * A ^ b - 1| ≤ η)
    (hη1 : η < 1) :
    |A / T - 1| ≤ η / ((b : ℝ) * (1 - η)) := by
  have hTne : T ≠ 0 := hT.ne'
  apply pow_residual_relative_bound (r := A / T) (η := η) (b := b)
  · exact div_pos hA hT
  · exact hb
  · exact hη0
  · convert hres using 1
    rw [div_pow, show x ^ a = 1 / T ^ b by
      have hxa : 0 < x ^ a := pow_pos hx a
      apply (eq_div_iff (pow_ne_zero b hTne)).2
      nlinarith]
    field_simp [hTne]
  · exact hη1

/-
**Signed enclosure, positive residual.**  If `A` overshoots
(`0 ≤ x^a A^b − 1`), then `T ≤ A` and `A/(1+ε) ≤ T`, where
`ε = η / (b(1−η))`.
-/
theorem residual_positive_enclosure {x A T η : ℝ} {a b : ℕ}
    (hx : 0 < x) (hA : 0 < A) (hT : 0 < T) (hb : 0 < b)
    (hunit : x ^ a * T ^ b = 1)
    (hη0 : 0 ≤ η) (hres : |x ^ a * A ^ b - 1| ≤ η) (hη1 : η < 1)
    (hpos : 0 ≤ x ^ a * A ^ b - 1) :
    A / (1 + η / ((b : ℝ) * (1 - η))) ≤ T ∧ T ≤ A := by
  have hD : 0 < (b : ℝ) * (1 - η) := mul_pos (by positivity) (by linarith)
  have hε0 : 0 ≤ η / ((b : ℝ) * (1 - η)) := div_nonneg hη0 hD.le
  have hrel := fractional_residual_relative_bound hx hA hT hb hunit hη0 hres hη1
  constructor
  · rw [div_le_iff₀ (by linarith : 0 < 1 + η / ((b : ℝ) * (1 - η)))]
    have hu := (abs_le.mp hrel).2
    have hcancel : A / T * T = A := div_mul_cancel₀ A hT.ne'
    nlinarith
  · exact residual_order_upper hx hA hT hb hunit (by linarith)

/-
**Signed enclosure, negative residual.**  If `A` undershoots
(`x^a A^b − 1 ≤ 0`) and the modulus `ε = η / (b(1−η)) < 1`, then `A ≤ T`
and `T ≤ A/(1−ε)`.  The hypothesis `ε < 1` is what makes `1 − ε > 0`, so
the division is justified rather than silent.
-/
theorem residual_negative_enclosure {x A T η : ℝ} {a b : ℕ}
    (hx : 0 < x) (hA : 0 < A) (hT : 0 < T) (hb : 0 < b)
    (hunit : x ^ a * T ^ b = 1)
    (hη0 : 0 ≤ η) (hres : |x ^ a * A ^ b - 1| ≤ η) (hη1 : η < 1)
    (hneg : x ^ a * A ^ b - 1 ≤ 0)
    (hε1 : η / ((b : ℝ) * (1 - η)) < 1) :
    A ≤ T ∧ T ≤ A / (1 - η / ((b : ℝ) * (1 - η))) := by
  have hden : 0 < 1 - η / ((b : ℝ) * (1 - η)) := sub_pos_of_lt hε1
  have hrel := fractional_residual_relative_bound hx hA hT hb hunit hη0 hres hη1
  constructor
  · exact residual_order_lower hx hA hT hb hunit (by linarith)
  · rw [le_div_iff₀ hden]
    have hl := (abs_le.mp hrel).1
    have hcancel : A / T * T = A := div_mul_cancel₀ A hT.ne'
    nlinarith

/-
**Worked bracket for `√10` through the generic interface.**  Instantiate
`x = 1/10`, `a = 1`, `b = 2`, `T = √10` (so `x^a T^b = 1`), and discharge the
endpoint residuals `x^a L^2 ≤ 1 ≤ x^a U^2` by exact arithmetic
(`31622² ≤ 10⁹ ≤ 31623²`).  This must genuinely invoke `residual_bracket`.
-/
theorem sqrt_ten_bracket_via_interface :
    (31622 : ℝ) / 10000 ≤ Real.sqrt 10 ∧ Real.sqrt 10 ≤ 31623 / 10000 := by
  apply residual_bracket (x := (1 / 10 : ℝ)) (a := 1) (b := 2)
  · norm_num
  · norm_num
  · norm_num
  · exact Real.sqrt_pos.2 (by norm_num)
  · norm_num
  · rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)]
    norm_num
  · norm_num
  · norm_num

end ResidualCertificate