/-
Target statements for Aristotle: the exact head–tail identity for inverse
integer powers, and the certified finite bounds for ζ(m), following
Proposition [Exact head–tail identity] and Corollary [Certified lower bound
for integer zeta partial sums] in `residue_packetization.tex`.

Please build on the existing development in RequestProject: the even slice
polynomial A_N(x) = ∑_j C(N,2j) x^j is already `slice 2 0 N x`, and its
strict positivity on x ≥ 0 is `one_le_slice_zero`.

Every theorem below is a requested result. Feel free to adjust Mathlib
spellings or strengthen hypotheses-free statements, but keep the mathematical
content of each theorem as stated.
-/
import RequestProject.ResidueSlices

open scoped BigOperators

namespace ResidueSlices

/-- Head polynomial `H_{m,N}(x) = ∑_{j < m} C(N, 2j) x^j`.  No explicit
truncation at `⌊N/2⌋` is needed: `N.choose (2*j) = 0` whenever `2*j > N`. -/
noncomputable def headPoly (m N : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range m, (N.choose (2 * j) : ℝ) * x ^ j

/-- Normalized tail term `T_{m,N}(x) = (A_N(x) − H_{m,N}(x)) / (x^m A_N(x))`. -/
noncomputable def tailTerm (m N : ℕ) (x : ℝ) : ℝ :=
  (slice 2 0 N x - headPoly m N x) / (x ^ m * slice 2 0 N x)

/-- Normalized head term `E_{m,N}(x) = H_{m,N}(x) / (x^m A_N(x))`. -/
noncomputable def headTerm (m N : ℕ) (x : ℝ) : ℝ :=
  headPoly m N x / (x ^ m * slice 2 0 N x)

theorem headPoly_nonneg (m N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ headPoly m N x := by
      exact Finset.sum_nonneg fun _ _ => mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hx _ )

/-
The head is a sub-sum of the (termwise nonnegative) even slice, so it
never exceeds the slice on the nonnegative axis.
-/
theorem headPoly_le_slice (m N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    headPoly m N x ≤ slice 2 0 N x := by
      unfold headPoly slice;
      rw [ ← Finset.sum_filter ];
      refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg _ _ );
      rotate_left;
      exact Finset.image ( fun j => 2 * j ) ( Finset.range m ) |> Finset.filter fun i => i ≤ N;
      · grind;
      · exact fun _ _ _ => mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hx _ );
      · rw [ Finset.sum_filter, Finset.sum_image ] <;> norm_num;
        exact Finset.sum_le_sum fun i hi => by split_ifs <;> simp_all +decide [ Nat.choose_eq_zero_of_lt ] ;

/-
**Exact head–tail identity** (`residue_packetization.tex`, Prop. 1):
for every `m ≥ 0`, `N`, and `x > 0`,  `T_{m,N}(x) + E_{m,N}(x) = x⁻ᵐ`.
-/
theorem head_tail_identity (m N : ℕ) {x : ℝ} (hx : 0 < x) :
    tailTerm m N x + headTerm m N x = (x ^ m)⁻¹ := by
      unfold tailTerm headTerm;
      field_simp;
      rw [ sub_add_cancel, div_self <| ne_of_gt <| lt_of_lt_of_le zero_lt_one <| one_le_slice_zero 2 N <| le_of_lt hx ]

theorem tailTerm_nonneg (m N : ℕ) {x : ℝ} (hx : 0 < x) :
    0 ≤ tailTerm m N x := by
      exact div_nonneg ( sub_nonneg_of_le <| headPoly_le_slice m N hx.le ) ( mul_nonneg ( pow_nonneg hx.le _ ) <| slice_nonneg 2 0 N hx.le )

theorem headTerm_nonneg (m N : ℕ) {x : ℝ} (hx : 0 < x) :
    0 ≤ headTerm m N x := by
      exact div_nonneg ( headPoly_nonneg _ _ hx.le ) ( mul_nonneg ( pow_nonneg hx.le _ ) ( slice_nonneg _ _ _ hx.le ) )

/-
Summing the identity over `1 ≤ n ≤ M` splits the Dirichlet partial sum
exactly into a rational head part `S_{M,N}(m)` and an exact error part
`𝓔_{M,N}(m)`.
-/
theorem partial_sum_decomposition (m N M : ℕ) :
    ∑ n ∈ Finset.Icc 1 M, ((n : ℝ) ^ m)⁻¹
      = ∑ n ∈ Finset.Icc 1 M, tailTerm m N (n : ℝ)
        + ∑ n ∈ Finset.Icc 1 M, headTerm m N (n : ℝ) := by
          rw [ ← Finset.sum_add_distrib, Finset.sum_congr rfl ];
          exact fun n hn => Eq.symm ( head_tail_identity m N ( Nat.cast_pos.mpr ( Finset.mem_Icc.mp hn |>.1 ) ) )

/-
**Certified two-sided bound for ζ(m)**, integer `m ≥ 2`
(`residue_packetization.tex`, Cor. 1).  Writing ζ(m) as the tsum of `n⁻ᵐ`
over `n ≥ 1`:
  `0 ≤ ζ(m) − S_{M,N}(m) ≤ 𝓔_{M,N}(m) + 1 / ((m−1) · M^(m−1))`,
where the Dirichlet tail `∑_{n>M} n⁻ᵐ` is bounded by the integral test
(termwise: `n⁻ᵐ ≤ ((n−1)^(1−m) − n^(1−m))/(m−1)`, then telescope).
-/
theorem zeta_certified_bounds (m N M : ℕ) (hm : 2 ≤ m) (hM : 1 ≤ M) :
    0 ≤ (∑' n : ℕ, ((n + 1 : ℝ) ^ m)⁻¹)
        - ∑ n ∈ Finset.Icc 1 M, tailTerm m N (n : ℝ) ∧
    (∑' n : ℕ, ((n + 1 : ℝ) ^ m)⁻¹)
        - ∑ n ∈ Finset.Icc 1 M, tailTerm m N (n : ℝ)
      ≤ ∑ n ∈ Finset.Icc 1 M, headTerm m N (n : ℝ)
        + (((m : ℝ) - 1) * (M : ℝ) ^ (m - 1))⁻¹ := by
          -- Split the zeta series into the finite sum up to M and the tail starting from M+1.
          have h_split : (∑' (n : ℕ), ((n + 1 : ℝ) ^ m)⁻¹) = (∑ n ∈ Finset.Icc 1 M, ((n : ℝ) ^ m)⁻¹) + (∑' (n : ℕ), ((n + M + 1 : ℝ) ^ m)⁻¹) := by
            erw [ ← Summable.sum_add_tsum_nat_add M ];
            · erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ' ];
            · exact_mod_cast summable_nat_add_iff 1 |>.2 <| Real.summable_nat_pow_inv.2 hm;
          -- Bound the tail by the integral test.
          have h_tail_bound : (∑' (n : ℕ), ((n + M + 1 : ℝ) ^ m)⁻¹) ≤ (1 / ((m - 1) * (M : ℝ) ^ (m - 1))) := by
            -- We'll use the fact that $\sum_{n=M+1}^{\infty} \frac{1}{n^m}$ is bounded above by $\int_{M}^{\infty} \frac{1}{x^m} \, dx$.
            have h_integral_bound : ∀ n : ℕ, ((n + M + 1 : ℝ) ^ m)⁻¹ ≤ ∫ x in (n + M : ℝ)..((n + 1) + M : ℝ), x ^ (-m : ℝ) := by
              intro n
              have h_integral_bound : ∀ x ∈ Set.Icc (n + M : ℝ) ((n + 1) + M : ℝ), x ^ (-m : ℝ) ≥ ((n + M + 1 : ℝ) ^ m)⁻¹ := by
                intro x hx; rw [ Real.rpow_neg ( by linarith [ hx.1 ] ) ] ; norm_cast; norm_num;
                exact inv_anti₀ ( pow_pos ( by linarith [ hx.1, show ( M : ℝ ) ≥ 1 by norm_cast ] ) _ ) ( pow_le_pow_left₀ ( by linarith [ hx.1, show ( M : ℝ ) ≥ 1 by norm_cast ] ) ( by linarith [ hx.2 ] ) _ );
              refine' le_trans _ ( intervalIntegral.integral_mono_on _ _ _ h_integral_bound ) <;> norm_num;
              apply_rules [ ContinuousOn.intervalIntegrable ];
              exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.inv₀ ( continuousAt_id.pow m ) ( pow_ne_zero _ <| by cases Set.mem_uIcc.mp hx <;> linarith [ show ( M : ℝ ) ≥ 1 by norm_cast ] );
            -- Summing the integral bounds from $n = 0$ to $\infty$, we get the desired result.
            have h_sum_integral_bound : ∀ N : ℕ, ∑ n ∈ Finset.range N, ((n + M + 1 : ℝ) ^ m)⁻¹ ≤ ∫ x in (M : ℝ)..((N + M) : ℝ), x ^ (-m : ℝ) := by
              intro N; induction' N with N ih <;> norm_num [ add_assoc, Finset.sum_range_succ ] at *;
              convert add_le_add ih ( h_integral_bound N ) using 1;
              rw [ intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ ContinuousOn.intervalIntegrable ] <;> exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.inv₀ ( continuousAt_id.pow _ ) ( pow_ne_zero _ <| by cases Set.mem_uIcc.mp hx <;> linarith [ show ( M : ℝ ) ≥ 1 by norm_cast ] );
            -- Taking the limit of the integral bound as $N$ approaches infinity, we get the desired result.
            have h_limit_integral_bound : Filter.Tendsto (fun N : ℕ => ∫ x in (M : ℝ)..((N + M) : ℝ), x ^ (-m : ℝ)) Filter.atTop (nhds (∫ x in Set.Ioi (M : ℝ), x ^ (-m : ℝ))) := by
              apply_rules [ MeasureTheory.intervalIntegral_tendsto_integral_Ioi ];
              · rw [ integrableOn_Ioi_rpow_iff ] <;> norm_num ; linarith;
                linarith;
              · exact Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop;
            -- Evaluating the integral $\int_{M}^{\infty} x^{-m} \, dx$, we get $\left[ \frac{x^{1-m}}{1-m} \right]_{M}^{\infty} = \frac{1}{(m-1)M^{m-1}}$.
            have h_integral_eval : ∫ x in Set.Ioi (M : ℝ), x ^ (-m : ℝ) = 1 / ((m - 1) * (M : ℝ) ^ (m - 1)) := by
              rw [ integral_Ioi_rpow_of_lt ] <;> norm_num;
              · rw [ ← neg_div_neg_eq ] ; cases m <;> norm_num [ Nat.succ_eq_add_one, pow_add ] at * ; ring;
              · linarith;
              · linarith;
            exact h_integral_eval ▸ le_of_tendsto_of_tendsto' ( Summable.hasSum ( by exact_mod_cast summable_nat_add_iff ( M + 1 ) |>.2 <| Real.summable_nat_pow_inv.2 <| by linarith ) |> HasSum.tendsto_sum_nat ) h_limit_integral_bound h_sum_integral_bound;
          have := partial_sum_decomposition m N M; simp_all +decide [ headTerm, tailTerm ] ;
          constructor <;> linarith [ show 0 ≤ ∑ x ∈ Finset.Icc 1 M, headPoly m N ( x : ℝ ) / ( x ^ m * slice 2 0 N ( x : ℝ ) ) from Finset.sum_nonneg fun _ _ => div_nonneg ( headPoly_nonneg _ _ <| Nat.cast_nonneg _ ) <| mul_nonneg ( pow_nonneg ( Nat.cast_nonneg _ ) _ ) <| slice_nonneg _ _ _ <| Nat.cast_nonneg _, show 0 ≤ ∑' n : ℕ, ( ( n + M + 1 : ℝ ) ^ m ) ⁻¹ from tsum_nonneg fun _ => inv_nonneg.2 <| pow_nonneg ( by positivity ) _ ]

end ResidueSlices