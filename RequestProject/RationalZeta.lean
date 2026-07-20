/-
Target statements for Aristotle: the rational-exponent diagonal zeta
theorem — composing the certified integer head–tail machinery
(HeadTailZeta.lean) with the certified uniform diagonal slice estimate
(DiagonalZeta.lean) into the paper's Theorem [Diagonal approximation to
ζ(s)] (`residue_packetization.tex`, §Finite zeta approximations).

Setting: s = m + k/g rational, with 2 ≤ g, 0 ≤ k < g, and 1 < s (which
forces 1 ≤ m, since k/g < 1).

Key available tools:
- `tailTerm`, `headTerm`, `headPoly`, `head_tail_identity`,
  `headPoly_le_slice`, and the integral-test tail machinery inside
  `zeta_certified_bounds` (HeadTailZeta.lean);
- `tendsto_slice_ratio_rpow` (RpowCorollaries.lean) for the pointwise
  slice-ratio limit;
- `diagonal_slice_ratio_bound` and `diagonal_threshold_eventually`
  (DiagonalZeta.lean) for the uniform diagonal estimate;
- `slice` has nonnegative coefficients, hence is monotone in `x ≥ 0`;
  `slice 2 0 N 1 = 2^(N-1)` for `N ≥ 1` (sum of even binomials), giving
  `slice 2 0 N (n:ℝ) ≥ 2^(N-1)` for `n ≥ 1`.

Proof route for the capstone (from the paper):
  ζ(s) − Z_N = Σ_{n=1}^N (n^{-s} − 𝒯_{s,N}(n)) + Σ_{n>N} n^{-s}.
Tail: integral test, Σ_{n>N} n^{-s} ≤ N^{1-s}/(s-1).
Kernel error for 1 ≤ n ≤ N, with a = tailTerm, b = slice ratio, c = n^{-k/g}:
  |a·b − n^{-m}·c| ≤ |a − n^{-m}|·|b| + n^{-m}·|b − c|;
  |a − n^{-m}| = headTerm m N n ≤ (Σ_{j<m} C(N,2j)) / 2^(N-1)
    ≤ C_m·N^(2m-2)·2^(1-N)   (using slice 2 0 N n ≥ 2^(N-1));
  |b − c| ≤ 4(g-1)·exp(−c_g·N^(1−1/g))·n^{-k/g} ≤ 4(g-1)·exp(−c_g·N^(1−1/g))
    once the threshold holds (diagonal_slice_ratio_bound +
    diagonal_threshold_eventually), and |b| ≤ 1 + |b − c| is then bounded.
Summing over n ≤ N contributes the factor N in the third term.

Every proof placeholder is a requested result. Minor Mathlib-name adjustments
are fine; keep the mathematical content of each statement.
-/
import RequestProject.HeadTailZeta
import RequestProject.DiagonalZeta

open scoped BigOperators

namespace ResidueSlices

/-- The rational exponent `s = m + k/g` as a real number. -/
noncomputable def sVal (m k g : ℕ) : ℝ := (m : ℝ) + (k : ℝ) / (g : ℝ)

/-- The mixed head–tail kernel `𝒯_{s,N}(x) = T_{m,N}(x) · Θ_{k,N}(x)`
(`residue_packetization.tex`, Def. [Head–tail approximant]). -/
noncomputable def mixedKernel (m g k N : ℕ) (x : ℝ) : ℝ :=
  tailTerm m N x * (slice g k N x / slice g 0 N x)

/-- The diagonal zeta approximant `Z_N(s) = Σ_{n=1}^N 𝒯_{s,N}(n)`. -/
noncomputable def diagZeta (m g k N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, mixedKernel m g k N (n : ℝ)

/-
Pointwise recovery of the integer power by the normalized tail:
`T_{m,N}(x) → x^{−m}` for `x > 0` (equivalently, `headTerm → 0`).
-/
theorem tendsto_tailTerm (m : ℕ) {x : ℝ} (hx : 0 < x) :
    Filter.Tendsto (fun N : ℕ => tailTerm m N x)
      Filter.atTop (nhds ((x ^ m)⁻¹)) := by
        -- We want to show that the head term tends to zero.
        have h_headTerm_to_zero : Filter.Tendsto (fun N => headTerm m N x) Filter.atTop (nhds 0) := by
          -- The numerator is a fixed finite sum in j<m of choose N (2j) x^j, polynomial growth in N,
          -- while denominator includes slice 2 0 N x which grows exponentially.
          have h_num_denom : Filter.Tendsto (fun N => headPoly m N x / slice 2 0 N x) Filter.atTop (nhds 0) := by
            -- The sum of the even terms in the binomial expansion of $(1 + \sqrt{x})^N$ is given by $\frac{(1 + \sqrt{x})^N + (1 - \sqrt{x})^N}{2}$.
            have h_even_sum : ∀ N : ℕ, slice 2 0 N x = ((1 + Real.sqrt x) ^ N + (1 - Real.sqrt x) ^ N) / 2 := by
              intro N
              have := two_mul_square_even N (Real.sqrt x)
              simp_all +decide [ slice ];
              rw [ ← this, Real.sq_sqrt hx.le ] ; ring;
            -- The polynomial part grows much slower than the exponential part.
            have h_poly_growth : Filter.Tendsto (fun N => headPoly m N x / ((1 + Real.sqrt x) ^ N)) Filter.atTop (nhds 0) := by
              -- The polynomial part grows much slower than the exponential part, so we can bound it above.
              have h_poly_bound : ∀ N : ℕ, headPoly m N x ≤ ∑ j ∈ Finset.range m, (N ^ (2 * j) : ℝ) * x ^ j := by
                intro N; exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right ( mod_cast Nat.le_trans ( Nat.choose_le_pow _ _ ) ( by ring_nf; norm_num ) ) ( pow_nonneg hx.le _ ) ;
              -- Each term in the sum $\sum_{j=0}^{m-1} N^{2j} x^j$ divided by $(1 + \sqrt{x})^N$ tends to zero as $N$ tends to infinity.
              have h_term_zero : ∀ j < m, Filter.Tendsto (fun N : ℕ => (N ^ (2 * j) : ℝ) * x ^ j / (1 + Real.sqrt x) ^ N) Filter.atTop (nhds 0) := by
                intro j hj
                have h_term_zero : Filter.Tendsto (fun N : ℕ => (N ^ (2 * j) : ℝ) / (1 + Real.sqrt x) ^ N) Filter.atTop (nhds 0) := by
                  -- We can convert this limit into a form that is easier to handle by substituting $y = N \log(1 + \sqrt{x})$.
                  suffices h_log : Filter.Tendsto (fun y : ℝ => (y / Real.log (1 + Real.sqrt x)) ^ (2 * j) / Real.exp y) Filter.atTop (nhds 0) by
                    convert h_log.comp ( tendsto_natCast_atTop_atTop.atTop_mul_const ( Real.log_pos <| show 1 + Real.sqrt x > 1 by norm_num; positivity ) ) using 2 ; norm_num [ Real.exp_nat_mul, Real.exp_log ( show 0 < 1 + Real.sqrt x by positivity ) ];
                    rw [ mul_div_cancel_right₀ _ ( ne_of_gt ( Real.log_pos ( by norm_num; positivity ) ) ) ];
                  -- We can factor out $(1 / \log(1 + \sqrt{x}))^{2j}$ from the limit.
                  suffices h_factor : Filter.Tendsto (fun y : ℝ => y ^ (2 * j) / Real.exp y) Filter.atTop (nhds 0) by
                    convert h_factor.div_const ( Real.log ( 1 + Real.sqrt x ) ^ ( 2 * j ) ) using 2 <;> ring;
                  simpa [ Real.exp_neg ] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero ( 2 * j );
                convert h_term_zero.const_mul ( x ^ j ) using 2 <;> ring;
              refine' squeeze_zero ( fun N => div_nonneg ( headPoly_nonneg m N hx.le ) ( by positivity ) ) ( fun N => div_le_div_of_nonneg_right ( h_poly_bound N ) ( by positivity ) ) _;
              simpa [ Finset.sum_div _ _ _ ] using tendsto_finset_sum _ fun j hj => h_term_zero j ( Finset.mem_range.mp hj );
            -- Since $(1 - \sqrt{x})^N$ is bounded, we can factor it out of the limit.
            have h_factor : Filter.Tendsto (fun N => ((1 + Real.sqrt x) ^ N + (1 - Real.sqrt x) ^ N) / (1 + Real.sqrt x) ^ N) Filter.atTop (nhds 1) := by
              norm_num [ add_div ];
              norm_num [ ne_of_gt ( show 0 < 1 + Real.sqrt x from by positivity ) ];
              exact le_trans ( tendsto_const_nhds.add ( tendsto_pow_atTop_nhds_zero_of_abs_lt_one ( show |(1 - Real.sqrt x) / (1 + Real.sqrt x)| < 1 from by rw [ abs_div, abs_of_nonneg ( by positivity : ( 0 : ℝ ) ≤ 1 + Real.sqrt x ) ] ; rw [ div_lt_iff₀ ( by positivity ) ] ; cases abs_cases ( 1 - Real.sqrt x ) <;> nlinarith [ Real.sqrt_nonneg x, Real.sq_sqrt hx.le ] ) |> Filter.Tendsto.congr ( by intros; rw [ div_pow ] ) ) ) ( by norm_num );
            convert h_poly_growth.const_mul 2 |> Filter.Tendsto.mul <| h_factor.inv₀ one_ne_zero using 2 <;> norm_num [ h_even_sum ] ; ring;
            -- Let's simplify the expression.
            field_simp
            ring;
            norm_num [ show ( 1 + Real.sqrt x ) ≠ 0 by positivity ]
          generalize_proofs at *;
          convert h_num_denom.div_const ( x ^ m ) using 2 <;> norm_num [ headTerm, hx.ne' ] ; ring;
        simpa using h_headTerm_to_zero.const_sub ( ( x ^ m ) ⁻¹ ) |> Filter.Tendsto.congr ( by intros; linarith [ head_tail_identity m ( ‹_› : ℕ ) hx ] )

/-
Pointwise convergence of the mixed kernel to the rational power:
`𝒯_{s,N}(x) → x^{−s}` for `x > 0`
(`residue_packetization.tex`, Thm. [Uniform approximation], pointwise form).
-/
theorem tendsto_mixedKernel {m g k : ℕ} (hg : 0 < g) (hk : k < g)
    {x : ℝ} (hx : 0 < x) :
    Filter.Tendsto (fun N : ℕ => mixedKernel m g k N x)
      Filter.atTop (nhds (x ^ (-sVal m k g))) := by
        convert Filter.Tendsto.mul ( tendsto_tailTerm m hx ) ( tendsto_slice_ratio_rpow hg hk hx ) using 1 ; norm_num [ sVal ] ; ring;
        rw [ Real.rpow_sub hx, Real.rpow_neg hx.le ] ; norm_cast ; norm_num ; ring

/-
**Diagonal approximation to ζ(s)** (`residue_packetization.tex`,
Thm. [Diagonal approximation]): for rational `s = m + k/g > 1`,
`Z_N(s) → ζ(s)`, with `ζ(s)` written as the tsum of `n^{−s}` over `n ≥ 1`.
-/
theorem tendsto_diagZeta {m g k : ℕ} (hg : 2 ≤ g) (hk : k < g)
    (hs : 1 < sVal m k g) :
    Filter.Tendsto (fun N : ℕ => diagZeta m g k N)
      Filter.atTop (nhds (∑' n : ℕ, ((n + 1 : ℝ) ^ (-sVal m k g)))) := by
        -- For each $n$, the term $\mathcal{T}_{s,N}(n)$ converges to $n^{-s}$ as $N \to \infty$.
        have h_term : ∀ n : ℕ, n ≥ 1 → Filter.Tendsto (fun N => mixedKernel m g k N (n : ℝ)) Filter.atTop (nhds ((n : ℝ) ^ (-sVal m k g))) := by
          exact fun n hn => tendsto_mixedKernel ( by linarith ) ( by linarith ) ( by positivity );
        convert tendsto_tsum_of_dominated_convergence _ _ _;
        rotate_left;
        exact inferInstance;
        use fun N n => if n + 1 ≤ N then mixedKernel m g k N ( n + 1 : ℝ ) else 0;
        use fun n => ( n + 1 : ℝ ) ^ ( -sVal m k g ) * ( 1 + 4 * ( g - 1 ) );
        · exact Summable.mul_right _ <| by simpa using summable_nat_add_iff 1 |>.2 <| Real.summable_nat_rpow.2 <| by linarith;
        · intro n; specialize h_term ( n + 1 ) ( by linarith ) ; simp_all +decide ;
          exact Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_gt_atTop n ] with x hx; aesop ) h_term;
        · -- By definition of $mixedKernel$, we know that for $n \geq 1$, $mixedKernel m g k N (n : ℝ)$ is bounded by $(n : ℝ) ^ (-sVal m k g) * (1 + 4 * (g - 1))$.
          have h_bound : ∀ᶠ N in Filter.atTop, ∀ n : ℕ, n ≥ 1 → n ≤ N → |mixedKernel m g k N (n : ℝ)| ≤ (n : ℝ) ^ (-sVal m k g) * (1 + 4 * (g - 1)) := by
            have h_bound : ∀ᶠ N in Filter.atTop, ∀ n : ℕ, n ≥ 1 → n ≤ N → |slice g k N (n : ℝ) / slice g 0 N (n : ℝ) - (n : ℝ) ^ (-(k : ℝ) / (g : ℝ))| ≤ 4 * (g - 1) * (n : ℝ) ^ (-(k : ℝ) / (g : ℝ)) * Real.exp (-(diagGap g * (N : ℝ) ^ (1 - (g : ℝ)⁻¹))) := by
              obtain ⟨ N₀, hN₀ ⟩ := diagonal_threshold_eventually hg;
              filter_upwards [ Filter.eventually_ge_atTop N₀ ] with N hN;
              intro n hn hnN;
              convert diagonal_slice_ratio_bound hg hk ( Complex.isPrimitiveRoot_exp _ _ ) hn hnN ( hN₀ N hN ) using 1;
              · ring;
              · linarith;
            have h_bound : ∀ᶠ N in Filter.atTop, ∀ n : ℕ, n ≥ 1 → n ≤ N → |slice g k N (n : ℝ) / slice g 0 N (n : ℝ)| ≤ (n : ℝ) ^ (-(k : ℝ) / (g : ℝ)) * (1 + 4 * (g - 1)) := by
              filter_upwards [ h_bound, Filter.eventually_gt_atTop 0 ] with N hN hN' n hn hn' ; specialize hN n hn hn' ; rw [ abs_le ] at * ; constructor <;> nlinarith [ show ( n : ℝ ) ^ ( -k / g : ℝ ) ≥ 0 by positivity, show ( 4 : ℝ ) * ( g - 1 ) ≥ 0 by exact mul_nonneg zero_le_four ( sub_nonneg.mpr <| Nat.one_le_cast.mpr <| by linarith ), Real.exp_pos ( - ( diagGap g * ( N : ℝ ) ^ ( 1 - ( g : ℝ ) ⁻¹ ) ) ), Real.exp_le_one_iff.mpr <| show - ( diagGap g * ( N : ℝ ) ^ ( 1 - ( g : ℝ ) ⁻¹ ) ) ≤ 0 by exact neg_nonpos.mpr <| mul_nonneg ( show 0 ≤ diagGap g by exact div_nonneg ( sub_nonneg.mpr <| Real.cos_le_one _ ) zero_le_four ) <| Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ] ;
            have h_bound : ∀ᶠ N in Filter.atTop, ∀ n : ℕ, n ≥ 1 → n ≤ N → |tailTerm m N (n : ℝ)| ≤ (n : ℝ) ^ (-m : ℝ) := by
              have h_bound : ∀ᶠ N in Filter.atTop, ∀ n : ℕ, n ≥ 1 → n ≤ N → tailTerm m N (n : ℝ) ≤ (n : ℝ) ^ (-m : ℝ) := by
                have h_bound : ∀ᶠ N in Filter.atTop, ∀ n : ℕ, n ≥ 1 → n ≤ N → tailTerm m N (n : ℝ) + headTerm m N (n : ℝ) = (n : ℝ) ^ (-m : ℝ) := by
                  simp +zetaDelta at *;
                  exact ⟨ 1, fun N hN n hn hn' => head_tail_identity m N ( by positivity ) ⟩;
                filter_upwards [ h_bound ] with N hN n hn hn' using by linarith [ hN n hn hn', show 0 ≤ headTerm m N ( n : ℝ ) from headTerm_nonneg m N ( by positivity ) ] ;
              filter_upwards [ h_bound ] with N hN n hn hn' using by rw [ abs_of_nonneg ( tailTerm_nonneg m N ( by positivity ) ) ] ; exact hN n hn hn';
            filter_upwards [ h_bound, ‹∀ᶠ N in Filter.atTop, ∀ n ≥ 1, n ≤ N → |slice g k N ( n : ℝ ) / slice g 0 N ( n : ℝ )| ≤ ( n : ℝ ) ^ ( - ( k : ℝ ) / ( g : ℝ ) ) * ( 1 + 4 * ( g - 1 ) ) › ] with N hN₁ hN₂ n hn hn' ; simp_all +decide [ sVal ];
            convert mul_le_mul ( hN₁ n hn hn' ) ( hN₂ n hn hn' ) ( by positivity ) ( by positivity ) using 1 ; ring;
            · rw [ ← abs_mul ] ; unfold mixedKernel ; ring;
            · rw [ Real.rpow_add ( by positivity ), Real.rpow_neg ( by positivity ) ] ; ring;
              norm_num [ Real.rpow_neg ( by positivity : 0 ≤ ( n : ℝ ) ) ] ; ring;
          filter_upwards [ h_bound ] with N hN k ; split_ifs <;> simp_all +decide ;
          · exact_mod_cast hN ( k + 1 ) ( by linarith ) ( by linarith );
          · exact mul_nonneg ( Real.rpow_nonneg ( by positivity ) _ ) ( by linarith [ show ( g : ℝ ) ≥ 2 by norm_cast ] );
        · rw [ tsum_eq_sum ];
          any_goals exact Finset.range ‹_›;
          · rw [ Finset.sum_congr rfl fun i hi => if_pos <| by linarith [ Finset.mem_range.mp hi ] ] ; norm_cast;
            exact Eq.symm ( by rw [ show diagZeta m g k _ = ∑ n ∈ Finset.Icc 1 _, mixedKernel m g k _ _ from rfl ] ; erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ' ] );
          · grind

/-
Integral-test bound for the tail of a real-exponent p-series.
-/
lemma real_rpow_tsum_tail_bound {s : ℝ} (hs : 1 < s) {N : ℕ} (hN : 1 ≤ N) :
    (∑' n : ℕ, ((n + N + 1 : ℝ) ^ (-s))) ≤
      (N : ℝ) ^ (1 - s) / (s - 1) := by
        -- For each $n$, the term $(n+N+1)^{-s}$ is less than or equal to the integral of $x^{-s}$ over $[n+N, n+N+1]$.
        have h_integral_bound : ∀ n : ℕ, (n + N + 1 : ℝ) ^ (-s) ≤ ∫ x in (n + N : ℝ).. (n + N + 1 : ℝ), x ^ (-s) := by
          intro n
          have h_integral_bound : ∀ x ∈ Set.Icc (n + N : ℝ) (n + N + 1 : ℝ), x ^ (-s) ≥ (n + N + 1 : ℝ) ^ (-s) := by
            intro x hx; rw [ ge_iff_le ] ; rw [ Real.rpow_le_rpow_iff_of_neg ] <;> linarith [ hx.1, hx.2, show ( n : ℝ ) + N ≥ 1 by norm_cast; linarith ] ;
          refine' le_trans _ ( intervalIntegral.integral_mono_on _ _ _ h_integral_bound ) <;> norm_num;
          apply_rules [ intervalIntegral.intervalIntegrable_rpow ] ; norm_num;
          exact Or.inr fun h => by linarith [ show ( N : ℝ ) ≥ 1 by norm_cast ] ;
        -- Summing the inequalities from the integral test, we get the desired result.
        have h_sum_integral_bound : ∀ M : ℕ, ∑ n ∈ Finset.range M, (n + N + 1 : ℝ) ^ (-s) ≤ ∫ x in (N : ℝ)..((M + N) : ℝ), x ^ (-s) := by
          intro M
          induction' M with M ih;
          · norm_num;
          · convert add_le_add ih ( h_integral_bound M ) using 1 <;> push_cast [ Finset.sum_range_succ ] <;> ring;
            rw [ intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ intervalIntegral.intervalIntegrable_rpow ] <;> norm_num;
            · exact Or.inr fun h => by linarith;
            · exact Or.inr fun h => by linarith [ show ( N : ℝ ) ≥ 1 by norm_cast ] ;
        -- Taking the limit of the integral bound as $M$ approaches infinity, we get the desired result.
        have h_limit_integral_bound : Filter.Tendsto (fun M : ℕ => ∫ x in (N : ℝ)..((M + N) : ℝ), x ^ (-s)) Filter.atTop (nhds (∫ x in Set.Ioi (N : ℝ), x ^ (-s))) := by
          apply_rules [ MeasureTheory.intervalIntegral_tendsto_integral_Ioi ];
          · rw [ integrableOn_Ioi_rpow_iff ] <;> norm_num ; linarith;
            linarith;
          · exact Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop;
        convert le_of_tendsto_of_tendsto' ( Summable.hasSum ( show Summable _ from _ ) |> HasSum.tendsto_sum_nat ) h_limit_integral_bound h_sum_integral_bound using 1;
        · rw [ integral_Ioi_rpow_of_lt ] <;> norm_num [ hs ];
          · rw [ ← neg_div_neg_eq ] ; ring;
          · linarith;
        · exact_mod_cast summable_nat_add_iff ( N + 1 ) |>.2 <| Real.summable_nat_rpow.2 <| by linarith;

/-
The normalized finite head is uniformly polynomial times exponentially small.
-/
lemma headTerm_uniform_bound {m : ℕ} (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N ≥ 1, ∀ n ∈ Finset.Icc 1 N,
      headTerm m N (n : ℝ) ≤
        C * (N : ℝ) ^ (2 * m - 2) * ((2 : ℝ)⁻¹) ^ N := by
          refine' ⟨ 8 * m, by positivity, fun N hN n hn => _ ⟩;
          -- By definition of $headTerm$, we have:
          have h_headTerm_def : headTerm m N (n : ℝ) ≤ (∑ j ∈ Finset.range m, (N.choose (2 * j) : ℝ) * (n : ℝ) ^ j) / ((2 : ℝ) ^ (N - 1) * (n : ℝ) ^ m) := by
            have h_headTerm_def : slice 2 0 N (n : ℝ) ≥ (2 : ℝ) ^ (N - 1) := by
              have h_slice_ge : slice 2 0 N (n : ℝ) ≥ slice 2 0 N 1 := by
                refine' Finset.sum_le_sum fun i hi => _;
                split_ifs <;> norm_num;
                exact le_mul_of_one_le_right ( Nat.cast_nonneg _ ) ( one_le_pow₀ ( mod_cast Finset.mem_Icc.mp hn |>.1 ) );
              have := two_mul_square_even N 1;
              cases N <;> norm_num [ pow_succ' ] at * ; linarith;
            refine' div_le_div_of_nonneg_left _ _ _;
            · exact headPoly_nonneg m N ( Nat.cast_nonneg _ );
            · exact mul_pos ( pow_pos ( by norm_num ) _ ) ( pow_pos ( Nat.cast_pos.mpr ( Finset.mem_Icc.mp hn |>.1 ) ) _ );
            · rw [ mul_comm ] ; gcongr;
          -- By definition of $headPoly$, we have:
          have h_headPoly_bound : (∑ j ∈ Finset.range m, (N.choose (2 * j) : ℝ) * (n : ℝ) ^ j) ≤ m * (N : ℝ) ^ (2 * m - 2) * (n : ℝ) ^ m := by
            have h_headPoly_bound : ∀ j ∈ Finset.range m, (N.choose (2 * j) : ℝ) * (n : ℝ) ^ j ≤ (N : ℝ) ^ (2 * m - 2) * (n : ℝ) ^ m := by
              intros j hj
              have h_choose_bound : (N.choose (2 * j) : ℝ) ≤ (N : ℝ) ^ (2 * j) := by
                exact_mod_cast Nat.le_trans ( Nat.choose_le_pow _ _ ) ( by norm_num );
              gcongr;
              · exact le_trans h_choose_bound ( pow_le_pow_right₀ ( mod_cast hN ) ( Nat.le_sub_of_add_le ( by linarith [ Finset.mem_range.mp hj ] ) ) );
              · exact_mod_cast Finset.mem_Icc.mp hn |>.1;
              · linarith [ Finset.mem_range.mp hj ];
            simpa [ mul_assoc ] using Finset.sum_le_sum h_headPoly_bound;
          rcases N with ( _ | N ) <;> simp_all +decide [ pow_succ' ];
          refine le_trans h_headTerm_def ?_;
          rw [ div_le_iff₀ ( by exact mul_pos ( pow_pos ( by norm_num ) _ ) ( pow_pos ( Nat.cast_pos.mpr hn.1 ) _ ) ) ];
          field_simp;
          nlinarith [ show 0 ≤ ( m : ℝ ) * ( N + 1 ) ^ ( 2 * m - 2 ) * n ^ m by positivity ]

/-
Uniform pointwise error for the mixed kernel on the diagonal range.
-/
lemma mixedKernel_diagonal_error {m g k : ℕ} (hm : 1 ≤ m)
    (hg : 2 ≤ g) (hk : k < g) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ n ∈ Finset.Icc 1 N,
      |((n : ℝ) ^ (-sVal m k g)) - mixedKernel m g k N (n : ℝ)| ≤
        C * (N : ℝ) ^ (2 * m - 2) * ((2 : ℝ)⁻¹) ^ N +
        D * Real.exp (-(diagGap g * (N : ℝ) ^ (1 - (g : ℝ)⁻¹))) := by
          obtain ⟨C₁, hC₁⟩ := headTerm_uniform_bound hm;
          obtain ⟨N₀, hN₀⟩ := diagonal_threshold_eventually hg;
          refine' ⟨ 3 * C₁, 4 * ( g - 1 ), _, _, N₀ + 1, _ ⟩ <;> try linarith;
          · linarith [ show ( g : ℝ ) ≥ 2 by norm_cast ];
          · intro N hN n hn;
            -- Set a=tailTerm, e=headTerm, b=slice ratio, c=n^(-k/g), p=n^-m.
            set a := tailTerm m N (n : ℝ)
            set e := headTerm m N (n : ℝ)
            set b := slice g k N (n : ℝ) / slice g 0 N (n : ℝ)
            set c := (n : ℝ) ^ (-(k : ℝ) / (g : ℝ))
            set p := (n : ℝ) ^ (-m : ℝ);
            -- Identities: a+e=p by head_tail_identity converted to real rpow; n^-s=p*c via rpow_add.
            have h_identities : a + e = p ∧ (n : ℝ) ^ (-sVal m k g) = p * c := by
              apply And.intro;
              · convert head_tail_identity m N ( Nat.cast_pos.mpr <| Finset.mem_Icc.mp hn |>.1 ) using 1;
                simp +zetaDelta at *;
              · rw [ ← Real.rpow_add ( by norm_cast; linarith [ Finset.mem_Icc.mp hn ] ) ] ; unfold sVal ; ring;
            -- Then p*c-a*b = e*b + p*(c-b). Triangle.
            have h_triangle : |p * c - a * b| ≤ e * |b| + p * |c - b| := by
              rw [ abs_le ];
              constructor <;> cases abs_cases b <;> cases abs_cases ( c - b ) <;> nlinarith [ show 0 ≤ a by exact tailTerm_nonneg m N ( by norm_cast; linarith [ Finset.mem_Icc.mp hn ] ), show 0 ≤ e by exact headTerm_nonneg m N ( by norm_cast; linarith [ Finset.mem_Icc.mp hn ] ) ];
            -- Diagonal bound gives |b-c|≤D*eN*c. Threshold plus exp≤1 gives |b|≤c*(1+2) or c*(1+D), so head contribution ≤ a constant multiple of supplied C bound since c≤1 for n≥1. p*c≤1 likewise, so spectral contribution ≤D eN.
            have h_bounds : |b - c| ≤ 4 * (g - 1) * Real.exp (-(diagGap g * (N : ℝ) ^ (1 - (g : ℝ)⁻¹))) * c ∧ |b| ≤ 3 * c := by
              have h_bounds : |b - c| ≤ 4 * (g - 1) * Real.exp (-(diagGap g * (N : ℝ) ^ (1 - (g : ℝ)⁻¹))) * c := by
                convert diagonal_slice_ratio_bound hg hk ( Complex.isPrimitiveRoot_exp _ _ ) ( Finset.mem_Icc.mp hn |>.1 ) ( Finset.mem_Icc.mp hn |>.2 ) ( hN₀ N ( by linarith ) ) using 1;
                linarith;
              have h_bounds : |b| ≤ c + |b - c| := by
                cases abs_cases ( b - c ) <;> cases abs_cases b <;> linarith [ show 0 ≤ c by positivity ];
              exact ⟨ by assumption, by nlinarith [ show ( g : ℝ ) ≥ 2 by norm_cast, show ( n : ℝ ) ^ ( -k / g : ℝ ) ≥ 0 by positivity, hN₀ N ( by linarith ) ] ⟩;
            -- Since $c \leq 1$ for $n \geq 1$, we have $p * |c - b| \leq 4 * (g - 1) * \exp(-(diagGap g * N^{1 - 1/g}))$.
            have h_p_c_b : p * |c - b| ≤ 4 * (g - 1) * Real.exp (-(diagGap g * (N : ℝ) ^ (1 - (g : ℝ)⁻¹))) := by
              have h_p_c_b : p * |c - b| ≤ p * (4 * (g - 1) * Real.exp (-(diagGap g * (N : ℝ) ^ (1 - (g : ℝ)⁻¹))) * c) := by
                exact mul_le_mul_of_nonneg_left ( by simpa only [ abs_sub_comm ] using h_bounds.1 ) ( by positivity );
              refine le_trans h_p_c_b ?_;
              rw [ mul_left_comm ];
              refine' mul_le_of_le_one_right ( mul_nonneg ( mul_nonneg zero_le_four ( sub_nonneg.mpr ( Nat.one_le_cast.mpr ( by linarith ) ) ) ) ( Real.exp_nonneg _ ) ) _;
              rw [ ← Real.rpow_add ( by norm_cast; linarith [ Finset.mem_Icc.mp hn ] ) ];
              exact le_trans ( Real.rpow_le_rpow_of_exponent_le ( mod_cast Finset.mem_Icc.mp hn |>.1 ) ( show ( -m + -k / g : ℝ ) ≤ 0 by exact add_nonpos ( neg_nonpos.mpr ( Nat.cast_nonneg _ ) ) ( div_nonpos_of_nonpos_of_nonneg ( neg_nonpos.mpr ( Nat.cast_nonneg _ ) ) ( Nat.cast_nonneg _ ) ) ) ) ( by norm_num );
            -- Since $c \leq 1$ for $n \geq 1$, we have $e * |b| \leq 3 * e$.
            have h_e_b : e * |b| ≤ 3 * e := by
              rw [ mul_comm ];
              exact mul_le_mul_of_nonneg_right ( h_bounds.2.trans ( mul_le_of_le_one_right ( by norm_num ) ( by exact le_trans ( Real.rpow_le_rpow_of_exponent_le ( mod_cast Finset.mem_Icc.mp hn |>.1 ) ( show ( -k : ℝ ) / g ≤ 0 by exact div_nonpos_of_nonpos_of_nonneg ( neg_nonpos.mpr ( Nat.cast_nonneg _ ) ) ( Nat.cast_nonneg _ ) ) ) ( by norm_num ) ) ) ) ( by exact div_nonneg ( headPoly_nonneg _ _ ( Nat.cast_nonneg _ ) ) ( mul_nonneg ( pow_nonneg ( Nat.cast_nonneg _ ) _ ) ( one_le_slice_zero _ _ ( Nat.cast_nonneg _ ) |> le_trans ( by norm_num ) ) ) );
            convert h_triangle.trans ( add_le_add h_e_b h_p_c_b ) |> le_trans <| add_le_add ( mul_le_mul_of_nonneg_left ( hC₁.2 N ( by linarith ) n hn ) zero_le_three ) le_rfl using 1 ; ring;
            · exact h_identities.2.symm ▸ rfl;
            · ring

/-
**Three-term error estimate** (same theorem, quantitative form):
for all sufficiently large `N`,
`|ζ(s) − Z_N(s)| ≤ N^(1−s)/(s−1) + C·N^(2m−1)·2^(−N)
  + D·N·exp(−c_g·N^(1−1/g))`.
-/
theorem diagZeta_error_bound {m g k : ℕ} (hg : 2 ≤ g) (hk : k < g)
    (hs : 1 < sVal m k g) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      |(∑' n : ℕ, ((n + 1 : ℝ) ^ (-sVal m k g))) - diagZeta m g k N| ≤
        (N : ℝ) ^ (1 - sVal m k g) / (sVal m k g - 1)
        + C * (N : ℝ) ^ (2 * m - 1) * ((2 : ℝ)⁻¹) ^ N
        + D * (N : ℝ) *
            Real.exp (-(diagGap g * (N : ℝ) ^ (1 - (g : ℝ)⁻¹))) := by
              have hm : 1 ≤ m := by
                contrapose! hs; simp_all +decide [ sVal ] ;
                exact div_le_one_of_le₀ ( mod_cast hk.le ) ( by positivity );
              obtain ⟨ C, D, hC, hD, N₀, hN₀ ⟩ := mixedKernel_diagonal_error hm hg hk;
              refine' ⟨ C, D, hC, hD, N₀ + 1, fun N hN => _ ⟩;
              have h_split : |∑' n : ℕ, ((n + 1 : ℝ) ^ (-sVal m k g)) - diagZeta m g k N| ≤ (∑' n : ℕ, ((n + N + 1 : ℝ) ^ (-sVal m k g))) + (∑ n ∈ Finset.Icc 1 N, |((n : ℝ) ^ (-sVal m k g)) - mixedKernel m g k N (n : ℝ)|) := by
                have h_split : ∑' n : ℕ, ((n + 1 : ℝ) ^ (-sVal m k g)) = ∑ n ∈ Finset.range N, ((n + 1 : ℝ) ^ (-sVal m k g)) + ∑' n : ℕ, ((n + N + 1 : ℝ) ^ (-sVal m k g)) := by
                  rw [ ← Summable.sum_add_tsum_nat_add ];
                  norm_cast;
                  exact_mod_cast summable_nat_add_iff 1 |>.2 <| Real.summable_nat_rpow.2 <| by linarith;
                have h_split : ∑ n ∈ Finset.Icc 1 N, ((n : ℝ) ^ (-sVal m k g)) = ∑ n ∈ Finset.range N, ((n + 1 : ℝ) ^ (-sVal m k g)) := by
                  erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ' ];
                have h_split : |∑ n ∈ Finset.Icc 1 N, ((n : ℝ) ^ (-sVal m k g)) - diagZeta m g k N| ≤ ∑ n ∈ Finset.Icc 1 N, |((n : ℝ) ^ (-sVal m k g)) - mixedKernel m g k N (n : ℝ)| := by
                  convert Finset.abs_sum_le_sum_abs _ _ using 2 ; aesop;
                  infer_instance;
                cases abs_cases ( ∑' n : ℕ, ( n + 1 : ℝ ) ^ ( -sVal m k g ) - diagZeta m g k N ) <;> cases abs_cases ( ∑ n ∈ Finset.Icc 1 N, ( n : ℝ ) ^ ( -sVal m k g ) - diagZeta m g k N ) <;> linarith [ show 0 ≤ ∑' n : ℕ, ( n + N + 1 : ℝ ) ^ ( -sVal m k g ) from tsum_nonneg fun _ => Real.rpow_nonneg ( by positivity ) _ ];
              refine le_trans h_split ?_;
              refine' le_trans ( add_le_add ( real_rpow_tsum_tail_bound hs ( by linarith ) ) ( Finset.sum_le_sum fun n hn => hN₀ N ( by linarith ) n hn ) ) _;
              rcases m with ( _ | m ) <;> simp_all +decide [ Nat.mul_succ, pow_succ' ] ; ring_nf ; norm_num

end ResidueSlices