/-
Target statements for Aristotle: the shifted/reversed rational approximants
`R_N(x; k, g) = A_N(x,k,g) / B_N(x,g)` of
`residue_slice_rational_approximation.tex`, with the corrected endpoint
treatment (Lemma [Relation with the forward slice family], as repaired):
the forward-slice relation holds for `1 ≤ k < g`, while at `k = 0` the
denominator carries the explicit `ε_N` endpoint correction, which is
nonzero exactly when `g ∣ N`.

Build on the existing development.  Key available tools:
`slice`, `one_le_slice_zero`, `slice_nonneg` (ResidueSlices.lean);
`packet_principal_deviation` (ExplicitSpectralRate.lean) — it gives
`g·slice g 0 N (t^g) ≥ (1+t)^N · (1 − (g−1)ρ^N)`, so the zeroth slice grows
like `(1+t)^N/g`, which dominates the endpoint power below.

Proof route for the convergence theorem: with `u = x⁻¹` and `t = u^(1/g)`,
the relation lemmas reduce the ratio to
`slice g k N u / (slice g 0 N u − ε_N·u^(q_N+1))`; the endpoint satisfies
`u^(q_N+1) = t^(g(q_N+1))` with `N ≤ g(q_N+1) ≤ N+g−1`, hence
`u^(q_N+1) ≤ max(1,t)^g · t^N`, while `slice g 0 N (t^g) ≳ (1+t)^N / (2g)`
for large `N` by `packet_principal_deviation`; since `t/(1+t) < 1` the
endpoint contribution vanishes and the slice-ratio limit
(`tendsto_general_slice_ratio`) gives the reversed limit `x^(k/g)`.

Every theorem below is a requested result.  Minor Mathlib-name adjustments are
fine; keep the mathematical content of each statement.
-/
import RequestProject.DiagonalZeta

open scoped BigOperators

namespace ResidueSlices

/-- Reversal degree `q_N = ⌊(N−1)/g⌋` (natural-number division). -/
def qIdx (g N : ℕ) : ℕ := (N - 1) / g

/-- Endpoint indicator `ε_N`: `1` when `g ∣ N`, else `0`. -/
noncomputable def epsIdx (g N : ℕ) : ℝ := if g ∣ N then 1 else 0

/-- The reversed (shifted) numerator polynomial
`A_N(x,k,g) = ∑_{j=0}^{q_N} C(N, gj+k) x^(q_N − j)`.
The denominator of the approximant is `revA g 0 N x`. -/
noncomputable def revA (g k N : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (qIdx g N + 1),
    (N.choose (g * j + k) : ℝ) * x ^ (qIdx g N - j)

/-
**Corrected forward-slice relation, numerator case** (`1 ≤ k < g`):
away from the `k = 0` endpoint, reversal is exact — every omitted slice
index has vanishing binomial coefficient.
-/
theorem revA_eq_slice {g k N : ℕ} (hg : 0 < g) (hk1 : 1 ≤ k) (hkg : k < g)
    {x : ℝ} (hx : 0 < x) :
    revA g k N x = x ^ qIdx g N * slice g k N x⁻¹ := by
      unfold revA slice qIdx;
      rw [ Finset.mul_sum _ _ _ ];
      rw [ ← Finset.sum_subset ( Finset.subset_iff.mpr _ ) ];
      any_goals exact Finset.filter ( fun j => g * j + k < N + 1 ) ( Finset.range ( ( N - 1 ) / g + 1 ) );
      · rw [ ← Finset.sum_subset ( show Finset.image ( fun j => g * j + k ) ( Finset.filter ( fun j => g * j + k < N + 1 ) ( Finset.range ( ( N - 1 ) / g + 1 ) ) ) ⊆ Finset.range ( N + 1 ) from ?_ ) ];
        · rw [ Finset.sum_image ] <;> norm_num;
          · rw [ if_pos ( Nat.mod_eq_of_lt hkg ) ] ; refine' Finset.sum_congr rfl fun i hi => _ ; rw [ show ( g * i + k ) / g = i by nlinarith [ Nat.div_mul_le_self ( g * i + k ) g, Nat.div_add_mod ( g * i + k ) g, Nat.mod_lt ( g * i + k ) hg ] ] ; ring;
            rw [ mul_assoc, show x ^ ( ( N - 1 ) / g ) = x ^ ( ( N - 1 ) / g - i ) * x ^ i by rw [ ← pow_add, Nat.sub_add_cancel ( show i ≤ ( N - 1 ) / g from Finset.mem_range_succ_iff.mp ( Finset.mem_filter.mp hi |>.1 ) ) ] ] ; ring;
            simp +decide [ mul_assoc, mul_comm, hx.ne' ];
          · exact fun a ha b hb hab => by nlinarith;
        · intro j hj₁ hj₂; contrapose! hj₂; simp_all +decide ;
          exact ⟨ j / g, ⟨ Nat.le_div_iff_mul_le hg |>.2 <| Nat.le_sub_one_of_lt <| by nlinarith [ Nat.mod_add_div j g ], by nlinarith [ Nat.mod_add_div j g ] ⟩, by linarith [ Nat.mod_add_div j g ] ⟩;
        · exact Finset.image_subset_iff.mpr fun j hj => Finset.mem_range.mpr <| Finset.mem_filter.mp hj |>.2;
      · simp +contextual [ Nat.choose_eq_zero_of_lt ];
      · aesop

/-
**Corrected forward-slice relation, denominator case** (`k = 0`, `N ≥ 1`):
the zeroth slice overshoots the reversed polynomial by exactly the `ε_N`
endpoint term, present precisely when `g ∣ N`.
-/
theorem revB_eq_slice {g N : ℕ} (hg : 0 < g) (hN : 1 ≤ N)
    {x : ℝ} (hx : 0 < x) :
    revA g 0 N x
      = x ^ qIdx g N * (slice g 0 N x⁻¹ - epsIdx g N * (x⁻¹) ^ (qIdx g N + 1)) := by
        unfold revA slice epsIdx qIdx;
        -- Split the sum into two parts: one where $j$ is a multiple of $g$ and one where it is not.
        have h_split : ∑ j ∈ Finset.range (N + 1), (if j % g = 0 then (N.choose j : ℝ) * x⁻¹ ^ (j / g) else 0) = ∑ j ∈ Finset.range ((N - 1) / g + 1), (N.choose (g * j) : ℝ) * x⁻¹ ^ j + (if g ∣ N then (N.choose N : ℝ) * x⁻¹ ^ (N / g) else 0) := by
          have h_split : Finset.filter (fun j => j % g = 0) (Finset.range (N + 1)) = Finset.image (fun j => g * j) (Finset.range ((N - 1) / g + 1)) ∪ (if g ∣ N then {N} else ∅) := by
            ext j
            simp [Finset.mem_union, Finset.mem_image];
            constructor;
            · intro hj
              by_cases h_div : j = N;
              · exact Or.inr ( by rw [ if_pos ( Nat.dvd_of_mod_eq_zero ( by aesop ) ) ] ; aesop );
              · exact Or.inl ⟨ j / g, Nat.le_div_iff_mul_le hg |>.2 <| Nat.le_sub_one_of_lt <| by linarith [ Nat.mod_add_div j g, Nat.lt_of_le_of_ne hj.1 h_div ], Nat.mul_div_cancel' <| Nat.dvd_of_mod_eq_zero hj.2 ⟩;
            · rintro ( ⟨ a, ha, rfl ⟩ | h ) <;> simp_all +decide [ Nat.dvd_iff_mod_eq_zero ];
              · nlinarith [ Nat.div_mul_le_self ( N - 1 ) g, Nat.sub_add_cancel hN ];
              · split_ifs at h <;> simp_all +decide;
          rw [ ← Finset.sum_filter, h_split, Finset.sum_union ] <;> norm_num;
          · split_ifs <;> simp_all +decide [ Finset.sum_image, hg.ne' ];
          · split_ifs <;> simp_all +decide [ Finset.disjoint_left ];
            intro a ha; nlinarith [ Nat.div_mul_le_self ( N - 1 ) g, Nat.sub_add_cancel hN, Nat.le_of_dvd hN ‹_› ] ;
        split_ifs at * <;> simp_all +decide [ Nat.dvd_iff_mod_eq_zero ];
        · rw [ show N / g = ( N - 1 ) / g + 1 from ?_ ];
          · simp +decide [ Finset.mul_sum _ _ _, mul_assoc, mul_comm, pow_add ];
            exact Finset.sum_congr rfl fun i hi => by rw [ inv_mul_eq_div, eq_div_iff ( pow_ne_zero _ hx.ne' ) ] ; rw [ mul_assoc, ← pow_add, tsub_add_cancel_of_le ( Finset.mem_range_succ_iff.mp hi ) ] ;
          · cases N <;> simp_all +decide [ Nat.succ_div ];
            exact Nat.dvd_of_mod_eq_zero ‹_›;
        · rw [ Finset.mul_sum _ _ _ ] ; refine' Finset.sum_congr rfl fun i hi => _ ; rw [ show x ^ ( ( N - 1 ) / g - i ) = x ^ ( ( N - 1 ) / g ) / x ^ i by rw [ eq_div_iff ( pow_ne_zero _ hx.ne' ), ← pow_add, Nat.sub_add_cancel ( Finset.mem_range_succ_iff.mp hi ) ] ] ; ring;

/-
Strict positivity of the reversed polynomials on the positive axis
(for `k ≤ N` the `j = 0` term `C(N,k)·x^(q_N)` is strictly positive and all
terms are nonnegative).  With `k = 0` this is pole-freeness of the
approximant family: the denominator never vanishes for `x > 0`.
-/
theorem revA_pos {g k N : ℕ} (hkN : k ≤ N) {x : ℝ} (hx : 0 < x) :
    0 < revA g k N x := by
      refine' lt_of_lt_of_le _ ( Finset.single_le_sum ( fun j _ => by positivity ) ( Finset.mem_range.mpr ( Nat.succ_pos _ ) ) ) ; norm_num [ hx ];
      exact Nat.choose_pos hkN

/-
**Positive-axis convergence of the reversed approximants**
(`residue_slice_rational_approximation.tex`, Thm. [Geometric convergence]):
`R_N(x;k,g) = A_N/B_N → x^(k/g)` for every `x > 0` — the positive-exponent
counterpart of `tendsto_slice_ratio_rpow`, via the corrected relation lemmas.
At `k = 0` the statement is the trivial `R_N ≡ 1`.
-/
theorem tendsto_reversed_ratio {g k : ℕ} (hg : 0 < g) (hk : k < g)
    {x : ℝ} (hx : 0 < x) :
    Filter.Tendsto (fun N : ℕ => revA g k N x / revA g 0 N x)
      Filter.atTop (nhds (x ^ ((k : ℝ) / (g : ℝ)))) := by
        by_cases hk0 : k = 0;
        · simp_all +decide [ div_self, ne_of_gt ( revA_pos _ _ ) ];
        · -- By revA_eq_slice and revB_eq_slice, we can rewrite the ratio.
          have h_ratio : ∀ N ≥ 1, k ≤ N → (revA g k N x) / (revA g 0 N x) = (slice g k N (x⁻¹) / (slice g 0 N (x⁻¹) - epsIdx g N * (x⁻¹) ^ (qIdx g N + 1))) := by
            intro N hN hkN
            have h_revA_k : revA g k N x = x ^ (qIdx g N) * slice g k N (x⁻¹) := by
              exact revA_eq_slice hg ( Nat.pos_of_ne_zero hk0 ) hk hx
            have h_revA_0 : revA g 0 N x = x ^ (qIdx g N) * (slice g 0 N (x⁻¹) - epsIdx g N * (x⁻¹) ^ (qIdx g N + 1)) := by
              convert revB_eq_slice hg hN hx using 1
            rw [h_revA_k, h_revA_0]
            field_simp [hx.ne'];
          -- Prove that $E_N / S_0(N) \to 0$.
          have h_endpoints : Filter.Tendsto (fun N => epsIdx g N * (x⁻¹) ^ (qIdx g N + 1) / slice g 0 N (x⁻¹)) Filter.atTop (nhds 0) := by
            -- By packet_principal_deviation at k'=0, we have g * S_0(N) ≥ (1+t)^N / 2 for large N.
            have h_bound : ∃ N0 : ℕ, ∀ N ≥ N0, g * slice g 0 N (x⁻¹) ≥ (1 + x⁻¹ ^ ((g : ℝ))⁻¹) ^ N / 2 := by
              have h_bound : ∃ N0 : ℕ, ∀ N ≥ N0, (g - 1) * spectralGap g (x⁻¹ ^ ((g : ℝ))⁻¹) (Complex.exp (2 * Real.pi * Complex.I / g)) ^ N ≤ 1 / 2 := by
                have h_bound : Filter.Tendsto (fun N => (g - 1) * spectralGap g (x⁻¹ ^ ((g : ℝ))⁻¹) (Complex.exp (2 * Real.pi * Complex.I / g)) ^ N) Filter.atTop (nhds 0) := by
                  have h_spectralGap_lt_one : spectralGap g (x⁻¹ ^ ((g : ℝ))⁻¹) (Complex.exp (2 * Real.pi * Complex.I / g)) < 1 := by
                    apply (spectralGap_mem_unitInterval hg (by positivity) (by
                    exact Complex.isPrimitiveRoot_exp _ hg.ne')).right;
                  simpa using tendsto_const_nhds.mul ( tendsto_pow_atTop_nhds_zero_of_lt_one ( show 0 ≤ spectralGap g ( x⁻¹ ^ ( g : ℝ ) ⁻¹ ) ( Complex.exp ( 2 * Real.pi * Complex.I / g ) ) from by
                                                                                                exact le_trans ( by norm_num ) ( Finset.le_max' _ _ ( Finset.mem_insert_self _ _ ) ) ) h_spectralGap_lt_one );
                simpa using h_bound.eventually ( ge_mem_nhds <| by norm_num );
              obtain ⟨ N0, hN0 ⟩ := h_bound;
              use N0 + 1;
              intro N hN;
              have := packet_principal_deviation hg ( show 0 < g from hg ) ( show 0 < x⁻¹ ^ ( ( g : ℝ ) ⁻¹ ) from by positivity ) ( show IsPrimitiveRoot ( Complex.exp ( 2 * Real.pi * Complex.I / g ) ) g from by
                                                                                                                                      exact Complex.isPrimitiveRoot_exp _ hg.ne' ) N
              generalize_proofs at *;
              rw [ show ( x⁻¹ ^ ( g : ℝ ) ⁻¹ ) ^ g = x⁻¹ by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ), inv_mul_cancel₀ ( by positivity ), Real.rpow_one ] ] at this;
              nlinarith [ abs_le.mp this, hN0 N ( by linarith ), show ( 1 + x⁻¹ ^ ( g : ℝ ) ⁻¹ ) ^ N > 0 by positivity ];
            -- Also endpoint u^(q+1)=t^(g(q+1)) and N≤g(q+1)≤N+g-1, bound by max(1,t)^g*t^N.
            have h_endpoint_bound : ∃ C : ℝ, ∀ N ≥ 1, epsIdx g N * (x⁻¹) ^ (qIdx g N + 1) ≤ C * (x⁻¹ ^ ((g : ℝ))⁻¹) ^ N := by
              -- Since $epsIdx g N$ is either 0 or 1, we can bound it by 1.
              use max 1 (x⁻¹ ^ ((g : ℝ))⁻¹) ^ g;
              intro N hN; rw [ epsIdx ] ; split_ifs <;> norm_num;
              · obtain ⟨ m, rfl ⟩ := ‹g ∣ N›; norm_num [ pow_mul, qIdx ] ; ring_nf; norm_num [ hx.ne' ] ;
                rw [ ← Real.rpow_natCast _ ( g * m ), ← Real.rpow_mul ( by positivity ), mul_comm ] ; norm_num [ hg.ne' ];
                rw [ show ( g * m - 1 ) / g = m - 1 from ?_ ];
                · rcases m <;> simp_all +decide [ pow_succ, mul_assoc ];
                  rw [ mul_comm ] ; gcongr;
                  exact le_mul_of_one_le_right ( by positivity ) ( one_le_pow₀ ( le_max_left _ _ ) );
                · exact Nat.le_antisymm ( Nat.le_sub_one_of_lt <| Nat.div_lt_of_lt_mul <| by rw [ tsub_lt_iff_left ] <;> nlinarith [ Nat.sub_add_cancel <| show 1 ≤ m from Nat.pos_of_ne_zero <| by aesop_cat ] ) ( Nat.le_div_iff_mul_le hg |>.2 <| Nat.le_sub_one_of_lt <| by nlinarith [ Nat.sub_add_cancel <| show 1 ≤ m from Nat.pos_of_ne_zero <| by aesop_cat ] );
              · positivity;
            -- Thus E/S0 ≤ constant*(t/(1+t))^N→0.
            obtain ⟨C, hC⟩ := h_endpoint_bound
            have h_final_bound : ∃ N0 : ℕ, ∀ N ≥ N0, epsIdx g N * (x⁻¹) ^ (qIdx g N + 1) / slice g 0 N (x⁻¹) ≤ 2 * g * C * (x⁻¹ ^ ((g : ℝ))⁻¹ / (1 + x⁻¹ ^ ((g : ℝ))⁻¹)) ^ N := by
              obtain ⟨ N0, hN0 ⟩ := h_bound; use Max.max N0 1; intro N hN; specialize hC N ( by linarith [ le_max_right N0 1 ] ) ; specialize hN0 N ( by linarith [ le_max_left N0 1 ] ) ; rw [ div_pow ] ; rw [ mul_div ] ; rw [ div_le_div_iff₀ ] <;> norm_num at *;
              · nlinarith [ show 0 ≤ ( 1 + x⁻¹ ^ ( g : ℝ ) ⁻¹ ) ^ N by positivity, show 0 ≤ C * ( x⁻¹ ^ ( g : ℝ ) ⁻¹ ) ^ N by exact mul_nonneg ( show 0 ≤ C by
                                                                                                                                                  contrapose! hC;
                                                                                                                                                  exact lt_of_lt_of_le ( mul_neg_of_neg_of_pos hC ( by positivity ) ) ( mul_nonneg ( by unfold epsIdx; positivity ) ( by positivity ) ) ) ( pow_nonneg ( by positivity ) _ ) ];
              · exact slice_zero_pos g N ( by positivity );
              · positivity;
            refine' squeeze_zero_norm' _ _;
            use fun N => 2 * g * C * ( x⁻¹ ^ ( g : ℝ ) ⁻¹ / ( 1 + x⁻¹ ^ ( g : ℝ ) ⁻¹ ) ) ^ N;
            · filter_upwards [ Filter.eventually_ge_atTop h_final_bound.choose ] with N hN using by rw [ Real.norm_of_nonneg ( div_nonneg ( mul_nonneg ( by unfold epsIdx; positivity ) ( by positivity ) ) ( by exact le_of_lt ( slice_zero_pos _ _ ( by positivity ) ) ) ) ] ; exact h_final_bound.choose_spec N hN;
            · exact MulZeroClass.mul_zero ( 2 * g * C ) ▸ tendsto_const_nhds.mul ( tendsto_pow_atTop_nhds_zero_of_lt_one ( by positivity ) ( by rw [ div_lt_iff₀ ( by positivity ) ] ; linarith [ Real.rpow_pos_of_pos ( inv_pos.mpr hx ) ( ( g : ℝ ) ⁻¹ ) ] ) );
          -- By tendsto_general_slice_ratio, we know that $S_k(N) / S_0(N) \to t^{-k}$.
          have h_slice_ratio : Filter.Tendsto (fun N => slice g k N (x⁻¹) / slice g 0 N (x⁻¹)) Filter.atTop (nhds ((x⁻¹) ^ (-(k : ℝ) / (g : ℝ)))) := by
            convert tendsto_slice_ratio_rpow hg hk ( inv_pos.mpr hx ) using 1;
          -- Rewrite the quotient as $(S_k/S_0)/(1-E_N/S_0)$.
          have h_quotient : Filter.Tendsto (fun N => (slice g k N (x⁻¹) / slice g 0 N (x⁻¹)) / (1 - epsIdx g N * (x⁻¹) ^ (qIdx g N + 1) / slice g 0 N (x⁻¹))) Filter.atTop (nhds ((x⁻¹) ^ (-(k : ℝ) / (g : ℝ)))) := by
            convert h_slice_ratio.div ( tendsto_const_nhds.sub h_endpoints ) _ using 2 <;> norm_num;
          refine' Filter.Tendsto.congr' _ ( h_quotient.trans _ );
          · filter_upwards [ Filter.eventually_ge_atTop 1, Filter.eventually_ge_atTop k ] with N hN₁ hN₂ using by rw [ h_ratio N hN₁ hN₂, div_div, mul_sub, mul_one, mul_div_cancel₀ _ ( ne_of_gt <| slice_zero_pos _ _ <| by positivity ) ] ;
          · norm_num [ neg_div, Real.rpow_neg_eq_inv_rpow ]

/-
Optional stretch goals, if the above goes smoothly:

1. Quantitative version: the error is `O(max(ρ(s,g), s/(1+s))^N)` with
   `s = x^(-1/g)` — the combined rate from the corrected endpoint analysis.

2. Monotonicity of `revA g 0 N x` in `x` on the positive axis.
-/

end ResidueSlices