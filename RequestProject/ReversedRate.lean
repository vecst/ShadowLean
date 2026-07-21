/-
Target statements for Aristotle: the combined geometric rate for the
shifted/reversed approximants of `ReversedApproximants.lean`, i.e. the
paper's claimed `O(max(ρ, t/(1+t))^N)` rate
(`residue_slice_rational_approximation.tex`).

Fixed data: `0 < g`, `k < g`, `x > 0`, with
  t = (x⁻¹) ^ (1/g),   ω = exp(2πi/g),
  ρ = spectralGap g t ω,   r = t/(1+t),   R = max ρ r.

Available tools:
- `revA`, `revA_eq_slice` (1 ≤ k < g), `revB_eq_slice`, `revA_pos`,
  `tendsto_reversed_ratio` (ReversedApproximants.lean);
- `general_slice_ratio_spectral_rate_exp` and
  `general_slice_ratio_explicit_rate_exp` for the forward error `≤ C·ρ^N`;
- `spectralGap_mem_unitInterval` for `0 ≤ ρ < 1`;
- `tendstoUniformlyOn_endpointCorrection` (CompactUniform.lean): the
  correction `epsIdx g N · (x⁻¹)^(q_N+1) / slice g 0 N (x⁻¹) → 0`.

Proof route:
- k = 0: the reversed ratio is identically 1 and x^(0/g)=1, error 0.
- k > 0: `revA_eq_slice`/`revB_eq_slice` write the reversed ratio as
  forwardRatio / (1 − correction), where forwardRatio =
  slice g k N (x⁻¹)/slice g 0 N (x⁻¹) has error ≤ C₁·ρ^N and the
  correction has |·| ≤ C₂·r^N; eventually |correction| ≤ 1/2 so
  |1 − correction|⁻¹ ≤ 2, and both terms are ≤ R^N.

Every `sorry` is a requested result.  Minor Mathlib-name adjustments are
fine; keep the mathematical content of each statement.
-/
import RequestProject.CompactUniform

open scoped BigOperators
open Asymptotics

namespace ResidueSlices

/-- The reversal variable `t = (x⁻¹)^(1/g)`. -/
noncomputable def revT (g : ℕ) (x : ℝ) : ℝ := (x⁻¹) ^ ((g : ℝ)⁻¹)

/-- The combined geometric rate `R = max(ρ, t/(1+t))`, with
`ρ = spectralGap g t ω` and `ω = exp(2πi/g)`. -/
noncomputable def combinedRate (g : ℕ) (x : ℝ) : ℝ :=
  max (spectralGap g (revT g x) (Complex.exp (2 * Real.pi * Complex.I / g)))
      (revT g x / (1 + revT g x))

/-
**Target 1.** The combined rate lies in `[0, 1)`; handles `g = 1`
(empty subordinate set, `ρ = 0`) and every `t > 0`.
-/
theorem combinedRate_mem_unitInterval {g : ℕ} (hg : 0 < g) {x : ℝ} (hx : 0 < x) :
    0 ≤ combinedRate g x ∧ combinedRate g x < 1 := by
      refine' ⟨ le_max_of_le_left _, max_lt _ _ ⟩;
      · exact le_trans ( by norm_num ) ( spectralGap_mem_unitInterval hg ( by exact Real.rpow_pos_of_pos ( inv_pos.mpr hx ) _ ) ( Complex.isPrimitiveRoot_exp g hg.ne' ) |>.1 );
      · apply (spectralGap_mem_unitInterval hg (by
        exact Real.rpow_pos_of_pos ( inv_pos.mpr hx ) _) (Complex.isPrimitiveRoot_exp g hg.ne')).right;
      · rw [ div_lt_iff₀ ] <;> linarith [ show 0 < revT g x from by exact Real.rpow_pos_of_pos ( inv_pos.mpr hx ) _ ]

/-
**Target 2.** The corrected endpoint term decays at the geometric rate
`r = t/(1+t)`.
-/
theorem endpointCorrection_geometric_bound {g : ℕ} (hg : 0 < g) {x : ℝ} (hx : 0 < x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      |epsIdx g N * (x⁻¹) ^ (qIdx g N + 1) / slice g 0 N (x⁻¹)|
        ≤ C * (revT g x / (1 + revT g x)) ^ N := by
          refine' ⟨ 2 * ( g : ℝ ) * ( Max.max 1 ( x⁻¹ ^ ( ( g : ℝ ) ⁻¹ ) ) ) ^ g, by positivity, _ ⟩;
          obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ N ≥ N₁, |(epsIdx g N * x⁻¹ ^ (qIdx g N + 1))| ≤ (max 1 (x⁻¹ ^ ((g : ℝ)⁻¹))) ^ g * (x⁻¹ ^ ((g : ℝ)⁻¹)) ^ N := by
            use 1; intro N hN; by_cases h : g ∣ N <;> simp_all +decide [ epsIdx ] ;
            · obtain ⟨ k, rfl ⟩ := h; norm_num [ qIdx ] ; ring_nf; norm_num [ hx.ne', hg.ne' ] ;
              rw [ abs_of_pos hx ] ; ring_nf ; norm_num [ hg.ne' ] ;
              rw [ ← Real.rpow_natCast _ ( g * k ), ← Real.rpow_mul ( by positivity ) ] ; norm_num [ hg.ne' ];
              rw [ show ( g * k - 1 ) / g = k - 1 from ?_, show k = k - 1 + 1 from ?_ ] <;> norm_num [ pow_add, pow_mul, hx.ne' ];
              · exact le_mul_of_one_le_right ( by positivity ) ( one_le_pow₀ ( le_max_left _ _ ) );
              · rw [ Nat.sub_add_cancel ( by nlinarith ) ];
              · exact Nat.le_antisymm ( Nat.le_sub_one_of_lt ( Nat.div_lt_of_lt_mul <| by rw [ tsub_lt_iff_left ] <;> nlinarith [ Nat.sub_add_cancel ( by nlinarith : 1 ≤ g * k ) ] ) ) ( Nat.le_div_iff_mul_le hg |>.2 <| Nat.le_sub_one_of_lt <| by nlinarith [ Nat.sub_add_cancel ( by nlinarith : 1 ≤ k ) ] );
            · positivity;
          obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, ∀ N ≥ N₂, |(slice g 0 N x⁻¹)| ≥ (1 + x⁻¹ ^ ((g : ℝ)⁻¹)) ^ N / (2 * (g : ℝ)) := by
            have := @packet_principal_deviation g 0 hg ( by linarith ) ( x⁻¹ ^ ( ( g : ℝ ) ⁻¹ ) ) ( by positivity );
            -- Choose $N₂$ such that for all $N ≥ N₂$, $(g - 1) * spectralGap g (x⁻¹ ^ ((g : ℝ)⁻¹)) ω ^ N ≤ 1 / 2$.
            obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, ∀ N ≥ N₂, (g - 1) * spectralGap g (x⁻¹ ^ ((g : ℝ)⁻¹)) (Complex.exp (2 * Real.pi * Complex.I / g)) ^ N ≤ 1 / 2 := by
              have h_spectralGap_lt_one : spectralGap g (x⁻¹ ^ ((g : ℝ)⁻¹)) (Complex.exp (2 * Real.pi * Complex.I / g)) < 1 := by
                apply (spectralGap_mem_unitInterval hg (by positivity) (by
                exact Complex.isPrimitiveRoot_exp _ hg.ne')).right;
              have h_spectralGap_pow_zero : Filter.Tendsto (fun N => (g - 1) * spectralGap g (x⁻¹ ^ ((g : ℝ)⁻¹)) (Complex.exp (2 * Real.pi * Complex.I / g)) ^ N) Filter.atTop (nhds 0) := by
                convert tendsto_const_nhds.mul ( tendsto_pow_atTop_nhds_zero_of_lt_one _ h_spectralGap_lt_one ) using 2 ; norm_num;
                exact Finset.le_max' _ _ ( Finset.mem_insert_self _ _ ) |> le_trans ( by norm_num );
              simpa using h_spectralGap_pow_zero.eventually ( ge_mem_nhds <| by norm_num );
            use N₂; intro N hN; specialize this ( show IsPrimitiveRoot ( Complex.exp ( 2 * Real.pi * Complex.I / g ) ) g from ?_ ) N; simp_all +decide [ ← Real.rpow_natCast, ← Real.rpow_mul ( inv_nonneg.mpr hx.le ) ] ;
            · exact Complex.isPrimitiveRoot_exp _ hg.ne';
            · rw [ show ( x⁻¹ ^ ( g : ℝ ) ⁻¹ ) ^ g = x⁻¹ by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ), inv_mul_cancel₀ ( by positivity ), Real.rpow_one ] ] at this;
              rw [ abs_le ] at this;
              rw [ ge_iff_le, div_le_iff₀ ] <;> cases abs_cases ( slice g 0 N x⁻¹ ) <;> nlinarith [ show ( g : ℝ ) ≥ 1 by norm_cast, hN₂ N hN, show ( 1 + x⁻¹ ^ ( ( g : ℝ ) ⁻¹ ) ) ^ N > 0 by positivity ];
          refine' ⟨ Max.max N₁ N₂, fun N hN => _ ⟩ ; simp_all +decide [ abs_div, div_pow ];
          refine' le_trans ( div_le_div_of_nonneg_left _ _ ( hN₂ N hN.2 ) ) _;
          · positivity;
          · positivity;
          · convert div_le_div_of_nonneg_right ( hN₁ N hN.1 ) ( by positivity : 0 ≤ ( 1 + x⁻¹ ^ ( g : ℝ ) ⁻¹ ) ^ N / ( 2 * g ) ) using 1 ; ring_nf!;
            grind

/-
**Target 3.** The reversed approximant converges at the combined rate
`R = max(ρ, t/(1+t))` — the paper's `O(max(ρ, t/(1+t))^N)` claim.
-/
theorem reversed_ratio_geometric_bound {g k : ℕ} (hg : 0 < g) (hk : k < g)
    {x : ℝ} (hx : 0 < x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      |revA g k N x / revA g 0 N x - x ^ ((k : ℝ) / (g : ℝ))|
        ≤ C * (combinedRate g x) ^ N := by
          by_cases hk0 : k = 0 <;> simp_all +decide [ div_eq_mul_inv ];
          · refine' ⟨ 0, by norm_num, 0, fun N hN => _ ⟩ ; norm_num [ ne_of_gt ( revA_pos ( show 0 ≤ N by linarith ) hx ) ];
          · -- Use the results from general_slice_ratio_spectral_rate_exp and endpointCorrection_geometric_bound.
            obtain ⟨C1, hC1_nonneg, N1, hN1⟩ : ∃ C1 : ℝ, 0 ≤ C1 ∧ ∃ N1 : ℕ, ∀ N ≥ N1, |slice g k N (x⁻¹) / slice g 0 N (x⁻¹) - (revT g x) ^ (-k : ℝ)| ≤ C1 * (spectralGap g (revT g x) (Complex.exp (2 * Real.pi * Complex.I / g))) ^ N := by
              have := general_slice_ratio_spectral_rate_exp hg hk ( show 0 < revT g x from by exact Real.rpow_pos_of_pos ( inv_pos.mpr hx ) _ );
              obtain ⟨ C, hC₀, hC ⟩ := this; use C, hC₀, 0; intro N hN; convert hC N using 1; norm_cast; norm_num [ Real.rpow_neg, hx.le, hg.ne' ] ;
              unfold revT; norm_num [ ← Real.rpow_natCast, ← Real.rpow_mul ( inv_nonneg.mpr hx.le ), hg.ne' ] ;
            obtain ⟨C2, hC2_nonneg, N2, hN2⟩ : ∃ C2 : ℝ, 0 ≤ C2 ∧ ∃ N2 : ℕ, ∀ N ≥ N2, |epsIdx g N * (x⁻¹) ^ (qIdx g N + 1) / slice g 0 N (x⁻¹)| ≤ C2 * (revT g x / (1 + revT g x)) ^ N := by
              convert endpointCorrection_geometric_bound hg hx using 1;
            -- Use the results from tendstoUniformlyOn_endpointCorrection to find N3 such that for all N ≥ N3, |correction| ≤ 1/2.
            obtain ⟨N3, hN3⟩ : ∃ N3 : ℕ, ∀ N ≥ N3, |epsIdx g N * (x⁻¹) ^ (qIdx g N + 1) / slice g 0 N (x⁻¹)| ≤ 1 / 2 := by
              have hN3 : Filter.Tendsto (fun N => |epsIdx g N * (x⁻¹) ^ (qIdx g N + 1) / slice g 0 N (x⁻¹)|) Filter.atTop (nhds 0) := by
                refine' squeeze_zero_norm' _ _;
                use fun N => C2 * ( revT g x / ( 1 + revT g x ) ) ^ N;
                · filter_upwards [ Filter.eventually_ge_atTop N2 ] with N hN using by simpa using hN2 N hN;
                · exact MulZeroClass.mul_zero ( C2 : ℝ ) ▸ tendsto_const_nhds.mul ( tendsto_pow_atTop_nhds_zero_of_lt_one ( by exact div_nonneg ( Real.rpow_nonneg ( inv_nonneg.2 hx.le ) _ ) ( by exact add_nonneg zero_le_one ( Real.rpow_nonneg ( inv_nonneg.2 hx.le ) _ ) ) ) ( by rw [ div_lt_iff₀ ] <;> linarith [ show 0 < revT g x from Real.rpow_pos_of_pos ( inv_pos.2 hx ) _ ] ) );
              simpa using hN3.eventually ( ge_mem_nhds <| by norm_num );
            refine' ⟨ 2 * C1 + 2 * |revT g x ^ (-k : ℝ)| * C2, _, Max.max N1 (Max.max N2 (Max.max N3 1)), _ ⟩ <;> norm_num;
            · positivity;
            · intro N hN1 hN2 hN3 hN4
              have h_ratio : revA g k N x / revA g 0 N x = (slice g k N (x⁻¹) / slice g 0 N (x⁻¹)) / (1 - epsIdx g N * (x⁻¹) ^ (qIdx g N + 1) / slice g 0 N (x⁻¹)) := by
                rw [ revA_eq_slice hg ( Nat.pos_of_ne_zero hk0 ) hk hx, revB_eq_slice hg hN4 hx ];
                rw [ mul_div_mul_left _ _ ( by positivity ), div_div, mul_sub, mul_one, mul_div_cancel₀ _ ( by exact ne_of_gt ( slice_zero_pos _ _ ( by positivity ) ) ) ];
              have h_bound : |revA g k N x / revA g 0 N x - revT g x ^ (-k : ℝ)| ≤ 2 * |slice g k N (x⁻¹) / slice g 0 N (x⁻¹) - revT g x ^ (-k : ℝ)| + 2 * |revT g x ^ (-k : ℝ)| * |epsIdx g N * (x⁻¹) ^ (qIdx g N + 1) / slice g 0 N (x⁻¹)| := by
                have h_bound : |revA g k N x / revA g 0 N x - revT g x ^ (-k : ℝ)| ≤ |slice g k N (x⁻¹) / slice g 0 N (x⁻¹) - revT g x ^ (-k : ℝ)| / |1 - epsIdx g N * (x⁻¹) ^ (qIdx g N + 1) / slice g 0 N (x⁻¹)| + |revT g x ^ (-k : ℝ)| * |epsIdx g N * (x⁻¹) ^ (qIdx g N + 1) / slice g 0 N (x⁻¹)| / |1 - epsIdx g N * (x⁻¹) ^ (qIdx g N + 1) / slice g 0 N (x⁻¹)| := by
                  rw [ h_ratio, ← abs_div ];
                  rw [ ← abs_mul, ← abs_div ];
                  rw [ show slice g k N x⁻¹ / slice g 0 N x⁻¹ / ( 1 - epsIdx g N * x⁻¹ ^ ( qIdx g N + 1 ) / slice g 0 N x⁻¹ ) - revT g x ^ ( -k : ℝ ) = ( slice g k N x⁻¹ / slice g 0 N x⁻¹ - revT g x ^ ( -k : ℝ ) ) / ( 1 - epsIdx g N * x⁻¹ ^ ( qIdx g N + 1 ) / slice g 0 N x⁻¹ ) + revT g x ^ ( -k : ℝ ) * ( epsIdx g N * x⁻¹ ^ ( qIdx g N + 1 ) / slice g 0 N x⁻¹ ) / ( 1 - epsIdx g N * x⁻¹ ^ ( qIdx g N + 1 ) / slice g 0 N x⁻¹ ) by
                        grind ];
                  grind;
                have h_bound : |1 - epsIdx g N * (x⁻¹) ^ (qIdx g N + 1) / slice g 0 N (x⁻¹)| ≥ 1 / 2 := by
                  cases abs_cases ( 1 - epsIdx g N * x⁻¹ ^ ( qIdx g N + 1 ) / slice g 0 N x⁻¹ ) <;> linarith [ abs_le.mp ( ‹∀ N ≥ N3, |epsIdx g N * x⁻¹ ^ ( qIdx g N + 1 ) / slice g 0 N x⁻¹| ≤ 1 / 2› N hN3 ) ];
                refine le_trans ‹_› ?_;
                exact add_le_add ( by rw [ div_le_iff₀ ] <;> nlinarith [ abs_nonneg ( slice g k N x⁻¹ / slice g 0 N x⁻¹ - revT g x ^ ( -k : ℝ ) ) ] ) ( by rw [ div_le_iff₀ ] <;> nlinarith [ abs_nonneg ( revT g x ^ ( -k : ℝ ) ), abs_nonneg ( epsIdx g N * x⁻¹ ^ ( qIdx g N + 1 ) / slice g 0 N x⁻¹ ), mul_nonneg ( abs_nonneg ( revT g x ^ ( -k : ℝ ) ) ) ( abs_nonneg ( epsIdx g N * x⁻¹ ^ ( qIdx g N + 1 ) / slice g 0 N x⁻¹ ) ) ] );
              convert h_bound.trans _ using 1;
              · unfold revT; norm_num [ Real.rpow_neg, Real.rpow_mul, hx.le ] ; ring_nf;
                norm_num [ Real.inv_rpow hx.le, Real.rpow_neg hx.le ];
                rw [ ← Real.rpow_natCast, ← Real.rpow_mul hx.le, ← Real.rpow_natCast, ← Real.rpow_mul hx.le ] ; ring_nf;
              · refine' le_trans ( add_le_add ( mul_le_mul_of_nonneg_left ( by solve_by_elim ) zero_le_two ) ( mul_le_mul_of_nonneg_left ( by solve_by_elim ) ( by positivity ) ) ) _;
                unfold combinedRate; ring_nf; norm_num;
                refine' add_le_add _ _;
                · gcongr;
                  · exact Finset.le_max' _ _ ( Finset.mem_insert_self _ _ ) |> le_trans ( by norm_num );
                  · exact le_max_left _ _;
                · norm_num [ mul_assoc, mul_comm, mul_left_comm, ← div_eq_mul_inv ];
                  rw [ mul_div_right_comm ];
                  rw [ mul_comm ] ; gcongr;
                  rw [ ← div_pow ] ; exact pow_le_pow_left₀ ( by exact div_nonneg ( by exact Real.rpow_nonneg ( inv_nonneg.2 hx.le ) _ ) ( by exact add_nonneg zero_le_one ( Real.rpow_nonneg ( inv_nonneg.2 hx.le ) _ ) ) ) ( le_max_right _ _ ) _;

/-
**Target 4 (optional).** The same result in `IsBigO` form at `atTop`.
-/
theorem reversed_ratio_isBigO {g k : ℕ} (hg : 0 < g) (hk : k < g)
    {x : ℝ} (hx : 0 < x) :
    (fun N : ℕ => revA g k N x / revA g 0 N x - x ^ ((k : ℝ) / (g : ℝ)))
      =O[Filter.atTop] (fun N : ℕ => (combinedRate g x) ^ N) := by
        obtain ⟨ C, hC₀, N₀, hN₀ ⟩ := reversed_ratio_geometric_bound hg hk hx;
        rw [ Asymptotics.isBigO_iff ];
        exact ⟨ C, Filter.eventually_atTop.mpr ⟨ N₀, fun N hN => by simpa only [ Real.norm_eq_abs, abs_pow, abs_of_nonneg ( show 0 ≤ combinedRate g x by linarith [ combinedRate_mem_unitInterval hg hx ] ) ] using hN₀ N hN ⟩ ⟩

end ResidueSlices