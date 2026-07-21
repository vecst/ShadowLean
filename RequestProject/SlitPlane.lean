/-
Principal-branch (slit-plane) convergence of the residue-slice ratio.

This is the complex-domain analogue of `tendsto_slice_ratio_rpow`
(`RpowCorollaries.lean`) and formalizes
`residue_slice_rational_approximation.tex`,
Thm. [Principal-branch convergence on the slit plane]:
for `x ∈ ℂ ∖ (−∞,0]` (i.e. `x ∈ Complex.slitPlane`),
  slice g k N x⁻¹ / slice g 0 N x⁻¹  →  x ^ (k/g)   (principal branch).

Available tools (all over ℂ already):
- `roots_of_unity_filter` (GeneralResidueConvergence.lean):
    ∑_a ω^(a(g−k)) (1 + t ω^a)^N = g · t^k · slice g k N (t^g), for t : ℂ.
- `tendsto_general_slice_ratio_of_dominance` and
  `tendsto_finite_mode_sum_zero` — the real-case dominance→limit skeleton to
  mirror over ℂ.
- `Complex.slitPlane`, `Complex.continuousOn_arg`, `Complex.cpow_natCast`,
  `Complex.cpow_mul`, `Complex.norm_natCast`.

Crux (Target 1).  Spectral dominance in the principal sector.  With
`s = |s|·e^{iθ}`, `|θ| < π/g`, and `ω^ℓ = e^{2πiℓ/g}`,
  ‖1 + ω^ℓ s‖² = 1 + ‖s‖² + 2·Re(ω^ℓ s),
so ‖1 + ω^ℓ s‖ < ‖1 + s‖ ⟺ Re(ω^ℓ s) < Re(s) ⟺ cos(θ + 2πℓ/g) < cos θ.
For every ℓ = 1,…,g−1 the shifted angle θ + 2πℓ/g reduces (mod 2π) to
magnitude ≥ 2π/g − |θ| > π/g − ... in fact ≥ π/g > |θ|, so the cosine
strictly drops.  (`s ≠ 0` is needed for strictness.)

Route (Target 2).  `x ∈ slitPlane ⟹ x⁻¹ ∈ slitPlane`, so
`s := (x⁻¹) ^ ((g:ℂ)⁻¹)` (principal `cpow`) satisfies `s ≠ 0`, `s^g = x⁻¹`,
and `|arg s| < π/g`.  Apply `roots_of_unity_filter` at `t = s`:
`g · s^k · slice g k N x⁻¹ = ∑_a ω^(a(g−k)) (1 + s ω^a)^N`, dominant term
`ℓ = 0` equal to `(1+s)^N`.  Target 1 makes every other channel strictly
smaller in modulus, so dividing by `(1+s)^N` and taking `N → ∞` sends the
subordinate modes to `0` (as in the real proof).  Hence
`slice g k N x⁻¹ / slice g 0 N x⁻¹ → s^(−k) = x^(k/g)` in the principal
branch (`cpow_mul` / `cpow_natCast` bookkeeping on the slit plane).

Every `sorry` is a requested result.  Minor Mathlib-name adjustments are
fine; keep the mathematical content of each statement.  (Local uniformity
and the reversed/endpoint `A_N/B_N` form are deliberately out of scope for
this run.)
-/
import RequestProject.RpowCorollaries

open scoped BigOperators

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

namespace ResidueSlices

/-
**Target 1 — complex spectral dominance.**  In the principal sector
`|arg s| < π/g` (with `s ≠ 0`), every nontrivial roots-of-unity channel is
strictly dominated by the principal one.
-/
theorem norm_one_add_root_mul_lt {g ℓ : ℕ} (hg : 0 < g)
    (hℓ0 : ℓ ≠ 0) (hℓg : ℓ < g) {s : ℂ} (hs : s ≠ 0)
    (harg : |s.arg| < Real.pi / (g : ℝ)) :
    ‖1 + Complex.exp (2 * Real.pi * Complex.I * (ℓ : ℂ) / (g : ℂ)) * s‖
      < ‖1 + s‖ := by
        -- By the properties of the argument function and the periodicity of the exponential function, we can simplify the expression.
        have h_arg : |s.arg + 2 * Real.pi * ℓ / g| > |s.arg| := by
          cases abs_cases ( s.arg + 2 * Real.pi * ℓ / g ) <;> cases abs_cases s.arg <;> nlinarith [ show ( ℓ : ℝ ) ≥ 1 by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hℓ0, show ( g : ℝ ) ≥ ℓ + 1 by exact_mod_cast hℓg, Real.pi_pos, mul_div_cancel₀ ( 2 * Real.pi * ℓ ) ( by positivity : ( g : ℝ ) ≠ 0 ), mul_div_cancel₀ ( Real.pi : ℝ ) ( by positivity : ( g : ℝ ) ≠ 0 ) ];
        have h_cos : Real.cos (s.arg + 2 * Real.pi * ℓ / g) < Real.cos (s.arg) := by
          by_cases h_case : |s.arg + 2 * Real.pi * ℓ / g| ≤ Real.pi;
          · rw [ ← Real.cos_abs ( s.arg + 2 * Real.pi * ℓ / g ), ← Real.cos_abs s.arg ] ; exact Real.cos_lt_cos_of_nonneg_of_le_pi ( by positivity ) ( by linarith ) ( by linarith ) ;
          · rw [ ← Real.cos_abs ( s.arg + 2 * Real.pi * ℓ / g ), ← Real.cos_abs s.arg ];
            rw [ ← Real.cos_two_pi_sub ] ; refine' Real.cos_lt_cos_of_nonneg_of_le_pi _ _ _ <;> try linarith [ Real.pi_pos, abs_nonneg ( s.arg + 2 * Real.pi * ℓ / g ) ];
            · positivity;
            · rw [ abs_lt ] at *;
              constructor <;> cases abs_cases ( s.arg + 2 * Real.pi * ℓ / g ) <;> nlinarith [ Real.pi_pos, show ( ℓ : ℝ ) + 1 ≤ g by norm_cast, mul_div_cancel₀ ( Real.pi : ℝ ) ( by positivity : ( g : ℝ ) ≠ 0 ), mul_div_cancel₀ ( 2 * Real.pi * ℓ : ℝ ) ( by positivity : ( g : ℝ ) ≠ 0 ) ];
        -- By the properties of the norm and the exponential function, we can simplify the expression.
        have h_norm : ‖1 + Complex.exp (2 * Real.pi * Complex.I * ℓ / g) * s‖ ^ 2 = 1 + ‖s‖ ^ 2 + 2 * ‖s‖ * Real.cos (s.arg + 2 * Real.pi * ℓ / g) ∧ ‖1 + s‖ ^ 2 = 1 + ‖s‖ ^ 2 + 2 * ‖s‖ * Real.cos s.arg := by
          norm_num [ Complex.normSq, Complex.sq_norm, Complex.exp_re, Complex.exp_im, Real.cos_add ];
          rw [ ← Complex.norm_mul_cos_arg, ← Complex.norm_mul_sin_arg ] ; ring ; norm_num [ Real.sin_sq, Real.cos_sq ] ; ring;
        nlinarith [ norm_pos_iff.mpr hs, norm_nonneg ( 1 + Complex.exp ( 2 * Real.pi * Complex.I * ℓ / g ) * s ), norm_nonneg ( 1 + s ) ]

/-
**Target 2 — principal-branch convergence on the slit plane.**  For every
`x ∈ ℂ ∖ (−∞,0]` and `0 ≤ k < g`, the residue-slice ratio converges to the
principal-branch power `x^(k/g)`.
-/
theorem tendsto_slice_ratio_cpow {g k : ℕ} (hg : 0 < g) (hk : k < g)
    {x : ℂ} (hx : x ∈ Complex.slitPlane) :
    Filter.Tendsto (fun N : ℕ => slice g k N x⁻¹ / slice g 0 N x⁻¹)
      Filter.atTop (nhds (x ^ ((k : ℂ) / (g : ℂ)))) := by
        revert hx;
        intro hx
        set s := (x⁻¹) ^ ((g : ℂ)⁻¹)
        have hs_ne_zero : s ≠ 0 := by
          aesop
        have hs_gt_one : ‖1 + s‖ > 0 := by
          simp_all +decide [ Complex.slitPlane ];
          contrapose! hx; simp_all +decide [Complex.ext_iff] ;
          -- Since $s = x^{-1/g}$, we have $s^g = x^{-1}$.
          have hs_pow : s ^ g = x⁻¹ := by
            rw [ ← Complex.cpow_nat_mul, mul_inv_cancel₀ ( Nat.cast_ne_zero.mpr hg.ne' ), Complex.cpow_one ];
          -- Since $s = -1$, we have $s^g = (-1)^g$.
          have hs_pow_neg_one : s ^ g = (-1 : ℂ) ^ g := by
            exact congr_arg ( · ^ g ) ( by norm_num [ Complex.ext_iff ] ; constructor <;> linarith );
          by_cases h : Even g <;> simp_all +decide;
          · norm_num [ hs_pow, s ] at *;
          · norm_num [ show x = -1 by simpa using inv_eq_iff_eq_inv.mp hs_pow.symm ] at *
        have hs_arg : |s.arg| < Real.pi / (g : ℝ) := by
          have hs_arg : |Complex.arg (x⁻¹)| < Real.pi := by
            have hs_arg : |Complex.arg x| < Real.pi := by
              cases hx <;> simp_all +decide [ Complex.arg ];
              · split_ifs <;> norm_num [ abs_lt ];
                · constructor <;> linarith [ Real.neg_pi_div_two_le_arcsin ( x.im / ‖x‖ ), Real.arcsin_le_pi_div_two ( x.im / ‖x‖ ), Real.pi_pos ];
                · linarith;
                · linarith;
              · split_ifs <;> norm_num [ abs_lt ];
                · constructor <;> linarith [ Real.neg_pi_div_two_le_arcsin ( x.im / ‖x‖ ), Real.arcsin_le_pi_div_two ( x.im / ‖x‖ ), Real.pi_pos ];
                · exact ⟨ by linarith [ Real.neg_pi_div_two_le_arcsin ( -x.im / ‖x‖ ), Real.arcsin_le_pi_div_two ( -x.im / ‖x‖ ), Real.pi_pos ], div_neg_of_neg_of_pos ( neg_neg_of_pos ( lt_of_le_of_ne ‹_› ( Ne.symm ‹_› ) ) ) ( norm_pos_iff.mpr ( show x ≠ 0 from by aesop ) ) ⟩;
                · exact ⟨ div_pos ( neg_pos.mpr ( lt_of_not_ge ‹_› ) ) ( norm_pos_iff.mpr ( by aesop ) ), by linarith [ Real.pi_pos, Real.arcsin_le_pi_div_two ( -x.im / ‖x‖ ) ] ⟩;
            rw [ Complex.arg_inv ];
            split_ifs <;> simp_all +decide [ abs_lt ];
          have hs_arg : Complex.arg (x⁻¹ ^ ((g : ℂ)⁻¹)) = (Complex.arg (x⁻¹)) / (g : ℝ) := by
            convert Complex.arg_mul_cos_add_sin_mul_I _ _ using 2;
            rotate_left;
            exact ‖x⁻¹‖ ^ ( ( g : ℝ ) ⁻¹ );
            · exact Real.rpow_pos_of_pos ( norm_pos_iff.mpr ( inv_ne_zero ( by rintro rfl; norm_num at hx ) ) ) _;
            · constructor <;> nlinarith [ abs_lt.mp hs_arg, show ( g : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ ( Complex.arg x⁻¹ ) ( by positivity : ( g : ℝ ) ≠ 0 ) ];
            · rw [ Complex.cpow_def_of_ne_zero ( inv_ne_zero <| by aesop ) ];
              rw [ Complex.log ] ; ring;
              rw [ Complex.exp_eq_exp_re_mul_sin_add_cos ] ; norm_num ; ring;
              rw [ Real.rpow_def_of_pos ( inv_pos.mpr ( norm_pos_iff.mpr ( show x ≠ 0 from by rintro rfl; norm_num at hx ) ) ) ] ; norm_num ; ring;
          rw [ hs_arg, abs_div, abs_of_nonneg ( by positivity : ( 0 : ℝ ) ≤ g ) ] ; gcongr
        have hs_pow : s ^ g = x⁻¹ := by
          rw [ ← Complex.cpow_nat_mul, mul_comm ] ; norm_num [ hg.ne' ];
        have h_filter : ∀ N : ℕ, g * s ^ k * slice g k N x⁻¹ = ∑ a ∈ Finset.range g, Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (g : ℂ)) ^ (g - k) * (1 + s * Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (g : ℂ))) ^ N := by
          intro N;
          convert roots_of_unity_filter hg hk ( Complex.isPrimitiveRoot_exp g hg.ne' ) s |> Eq.symm using 1;
          rw [ hs_pow ];
          norm_num [ ← Complex.exp_nat_mul, mul_div_assoc, mul_comm ];
          grind;
        have h_filter_zero : ∀ N : ℕ, g * slice g 0 N x⁻¹ = ∑ a ∈ Finset.range g, (1 + s * Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (g : ℂ))) ^ N := by
          intro N
          have h_filter_zero_step : ∑ a ∈ Finset.range g, (1 + s * Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (g : ℂ))) ^ N = ∑ a ∈ Finset.range g, ∑ j ∈ Finset.range (N + 1), (N.choose j : ℂ) * s ^ j * Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * j / (g : ℂ)) := by
            simp +decide [ add_comm ( 1 : ℂ ), add_pow, mul_pow, mul_assoc, mul_comm, mul_left_comm, ← Complex.exp_nat_mul ];
            exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring;
          have h_filter_zero_step : ∑ a ∈ Finset.range g, ∑ j ∈ Finset.range (N + 1), (N.choose j : ℂ) * s ^ j * Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * j / (g : ℂ)) = ∑ j ∈ Finset.range (N + 1), (N.choose j : ℂ) * s ^ j * ∑ a ∈ Finset.range g, Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * j / (g : ℂ)) := by
            rw [ Finset.sum_comm, Finset.sum_congr rfl fun _ _ => Finset.mul_sum _ _ _ ];
          have h_filter_zero_step : ∀ j ∈ Finset.range (N + 1), ∑ a ∈ Finset.range g, Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * j / (g : ℂ)) = if j % g = 0 then (g : ℂ) else 0 := by
            intro j hj; split_ifs <;> simp_all +decide [← Complex.exp_nat_mul] ;
            · obtain ⟨ k, rfl ⟩ := Nat.dvd_of_mod_eq_zero ‹_›; norm_num [ mul_assoc, mul_left_comm, mul_div_cancel₀, hg.ne' ] ;
              exact Eq.trans ( Finset.sum_congr rfl fun _ _ => by rw [ Complex.exp_eq_one_iff ] ; use k * ‹ℕ›; push_cast; rw [ div_eq_iff ( Nat.cast_ne_zero.mpr hg.ne' ) ] ; ring ) ( by norm_num );
            · have h_geom_sum : ∑ a ∈ Finset.range g, (Complex.exp (2 * Real.pi * Complex.I * j / g)) ^ a = 0 := by
                rw [ geom_sum_eq ] <;> norm_num [ ← Complex.exp_nat_mul, mul_div_cancel₀, hg.ne' ];
                · exact Or.inl ( sub_eq_zero_of_eq <| Complex.exp_eq_one_iff.mpr ⟨ j, by push_cast; ring ⟩ );
                · rw [ Complex.exp_eq_one_iff ];
                  field_simp;
                  exact fun ⟨ n, hn ⟩ => ‹¬j % g = 0› <| Nat.mod_eq_zero_of_dvd <| Int.natCast_dvd_natCast.mp <| ⟨ n, by rw [ div_eq_iff ( Nat.cast_ne_zero.mpr hg.ne' ) ] at hn; norm_cast at *; linarith ⟩;
              exact Eq.trans ( Finset.sum_congr rfl fun _ _ => by rw [ ← Complex.exp_nat_mul ] ; ring ) h_geom_sum;
          simp_all +decide [ Finset.sum_ite ];
          unfold slice; simp +decide [ Finset.sum_ite ] ; ring;
          rw [ Finset.mul_sum _ _ _ ] ; refine' Finset.sum_congr rfl fun i hi => _ ; rw [ ← hs_pow ] ; ring;
          rw [ Nat.mul_div_cancel' ( Nat.dvd_of_mod_eq_zero ( Finset.mem_filter.mp hi |>.2 ) ) ];
        have h_filter_ratio : Filter.Tendsto (fun N : ℕ => (∑ a ∈ Finset.range g, Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (g : ℂ)) ^ (g - k) * (1 + s * Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (g : ℂ))) ^ N) / (∑ a ∈ Finset.range g, (1 + s * Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (g : ℂ))) ^ N)) Filter.atTop (nhds (Complex.exp (2 * Real.pi * Complex.I * (0 : ℂ) / (g : ℂ)) ^ (g - k) * (1 + s * Complex.exp (2 * Real.pi * Complex.I * (0 : ℂ) / (g : ℂ))) ^ 0 / (1 + s * Complex.exp (2 * Real.pi * Complex.I * (0 : ℂ) / (g : ℂ))) ^ 0)) := by
          have h_filter_ratio : Filter.Tendsto (fun N : ℕ => (∑ a ∈ Finset.range g \ {0}, Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (g : ℂ)) ^ (g - k) * (1 + s * Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (g : ℂ))) ^ N) / (1 + s) ^ N) Filter.atTop (nhds 0) := by
            have h_filter_ratio : ∀ a ∈ Finset.range g \ {0}, Filter.Tendsto (fun N : ℕ => (Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (g : ℂ)) ^ (g - k) * (1 + s * Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (g : ℂ))) ^ N) / (1 + s) ^ N) Filter.atTop (nhds 0) := by
              intro a ha
              have h_abs : ‖1 + s * Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (g : ℂ))‖ < ‖1 + s‖ := by
                convert norm_one_add_root_mul_lt hg ( show a ≠ 0 from by aesop ) ( show a < g from by aesop ) hs_ne_zero hs_arg using 1 ; ring;
              have h_abs_pow : Filter.Tendsto (fun N : ℕ => ((1 + s * Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (g : ℂ))) / (1 + s)) ^ N) Filter.atTop (nhds 0) := by
                exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one ( by rw [ norm_div ] ; exact div_lt_one hs_gt_one |>.2 h_abs );
              convert h_abs_pow.const_mul ( Complex.exp ( 2 * Real.pi * Complex.I * a / g ) ^ ( g - k ) ) using 2 <;> ring;
              rw [ show ( Complex.exp ( Real.pi * Complex.I * a * ( g : ℂ ) ⁻¹ * 2 ) * s * ( 1 + s ) ⁻¹ + ( 1 + s ) ⁻¹ ) = ( 1 + Complex.exp ( Real.pi * Complex.I * a * ( g : ℂ ) ⁻¹ * 2 ) * s ) * ( 1 + s ) ⁻¹ by ring ] ; rw [ mul_pow ] ; ring;
            simpa [ Finset.sum_div _ _ _ ] using tendsto_finset_sum _ h_filter_ratio;
          have h_filter_ratio : Filter.Tendsto (fun N : ℕ => (∑ a ∈ Finset.range g, (1 + s * Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (g : ℂ))) ^ N) / (1 + s) ^ N) Filter.atTop (nhds 1) := by
            have h_filter_ratio : Filter.Tendsto (fun N : ℕ => (∑ a ∈ Finset.range g \ {0}, (1 + s * Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (g : ℂ))) ^ N) / (1 + s) ^ N) Filter.atTop (nhds 0) := by
              have h_filter_ratio : ∀ a ∈ Finset.range g \ {0}, Filter.Tendsto (fun N : ℕ => (1 + s * Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (g : ℂ))) ^ N / (1 + s) ^ N) Filter.atTop (nhds 0) := by
                intro a ha
                have h_abs : ‖1 + s * Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (g : ℂ))‖ < ‖1 + s‖ := by
                  convert norm_one_add_root_mul_lt hg ( show a ≠ 0 from by aesop ) ( show a < g from by aesop ) hs_ne_zero hs_arg using 1 ; ring;
                have h_abs_pow : Filter.Tendsto (fun N : ℕ => (‖1 + s * Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (g : ℂ))‖ / ‖1 + s‖) ^ N) Filter.atTop (nhds 0) := by
                  exact tendsto_pow_atTop_nhds_zero_of_lt_one ( div_nonneg ( norm_nonneg _ ) ( norm_nonneg _ ) ) ( by rwa [ div_lt_one hs_gt_one ] );
                exact tendsto_zero_iff_norm_tendsto_zero.mpr ( by simpa [ div_pow ] using h_abs_pow );
              simpa [ Finset.sum_div _ _ _ ] using tendsto_finset_sum _ h_filter_ratio;
            convert h_filter_ratio.add_const 1 using 2 <;> norm_num [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_range.mpr hg ) ];
            rw [ add_div, div_self ( pow_ne_zero _ ( by aesop ) ) ] ; ring;
          convert Filter.Tendsto.div ( ‹Filter.Tendsto ( fun N : ℕ => ( ∑ a ∈ Finset.range g \ { 0 }, Complex.exp ( 2 * Real.pi * Complex.I * a / g ) ^ ( g - k ) * ( 1 + s * Complex.exp ( 2 * Real.pi * Complex.I * a / g ) ) ^ N ) / ( 1 + s ) ^ N ) Filter.atTop ( nhds 0 ) ›.add_const ( Complex.exp ( 2 * Real.pi * Complex.I * 0 / g ) ^ ( g - k ) ) ) h_filter_ratio _ using 2 <;> norm_num;
          rw [ Finset.sum_eq_sum_diff_singleton_add ( Finset.mem_range.mpr hg ) ] ; ring;
          simp +decide [mul_assoc, mul_comm, mul_left_comm,
            show (1 + s) ≠ 0 from by
              intro h
              norm_num [show s = -1 by linear_combination' h] at *];
        convert h_filter_ratio.const_mul ( s ^ k )⁻¹ using 2 <;> norm_num [ ← h_filter, ← h_filter_zero ];
        · simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, hg.ne', hs_ne_zero ];
        · rw [ ← Complex.cpow_nat_mul ] ; ring_nf;
          rw [Complex.inv_cpow, inv_inv]
          exact (Complex.mem_slitPlane_iff_arg.mp hx).1

end ResidueSlices