import RequestProject.GeneralResidueConvergence
import Mathlib

open scoped BigOperators

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

namespace ResidueSlices

/-- The relative size of a Fourier channel compared with the positive real
principal channel. -/
noncomputable def channelRatio (t : ℝ) (ω : ℂ) (a : ℕ) : ℝ :=
  ‖1 + (t : ℂ) * ω ^ a‖ / (1 + t)

/-- The spectral radius of the subordinate roots-of-unity channels.  The
inserted zero gives the natural value `0` when there are no subordinate
channels (in particular, when `g = 1`). -/
noncomputable def spectralGap (g : ℕ) (t : ℝ) (ω : ℂ) : ℝ :=
  let channels := (Finset.range g \ {0}).image (channelRatio t ω)
  (insert 0 channels).max' ⟨0, Finset.mem_insert_self 0 channels⟩

/-
Every subordinate channel is bounded by the spectral gap.
-/
lemma channelRatio_le_spectralGap {g a : ℕ} {t : ℝ} {ω : ℂ}
    (ha : a ∈ Finset.range g) (ha0 : a ≠ 0) :
    channelRatio t ω a ≤ spectralGap g t ω := by
  exact Finset.le_max' _ _ ( Finset.mem_insert_of_mem <| Finset.mem_image.mpr ⟨ a, Finset.mem_sdiff.mpr ⟨ ha, by aesop ⟩, rfl ⟩ )

/-
Strict dominance of the principal channel is quantitatively retained by
`spectralGap`: it is nonnegative and strictly below one.
-/
lemma spectralGap_mem_unitInterval {g : ℕ} (hg : 0 < g) {t : ℝ} (ht : 0 < t)
    {ω : ℂ} (hω : IsPrimitiveRoot ω g) :
    0 ≤ spectralGap g t ω ∧ spectralGap g t ω < 1 := by
  -- Every element in the image of `channelRatio` is strictly less than 1.
  have h_channel_ratio_lt_one : ∀ a ∈ Finset.range g, a ≠ 0 → channelRatio t ω a < 1 := by
    intros a ha ha0
    have h_norm : ‖ω ^ a‖ = 1 := by
      have := hω.pow_eq_one; replace := congr_arg Norm.norm this; norm_num at this; rw [ pow_eq_one_iff_of_nonneg ] at this <;> aesop;
    unfold channelRatio; rw [ div_lt_one ( by positivity ) ] ; exact norm_one_add_pos_mul_lt h_norm ( by exact fun h => ha0 <| by have := hω.pow_inj ( by linarith [ Finset.mem_range.mp ha ] : a < g ) ( by linarith [ Finset.mem_range.mp ha ] : 0 < g ) ; aesop ) ht;
  unfold spectralGap; simp_all +decide [ Finset.max' ] ;
  exact fun a x hx hx' hx'' => hx''.symm ▸ h_channel_ratio_lt_one x hx hx'

/-
Quantitative spectral recovery for Pascal residue packets.  The error is
bounded for every row by a constant times the `N`-th power of the largest
subordinate-channel ratio.  Thus the rate is exactly controlled by the finite
roots-of-unity spectral gap.
-/
theorem general_slice_ratio_spectral_rate
    {g k : ℕ} (hg : 0 < g) (hk : k < g) {t : ℝ} (ht : 0 < t)
    {ω : ℂ} (hω : IsPrimitiveRoot ω g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖slice g k N (t ^ g) / slice g 0 N (t ^ g) - (t ^ k)⁻¹‖ ≤
        C * (spectralGap g t ω) ^ N := by
  by_cases h : spectralGap g t ω = 0;
  · use ‖slice g k 0 (t ^ g) / slice g 0 0 (t ^ g) - (t ^ k)⁻¹‖;
    have h_error_zero : ∀ a ∈ Finset.range g, a ≠ 0 → ‖1 + (t : ℂ) * ω ^ a‖ = 0 := by
      intros a ha ha0
      have h_channel_zero : channelRatio t ω a ≤ spectralGap g t ω := by
        exact channelRatio_le_spectralGap ha ha0;
      unfold channelRatio at h_channel_zero;
      rw [ div_le_iff₀ ] at h_channel_zero <;> nlinarith [ norm_nonneg ( 1 + t * ω ^ a ) ];
    have h_error_zero : ∀ N ≥ 1, slice g k N (t ^ g) / slice g 0 N (t ^ g) = (t ^ k)⁻¹ := by
      intros N hN
      have h_filter : ∑ a ∈ Finset.range g, ω ^ (a * (g - k)) * (1 + t * ω ^ a) ^ N = (g : ℂ) * t ^ k * slice g k N (t ^ g) := by
        convert roots_of_unity_filter hg hk hω t using 1;
        unfold slice; norm_num [ Finset.sum_ite ] ;
      have h_filter_zero : ∑ a ∈ Finset.range g, ω ^ (a * g) * (1 + t * ω ^ a) ^ N = (g : ℂ) * slice g 0 N (t ^ g) := by
        convert roots_of_unity_filter hg ( show 0 < g from hg ) hω t using 1;
        norm_num [ slice ];
        exact Or.inl <| Finset.sum_congr rfl fun _ _ => by split_ifs <;> norm_num;
      have h_filter_zero : ∑ a ∈ Finset.range g, ω ^ (a * (g - k)) * (1 + t * ω ^ a) ^ N = ω ^ (0 * (g - k)) * (1 + t * ω ^ 0) ^ N := by
        rw [ Finset.sum_eq_single 0 ] <;> aesop;
      have h_filter_zero : ∑ a ∈ Finset.range g, ω ^ (a * g) * (1 + t * ω ^ a) ^ N = ω ^ (0 * g) * (1 + t * ω ^ 0) ^ N := by
        rw [ Finset.sum_eq_single 0 ] <;> simp_all +decide [ pow_mul' ];
        exact fun _ _ _ => Or.inr ( by linarith );
      simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
      rw [ inv_eq_one_div, div_eq_div_iff ] <;> norm_cast at * <;> simp_all +decide [ ne_of_gt ];
      · nlinarith [ show ( g : ℝ ) > 0 by positivity ];
      · exact ne_of_gt ( lt_of_lt_of_le zero_lt_one ( one_le_slice_zero g N ( by positivity ) ) );
    simp_all +decide [ slice ];
    intro N; specialize h_error_zero N; rcases N with ( _ | N ) <;> simp_all +decide [ Finset.sum_range_succ' ] ;
  · -- When $\rho > 0$, we show $U_N = 1 + O(\rho^N)$ and $V_N = 1 + O(\rho^N)$, giving the desired bound.
    have h_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, ‖(g * t ^ k * slice g k N (t ^ g)) / (1 + t) ^ N - 1‖ ≤ C * (spectralGap g t ω) ^ N ∧ ‖(g * slice g 0 N (t ^ g)) / (1 + t) ^ N - 1‖ ≤ C * (spectralGap g t ω) ^ N := by
      have h_bound : ∀ N : ℕ, ‖(g * t ^ k * slice g k N (t ^ g)) / (1 + t) ^ N - 1‖ ≤ ∑ a ∈ Finset.range g \ {0}, ‖ω ^ (a * (g - k)) * (1 + t * ω ^ a) ^ N / (1 + t) ^ N‖ ∧ ‖(g * slice g 0 N (t ^ g)) / (1 + t) ^ N - 1‖ ≤ ∑ a ∈ Finset.range g \ {0}, ‖ω ^ (a * g) * (1 + t * ω ^ a) ^ N / (1 + t) ^ N‖ := by
        intro N
        have h_bound : (g * t ^ k * slice g k N (t ^ g)) / (1 + t) ^ N - 1 = ∑ a ∈ Finset.range g \ {0}, ω ^ (a * (g - k)) * (1 + t * ω ^ a) ^ N / (1 + t) ^ N ∧ (g * slice g 0 N (t ^ g)) / (1 + t) ^ N - 1 = ∑ a ∈ Finset.range g \ {0}, ω ^ (a * g) * (1 + t * ω ^ a) ^ N / (1 + t) ^ N := by
          have h_bound : (g * t ^ k * slice g k N (t ^ g)) = ∑ a ∈ Finset.range g, ω ^ (a * (g - k)) * (1 + t * ω ^ a) ^ N ∧ (g * slice g 0 N (t ^ g)) = ∑ a ∈ Finset.range g, ω ^ (a * g) * (1 + t * ω ^ a) ^ N := by
            constructor;
            · convert roots_of_unity_filter hg hk hω t |> Eq.symm using 1;
              norm_num [ slice ];
              exact Or.inl <| Finset.sum_congr rfl fun _ _ => by split_ifs <;> norm_num;
            · convert roots_of_unity_filter hg ( show 0 < g from hg ) hω t |> Eq.symm using 1;
              norm_num [ slice ];
              exact Or.inl ( Finset.sum_congr rfl fun _ _ => by split_ifs <;> norm_num );
          simp_all +decide [ ← Finset.sum_div _ _ _ ];
          exact ⟨ by rw [ sub_div, div_self ( by norm_cast; positivity ) ], by rw [ sub_div, div_self ( by norm_cast; positivity ) ] ⟩;
        convert And.intro ( norm_sum_le _ _ ) ( norm_sum_le _ _ ) using 2;
        · rw [ ← h_bound.1 ] ; norm_cast;
        · convert congr_arg Norm.norm h_bound.2 using 1;
          norm_num [ Complex.norm_def, Complex.normSq ];
          norm_cast ; norm_num [ Complex.normSq, Complex.div_re, Complex.div_im ];
          rw [ Real.sqrt_mul_self_eq_abs ];
      -- Since $|\omega^{a(g-k)}| = 1$ and $|\omega^{ag}| = 1$, we can simplify the bounds.
      have h_simplified_bound : ∀ N : ℕ, ‖(g * t ^ k * slice g k N (t ^ g)) / (1 + t) ^ N - 1‖ ≤ ∑ a ∈ Finset.range g \ {0}, (channelRatio t ω a) ^ N ∧ ‖(g * slice g 0 N (t ^ g)) / (1 + t) ^ N - 1‖ ≤ ∑ a ∈ Finset.range g \ {0}, (channelRatio t ω a) ^ N := by
        convert h_bound using 3 <;> norm_num [ channelRatio ];
        · norm_cast ; norm_num [ hω.norm'_eq_one ];
          rw [ hω.norm'_eq_one ] ; norm_num [ abs_of_pos ( by positivity : 0 < 1 + t ) ] ; ring;
          · ac_rfl;
          · linarith;
        · norm_cast ; norm_num [ pow_mul', hω.pow_eq_one ];
          rw [ hω.norm'_eq_one ] ; norm_num [ abs_of_pos ( by positivity : 0 < 1 + t ) ] ; ring;
          · ac_rfl;
          · linarith;
      refine' ⟨ ∑ a ∈ Finset.range g \ { 0 }, 1, _, _ ⟩ <;> norm_num;
      intro N; specialize h_simplified_bound N; refine' ⟨ le_trans h_simplified_bound.1 _, le_trans h_simplified_bound.2 _ ⟩; all_goals exact le_trans ( Finset.sum_le_sum fun x hx => pow_le_pow_left₀ ( by exact div_nonneg ( norm_nonneg _ ) ( by positivity ) ) ( channelRatio_le_spectralGap ( Finset.mem_sdiff.mp hx |>.1 ) ( by aesop ) ) _ ) ( by norm_num );
    obtain ⟨C, hC_nonneg, hC_bound⟩ := h_bound
    obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ N ≥ M, ‖(g * slice g 0 N (t ^ g)) / (1 + t) ^ N‖ ≥ 1 / 2 := by
      have h_bound : Filter.Tendsto (fun N : ℕ => ‖(g * slice g 0 N (t ^ g)) / (1 + t) ^ N‖) Filter.atTop (nhds 1) := by
        have h_bound : Filter.Tendsto (fun N : ℕ => (g * slice g 0 N (t ^ g)) / (1 + t) ^ N) Filter.atTop (nhds 1) := by
          have h_bound : Filter.Tendsto (fun N : ℕ => (g * slice g 0 N (t ^ g)) / (1 + t) ^ N - 1) Filter.atTop (nhds 0) := by
            exact squeeze_zero_norm ( fun N => hC_bound N |>.2 ) ( by simpa using tendsto_const_nhds.mul ( tendsto_pow_atTop_nhds_zero_of_lt_one ( by linarith [ show 0 ≤ spectralGap g t ω from by linarith [ spectralGap_mem_unitInterval hg ht hω ] ] ) ( show spectralGap g t ω < 1 from by linarith [ spectralGap_mem_unitInterval hg ht hω ] ) ) );
          simpa using h_bound.add_const 1;
        simpa using h_bound.norm;
      exact Filter.eventually_atTop.mp ( h_bound.eventually ( le_mem_nhds <| by norm_num ) );
    -- Using the bounds on $U_N$ and $V_N$, we can bound the error.
    have h_error_bound : ∀ N ≥ M, ‖(slice g k N (t ^ g)) / (slice g 0 N (t ^ g)) - (t ^ k)⁻¹‖ ≤ (4 * C / t ^ k) * (spectralGap g t ω) ^ N := by
      intro N hN
      have h_error_bound_step : ‖(g * t ^ k * slice g k N (t ^ g)) / (1 + t) ^ N / ((g * slice g 0 N (t ^ g)) / (1 + t) ^ N) - 1‖ ≤ 4 * C * (spectralGap g t ω) ^ N := by
        have h_error_bound_step : ‖(g * t ^ k * slice g k N (t ^ g)) / (1 + t) ^ N / ((g * slice g 0 N (t ^ g)) / (1 + t) ^ N) - 1‖ ≤ ‖(g * t ^ k * slice g k N (t ^ g)) / (1 + t) ^ N - (g * slice g 0 N (t ^ g)) / (1 + t) ^ N‖ / ‖(g * slice g 0 N (t ^ g)) / (1 + t) ^ N‖ := by
          rw [ div_sub_one ];
          · rw [ norm_div ];
          · exact fun h => by have := hM N hN; norm_num [ h ] at this;
        have h_error_bound_step : ‖(g * t ^ k * slice g k N (t ^ g)) / (1 + t) ^ N - (g * slice g 0 N (t ^ g)) / (1 + t) ^ N‖ ≤ 2 * C * (spectralGap g t ω) ^ N := by
          convert le_trans ( norm_sub_le _ _ ) ( add_le_add ( hC_bound N |>.1 ) ( hC_bound N |>.2 ) ) using 1 ; ring;
          ring;
        refine le_trans ‹_› ?_;
        rw [ div_le_iff₀ ] <;> nlinarith [ hM N hN, show 0 ≤ C * spectralGap g t ω ^ N by exact mul_nonneg hC_nonneg ( pow_nonneg ( by linarith [ spectralGap_mem_unitInterval hg ht hω ] ) _ ) ];
      convert mul_le_mul_of_nonneg_left h_error_bound_step ( show 0 ≤ ( t ^ k ) ⁻¹ by positivity ) using 1 <;> ring;
      norm_num [ mul_assoc, mul_comm, mul_left_comm, hg.ne', ht.ne' ];
      field_simp;
      rw [ abs_div, abs_of_nonneg ( by positivity : 0 ≤ t ^ k ), mul_div_cancel₀ _ ( by positivity ) ] ; ring;
    use Max.max ( 4 * C / t ^ k ) ( ∑ N ∈ Finset.range M, ‖slice g k N ( t ^ g ) / slice g 0 N ( t ^ g ) - ( t ^ k ) ⁻¹‖ / spectralGap g t ω ^ N );
    refine' ⟨ le_max_of_le_left ( by positivity ), fun N => _ ⟩;
    by_cases hN : N < M;
    · refine' le_trans _ ( mul_le_mul_of_nonneg_right ( le_max_right _ _ ) ( pow_nonneg ( _ ) _ ) );
      · rw [ Finset.sum_mul _ _ _ ];
        refine' le_trans _ ( Finset.single_le_sum ( fun i _ => _ ) ( Finset.mem_range.mpr hN ) );
        · rw [ div_mul_cancel₀ _ ( pow_ne_zero _ h ) ];
        · exact mul_nonneg ( div_nonneg ( norm_nonneg _ ) ( pow_nonneg ( by exact le_of_lt ( show 0 < spectralGap g t ω from lt_of_le_of_ne ( by exact le_trans ( by norm_num ) ( Finset.le_max' _ _ ( Finset.mem_insert_self _ _ ) ) ) ( Ne.symm h ) ) ) _ ) ) ( pow_nonneg ( by exact le_of_lt ( show 0 < spectralGap g t ω from lt_of_le_of_ne ( by exact le_trans ( by norm_num ) ( Finset.le_max' _ _ ( Finset.mem_insert_self _ _ ) ) ) ( Ne.symm h ) ) ) _ );
      · exact le_trans ( by norm_num ) ( spectralGap_mem_unitInterval hg ht hω |>.1 );
    · exact le_trans ( h_error_bound N ( le_of_not_gt hN ) ) ( mul_le_mul_of_nonneg_right ( le_max_left _ _ ) ( pow_nonneg ( by linarith [ spectralGap_mem_unitInterval hg ht hω ] ) _ ) )

/-- Canonical version using `exp (2πi/g)` as the primitive root. -/
theorem general_slice_ratio_spectral_rate_exp
    {g k : ℕ} (hg : 0 < g) (hk : k < g) {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖slice g k N (t ^ g) / slice g 0 N (t ^ g) - (t ^ k)⁻¹‖ ≤
        C * (spectralGap g t (Complex.exp (2 * Real.pi * Complex.I / g))) ^ N := by
  simpa using general_slice_ratio_spectral_rate hg hk ht
    (Complex.isPrimitiveRoot_exp g hg.ne')

end ResidueSlices