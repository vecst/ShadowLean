import RequestProject.ResidueSlices
import Mathlib

open scoped BigOperators

namespace ResidueSlices

/-- Orthogonality of powers of a primitive root of unity, in the finite form
needed for residue extraction. -/
lemma primitive_root_power_sum {K : Type*} [Field K] {g m : ℕ} {ω : K}
    (hω : IsPrimitiveRoot ω g) :
    (∑ a ∈ Finset.range g, ω ^ (a * m)) = if g ∣ m then (g : K) else 0 := by
  split_ifs with hgm
  · have hm : ω ^ m = 1 := (hω.pow_eq_one_iff_dvd m).2 hgm
    have hterm : ∀ a : ℕ, ω ^ (a * m) = 1 := by
      intro a
      rw [mul_comm, pow_mul, hm, one_pow]
    simp_rw [hterm]
    simp
  · have hm : ω ^ m ≠ 1 := by
      exact fun he => hgm ((hω.pow_eq_one_iff_dvd m).mp he)
    have heq : ∑ a ∈ Finset.range g, ω ^ (a * m) =
        ∑ a ∈ Finset.range g, (ω ^ m) ^ a := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [mul_comm, pow_mul]
    rw [heq, geom_sum_eq hm]
    have hp : (ω ^ m) ^ g = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
    rw [hp, sub_self, zero_div]

/-
The roots-of-unity filter for a compressed Pascal packet.  Multiplication
by `t^k` restores the exponent removed by compression.
-/
theorem roots_of_unity_filter {g k N : ℕ} (hg : 0 < g) (hk : k < g)
    {ω : ℂ} (hω : IsPrimitiveRoot ω g) (t : ℂ) :
    ∑ a ∈ Finset.range g, ω ^ (a * (g - k)) * (1 + t * ω ^ a) ^ N =
      (g : ℂ) * t ^ k * slice g k N (t ^ g) := by
  -- Expand each (1+t*ω^a)^N by add_pow.
  have h_expand : ∑ a ∈ Finset.range g, ω ^ (a * (g - k)) * (1 + t * ω ^ a) ^ N = ∑ j ∈ Finset.range (N + 1), (Nat.choose N j : ℂ) * t ^ j * ∑ a ∈ Finset.range g, ω ^ (a * (g - k + j)) := by
    simp +decide [ add_comm ( 1 : ℂ ), add_pow, mul_pow, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
  -- Apply primitive_root_power_sum to the inner sum.
  have h_inner : ∀ j ∈ Finset.range (N + 1), ∑ a ∈ Finset.range g, ω ^ (a * (g - k + j)) = if g ∣ (g - k + j) then (g : ℂ) else 0 := by
    intro j hj; convert primitive_root_power_sum hω using 1;
  -- Since $g$ divides $g - k + j$ if and only if $j \equiv k \pmod{g}$, we can rewrite the sum.
  have h_div : ∀ j ∈ Finset.range (N + 1), (g ∣ (g - k + j)) ↔ (j % g = k) := by
    intro j hj;
    constructor <;> intro h <;> rw [ Nat.dvd_iff_mod_eq_zero ] at * <;> simp_all +decide [ ← ZMod.val_natCast, Nat.cast_sub hk.le ];
    · rw [ neg_add_eq_zero ] at h;
      rw [ ← h, ZMod.val_cast_of_lt hk ];
    · simp +decide [← h];
  simp_all +decide [ Finset.sum_ite, slice ];
  rw [ Finset.mul_sum _ _ _ ] ; refine' Finset.sum_congr rfl fun x hx => _ ; rw [ ← Nat.mod_add_div x g ] ; simp_all +decide [ pow_add, pow_mul ] ; ring;
  norm_num [ Nat.add_mul_div_left _ _ hg ];
  norm_num [ Nat.div_eq_of_lt hk ]

/-
A finite collection of exponentially decaying modes tends to zero.
-/
lemma tendsto_finite_mode_sum_zero {g : ℕ} (c q : ℕ → ℂ)
    (hq : ∀ a ∈ Finset.range g, ‖q a‖ < 1) :
    Filter.Tendsto (fun N : ℕ => ∑ a ∈ Finset.range g, c a * (q a) ^ N)
      Filter.atTop (nhds 0) := by
  exact le_trans ( tendsto_finset_sum _ fun i hi => tendsto_const_nhds.mul ( tendsto_pow_atTop_nhds_zero_of_norm_lt_one ( hq i hi ) ) ) ( by norm_num )

/-- A nontrivial power below the order of a primitive root cannot be one. -/
lemma primitive_root_pow_ne_one {g a : ℕ} {ω : ℂ} (hω : IsPrimitiveRoot ω g)
    (ha : a < g) (ha0 : a ≠ 0) : ω ^ a ≠ 1 := by
  intro h
  have hd : g ∣ a := (hω.pow_eq_one_iff_dvd a).mp h
  exact ha0 (Nat.eq_zero_of_dvd_of_lt hd ha)

/-
On the unit circle, every point except `1` gives a strictly smaller
binomial wave than the positive real point.
-/
lemma norm_one_add_pos_mul_lt {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1)
    {t : ℝ} (ht : 0 < t) : ‖1 + (t : ℂ) * z‖ < 1 + t := by
  simp_all +decide [ Complex.normSq, Complex.norm_def ];
  rw [ Real.sqrt_lt' ] <;> ring;
  · by_cases hz_re : z.re = 1;
    · simp_all +decide [ Complex.ext_iff ];
    · nlinarith [ mul_self_pos.mpr ( sub_ne_zero.mpr hz_re ), mul_pos ht ( sub_pos.mpr ( lt_of_le_of_ne ( show z.re ≤ 1 by nlinarith ) hz_re ) ) ];
  · positivity

/-- General residue-packet convergence from spectral dominance of the
principal binomial wave. The hypotheses are the finite Fourier data: `ω` is
primitive and every nontrivial wave is strictly smaller than `1 + t`. -/
theorem tendsto_general_slice_ratio_of_dominance
    {g k : ℕ} (hg : 0 < g) (hk : k < g) {t : ℝ} (ht : 0 < t)
    {ω : ℂ} (hω : IsPrimitiveRoot ω g)
    (hdom : ∀ a ∈ Finset.range g, a ≠ 0 →
      ‖1 + (t : ℂ) * ω ^ a‖ < 1 + t) :
    Filter.Tendsto
      (fun N : ℕ => slice g k N (t ^ g) / slice g 0 N (t ^ g))
      Filter.atTop (nhds (t ^ k)⁻¹) := by
  -- Using the roots_of_unity_filter, we can express the slices in terms of the sums involving ω.
  have h_sums : ∀ N : ℕ, (g : ℂ) * t ^ k * slice g k N (t ^ g) = ∑ a ∈ Finset.range g, ω ^ (a * (g - k)) * (1 + t * ω ^ a) ^ N ∧ (g : ℂ) * slice g 0 N (t ^ g) = ∑ a ∈ Finset.range g, ω ^ (a * g) * (1 + t * ω ^ a) ^ N := by
    intro N
    constructor;
    · convert roots_of_unity_filter hg hk hω t |> Eq.symm using 1;
      unfold slice; norm_num [ Finset.sum_ite ] ;
    · convert roots_of_unity_filter hg ( by linarith : 0 < g ) hω t |> Eq.symm using 1 ; norm_num [ pow_mul' ];
      unfold slice; norm_num [ Finset.sum_ite ] ;
  -- Divide both sides of the equation by $(1 + t)^N$ and take the limit as $N \to \infty$.
  have h_limit : Filter.Tendsto (fun N : ℕ => (∑ a ∈ Finset.range g, ω ^ (a * (g - k)) * (1 + t * ω ^ a) ^ N) / (1 + t) ^ N) Filter.atTop (nhds (ω ^ (0 * (g - k)))) ∧ Filter.Tendsto (fun N : ℕ => (∑ a ∈ Finset.range g, ω ^ (a * g) * (1 + t * ω ^ a) ^ N) / (1 + t) ^ N) Filter.atTop (nhds (ω ^ (0 * g))) := by
    have h_limit : ∀ a ∈ Finset.range g, a ≠ 0 → Filter.Tendsto (fun N : ℕ => (ω ^ (a * (g - k)) * (1 + t * ω ^ a) ^ N) / (1 + t) ^ N) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun N : ℕ => (ω ^ (a * g) * (1 + t * ω ^ a) ^ N) / (1 + t) ^ N) Filter.atTop (nhds 0) := by
      intro a ha ha'; refine' ⟨ _, _ ⟩ <;> rw [ tendsto_zero_iff_norm_tendsto_zero ] <;> norm_num [ mul_div_assoc ] ;
      · norm_cast ; simp_all +decide [ ← div_pow ];
        exact le_trans ( Filter.Tendsto.mul tendsto_const_nhds ( tendsto_pow_atTop_nhds_zero_of_lt_one ( by positivity ) ( by rw [ div_lt_iff₀ ] <;> cases abs_cases ( 1 + t ) <;> linarith [ hdom a ha ha', norm_nonneg ( 1 + t * ω ^ a ) ] ) ) ) ( by norm_num );
      · convert tendsto_const_nhds.mul ( tendsto_pow_atTop_nhds_zero_of_lt_one ( by positivity ) ( show ‖1 + t * ω ^ a‖ / ‖1 + t‖ < 1 from _ ) ) using 2 <;> norm_num [ abs_of_pos, ht ];
        convert rfl using 2;
        · norm_num [ abs_of_pos, add_pos, ht ];
          norm_cast ; norm_num [ div_pow ];
          rw [ abs_of_nonneg ( by positivity ) ];
        · rw [ div_lt_iff₀ ] <;> cases abs_cases ( 1 + t ) <;> linarith [ hdom a ha ha', norm_nonneg ( 1 + t * ω ^ a ) ];
    simp_all +decide [ Finset.sum_div _ _ _ ];
    constructor <;> rw [ tendsto_iff_norm_sub_tendsto_zero ];
    · rw [ show ( fun e => ‖∑ i ∈ Finset.range g, ω ^ ( i * ( g - k ) ) * ( 1 + t * ω ^ i ) ^ e / ( 1 + t ) ^ e - 1‖ ) = fun e => ‖∑ i ∈ Finset.range g \ { 0 }, ω ^ ( i * ( g - k ) ) * ( 1 + t * ω ^ i ) ^ e / ( 1 + t ) ^ e‖ from funext fun _ => ?_ ];
      · exact squeeze_zero ( fun _ => norm_nonneg _ ) ( fun _ => norm_sum_le _ _ ) ( by simpa using tendsto_finset_sum _ fun i hi => Filter.Tendsto.norm ( h_limit i ( Finset.mem_range.mp ( Finset.mem_sdiff.mp hi |>.1 ) ) ( by aesop ) |>.1 ) );
      · simp +decide [ Finset.sum_eq_sum_diff_singleton_add ( Finset.mem_range.mpr hg ) ];
        rw [ div_self <| by norm_cast; positivity, add_sub_cancel_right ];
    · rw [ Filter.tendsto_congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with N hN; rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_range.mpr hg ) ] ) ];
      norm_num [ show ( 1 + t : ℂ ) ≠ 0 by norm_cast; linarith ];
      exact squeeze_zero ( fun _ => norm_nonneg _ ) ( fun N => norm_sum_le _ _ ) ( by simpa using tendsto_finset_sum _ fun x hx => Filter.Tendsto.norm ( h_limit x ( Finset.mem_range.mp ( Finset.mem_sdiff.mp hx |>.1 ) ) ( by aesop ) |>.2 ) );
  convert Complex.continuous_re.continuousAt.tendsto.comp ( h_limit.1.div h_limit.2 _ ) |> ( fun h => h.div_const ( t ^ k : ℝ ) ) using 2 <;> norm_num [ ← h_sums ];
  rw [ div_div_div_cancel_right₀ ( by norm_cast; positivity ) ] ; norm_cast ; simp +decide [ mul_assoc, mul_comm ] ; ring;
  simp +decide [mul_assoc, mul_comm, mul_left_comm, hg.ne', ht.ne']

/-- The spectral-dominance hypothesis follows automatically for any primitive
`g`-th root of unity. -/
theorem tendsto_general_slice_ratio_with_primitive
    {g k : ℕ} (hg : 0 < g) (hk : k < g) {t : ℝ} (ht : 0 < t)
    {ω : ℂ} (hω : IsPrimitiveRoot ω g) :
    Filter.Tendsto
      (fun N : ℕ => slice g k N (t ^ g) / slice g 0 N (t ^ g))
      Filter.atTop (nhds (t ^ k)⁻¹) := by
  apply tendsto_general_slice_ratio_of_dominance;
  all_goals norm_cast;
  intro a ha ha'; have := hω.pow_eq_one; simp_all +decide [ IsPrimitiveRoot.iff_def ] ;
  have h_norm : ‖ω ^ a‖ = 1 := by
    have := congr_arg Norm.norm this ; norm_num at this ; rw [ pow_eq_one_iff_of_nonneg ] at this <;> aesop;
  convert norm_one_add_pos_mul_lt h_norm _ ht using 1;
  exact fun h => ha' <| Nat.eq_zero_of_dvd_of_lt ( hω a h ) ha

/-- For every positive `t`, every packet ratio in a positive-width Pascal
residue decomposition converges to the corresponding reciprocal power.  With
`x = t^g`, this is `x^(-k/g)` without requiring real fractional powers in the
statement. -/
theorem tendsto_general_slice_ratio
    {g k : ℕ} (hg : 0 < g) (hk : k < g) {t : ℝ} (ht : 0 < t) :
    Filter.Tendsto
      (fun N : ℕ => slice g k N (t ^ g) / slice g 0 N (t ^ g))
      Filter.atTop (nhds (t ^ k)⁻¹) := by
  convert tendsto_general_slice_ratio_with_primitive hg hk ht ( Complex.isPrimitiveRoot_exp g hg.ne' ) using 1

end ResidueSlices