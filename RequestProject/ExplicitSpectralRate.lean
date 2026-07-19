import RequestProject.QuantitativeSpectralGap

open scoped BigOperators

namespace ResidueSlices

/-- The complex slice at a real argument is the cast of the real slice. -/
lemma slice_ofReal (g r N : ℕ) (x : ℝ) :
    slice g r N ((x : ℂ)) = ((slice g r N x : ℝ) : ℂ) := by
  simp only [slice]
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> push_cast <;> ring

/-- Explicit deviation of a filtered packet from the principal binomial wave:
`|g·t^k'·slice − (1+t)^N| ≤ (g−1)·ρ^N·(1+t)^N`. -/
lemma packet_principal_deviation
    {g k' : ℕ} (hg : 0 < g) (hk' : k' < g) {t : ℝ} (ht : 0 < t)
    {ω : ℂ} (hω : IsPrimitiveRoot ω g) (N : ℕ) :
    |(g : ℝ) * t ^ k' * slice g k' N (t ^ g) - (1 + t) ^ N| ≤
      ((g : ℝ) - 1) * spectralGap g t ω ^ N * (1 + t) ^ N := by
  have hωnorm : ‖ω‖ = 1 := hω.norm'_eq_one hg.ne'
  have hfilter := roots_of_unity_filter (N := N) hg hk' hω (t : ℂ)
  have hcast : slice g k' N ((t : ℂ) ^ g) = ((slice g k' N (t ^ g) : ℝ) : ℂ) := by
    rw [show ((t : ℂ)) ^ g = ((t ^ g : ℝ) : ℂ) by norm_cast]
    exact slice_ofReal g k' N (t ^ g)
  rw [hcast] at hfilter
  have h0 : (0 : ℕ) ∈ Finset.range g := Finset.mem_range.mpr hg
  rw [← Finset.add_sum_erase _ _ h0] at hfilter
  simp only [Nat.zero_mul, pow_zero, one_mul, mul_one] at hfilter
  have hdiff : (((g : ℝ) * t ^ k' * slice g k' N (t ^ g) - (1 + t) ^ N : ℝ) : ℂ)
      = ∑ a ∈ (Finset.range g).erase 0,
          ω ^ (a * (g - k')) * (1 + (t : ℂ) * ω ^ a) ^ N := by
    push_cast
    linear_combination -hfilter
  have habs : |(g : ℝ) * t ^ k' * slice g k' N (t ^ g) - (1 + t) ^ N|
      = ‖∑ a ∈ (Finset.range g).erase 0,
          ω ^ (a * (g - k')) * (1 + (t : ℂ) * ω ^ a) ^ N‖ := by
    rw [← hdiff, Complex.norm_real, Real.norm_eq_abs]
  rw [habs]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ a ∈ (Finset.range g).erase 0,
      ‖ω ^ (a * (g - k')) * (1 + (t : ℂ) * ω ^ a) ^ N‖ ≤
        spectralGap g t ω ^ N * (1 + t) ^ N := by
    intro a ha
    obtain ⟨ha0, harange⟩ := Finset.mem_erase.mp ha
    have h1 : ‖ω ^ (a * (g - k'))‖ = 1 := by rw [norm_pow, hωnorm, one_pow]
    rw [norm_mul, h1, one_mul, norm_pow]
    have h2 : ‖1 + (t : ℂ) * ω ^ a‖ = channelRatio t ω a * (1 + t) := by
      unfold channelRatio
      rw [div_mul_cancel₀]
      exact (by positivity : (0 : ℝ) < 1 + t).ne'
    rw [h2, mul_pow]
    have h3 : channelRatio t ω a ≤ spectralGap g t ω :=
      channelRatio_le_spectralGap harange ha0
    have h4 : 0 ≤ channelRatio t ω a :=
      div_nonneg (norm_nonneg _) (by positivity)
    gcongr
  refine le_trans (Finset.sum_le_card_nsmul _ _ _ hterm) ?_
  rw [Finset.card_erase_of_mem h0, Finset.card_range, nsmul_eq_mul]
  rw [Nat.cast_sub hg, Nat.cast_one, mul_assoc]

/-- **Explicit-constant spectral rate.**  Once the row index `N` clears the
explicit threshold `(g−1)·ρ^N ≤ 1/2`, the slice-ratio error is bounded by
`4(g−1)·ρ^N / t^k` — a fully computable error bar with no existential
constant.  Here `ρ = spectralGap g t ω`. -/
theorem general_slice_ratio_explicit_rate
    {g k : ℕ} (hg : 0 < g) (hk : k < g) {t : ℝ} (ht : 0 < t)
    {ω : ℂ} (hω : IsPrimitiveRoot ω g) {N : ℕ}
    (hN : ((g : ℝ) - 1) * spectralGap g t ω ^ N ≤ 1 / 2) :
    |slice g k N (t ^ g) / slice g 0 N (t ^ g) - (t ^ k)⁻¹| ≤
      4 * (((g : ℝ) - 1) * spectralGap g t ω ^ N) / t ^ k := by
  have hρ := spectralGap_mem_unitInterval hg ht hω
  have hg1 : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  set ρ := spectralGap g t ω with hρdef
  set β := ((g : ℝ) - 1) * ρ ^ N with hβdef
  set D := (1 + t) ^ N with hDdef
  have hDpos : (0 : ℝ) < D := by positivity
  have hβ0 : 0 ≤ β := mul_nonneg (by linarith) (pow_nonneg hρ.1 N)
  have hA := packet_principal_deviation hg hk ht hω N
  have hB := packet_principal_deviation hg hg ht hω N
  rw [pow_zero, mul_one] at hB
  have hS0pos : (0 : ℝ) < slice g 0 N (t ^ g) :=
    zero_lt_one.trans_le (one_le_slice_zero g N (by positivity))
  have hgS0 : D / 2 ≤ (g : ℝ) * slice g 0 N (t ^ g) := by
    have h1 := abs_le.mp hB
    nlinarith [hDpos, hN]
  have hnum : |(g : ℝ) * t ^ k * slice g k N (t ^ g) - (g : ℝ) * slice g 0 N (t ^ g)|
      ≤ 2 * β * D := by
    calc |(g : ℝ) * t ^ k * slice g k N (t ^ g) - (g : ℝ) * slice g 0 N (t ^ g)|
        ≤ |(g : ℝ) * t ^ k * slice g k N (t ^ g) - D| +
          |D - (g : ℝ) * slice g 0 N (t ^ g)| := abs_sub_le _ _ _
      _ = |(g : ℝ) * t ^ k * slice g k N (t ^ g) - D| +
          |(g : ℝ) * slice g 0 N (t ^ g) - D| := by rw [abs_sub_comm D]
      _ ≤ β * D + β * D := add_le_add hA hB
      _ = 2 * β * D := by ring
  have hkey : slice g k N (t ^ g) / slice g 0 N (t ^ g) - (t ^ k)⁻¹
      = ((g : ℝ) * t ^ k * slice g k N (t ^ g) - (g : ℝ) * slice g 0 N (t ^ g)) /
        ((g : ℝ) * t ^ k * slice g 0 N (t ^ g)) := by
    have hgne : (g : ℝ) ≠ 0 := by positivity
    field_simp
  rw [hkey, abs_div,
    abs_of_pos (show (0 : ℝ) < (g : ℝ) * t ^ k * slice g 0 N (t ^ g) by positivity)]
  have hden : t ^ k * (D / 2) ≤ (g : ℝ) * t ^ k * slice g 0 N (t ^ g) := by
    calc t ^ k * (D / 2) ≤ t ^ k * ((g : ℝ) * slice g 0 N (t ^ g)) := by
          exact mul_le_mul_of_nonneg_left hgS0 (by positivity)
      _ = (g : ℝ) * t ^ k * slice g 0 N (t ^ g) := by ring
  calc |(g : ℝ) * t ^ k * slice g k N (t ^ g) - (g : ℝ) * slice g 0 N (t ^ g)| /
        ((g : ℝ) * t ^ k * slice g 0 N (t ^ g))
      ≤ (2 * β * D) / (t ^ k * (D / 2)) := by
        apply div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = 4 * β / t ^ k := by
        field_simp
        ring

/-- Canonical version at `ω = exp(2πi/g)`. -/
theorem general_slice_ratio_explicit_rate_exp
    {g k : ℕ} (hg : 0 < g) (hk : k < g) {t : ℝ} (ht : 0 < t) {N : ℕ}
    (hN : ((g : ℝ) - 1) *
        spectralGap g t (Complex.exp (2 * Real.pi * Complex.I / g)) ^ N ≤ 1 / 2) :
    |slice g k N (t ^ g) / slice g 0 N (t ^ g) - (t ^ k)⁻¹| ≤
      4 * (((g : ℝ) - 1) *
        spectralGap g t (Complex.exp (2 * Real.pi * Complex.I / g)) ^ N) / t ^ k :=
  general_slice_ratio_explicit_rate hg hk ht
    (Complex.isPrimitiveRoot_exp g hg.ne') hN

end ResidueSlices
