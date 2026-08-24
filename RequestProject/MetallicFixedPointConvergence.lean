/-
Metallic cutoff Phase C2A: spectral form and convergence of the canonical
metallic fixed point.

RequestProject.MetallicFixedPoint constructs the unique canonical point
evenFixedPoint m in [silver,3] for every m >= 1 with recoveryMap m
(evenFixedPoint m) = evenFixedPoint m. This module supplies the exact
two-eigenvalue representation of the finite metallic row, proves uniform
convergence of the recovery maps on [silver,3], and proves
evenFixedPoint m -> silver with explicit coarse geometric bounds (constants 6
and 18*silver).

This phase does NOT attempt the sharp limit
spectralBase^(2m) * (evenFixedPoint m - silver) -> 4*silver (Phase C2B); the
present estimate is intentionally coarse.
-/
import RequestProject.MetallicFixedPoint

open Set

namespace MetallicCutoff

noncomputable def positiveFixedRoot (delta : ℝ) : ℝ :=
  ((delta - 1) + Real.sqrt ((delta - 1) ^ 2 + 4)) / 2

noncomputable def negativeFixedRoot (delta : ℝ) : ℝ :=
  ((delta - 1) - Real.sqrt ((delta - 1) ^ 2 + 4)) / 2

noncomputable def rowSpectralRatio (delta : ℝ) : ℝ :=
  ((delta + 1) - Real.sqrt ((delta - 1) ^ 2 + 4)) /
    ((delta + 1) + Real.sqrt ((delta - 1) ^ 2 + 4))

/-! ### Numeric preliminaries -/

private lemma sqrt_two_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

private lemma sqrt_two_lb : (1.4142 : ℝ) < Real.sqrt 2 := by
  have h0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  nlinarith [sqrt_two_sq]

private lemma sqrt_two_ub : Real.sqrt 2 < 1.4143 := by
  have h0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  nlinarith [sqrt_two_sq]

private lemma beta_eq : beta = 2 * (Real.sqrt 2 - 1) := by
  have h1 := sqrt_two_lb
  rw [beta, silver, div_eq_iff (by nlinarith)]
  nlinarith [sqrt_two_sq]

private lemma beta_pos' : 0 < beta := by
  rw [beta_eq]; linarith [sqrt_two_lb]

private lemma one_sub_beta : 1 - beta = spectralRatio := by
  rw [beta_eq, spectralRatio]; ring

private lemma spectralRatio_pos : 0 < spectralRatio := by
  rw [spectralRatio]; linarith [sqrt_two_ub]

private lemma spectralRatio_lt_third : spectralRatio < 1 / 3 := by
  rw [spectralRatio]; linarith [sqrt_two_lb]

private lemma silver_pos' : 0 < silver := silver_identities.1

/-! ### Exact eigenvalue data -/

private lemma disc_sq (delta : ℝ) :
    Real.sqrt ((delta - 1) ^ 2 + 4) ^ 2 = (delta - 1) ^ 2 + 4 :=
  Real.sq_sqrt (by positivity)

private lemma disc_ge_two (delta : ℝ) : 2 ≤ Real.sqrt ((delta - 1) ^ 2 + 4) := by
  have h0 : 0 ≤ Real.sqrt ((delta - 1) ^ 2 + 4) := Real.sqrt_nonneg _
  nlinarith [disc_sq delta, sq_nonneg (delta - 1)]

private lemma disc_lt_add_one {delta : ℝ} (hdelta : 1 < delta) :
    Real.sqrt ((delta - 1) ^ 2 + 4) < delta + 1 := by
  have h0 : 0 ≤ Real.sqrt ((delta - 1) ^ 2 + 4) := Real.sqrt_nonneg _
  nlinarith [disc_sq delta]

/-- The exact two-eigenvalue closed form for the metallic row state. -/
private lemma state_closed_form {delta D : ℝ} (hD : D ^ 2 = (delta - 1) ^ 2 + 4) (N : ℕ) :
    2 * D * (state delta N).1 =
        (delta - 1 + D) * ((delta + 1 + D) / 2) ^ N +
          (1 - delta + D) * ((delta + 1 - D) / 2) ^ N ∧
      D * (state delta N).2 =
        ((delta + 1 + D) / 2) ^ N - ((delta + 1 - D) / 2) ^ N := by
  induction N with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp [state]; ring
    · simp [state]
  | succ N ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [state_succ]
    refine ⟨?_, ?_⟩
    · have hrw : 2 * D * (delta * (state delta N).1 + (state delta N).2) =
          delta * (2 * D * (state delta N).1) + 2 * (D * (state delta N).2) := by ring
      simp only
      rw [hrw, h1, h2]
      linear_combination
        ((((delta + 1 - D) / 2) ^ N - ((delta + 1 + D) / 2) ^ N) / 2) * hD
    · have hrw : D * ((state delta N).1 + (state delta N).2) =
          (2 * D * (state delta N).1) / 2 + D * (state delta N).2 := by ring
      simp only
      rw [hrw, h1, h2]
      ring

theorem rowSpectralRatio_mem_unitInterval {delta : ℝ} (hdelta : 1 < delta) :
    rowSpectralRatio delta ∈ Set.Ioo (0 : ℝ) 1 := by
  have hD0 : 0 < Real.sqrt ((delta - 1) ^ 2 + 4) := lt_of_lt_of_le (by norm_num) (disc_ge_two delta)
  have hlt := disc_lt_add_one hdelta
  have hden : 0 < (delta + 1) + Real.sqrt ((delta - 1) ^ 2 + 4) := by linarith
  constructor
  · exact div_pos (by linarith) hden
  · rw [rowSpectralRatio, div_lt_one hden]; linarith

/-- The exact spectral decomposition of the finite metallic row ratio. -/
theorem ratio_spectral_decomposition {delta : ℝ} (hdelta : 1 < delta)
    {N : ℕ} (hN : 1 ≤ N) :
    ratio delta N =
      positiveFixedRoot delta +
        Real.sqrt ((delta - 1) ^ 2 + 4) * rowSpectralRatio delta ^ N /
          (1 - rowSpectralRatio delta ^ N) := by
  set D := Real.sqrt ((delta - 1) ^ 2 + 4) with hDdef
  have hD2 : D ^ 2 = (delta - 1) ^ 2 + 4 := disc_sq delta
  have hD0 : 0 < D := lt_of_lt_of_le (by norm_num) (disc_ge_two delta)
  have hlt := disc_lt_add_one hdelta
  set L := (delta + 1 + D) / 2 with hLdef
  set M := (delta + 1 - D) / 2 with hMdef
  have hM0 : 0 < M := by rw [hMdef]; linarith
  have hML : M < L := by rw [hLdef, hMdef]; linarith
  have hL0 : 0 < L := lt_trans hM0 hML
  have hpow : M ^ N < L ^ N := pow_lt_pow_left₀ hML hM0.le (by omega)
  have hLN : (0 : ℝ) < L ^ N := pow_pos hL0 N
  obtain ⟨h1, h2⟩ := state_closed_form (delta := delta) (D := D) hD2 N
  have hrho : rowSpectralRatio delta = M / L := by
    rw [rowSpectralRatio, hLdef, hMdef, ← hDdef]
    rw [div_eq_div_iff (by linarith) (by linarith)]
    ring
  have hrhoN : rowSpectralRatio delta ^ N = M ^ N / L ^ N := by
    rw [hrho, div_pow]
  have hone : 1 - rowSpectralRatio delta ^ N = (L ^ N - M ^ N) / L ^ N := by
    rw [hrhoN]; field_simp
  have hnum : (state delta N).1 =
      ((delta - 1 + D) * L ^ N + (1 - delta + D) * M ^ N) / (2 * D) := by
    field_simp at h1 ⊢
    linarith [h1]
  have hden : (state delta N).2 = (L ^ N - M ^ N) / D := by
    field_simp at h2 ⊢
    linarith [h2]
  have hsub : (0 : ℝ) < L ^ N - M ^ N := by linarith
  have hDne : D ≠ 0 := hD0.ne'
  have hLNne : L ^ N ≠ 0 := hLN.ne'
  have hsubne : L ^ N - M ^ N ≠ 0 := hsub.ne'
  rw [ratio, numerator, denominator, hnum, hden, hone, hrhoN, positiveFixedRoot, ← hDdef]
  field_simp
  ring

theorem roots_and_ratio_at_three :
    positiveFixedRoot 3 = silver ∧
    negativeFixedRoot 3 = 1 - Real.sqrt 2 ∧
    rowSpectralRatio 3 = spectralRatio := by
  have h8 : ((3 : ℝ) - 1) ^ 2 + 4 = 8 := by norm_num
  have hs8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num)]
  have hD : Real.sqrt (((3 : ℝ) - 1) ^ 2 + 4) = 2 * Real.sqrt 2 := by rw [h8, hs8]
  refine ⟨?_, ?_, ?_⟩
  · rw [positiveFixedRoot, hD, silver]; ring
  · rw [negativeFixedRoot, hD]; ring
  · rw [rowSpectralRatio, hD, spectralRatio,
      div_eq_iff (by nlinarith [sqrt_two_lb] : (3 : ℝ) + 1 + 2 * Real.sqrt 2 ≠ 0)]
    nlinarith [sqrt_two_sq]

/-! ### Uniform interval bounds -/

private lemma three_le_shift {z : ℝ} (hz : z ∈ Set.Icc silver 3) : 3 ≤ 1 + beta * z := by
  have hbs : beta * silver = 2 := silver_identities.2.1
  have : beta * silver ≤ beta * z := mul_le_mul_of_nonneg_left hz.1 beta_pos'.le
  linarith [hbs ▸ this]

private lemma shift_le {z : ℝ} (hz : z ∈ Set.Icc silver 3) : beta * z ≤ 3 := by
  have hb : beta = 2 * (Real.sqrt 2 - 1) := beta_eq
  have : beta * z ≤ beta * 3 := mul_le_mul_of_nonneg_left hz.2 beta_pos'.le
  rw [hb] at this ⊢
  nlinarith [sqrt_two_ub]

private lemma rowSpectralRatio_le {delta : ℝ} (hdelta : 1 < delta) :
    rowSpectralRatio delta ≤ spectralRatio := by
  set D := Real.sqrt ((delta - 1) ^ 2 + 4) with hDdef
  have hD2 : D ^ 2 = (delta - 1) ^ 2 + 4 := disc_sq delta
  have hD0 : 0 < D := lt_of_lt_of_le (by norm_num) (disc_ge_two delta)
  have hlt : D < delta + 1 := disc_lt_add_one hdelta
  have hden : 0 < (delta + 1) + D := by linarith
  have hkey : ((delta + 1) * (2 * Real.sqrt 2 - 2)) ^ 2 ≤ (D * (4 - 2 * Real.sqrt 2)) ^ 2 := by
    nlinarith [sq_nonneg (delta - 3), sqrt_two_sq, sqrt_two_lb, sqrt_two_ub, hD2]
  have h1 : 0 ≤ (delta + 1) * (2 * Real.sqrt 2 - 2) := by nlinarith [sqrt_two_lb]
  have h2 : 0 ≤ D * (4 - 2 * Real.sqrt 2) := by nlinarith [sqrt_two_ub]
  have hlin : (delta + 1) * (2 * Real.sqrt 2 - 2) ≤ D * (4 - 2 * Real.sqrt 2) := by
    nlinarith [hkey, h1, h2]
  rw [rowSpectralRatio, ← hDdef, div_le_iff₀ hden, spectralRatio]
  nlinarith [hlin]

private lemma disc_shift_le_four {z : ℝ} (hz : z ∈ Set.Icc silver 3) :
    Real.sqrt (((1 + beta * z) - 1) ^ 2 + 4) ≤ 4 := by
  have h0 : 0 ≤ Real.sqrt (((1 + beta * z) - 1) ^ 2 + 4) := Real.sqrt_nonneg _
  have hsq := disc_sq (1 + beta * z)
  have hbz : beta * z ≤ 3 := shift_le hz
  have hbz0 : 0 < beta * z := mul_pos beta_pos' (lt_of_lt_of_le silver_pos' hz.1)
  nlinarith [hsq, h0]

theorem recoveryMap_sub_positiveFixedRoot_bound {m : ℕ} (hm : 1 ≤ m)
    {z : ℝ} (hz : z ∈ Set.Icc silver 3) :
    0 ≤ recoveryMap m z - positiveFixedRoot (1 + beta * z) ∧
    recoveryMap m z - positiveFixedRoot (1 + beta * z) ≤
      6 * spectralRatio ^ (2 * m) := by
  have hdelta : 1 < 1 + beta * z := by linarith [three_le_shift hz]
  have hN : 1 ≤ 2 * m := by omega
  have hdec := ratio_spectral_decomposition hdelta hN
  have hrec : recoveryMap m z = ratio (1 + beta * z) (2 * m) := rfl
  set rho := rowSpectralRatio (1 + beta * z) with hrhodef
  obtain ⟨hrho0, hrho1⟩ := rowSpectralRatio_mem_unitInterval hdelta
  have hrhole : rho ≤ spectralRatio := rowSpectralRatio_le hdelta
  have hsr0 : 0 < spectralRatio := spectralRatio_pos
  have hsr3 : spectralRatio < 1 / 3 := spectralRatio_lt_third
  have hpowle : rho ^ (2 * m) ≤ spectralRatio ^ (2 * m) :=
    pow_le_pow_left₀ hrho0.le hrhole _
  have hpow0 : 0 < rho ^ (2 * m) := pow_pos hrho0 _
  have hsrpow2 : spectralRatio ^ (2 * m) ≤ spectralRatio ^ 2 :=
    pow_le_pow_of_le_one hsr0.le (by linarith) (by omega)
  have hsmall : spectralRatio ^ (2 * m) ≤ 1 / 9 := by
    have : spectralRatio ^ 2 ≤ 1 / 9 := by nlinarith
    linarith
  have hone : (0 : ℝ) < 1 - rho ^ (2 * m) := by linarith
  have hDle : Real.sqrt (((1 + beta * z) - 1) ^ 2 + 4) ≤ 4 := disc_shift_le_four hz
  have hD0 : 0 ≤ Real.sqrt (((1 + beta * z) - 1) ^ 2 + 4) := Real.sqrt_nonneg _
  have hdiff : recoveryMap m z - positiveFixedRoot (1 + beta * z) =
      Real.sqrt (((1 + beta * z) - 1) ^ 2 + 4) * rho ^ (2 * m) / (1 - rho ^ (2 * m)) := by
    rw [hrec, hdec]; ring
  rw [hdiff]
  constructor
  · positivity
  · rw [div_le_iff₀ hone]
    nlinarith [hpowle, hpow0, hD0, hDle, hsmall, pow_pos hsr0 (2 * m)]

theorem tendstoUniformlyOn_recoveryMap :
    TendstoUniformlyOn
      (fun m z => recoveryMap m z)
      (fun z => positiveFixedRoot (1 + beta * z))
      Filter.atTop (Set.Icc silver 3) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro eps heps
  have hsr0 : 0 < spectralRatio := spectralRatio_pos
  have hsr1 : spectralRatio < 1 := by linarith [spectralRatio_lt_third]
  have htend : Filter.Tendsto (fun m : ℕ => 6 * spectralRatio ^ (2 * m)) Filter.atTop
      (nhds 0) := by
    have h1 : Filter.Tendsto (fun m : ℕ => (spectralRatio ^ 2) ^ m) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by nlinarith)
    have h2 : (fun m : ℕ => 6 * spectralRatio ^ (2 * m)) =
        fun m : ℕ => 6 * (spectralRatio ^ 2) ^ m := by
      funext m; rw [← pow_mul]
    rw [h2]
    simpa using h1.const_mul (6 : ℝ)
  have heventually := htend.eventually (gt_mem_nhds heps)
  filter_upwards [heventually, Filter.eventually_ge_atTop 1] with m hm hm1
  intro z hz
  obtain ⟨hlow, hhigh⟩ := recoveryMap_sub_positiveFixedRoot_bound hm1 hz
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-! ### The limiting fixed point equation -/

private lemma positiveFixedRoot_sq (delta : ℝ) :
    positiveFixedRoot delta ^ 2 = (delta - 1) * positiveFixedRoot delta + 1 := by
  rw [positiveFixedRoot]
  linear_combination (1 / 4 : ℝ) * disc_sq delta

private lemma positiveFixedRoot_pos {delta : ℝ} (hdelta : 1 < delta) :
    0 < positiveFixedRoot delta := by
  have h0 : 0 < Real.sqrt ((delta - 1) ^ 2 + 4) :=
    lt_of_lt_of_le (by norm_num) (disc_ge_two delta)
  rw [positiveFixedRoot]; linarith

private lemma one_sub_beta_silver_sq : (1 - beta) * silver ^ 2 = 1 := by
  rw [one_sub_beta, ← silver_identities.2.2.1]
  linarith [silver_identities.2.2.2]

theorem positiveFixedRoot_recovery_fixed_iff {z : ℝ}
    (hz : z ∈ Set.Icc silver 3) :
    positiveFixedRoot (1 + beta * z) = z ↔ z = silver := by
  have hz0 : 0 < z := lt_of_lt_of_le silver_pos' hz.1
  have hbz : 0 < beta * z := mul_pos beta_pos' hz0
  have hdelta : 1 < 1 + beta * z := by linarith
  have hroot := positiveFixedRoot_sq (1 + beta * z)
  have hbeta1 : 0 < 1 - beta := by rw [one_sub_beta]; exact spectralRatio_pos
  have hsilver := one_sub_beta_silver_sq
  constructor
  · intro hfix
    rw [hfix] at hroot
    have hzsq : (1 - beta) * z ^ 2 = 1 := by nlinarith [hroot]
    have hsq : z ^ 2 = silver ^ 2 := by
      have := hsilver
      nlinarith [hzsq]
    nlinarith [hsq, silver_pos', hz0]
  · intro hzs
    subst hzs
    have h3 : 1 + beta * silver = 3 := by
      have := silver_identities.2.1
      linarith
    rw [h3]
    exact roots_and_ratio_at_three.1

/-! ### Explicit bound and convergence of the canonical fixed point -/

theorem evenFixedPoint_sub_silver_bound {m : ℕ} (hm : 1 ≤ m) :
    0 ≤ evenFixedPoint m - silver ∧
    evenFixedPoint m - silver ≤
      18 * silver * spectralRatio ^ (2 * m) := by
  obtain ⟨hmem, -, hfix⟩ := evenFixedPoint_spec hm
  set z := evenFixedPoint m with hzdef
  have hz0 : 0 < z := lt_of_lt_of_le silver_pos' hmem.1
  have hdelta : 1 < 1 + beta * z := by linarith [mul_pos beta_pos' hz0]
  set L := positiveFixedRoot (1 + beta * z) with hLdef
  have hL0 : 0 < L := positiveFixedRoot_pos hdelta
  have hroot : L ^ 2 = (beta * z) * L + 1 := by
    have := positiveFixedRoot_sq (1 + beta * z)
    rw [← hLdef] at this
    linarith [this]
  obtain ⟨hlow, hhigh⟩ := recoveryMap_sub_positiveFixedRoot_bound hm hmem
  rw [hfix, ← hLdef] at hlow hhigh
  have hbeta1 : 0 < 1 - beta := by rw [one_sub_beta]; exact spectralRatio_pos
  have hsilver := one_sub_beta_silver_sq
  have hkey : (1 - beta) * (z - silver) * (z + silver) = (z - L) * (z + L - beta * z) := by
    nlinarith [hroot, hsilver]
  refine ⟨by linarith [hmem.1], ?_⟩
  have hzle : z ≤ 3 := hmem.2
  have hLz : L ≤ z := by linarith
  have hrhs : (z - L) * (z + L - beta * z) ≤ 36 * spectralRatio ^ (2 * m) := by
    have h1 : z + L - beta * z ≤ 6 := by nlinarith [beta_pos'.le, hz0]
    have h2 : 0 ≤ z + L - beta * z := by nlinarith [hbeta1, hL0, hz0]
    nlinarith [hlow, hhigh, pow_pos spectralRatio_pos (2 * m)]
  have hlhs : (1 - beta) * (2 * silver) * (z - silver) ≤
      (1 - beta) * (z - silver) * (z + silver) := by
    nlinarith [mul_nonneg (mul_nonneg hbeta1.le (sub_nonneg.mpr hmem.1))
      (sub_nonneg.mpr hmem.1)]
  have hcoef : (1 - beta) * (2 * silver) = 2 / silver := by
    rw [eq_div_iff silver_pos'.ne']
    linear_combination (2 : ℝ) * hsilver
  have hfinal : (2 / silver) * (z - silver) ≤ 36 * spectralRatio ^ (2 * m) := by
    rw [← hcoef]; linarith [hkey ▸ hlhs]
  have hspos : 0 < silver := silver_pos'
  rw [div_mul_eq_mul_div, div_le_iff₀ hspos] at hfinal
  nlinarith [hfinal]

theorem tendsto_evenFixedPoint :
    Filter.Tendsto evenFixedPoint Filter.atTop (nhds silver) := by
  have hsr0 : 0 < spectralRatio := spectralRatio_pos
  have hsr1 : spectralRatio < 1 := by linarith [spectralRatio_lt_third]
  have htend : Filter.Tendsto (fun m : ℕ => 18 * silver * spectralRatio ^ (2 * m))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun m : ℕ => (spectralRatio ^ 2) ^ m) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by nlinarith)
    have h2 : (fun m : ℕ => 18 * silver * spectralRatio ^ (2 * m)) =
        fun m : ℕ => (18 * silver) * (spectralRatio ^ 2) ^ m := by
      funext m; rw [← pow_mul]
    rw [h2]
    simpa using h1.const_mul (18 * silver)
  have hsq : Filter.Tendsto (fun m : ℕ => evenFixedPoint m - silver) Filter.atTop (nhds 0) := by
    refine squeeze_zero' ?_ ?_ htend
    · filter_upwards [Filter.eventually_ge_atTop 1] with m hm
      exact (evenFixedPoint_sub_silver_bound hm).1
    · filter_upwards [Filter.eventually_ge_atTop 1] with m hm
      exact (evenFixedPoint_sub_silver_bound hm).2
  have := hsq.add (tendsto_const_nhds (x := silver) (f := Filter.atTop (α := ℕ)))
  simpa using this

end MetallicCutoff
