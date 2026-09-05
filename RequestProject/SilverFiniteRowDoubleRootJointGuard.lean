/-
Cubic-silver finite-row crossover, Phase B4B12: bounded-window joint
negative-center-error and derivative-noncancellation selector.

Closes the joint-row gap: one finite-row `J` with BOTH a genuinely negative center
error `E_J <= -c*rho^J` and a strong derivative `c*J*rho^J <= |d_J|`, on a
bounded-delay schedule. `jointCenterGuardScore` is `min(-E_N/rho^N,
|d_N|/(N*rho^N))`; `jointCenterGuardRow N L alpha` is the classical finite-max
selector over `[N,N+L]`. The new geometry (`exists_bounded_joint_center_phase_guard`)
is a uniform bounded-window phase guard: for `alpha > 1` the unit channel argument
lies in `(0, π/2)`, so on the half-turn `(π/2, 3π/2)` the center phase is negative
and the derivative phase has a controlled zero, leaving a window of length at least
`π/2` reached by the forward orbit; a single `L` and `c > 0` (both depending only on
`alpha`) come from an open cover of the unit circle by positivity sets, compactness,
and the extreme-value theorem. The two normalized phase limits transfer the geometry
to the actual endpoint-corrected reversed-ratio errors, and score maximality passes
both guards to the selector, whose negative-error inner scale is nondegenerate.
`L`, `c`, and the onset depend on `alpha` only; `alpha > 1` is strict; rates are at
`J`. This proves no monotonicity of the selector, no agreement with adaptiveRow or
adaptiveDerivativeRow, no driver domination, no opposite Taylor-discriminant signs,
and no finite-row root splitting.
-/
import RequestProject.SilverFiniteRowDoubleRootSymmetryRate
open scoped Real Topology BigOperators
open Filter

namespace SilverFiniteRow

/-- A signed center-error guard together with an unsigned derivative guard. -/
noncomputable def jointCenterGuardScore (N : Nat) (alpha : Real) : Real :=
  min (-centerError N alpha / centerRho alpha ^ N)
    (|centerDerivativeError N alpha| / ((N : Real) * centerRho alpha ^ N))

/-- A maximizer in the nonempty inclusive window [N,N+L]. Ties are arbitrary. -/
noncomputable def jointCenterGuardRow (N L : Nat) (alpha : Real) : Nat :=
  N + Classical.epsilon (fun j : Nat => j ≤ L ∧
    ∀ i : Nat, i ≤ L →
      jointCenterGuardScore (N + i) alpha ≤ jointCenterGuardScore (N + j) alpha)

-- Target 1: even N=0 and L=0 are allowed; divisions use Lean's total field operations.
theorem exists_jointCenterGuardScore_max (N L : Nat) (alpha : Real) :
    ∃ j : Nat, j ≤ L ∧ ∀ i : Nat, i ≤ L →
      jointCenterGuardScore (N + i) alpha ≤ jointCenterGuardScore (N + j) alpha := by
  obtain ⟨j, hjmem, hj⟩ := Finset.exists_max_image (Finset.range (L + 1))
    (fun i => jointCenterGuardScore (N + i) alpha) ⟨0, by simp⟩
  exact ⟨j, Nat.lt_succ_iff.mp (Finset.mem_range.mp hjmem),
    fun i hi => hj i (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))⟩

-- Target 2.
theorem jointCenterGuardRow_bounds (N L : Nat) (alpha : Real) :
    N ≤ jointCenterGuardRow N L alpha ∧ jointCenterGuardRow N L alpha ≤ N + L := by
  have hspec := Classical.epsilon_spec (exists_jointCenterGuardScore_max N L alpha)
  exact ⟨Nat.le_add_right _ _, Nat.add_le_add_left hspec.1 N⟩

-- Target 3.
theorem jointCenterGuardRow_score_max (N L : Nat) (alpha : Real)
    {j : Nat} (hj : j ≤ L) :
    jointCenterGuardScore (N + j) alpha ≤
      jointCenterGuardScore (jointCenterGuardRow N L alpha) alpha := by
  exact (Classical.epsilon_spec (exists_jointCenterGuardScore_max N L alpha)).2 j hj

-- Target 4: cofinal, not necessarily strictly increasing.
theorem tendsto_jointCenterGuardRow (L : Nat) (alpha : Real) :
    Filter.Tendsto (fun N : Nat => jointCenterGuardRow N L alpha)
      Filter.atTop Filter.atTop := by
  exact Filter.tendsto_atTop_mono (fun N => (jointCenterGuardRow_bounds N L alpha).1)
    Filter.tendsto_id

/-- The center channel is its own modulus times the unit channel. -/
private theorem centerChannel_eq_rho_mul_unit
    {alpha : Real} (halpha : 0 < alpha) :
    centerChannel alpha = (centerRho alpha : Complex) * centerUnitChannel alpha := by
  have hrho : (centerRho alpha : Complex) ≠ 0 := by
    simpa using (ne_of_gt (centerRho_pos halpha))
  unfold centerUnitChannel
  field_simp

-- Target 5: the signed normalized center error, with the corrected endpoint.
theorem tendsto_centerError_sub_phase_normalized
    {alpha : Real} (halpha : 1 < alpha) :
    Filter.Tendsto
      (fun N : Nat => centerError N alpha / centerRho alpha ^ N -
        2 * alpha * Complex.re ((centerOmega ^ 2 - 1) * centerUnitChannel alpha ^ N))
      Filter.atTop (nhds 0) := by
  have halpha0 : 0 < alpha := lt_trans one_pos halpha
  obtain ⟨hrho0, hrho1⟩ := centerRho_mem_unitInterval halpha0
  set M : Real := ‖centerOmega ^ 2 - 1‖ with hM
  set P : Nat → Real :=
    fun N => Complex.re ((centerOmega ^ 2 - 1) * centerUnitChannel alpha ^ N) with hP
  have hPbdd : ∀ N : Nat, |P N| ≤ M := by
    intro N
    have hnorm : ‖(centerOmega ^ 2 - 1) * centerUnitChannel alpha ^ N‖ = M := by
      rw [hM, norm_mul, norm_pow, norm_centerUnitChannel halpha0, one_pow, mul_one]
    rw [hP]
    calc |Complex.re ((centerOmega ^ 2 - 1) * centerUnitChannel alpha ^ N)|
        ≤ ‖(centerOmega ^ 2 - 1) * centerUnitChannel alpha ^ N‖ := Complex.abs_re_le_norm _
      _ = M := hnorm
  have hD : Tendsto (fun N : Nat => centerDenominatorWave N alpha) atTop (nhds 1) :=
    tendsto_centerDenominatorWave halpha0
  have hW : Tendsto (fun N : Nat => centerEndpointTerm N alpha / centerRho alpha ^ N)
      atTop (nhds 0) := tendsto_centerEndpointTerm_div_rho_pow halpha
  have hnum1 : Tendsto (fun N : Nat => 2 * P N * (1 - centerDenominatorWave N alpha))
      atTop (nhds 0) := by
    have hMnn : (0 : Real) ≤ M := le_trans (abs_nonneg _) (hPbdd 0)
    refine squeeze_zero_norm (a := fun N : Nat => 2 * M * |1 - centerDenominatorWave N alpha|)
      (fun N => ?_) ?_
    · have h1 : |2 * P N * (1 - centerDenominatorWave N alpha)|
          = 2 * |P N| * |1 - centerDenominatorWave N alpha| := by
        rw [abs_mul, abs_mul]; norm_num
      rw [Real.norm_eq_abs, h1]
      have h2 := hPbdd N
      nlinarith [abs_nonneg (1 - centerDenominatorWave N alpha), abs_nonneg (P N)]
    · have h2 : Tendsto (fun N : Nat => |1 - centerDenominatorWave N alpha|) atTop (nhds 0) := by
        have := (tendsto_const_nhds (x := (1 : Real)) (f := atTop (α := Nat))).sub hD
        simpa using this.abs
      simpa using h2.const_mul (2 * M)
  have hnum : Tendsto
      (fun N : Nat => alpha * ((2 * P N * (1 - centerDenominatorWave N alpha) +
        centerEndpointTerm N alpha / centerRho alpha ^ N) / centerDenominatorWave N alpha))
      atTop (nhds 0) := by
    have hq := (hnum1.add hW).div hD one_ne_zero
    simpa using (hq.const_mul alpha)
  refine hnum.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hden : 0 < centerDenominatorWave N alpha := centerDenominatorWave_pos hN halpha0
  have hpow : (0 : Real) < centerRho alpha ^ N := pow_pos hrho0 N
  have hchan : Complex.re ((centerOmega ^ 2 - 1) * centerChannel alpha ^ N)
      = centerRho alpha ^ N * P N := by
    rw [centerChannel_eq_rho_mul_unit halpha0, mul_pow, ← mul_assoc,
      show (centerOmega ^ 2 - 1) * ((centerRho alpha : Complex) ^ N)
        = ((centerRho alpha ^ N : Real) : Complex) * (centerOmega ^ 2 - 1) by push_cast; ring,
      mul_assoc, Complex.re_ofReal_mul]
  rw [centerError_channel_formula hN halpha0, hchan]
  field_simp
  ring

-- Target 6: the signed normalized derivative; no absolute value inside the limit.
theorem tendsto_centerDerivativeError_sub_phase_normalized
    {alpha : Real} (halpha : 1 < alpha) :
    Filter.Tendsto
      (fun N : Nat => centerDerivativeError N alpha /
          ((N : Real) * centerRho alpha ^ N) -
        2 * alpha * Complex.re
          (centerDerivativeChannelCoefficient alpha * centerUnitChannel alpha ^ N))
      Filter.atTop (nhds 0) := by
  have halpha0 : 0 < alpha := lt_trans one_pos halpha
  refine (tendsto_centerDerivativeError_sub_leading_normalized halpha).congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  rw [sub_div, centerDerivativeLeadingTerm_normalized hN halpha0]

/-- Polar identity for the real part of a rotated complex number. -/
private theorem re_mul_exp_aux (a : Complex) (x : Real) :
    (a * Complex.exp ((x : Complex) * Complex.I)).re = ‖a‖ * Real.cos (Complex.arg a + x) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I a]
  rw [mul_assoc, ← Complex.exp_add]
  have h : (Complex.arg a : Complex) * Complex.I + (x : Complex) * Complex.I
      = ((Complex.arg a + x : Real) : Complex) * Complex.I := by push_cast; ring
  rw [h, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- A unit vector rotated by a power of a unit vector, in exponential form. -/
private theorem unit_mul_pow_eq_exp {u z : Complex} (hu : ‖u‖ = 1) (hz : ‖z‖ = 1) (j : Nat) :
    z * u ^ j = Complex.exp (((z.arg + j * u.arg : Real) : Complex) * Complex.I) := by
  have hue : u = Complex.exp ((u.arg : Complex) * Complex.I) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I u]
    rw [hu]; simp
  have hze : z = Complex.exp ((z.arg : Complex) * Complex.I) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z]
    rw [hz]; simp
  conv_lhs => rw [hze, hue]
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Two zeros of a shifted cosine at distance less than `π` coincide. -/
private theorem cos_shift_zero_unique {psi t1 t2 : Real}
    (h1 : Real.cos (t1 + psi) = 0) (h2 : Real.cos (t2 + psi) = 0)
    (hlt : |t1 - t2| < Real.pi) : t1 = t2 := by
  obtain ⟨k1, hk1⟩ := Real.cos_eq_zero_iff.mp h1
  obtain ⟨k2, hk2⟩ := Real.cos_eq_zero_iff.mp h2
  have hdiff : t1 - t2 = ((k1 : Real) - k2) * Real.pi := by
    have h : (t1 + psi) - (t2 + psi)
        = (2 * (k1 : Real) + 1) * Real.pi / 2 - (2 * (k2 : Real) + 1) * Real.pi / 2 := by
      rw [hk1, hk2]
    field_simp at h ⊢
    linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [hdiff, abs_mul, abs_of_pos hpi] at hlt
  have hk : |(k1 : Real) - k2| < 1 := by
    by_contra hcon
    have hge : (1 : Real) ≤ |(k1 : Real) - k2| := not_lt.mp hcon
    nlinarith [abs_nonneg ((k1 : Real) - k2)]
  have hkz : k1 = k2 := by
    have hz : |(k1 : Int) - k2| < 1 := by
      exact_mod_cast (by push_cast; exact hk : |((k1 - k2 : Int) : Real)| < 1)
    rw [abs_lt] at hz
    omega
  rw [hkz] at hdiff
  simp at hdiff
  linarith

/-- A window of length at least `π/2` on which the cosine is negative and a
shifted cosine is nonzero. -/
private theorem exists_good_window (psi : Real) :
    ∃ A B : Real, Real.pi / 2 ≤ B - A ∧
      ∀ t : Real, A < t → t < B → Real.cos t < 0 ∧ Real.cos (t + psi) ≠ 0 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  by_cases hex : ∃ p : Real, Real.pi / 2 < p ∧ p < 3 * Real.pi / 2 ∧ Real.cos (p + psi) = 0
  · obtain ⟨p, hp1, hp2, hp3⟩ := hex
    have key : ∀ t : Real, Real.pi / 2 < t → t < 3 * Real.pi / 2 → t ≠ p →
        Real.cos t < 0 ∧ Real.cos (t + psi) ≠ 0 := by
      intro t ht1 ht2 htne
      refine ⟨Real.cos_neg_of_pi_div_two_lt_of_lt ht1 (by linarith), ?_⟩
      intro hzero
      exact htne (cos_shift_zero_unique hzero hp3 (by rw [abs_lt]; constructor <;> linarith))
    by_cases hcase : Real.pi ≤ p
    · exact ⟨Real.pi / 2, p, by linarith,
        fun t ht1 ht2 => key t ht1 (by linarith) (ne_of_lt ht2)⟩
    · have hcase' : p < Real.pi := not_le.mp hcase
      exact ⟨p, 3 * Real.pi / 2, by linarith,
        fun t ht1 ht2 => key t (by linarith) ht2 (ne_of_gt ht1)⟩
  · refine ⟨Real.pi / 2, 3 * Real.pi / 2, by linarith, fun t ht1 ht2 => ⟨?_, ?_⟩⟩
    · exact Real.cos_neg_of_pi_div_two_lt_of_lt ht1 (by linarith)
    · exact fun hzero => hex ⟨t, ht1, ht2, hzero⟩

/-- Some point of the forward rotation orbit lands strictly inside a window
of length larger than the rotation step. -/
private theorem exists_orbit_hit {s theta A B : Real} (hth : 0 < theta) (hlen : theta < B - A) :
    ∃ (j : Nat) (k : Int), A + 2 * Real.pi * k < s + j * theta ∧
      s + j * theta < B + 2 * Real.pi * k := by
  obtain ⟨k, hk⟩ := exists_nat_gt ((s - A) / (2 * Real.pi))
  have hpi : (0 : Real) < 2 * Real.pi := by positivity
  have hA : s < A + 2 * Real.pi * k := by
    have := (div_lt_iff₀ hpi).mp hk
    linarith
  set A2 : Real := A + 2 * Real.pi * (k : Real) with hA2
  have hpos : 0 < A2 - s := by simp only [hA2]; linarith
  set m : Int := ⌊(A2 - s) / theta⌋ + 1 with hm
  have hm0 : 0 < m := by
    have h : (0 : Real) ≤ (A2 - s) / theta := by positivity
    have := Int.floor_nonneg.mpr h
    omega
  have hmc : ((m.toNat : Real)) = (m : Real) := by exact_mod_cast Int.toNat_of_nonneg hm0.le
  refine ⟨m.toNat, (k : Int), ?_, ?_⟩
  · rw [hmc]
    have h1 : (A2 - s) / theta < (m : Real) := by
      rw [hm]; push_cast; exact Int.lt_floor_add_one _
    have h3 := (div_lt_iff₀ hth).mp h1
    push_cast
    push_cast [hA2] at h3 ⊢
    linarith
  · rw [hmc]
    have h1 : (m : Real) ≤ (A2 - s) / theta + 1 := by
      rw [hm]; push_cast
      have := Int.floor_le ((A2 - s) / theta)
      linarith
    have h2 : (m : Real) * theta ≤ (A2 - s) + theta := by
      have h4 := mul_le_mul_of_nonneg_right h1 hth.le
      rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hth), one_mul] at h4
      linarith
    push_cast [hA2] at h2 ⊢
    linarith

/-- Pointwise noncancellation along the rotation orbit of any unit vector. -/
private theorem exists_index_good {C H u z : Complex} (hC : C ≠ 0) (hH : H ≠ 0)
    (hu : ‖u‖ = 1) (hu0 : 0 < u.arg) (hu2 : u.arg < Real.pi / 2) (hz : ‖z‖ = 1) :
    ∃ j : Nat, (C * (z * u ^ j)).re < 0 ∧ (H * (z * u ^ j)).re ≠ 0 := by
  obtain ⟨A, B, hlen, hgood⟩ := exists_good_window (H.arg - C.arg)
  obtain ⟨j, k, h1, h2⟩ := exists_orbit_hit (s := C.arg + z.arg) (theta := u.arg)
    hu0 (lt_of_lt_of_le hu2 hlen)
  set t : Real := C.arg + z.arg + j * u.arg - 2 * Real.pi * k with ht
  obtain ⟨hcos, hcos2⟩ := hgood t (by rw [ht]; linarith) (by rw [ht]; linarith)
  have hCre : (C * (z * u ^ j)).re = ‖C‖ * Real.cos t := by
    rw [unit_mul_pow_eq_exp hu hz j, re_mul_exp_aux]
    congr 1
    rw [ht]
    have hper := Real.cos_add_int_mul_two_pi
      (C.arg + z.arg + j * u.arg - 2 * Real.pi * k) k
    rw [show C.arg + z.arg + (j : Real) * u.arg - 2 * Real.pi * k + (k : Real) * (2 * Real.pi)
      = C.arg + (z.arg + j * u.arg) by ring] at hper
    exact hper
  have hHre : (H * (z * u ^ j)).re = ‖H‖ * Real.cos (t + (H.arg - C.arg)) := by
    rw [unit_mul_pow_eq_exp hu hz j, re_mul_exp_aux]
    congr 1
    rw [ht]
    have hper := Real.cos_add_int_mul_two_pi
      (C.arg + z.arg + j * u.arg - 2 * Real.pi * k + (H.arg - C.arg)) k
    rw [show C.arg + z.arg + (j : Real) * u.arg - 2 * Real.pi * k + (H.arg - C.arg) +
      (k : Real) * (2 * Real.pi) = H.arg + (z.arg + j * u.arg) by ring] at hper
    exact hper
  refine ⟨j, ?_, ?_⟩
  · rw [hCre]
    exact mul_neg_of_pos_of_neg (norm_pos_iff.mpr hC) hcos
  · rw [hHre]
    exact mul_ne_zero (ne_of_gt (norm_pos_iff.mpr hH)) hcos2

/-- Uniform (in the unit vector) bounded-window joint guard for two nonzero
directions and a rotation by an angle in `(0, π/2)`. -/
private theorem exists_uniform_guard {C H u : Complex} (hC : C ≠ 0) (hH : H ≠ 0)
    (hu : ‖u‖ = 1) (hu0 : 0 < u.arg) (hu2 : u.arg < Real.pi / 2) :
    ∃ L : Nat, ∃ c : Real, 0 < c ∧ ∀ z : Complex, ‖z‖ = 1 → ∃ j : Nat, j ≤ L ∧
      (C * (z * u ^ j)).re ≤ -c ∧ c ≤ |(H * (z * u ^ j)).re| := by
  classical
  set g : Nat → Complex → Real :=
    fun j z => min (-(C * (z * u ^ j)).re) |(H * (z * u ^ j)).re| with hg
  set G : Nat → Complex → Real :=
    fun L z => ∑ j ∈ Finset.range (L + 1), max 0 (g j z) with hG
  have hgcont : ∀ j : Nat, Continuous (g j) := by
    intro j
    have h1 : Continuous fun z : Complex => (C * (z * u ^ j)).re :=
      Complex.continuous_re.comp (continuous_const.mul (continuous_id.mul continuous_const))
    have h2 : Continuous fun z : Complex => (H * (z * u ^ j)).re :=
      Complex.continuous_re.comp (continuous_const.mul (continuous_id.mul continuous_const))
    exact h1.neg.min h2.abs
  have hGcont : ∀ L : Nat, Continuous (G L) :=
    fun L => continuous_finsetSum _ (fun j _ => continuous_const.max (hgcont j))
  have hGmono : ∀ {L L' : Nat}, L ≤ L' → ∀ z, G L z ≤ G L' z := by
    intro L L' hLL z
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun i _ _ => le_max_left _ _)
  set U : Nat → Set Complex := fun L => {z : Complex | 0 < G L z} with hU
  have hUopen : ∀ L, IsOpen (U L) := fun L => isOpen_lt continuous_const (hGcont L)
  have hcover : Metric.sphere (0 : Complex) 1 ⊆ ⋃ L, U L := by
    intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    obtain ⟨j, hj1, hj2⟩ := exists_index_good hC hH hu hu0 hu2 hz
    refine Set.mem_iUnion.mpr ⟨j, show (0 : Real) < G j z from ?_⟩
    have hpos : 0 < g j z := lt_min (by linarith) (abs_pos.mpr hj2)
    exact Finset.sum_pos' (fun i _ => le_max_left _ _)
      ⟨j, Finset.self_mem_range_succ j, lt_max_of_lt_right hpos⟩
  obtain ⟨t, ht⟩ := (isCompact_sphere (0 : Complex) 1).elim_finite_subcover U hUopen hcover
  set L : Nat := t.sup id with hL
  have hLpos : ∀ z : Complex, ‖z‖ = 1 → 0 < G L z := by
    intro z hz
    have hzs : z ∈ Metric.sphere (0 : Complex) 1 := mem_sphere_zero_iff_norm.mpr hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (ht hzs)
    obtain ⟨hit, hiU⟩ := Set.mem_iUnion.mp hi
    exact lt_of_lt_of_le hiU (hGmono (Finset.le_sup (f := id) hit) z)
  obtain ⟨z0, hz0, hmin⟩ := (isCompact_sphere (0 : Complex) 1).exists_isMinOn
    ⟨1, by simp⟩ (hGcont L).continuousOn
  have hc0 : 0 < G L z0 := hLpos z0 (mem_sphere_zero_iff_norm.mp hz0)
  refine ⟨L, G L z0 / (L + 1), by positivity, ?_⟩
  intro z hz
  have hzs : z ∈ Metric.sphere (0 : Complex) 1 := mem_sphere_zero_iff_norm.mpr hz
  have hge : G L z0 ≤ G L z := hmin hzs
  set c : Real := G L z0 / (L + 1) with hc
  have hcpos : 0 < c := by positivity
  have hexj : ∃ j ∈ Finset.range (L + 1), c ≤ max 0 (g j z) := by
    by_contra hcon
    have hall : ∀ j ∈ Finset.range (L + 1), max 0 (g j z) < c := by
      intro j hj
      by_contra h2
      exact hcon ⟨j, hj, not_lt.mp h2⟩
    have hsum : ∑ j ∈ Finset.range (L + 1), max 0 (g j z) < ∑ _j ∈ Finset.range (L + 1), c :=
      Finset.sum_lt_sum_of_nonempty ⟨0, by simp⟩ hall
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    have hkey : (((L : Nat) + 1 : Nat) : Real) * c = G L z0 := by
      rw [hc]; push_cast; field_simp
    rw [hkey] at hsum
    have hlt : G L z < G L z0 := hsum
    linarith
  obtain ⟨j, hjmem, hjge⟩ := hexj
  have hcg : c ≤ g j z := by
    rcases le_max_iff.mp hjge with h | h
    · exact absurd h (not_le.mpr hcpos)
    · exact h
  refine ⟨j, Nat.lt_succ_iff.mp (Finset.mem_range.mp hjmem), ?_, ?_⟩
  · have h2 : c ≤ -(C * (z * u ^ j)).re := le_trans hcg (min_le_left _ _)
    linarith
  · exact le_trans hcg (min_le_right _ _)

private theorem centerOmega_re : centerOmega.re = -(1 / 2) := by
  have h : (2 * (Real.pi : Complex) * Complex.I / 3)
      = ((2 * Real.pi / 3 : Real) : Complex) * Complex.I := by push_cast; ring
  unfold centerOmega
  rw [h, Complex.exp_ofReal_mul_I_re,
    show (2 * Real.pi / 3 : Real) = Real.pi - Real.pi / 3 by ring,
    Real.cos_pi_sub, Real.cos_pi_div_three]

private theorem centerOmega_im : centerOmega.im = Real.sqrt 3 / 2 := by
  have h : (2 * (Real.pi : Complex) * Complex.I / 3)
      = ((2 * Real.pi / 3 : Real) : Complex) * Complex.I := by push_cast; ring
  unfold centerOmega
  rw [h, Complex.exp_ofReal_mul_I_im,
    show (2 * Real.pi / 3 : Real) = Real.pi - Real.pi / 3 by ring,
    Real.sin_pi_sub, Real.sin_pi_div_three]

private theorem centerChannel_re_im {alpha : Real} (halpha : 0 < alpha) :
    (centerChannel alpha).re = (1 + centerT alpha)⁻¹ * (1 - centerT alpha / 2) ∧
      (centerChannel alpha).im = (1 + centerT alpha)⁻¹ * (centerT alpha * (Real.sqrt 3 / 2)) := by
  have ht : 0 < centerT alpha := centerT_pos halpha
  have hc : centerChannel alpha
      = (((1 + centerT alpha)⁻¹ : Real) : Complex) *
        (1 + (centerT alpha : Complex) * centerOmega) := by
    unfold centerChannel
    push_cast
    field_simp
  constructor
  · rw [hc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, centerOmega_re, Complex.one_re]
    ring
  · rw [hc, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, centerOmega_im, Complex.one_im]
    ring

private theorem centerUnitChannel_re_pos {alpha : Real} (halpha : 1 < alpha) :
    0 < (centerUnitChannel alpha).re := by
  have halpha0 : 0 < alpha := lt_trans one_pos halpha
  have ht : 0 < centerT alpha := centerT_pos halpha0
  have ht1 : centerT alpha < 1 := by
    unfold centerT
    rw [inv_lt_one_iff₀]
    exact Or.inr halpha
  have hrho : 0 < centerRho alpha := centerRho_pos halpha0
  unfold centerUnitChannel
  rw [Complex.div_ofReal_re, (centerChannel_re_im halpha0).1]
  have h1 : 0 < (1 + centerT alpha)⁻¹ := by positivity
  have h2 : 0 < 1 - centerT alpha / 2 := by linarith
  positivity

private theorem centerUnitChannel_im_pos {alpha : Real} (halpha : 0 < alpha) :
    0 < (centerUnitChannel alpha).im := by
  have ht : 0 < centerT alpha := centerT_pos halpha
  have hrho : 0 < centerRho alpha := centerRho_pos halpha
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  unfold centerUnitChannel
  rw [Complex.div_ofReal_im, (centerChannel_re_im halpha).2]
  have h1 : 0 < (1 + centerT alpha)⁻¹ := by positivity
  positivity

private theorem centerUnitChannel_arg_mem {alpha : Real} (halpha : 1 < alpha) :
    0 < (centerUnitChannel alpha).arg ∧ (centerUnitChannel alpha).arg < Real.pi / 2 := by
  have halpha0 : 0 < alpha := lt_trans one_pos halpha
  have him : 0 < (centerUnitChannel alpha).im := centerUnitChannel_im_pos halpha0
  have hre : 0 < (centerUnitChannel alpha).re := centerUnitChannel_re_pos halpha
  refine ⟨?_, Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hre)⟩
  have hnn : 0 ≤ (centerUnitChannel alpha).arg := Complex.arg_nonneg_iff.mpr him.le
  rcases lt_or_eq_of_le hnn with h | h
  · exact h
  · exact absurd (Complex.arg_eq_zero_iff.mp h.symm).2 (ne_of_gt him)

private theorem re_ofReal_scale (r : Real) (X w : Complex) :
    ((r : Complex) * X * w).re = r * ((X * w).re) := by
  rw [mul_assoc, Complex.re_ofReal_mul]

-- Target 7: the main new geometry. L and c depend on alpha, not on z.
theorem exists_bounded_joint_center_phase_guard
    {alpha : Real} (halpha : 1 < alpha) :
    ∃ L : Nat, ∃ c : Real, 0 < c ∧
      ∀ z : Complex, norm z = 1 → ∃ j : Nat, j ≤ L ∧
        2 * alpha * Complex.re
          ((centerOmega ^ 2 - 1) * (z * centerUnitChannel alpha ^ j)) ≤ -c ∧
        c ≤ |2 * alpha * Complex.re
          (centerDerivativeChannelCoefficient alpha * (z * centerUnitChannel alpha ^ j))| := by
  have halpha0 : 0 < alpha := lt_trans one_pos halpha
  have h2a : ((2 * alpha : Real) : Complex) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  have homega : centerOmega ^ 2 - 1 ≠ 0 := by
    have h2 : centerOmega ^ 2 ≠ 1 :=
      centerOmega_isPrimitiveRoot.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
    exact sub_ne_zero.mpr h2
  obtain ⟨harg0, harg2⟩ := centerUnitChannel_arg_mem halpha
  obtain ⟨L, c, hc, hguard⟩ := exists_uniform_guard
    (C := ((2 * alpha : Real) : Complex) * (centerOmega ^ 2 - 1))
    (H := ((2 * alpha : Real) : Complex) * centerDerivativeChannelCoefficient alpha)
    (u := centerUnitChannel alpha)
    (mul_ne_zero h2a homega)
    (mul_ne_zero h2a (centerDerivativeChannelCoefficient_ne_zero halpha0))
    (norm_centerUnitChannel halpha0) harg0 harg2
  refine ⟨L, c, hc, ?_⟩
  intro z hz
  obtain ⟨j, hjL, h1, h2⟩ := hguard z hz
  rw [re_ofReal_scale] at h1 h2
  exact ⟨j, hjL, h1, h2⟩

-- Target 8: transfer to actual finite-row errors; a single L,c for the whole tail.
theorem eventually_bounded_jointCenterGuardScore
    {alpha : Real} (halpha : 1 < alpha) :
    ∃ L : Nat, ∃ c : Real, 0 < c ∧
      ∀ᶠ N : Nat in Filter.atTop, ∃ j : Nat, j ≤ L ∧
        c ≤ jointCenterGuardScore (N + j) alpha := by
  have halpha0 : 0 < alpha := lt_trans one_pos halpha
  obtain ⟨hrho0, hrho1⟩ := centerRho_mem_unitInterval halpha0
  obtain ⟨L, c0, hc0, hguard⟩ := exists_bounded_joint_center_phase_guard halpha
  refine ⟨L, c0 / 2, by positivity, ?_⟩
  have hE : ∀ᶠ M : Nat in Filter.atTop,
      |centerError M alpha / centerRho alpha ^ M -
        2 * alpha * Complex.re
          ((centerOmega ^ 2 - 1) * centerUnitChannel alpha ^ M)| < c0 / 2 :=
    ((tendsto_centerError_sub_phase_normalized halpha).abs).eventually_lt_const
      (by simpa using half_pos hc0)
  have hD : ∀ᶠ M : Nat in Filter.atTop,
      |centerDerivativeError M alpha / ((M : Real) * centerRho alpha ^ M) -
        2 * alpha * Complex.re (centerDerivativeChannelCoefficient alpha *
          centerUnitChannel alpha ^ M)| < c0 / 2 :=
    ((tendsto_centerDerivativeError_sub_phase_normalized halpha).abs).eventually_lt_const
      (by simpa using half_pos hc0)
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp (hE.and hD)
  filter_upwards [Filter.eventually_ge_atTop (max N1 1)] with N hN
  have hzn : norm (centerUnitChannel alpha ^ N) = 1 := by
    rw [norm_pow, norm_centerUnitChannel halpha0, one_pow]
  obtain ⟨j, hjL, hj1, hj2⟩ := hguard (centerUnitChannel alpha ^ N) hzn
  refine ⟨j, hjL, ?_⟩
  have hpowadd : centerUnitChannel alpha ^ N * centerUnitChannel alpha ^ j
      = centerUnitChannel alpha ^ (N + j) := (pow_add _ _ _).symm
  rw [hpowadd] at hj1 hj2
  have hNN1 : N1 ≤ N + j := le_trans (le_trans (le_max_left N1 1) hN) (Nat.le_add_right N j)
  have hN1' : 1 ≤ N + j := le_trans (le_trans (le_max_right N1 1) hN) (Nat.le_add_right N j)
  obtain ⟨hrE, hrD⟩ := hN1 (N + j) hNN1
  have hpow : (0 : Real) < centerRho alpha ^ (N + j) := pow_pos hrho0 (N + j)
  have hNpos : (0 : Real) < ((N + j : Nat) : Real) := by exact_mod_cast hN1'
  have hden : (0 : Real) < ((N + j : Nat) : Real) * centerRho alpha ^ (N + j) := by positivity
  rw [jointCenterGuardScore]
  refine le_min ?_ ?_
  · have habs := abs_lt.mp hrE
    rw [neg_div]
    linarith [habs.1, habs.2]
  · have hkey : c0 - c0 / 2 ≤
        |centerDerivativeError (N + j) alpha /
          (((N + j : Nat) : Real) * centerRho alpha ^ (N + j))| := by
      have hb := abs_sub_abs_le_abs_sub
        (2 * alpha * Complex.re (centerDerivativeChannelCoefficient alpha *
          centerUnitChannel alpha ^ (N + j)))
        (centerDerivativeError (N + j) alpha /
          (((N + j : Nat) : Real) * centerRho alpha ^ (N + j)))
      have h3 : |(2 : Real) * alpha * Complex.re (centerDerivativeChannelCoefficient alpha *
            centerUnitChannel alpha ^ (N + j)) -
          centerDerivativeError (N + j) alpha /
            (((N + j : Nat) : Real) * centerRho alpha ^ (N + j))| < c0 / 2 := by
        rw [abs_sub_comm]; exact hrD
      linarith [hj2, hb, h3]
    rw [abs_div, abs_of_pos hden] at hkey
    linarith

-- Target 9: both guards hold at the SAME chosen row, at its OWN spectral scale.
theorem eventually_jointCenterGuardRow_guards
    {alpha : Real} (halpha : 1 < alpha) :
    ∃ L : Nat, ∃ c : Real, 0 < c ∧
      ∀ᶠ N : Nat in Filter.atTop,
        centerError (jointCenterGuardRow N L alpha) alpha ≤
          -c * centerRho alpha ^ (jointCenterGuardRow N L alpha) ∧
        c * ((jointCenterGuardRow N L alpha : Nat) : Real) *
            centerRho alpha ^ (jointCenterGuardRow N L alpha) ≤
          |centerDerivativeError (jointCenterGuardRow N L alpha) alpha| := by
  have halpha0 : 0 < alpha := lt_trans one_pos halpha
  obtain ⟨hrho0, hrho1⟩ := centerRho_mem_unitInterval halpha0
  obtain ⟨L, c, hc, hev⟩ := eventually_bounded_jointCenterGuardScore halpha
  refine ⟨L, c, hc, ?_⟩
  filter_upwards [hev, Filter.eventually_ge_atTop 1] with N hN hN1
  obtain ⟨j, hjL, hscore⟩ := hN
  set J : Nat := jointCenterGuardRow N L alpha with hJ
  have hcJ : c ≤ jointCenterGuardScore J alpha :=
    le_trans hscore (jointCenterGuardRow_score_max N L alpha hjL)
  have hJ1 : 1 ≤ J := le_trans hN1 (jointCenterGuardRow_bounds N L alpha).1
  have hpow : (0 : Real) < centerRho alpha ^ J := pow_pos hrho0 J
  have hJpos : (0 : Real) < (J : Real) := by exact_mod_cast hJ1
  have hden : (0 : Real) < (J : Real) * centerRho alpha ^ J := by positivity
  rw [jointCenterGuardScore, le_min_iff] at hcJ
  obtain ⟨hc1, hc2⟩ := hcJ
  constructor
  · rw [le_div_iff₀ hpow] at hc1
    linarith
  · rw [le_div_iff₀ hden] at hc2
    linarith [hc2]

-- Target 10: the negative-error inner scale is nondegenerate on that schedule.
theorem eventually_jointCenterGuardRow_innerScale_lower
    {alpha : Real} (halpha : 1 < alpha) :
    ∃ L : Nat, ∃ c : Real, 0 < c ∧
      ∀ᶠ N : Nat in Filter.atTop,
        centerError (jointCenterGuardRow N L alpha) alpha < 0 ∧
        c * centerRho alpha ^ (jointCenterGuardRow N L alpha) ≤
          |centerError (jointCenterGuardRow N L alpha) alpha| ∧
        c * ((jointCenterGuardRow N L alpha : Nat) : Real) *
            centerRho alpha ^ (jointCenterGuardRow N L alpha) ≤
          |centerDerivativeError (jointCenterGuardRow N L alpha) alpha| ∧
        0 < centerInnerScale (jointCenterGuardRow N L alpha) alpha ∧
        (c / alpha) * centerRho alpha ^ (jointCenterGuardRow N L alpha) ≤
          centerInnerScale (jointCenterGuardRow N L alpha) alpha ^ 2 := by
  have halpha0 : 0 < alpha := lt_trans one_pos halpha
  obtain ⟨hrho0, hrho1⟩ := centerRho_mem_unitInterval halpha0
  obtain ⟨L, c, hc, hev⟩ := eventually_jointCenterGuardRow_guards halpha
  refine ⟨L, c, hc, ?_⟩
  filter_upwards [hev] with N hN
  obtain ⟨hE, hD⟩ := hN
  set J : Nat := jointCenterGuardRow N L alpha with hJ
  have hpow : (0 : Real) < centerRho alpha ^ J := pow_pos hrho0 J
  have hneg : centerError J alpha < 0 := by nlinarith
  have habs : c * centerRho alpha ^ J ≤ |centerError J alpha| := by
    rw [abs_of_neg hneg]
    linarith
  refine ⟨hneg, habs, hD, centerInnerScale_pos_of_centerError_neg J halpha0 hneg, ?_⟩
  rw [centerInnerScale_sq J halpha0, le_div_iff₀ halpha0]
  have : c / alpha * centerRho alpha ^ J * alpha = c * centerRho alpha ^ J := by
    field_simp
  rw [this]
  exact habs

end SilverFiniteRow
