/-
Silver finite-row quantitative remainder layer. Builds on
`SilverFiniteRowBridge`: rewrites the exact finite-row cubic bridge as the
center-error quadratic crossover equation, isolates the remainder into three
explicit pieces (packet-deviation variation, fixed-point-factor drift, cubic
displacement), bounds those pieces on a local radius/deviation/variation
budget, and connects the ± center-error cases to the normalized quadratics of
`SilverCrossover`. Silver constant of α³=7+7α (NOT metallic 1+√2).

This run certifies the exact normalized finite-row equation and a reusable
conditional remainder bound only — NO fixed-point existence, NO rate relative
to √|centerError|, NO root location (later analytic step).

Proof routes (keep every statement verbatim; minor lemma-name changes ok):
- T1 quadraticCrossover_eq_centerRemainder_of_fixed: specialize
  cubic_displacement_eq_packetDeviation_factor_of_fixed at mu = 1+muShift;
  unfold quadraticCrossover/centerRemainder/fixedPointFactor; halpha.ne' to
  clear 3*alpha; ring/linear_combination; sign 1-(1+muShift) = -muShift.
- T2 centerRemainder_decomposition: unfold centerRemainder/deviationVariation;
  identity D*Q - 3α²E = (D-E)*Q + E*(Q-3α²); ring (holds even at α=0, common
  denom uncancelled).
- T3 fixedPointFactor_eq_of_fixed: unfold fixedPointFactor/packetDeviation;
  fixed point ⇒ D = (α+δ)-u so u = (α+δ)-D; substitute + ring.
- T4 fixedPointFactor_sub_bound: after T3, Q-3α² = 6αδ+3δ² -3(α+δ)D +D²;
  triangle ineq, abs_mul, hdelta, hdeviation, |α+δ|≤α+r; nonnegativity of
  α,r,d for each monotone step; envelope exact, do not enlarge.
- T5 fixedPointFactor_abs_bound: T4 + |Q| ≤ |Q-3α²| + 3α².
- T6 centerRemainder_abs_bound: rewrite T2, abs_div, |3α|=3α, apply T4-T5 and
  |δ|≤r,|D|≤d,|dev.var|≤v; |δ³|≤r³; envelope exact.
- T7 normalized_positive_crossover_equation: T1 with muShift=λ·scale/α,
  delta=scale·y, E=centerError; combine quadraticCrossover_rescale_pos.
- T8 normalized_negative_crossover_equation: same via
  quadraticCrossover_rescale_neg; keep α*(-centerError) and y²-λy+1.
- T9 tendstoUniformlyOn_packetDeviation: tendstoUniformlyOn_finiteMap minus the
  stationary limitingMap (or Metric.tendstoUniformlyOn_iff); K may be empty.
- T10 tendstoUniformlyOn_deviationVariation: pull T9 back along δ↦α+δ on the
  compact image, subtract scalar centerError (→0 by tendsto_centerError); or
  direct Metric.tendstoUniformlyOn_iff. No √|centerError| rate.
Certification: T2 no α≠0; T3-5 use fixed-point equality + algebra only (no
positive input); r,d,v explicitly ≥0; ± targets stay separate; if a target
cannot close, omit it and report its exact name.
-/
import RequestProject.SilverFiniteRowBridge

open scoped Real Topology

namespace SilverFiniteRow

noncomputable def fixedPointFactor (alpha mu delta : Real) : Real :=
  let z := alpha + delta
  z^2 + z*limitingMap alpha mu z + limitingMap alpha mu z^2

noncomputable def deviationVariation
    (N : Nat) (alpha mu delta : Real) : Real :=
  packetDeviation N alpha mu (alpha + delta) - centerError N alpha

noncomputable def centerRemainder
    (N : Nat) (alpha muShift delta : Real) : Real :=
  let mu := 1 + muShift
  (packetDeviation N alpha mu (alpha + delta) *
        fixedPointFactor alpha mu delta -
      delta^3 - 3*alpha^2*centerError N alpha) /
    (3*alpha)

noncomputable def factorEnvelope (alpha r d : Real) : Real :=
  6*alpha*r + 3*r^2 + 3*(alpha + r)*d + d^2

theorem quadraticCrossover_eq_centerRemainder_of_fixed
    {N : Nat} {alpha muShift delta : Real}
    (halpha : 0 < alpha)
    (hinput : 0 < affineInput alpha (1 + muShift) (alpha + delta))
    (hfixed :
      finiteMap N alpha (1 + muShift) (alpha + delta) = alpha + delta) :
    SilverCrossover.quadraticCrossover alpha (centerError N alpha)
        muShift delta =
      centerRemainder N alpha muShift delta := by
  have h := cubic_displacement_eq_packetDeviation_factor_of_fixed hinput hfixed
  have h3 : (3 : Real) * alpha ≠ 0 := by positivity
  simp only [SilverCrossover.quadraticCrossover, centerRemainder, fixedPointFactor]
  rw [eq_div_iff h3]
  linear_combination h

theorem centerRemainder_decomposition
    (N : Nat) (alpha muShift delta : Real) :
    centerRemainder N alpha muShift delta =
      (deviationVariation N alpha (1 + muShift) delta *
            fixedPointFactor alpha (1 + muShift) delta +
          centerError N alpha *
            (fixedPointFactor alpha (1 + muShift) delta - 3*alpha^2) -
          delta^3) /
        (3*alpha) := by
  simp only [centerRemainder, deviationVariation, fixedPointFactor]
  ring

theorem fixedPointFactor_eq_of_fixed
    {N : Nat} {alpha mu delta : Real}
    (hfixed : finiteMap N alpha mu (alpha + delta) = alpha + delta) :
    fixedPointFactor alpha mu delta =
      3*(alpha + delta)^2 -
        3*(alpha + delta)*
          packetDeviation N alpha mu (alpha + delta) +
        packetDeviation N alpha mu (alpha + delta)^2 := by
  have hdev : packetDeviation N alpha mu (alpha + delta) =
      (alpha + delta) - limitingMap alpha mu (alpha + delta) := by
    rw [packetDeviation, hfixed]
  simp only [fixedPointFactor]
  rw [hdev]
  ring

set_option linter.unusedVariables false in
theorem fixedPointFactor_sub_bound
    {N : Nat} {alpha mu delta r d : Real}
    (halpha : 0 <= alpha) (hr : 0 <= r) (hd : 0 <= d)
    (hdelta : |delta| <= r)
    (hdeviation : |packetDeviation N alpha mu (alpha + delta)| <= d)
    (hfixed : finiteMap N alpha mu (alpha + delta) = alpha + delta) :
    |fixedPointFactor alpha mu delta - 3*alpha^2| <=
      factorEnvelope alpha r d := by
  set D : Real := packetDeviation N alpha mu (alpha + delta) with hD
  have key : fixedPointFactor alpha mu delta - 3*alpha^2 =
      6*alpha*delta + 3*delta^2 - 3*((alpha + delta)*D) + D^2 := by
    rw [fixedPointFactor_eq_of_fixed hfixed, ← hD]; ring
  have hz : |alpha + delta| ≤ alpha + r := by
    calc |alpha + delta| ≤ |alpha| + |delta| := abs_add_le _ _
      _ ≤ alpha + r := by rw [abs_of_nonneg halpha]; linarith
  have e1 : |6*alpha*delta| ≤ 6*alpha*r := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:Real) ≤ 6*alpha)]
    exact mul_le_mul_of_nonneg_left hdelta (by positivity)
  have e2 : |3*delta^2| ≤ 3*r^2 := by
    rw [abs_of_nonneg (by positivity : (0:Real) ≤ 3*delta^2)]
    have : delta^2 ≤ r^2 := by
      rw [← sq_abs delta]; exact pow_le_pow_left₀ (abs_nonneg _) hdelta 2
    linarith
  have e3 : |3*((alpha + delta)*D)| ≤ 3*((alpha + r)*d) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:Real) ≤ (3:Real)), abs_mul]
    have hb : |alpha + delta| * |D| ≤ (alpha + r) * d :=
      mul_le_mul hz hdeviation (abs_nonneg _) (by linarith)
    linarith
  have e4 : |D^2| ≤ d^2 := by
    rw [abs_of_nonneg (by positivity : (0:Real) ≤ D^2), ← sq_abs D]
    exact pow_le_pow_left₀ (abs_nonneg _) hdeviation 2
  obtain ⟨a1, b1⟩ := abs_le.mp e1
  obtain ⟨a2, b2⟩ := abs_le.mp e2
  obtain ⟨a3, b3⟩ := abs_le.mp e3
  obtain ⟨a4, b4⟩ := abs_le.mp e4
  rw [key, factorEnvelope, abs_le]
  constructor <;> linarith

theorem fixedPointFactor_abs_bound
    {N : Nat} {alpha mu delta r d : Real}
    (halpha : 0 <= alpha) (hr : 0 <= r) (hd : 0 <= d)
    (hdelta : |delta| <= r)
    (hdeviation : |packetDeviation N alpha mu (alpha + delta)| <= d)
    (hfixed : finiteMap N alpha mu (alpha + delta) = alpha + delta) :
    |fixedPointFactor alpha mu delta| <=
      3*alpha^2 + factorEnvelope alpha r d := by
  have h := fixedPointFactor_sub_bound halpha hr hd hdelta hdeviation hfixed
  have h2 : |fixedPointFactor alpha mu delta| ≤
      |fixedPointFactor alpha mu delta - 3*alpha^2| + |3*alpha^2| := by
    have := abs_add_le (fixedPointFactor alpha mu delta - 3*alpha^2) (3*alpha^2)
    simpa using this
  rw [abs_of_nonneg (by positivity : (0:Real) ≤ 3*alpha^2)] at h2
  linarith

theorem centerRemainder_abs_bound
    {N : Nat} {alpha muShift delta r d v : Real}
    (halpha : 0 < alpha) (hr : 0 <= r) (hd : 0 <= d) (hv : 0 <= v)
    (hdelta : |delta| <= r)
    (hdeviation :
      |packetDeviation N alpha (1 + muShift) (alpha + delta)| <= d)
    (hvariation :
      |deviationVariation N alpha (1 + muShift) delta| <= v)
    (hfixed :
      finiteMap N alpha (1 + muShift) (alpha + delta) = alpha + delta) :
    |centerRemainder N alpha muShift delta| <=
      (v*(3*alpha^2 + factorEnvelope alpha r d) +
          |centerError N alpha| * factorEnvelope alpha r d + r^3) /
        (3*alpha) := by
  have h3 : (0 : Real) < 3*alpha := by linarith
  have hQ := fixedPointFactor_abs_bound (N := N) (mu := 1 + muShift) halpha.le hr hd
    hdelta hdeviation hfixed
  have hQ2 := fixedPointFactor_sub_bound (N := N) (mu := 1 + muShift) halpha.le hr hd
    hdelta hdeviation hfixed
  have hFE : 0 ≤ factorEnvelope alpha r d := by
    have := abs_nonneg (fixedPointFactor alpha (1 + muShift) delta - 3*alpha^2)
    linarith
  set V : Real := deviationVariation N alpha (1 + muShift) delta with hV
  set Q : Real := fixedPointFactor alpha (1 + muShift) delta with hQdef
  set E : Real := centerError N alpha with hE
  have b1 : |V * Q| ≤ v * (3*alpha^2 + factorEnvelope alpha r d) := by
    rw [abs_mul]
    exact mul_le_mul hvariation hQ (abs_nonneg _) hv
  have b2 : |E * (Q - 3*alpha^2)| ≤ |E| * factorEnvelope alpha r d := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hQ2 (abs_nonneg _)
  have b3 : |delta^3| ≤ r^3 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hdelta 3
  have hnum : |V * Q + E * (Q - 3*alpha^2) - delta^3| ≤
      v*(3*alpha^2 + factorEnvelope alpha r d) +
        |E| * factorEnvelope alpha r d + r^3 := by
    have t1 := abs_add_le (V * Q) (E * (Q - 3*alpha^2))
    calc |V * Q + E * (Q - 3*alpha^2) - delta^3|
        ≤ |V * Q + E * (Q - 3*alpha^2)| + |delta^3| := abs_sub _ _
      _ ≤ (|V * Q| + |E * (Q - 3*alpha^2)|) + |delta^3| := by linarith
      _ ≤ _ := by linarith
  rw [centerRemainder_decomposition, ← hV, ← hQdef, ← hE, abs_div,
    abs_of_pos h3]
  exact (div_le_div_iff_of_pos_right h3).mpr hnum

theorem normalized_positive_crossover_equation
    {N : Nat} {alpha lambda y : Real}
    (halpha : 0 < alpha) (herror : 0 < centerError N alpha)
    (hinput :
      0 < affineInput alpha
        (1 + lambda * SilverCrossover.crossoverScale alpha (centerError N alpha) / alpha)
        (alpha + SilverCrossover.crossoverScale alpha (centerError N alpha) * y))
    (hfixed :
      finiteMap N alpha
          (1 + lambda * SilverCrossover.crossoverScale alpha (centerError N alpha) / alpha)
          (alpha + SilverCrossover.crossoverScale alpha (centerError N alpha) * y) =
        alpha + SilverCrossover.crossoverScale alpha (centerError N alpha) * y) :
    alpha*centerError N alpha*(y^2 - lambda*y - 1) =
      centerRemainder N alpha
        (lambda * SilverCrossover.crossoverScale alpha (centerError N alpha) / alpha)
        (SilverCrossover.crossoverScale alpha (centerError N alpha) * y) := by
  have h1 := quadraticCrossover_eq_centerRemainder_of_fixed (N := N) halpha hinput hfixed
  have h2 := SilverCrossover.quadraticCrossover_rescale_pos
    (alpha := alpha) (packetError := centerError N alpha) (lambda := lambda) (y := y)
    halpha herror
  rw [← h1, h2]

theorem normalized_negative_crossover_equation
    {N : Nat} {alpha lambda y : Real}
    (halpha : 0 < alpha) (herror : centerError N alpha < 0)
    (hinput :
      0 < affineInput alpha
        (1 + lambda * SilverCrossover.crossoverScale alpha (centerError N alpha) / alpha)
        (alpha + SilverCrossover.crossoverScale alpha (centerError N alpha) * y))
    (hfixed :
      finiteMap N alpha
          (1 + lambda * SilverCrossover.crossoverScale alpha (centerError N alpha) / alpha)
          (alpha + SilverCrossover.crossoverScale alpha (centerError N alpha) * y) =
        alpha + SilverCrossover.crossoverScale alpha (centerError N alpha) * y) :
    alpha*(-centerError N alpha)*(y^2 - lambda*y + 1) =
      centerRemainder N alpha
        (lambda * SilverCrossover.crossoverScale alpha (centerError N alpha) / alpha)
        (SilverCrossover.crossoverScale alpha (centerError N alpha) * y) := by
  have h1 := quadraticCrossover_eq_centerRemainder_of_fixed (N := N) halpha hinput hfixed
  have h2 := SilverCrossover.quadraticCrossover_rescale_neg
    (alpha := alpha) (packetError := centerError N alpha) (lambda := lambda) (y := y)
    halpha herror
  rw [← h1, h2]

theorem tendstoUniformlyOn_packetDeviation
    (alpha mu : Real) {K : Set Real}
    (hK : IsCompact K)
    (hinput : ∀ z ∈ K, 0 < affineInput alpha mu z) :
    TendstoUniformlyOn
      (fun N z => packetDeviation N alpha mu z)
      (fun _ => 0)
      Filter.atTop K := by
  have h := tendstoUniformlyOn_finiteMap alpha mu hK hinput
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro e he
  filter_upwards [h e he] with N hN z hz
  have hz2 := hN z hz
  simpa [packetDeviation, Real.dist_eq, abs_sub_comm] using hz2

theorem tendstoUniformlyOn_deviationVariation
    {alpha : Real} (halpha : 0 < alpha) (mu : Real) {K : Set Real}
    (hK : IsCompact K)
    (hinput : ∀ delta ∈ K, 0 < affineInput alpha mu (alpha + delta)) :
    TendstoUniformlyOn
      (fun N delta => deviationVariation N alpha mu delta)
      (fun _ => 0)
      Filter.atTop K := by
  have hKc : IsCompact ((fun d : Real => alpha + d) '' K) := hK.image (by fun_prop)
  have hpos : ∀ z ∈ (fun d : Real => alpha + d) '' K, 0 < affineInput alpha mu z := by
    rintro z ⟨d, hd, rfl⟩
    exact hinput d hd
  have h := tendstoUniformlyOn_packetDeviation alpha mu hKc hpos
  have hc := tendsto_centerError halpha
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro e he
  have he2 : 0 < e/2 := by linarith
  have h2 := Metric.tendsto_nhds.mp hc (e/2) he2
  filter_upwards [h (e/2) he2, h2] with N hN1 hN2 d hd
  have hA := hN1 (alpha + d) (Set.mem_image_of_mem _ hd)
  rw [Real.dist_eq] at hA hN2 ⊢
  have hA' : |packetDeviation N alpha mu (alpha + d)| < e/2 := by
    simpa using hA
  have hB' : |centerError N alpha| < e/2 := by simpa using hN2
  have hsum : |packetDeviation N alpha mu (alpha + d) - centerError N alpha| ≤
      |packetDeviation N alpha mu (alpha + d)| + |centerError N alpha| :=
    abs_sub _ _
  simp only [deviationVariation, zero_sub, abs_neg]
  linarith

end SilverFiniteRow
