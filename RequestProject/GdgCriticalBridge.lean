/-
gd_g completion roadmap, Phase 3B — the CRITICAL BRIDGE: from per-lobe
angle-stationary witnesses (Phase 3A) to located, nonsingular roots of the
actual criticalTetranomial free factor.

Phase 3A proved a genuine HasDerivAt (gdgSignedInterior g) 0 φ witness inside
every retained lobe. This module identifies that signed real function with the
already-declared pulled complex cover A²/Qᵍ on the unit circle u = exp(iφ), and
transports each stationary witness into a root of the existing
criticalTetranomial derivative factor — with the numerator and quadratic channel
factors explicitly proved nonzero. Existence only: NO uniqueness, degree
exhaustion, critical-value separation, monodromy, or Galois conclusion.

Coordinate: u = exp(iφ) (NOT −exp(iφ)); the + sign in coverQuadratic forces this —
the pole φ = π−θ_g maps to u+u⁻¹ = −2cos θ_g, a root of 1 + 2cos θ_g·u + u².

Proof routes (statements/defs verbatim; standard axioms only; no numeric π):

* T1 gdgUnitCircle_ne_zero: Complex.exp_ne_zero.
* T2 add_inv_eq_blockCoord: e^{iφ}+e^{−iφ}=2cos φ (Euler); exact + sign, real cast.
* T3 coverQuadratic_gdgUnitCircle: coverQuadratic (2cos θ_g) u = u·(denom); via
  gdgCosCoeff g = 2 cos θ_g, T2, u≠0. Both vanish at φ=π−θ_g.
* T4 coverNumerator_sq_gdgUnitCircle: (1−ε u^g)² = u^g(2cos(gφ)−2ε), ε=(−1)^g; via
  u^g=e^{igφ}, Euler, parity-compatible ℝ/ℂ casts of (−1)^g. Keep the square + u^g.
* T5 gdgPulledCover_..._eq_signed: combine T3,T4, cancel the nonzero u-power ⇒
  gdgPulledCover g (u φ) = (gdgSignedInterior g φ : ℂ). Totalized equality (valid
  even at denom 0), but derivative/critical uses below require denom ≠ 0 — do NOT
  infer regularity at the pole from this.
* T6 gdgPulledCover_hasDerivAt: differentiate A²/Qᵍ; reuse
  coverDerivativeNumerator_eq_criticalTetranomial (bracket = −g·criticalTetranomial)
  ⇒ deriv = −g·A·G/Q^{g+1}. Preserve every factor/exponent (not merely G, not a
  proportionality).
* T7 gdgBlockCoord_hasDerivAt = −2 sin φ; _deriv_ne_zero_on_prePole: 0<φ<π ⇒
  sin φ>0 on the retained interior — the angle→block map is a valid local coord.
* T8 criticalTetranomial_..._of_stationary: (1) T3+u≠0+hden ⇒ Q≠0; (2) T5+hval ⇒
  pulled value ≠0 ⇒ A≠0; (3) HasDerivAt.ofReal_comp on hstat; (4) real/complex
  chain rule through u φ (unit-circle deriv I·u φ ≠ 0); (5) rewrite via T5,
  uniqueness of derivative ⇒ pulled-cover deriv = 0; (6) T6 + cancel
  g, A, Qᵍ⁺¹, I, u φ ⇒ criticalTetranomial = 0. hval rules out endpoint
  stationary points (needed for the A≠0 cancellation). Conclusion also certifies
  A≠0 ∧ Q≠0.
* T9/T10 exists_even/odd_..._unitCircle_root: take φ,hstat from the Phase 3A
  even/odd Rolle theorem; hval from the strict interior sign; hden from retained
  denominator positivity (before-pole); apply T8; then 0<φ<π−θ_g<π and cos
  antitone ⇒ −2cos θ_g < 2cos φ < 2, i.e. gdgBlockCoord φ ∈ Ioo (−gdgCosCoeff g) 2.
  g=5: retained-odd hypothesis uninhabited ⇒ T10 vacuous; do not invent a lobe.

Guardrails: u=exp(iφ) not its negative; keep the numerator square, u^g factor,
derivative scale, Q^{g+1}; never cancel A or Q without a proved nonzero fact; the
totalized identity does not regularize the pole; block-coord derivative nonzero
only after 0<φ<π; existence only (no uniqueness/exhaustion/separation/monodromy);
no false globally-decreasing-log-derivative route.

Certification: no sorry/admit/new axiom/unsafe/implemented_by; no weakening;
keep unclosable targets out + report; run module, Main, audit --wfail
(v4.33.0-rc2); report #print axioms per public theorem. This completes the Phase
3B bridge from per-lobe angle-stationary witnesses to located, nonsingular roots
of the actual critical tetranomial — but NOT uniqueness, degree exhaustion, full
critical-value separation, or monodromy.
-/
import Mathlib
import RequestProject.GdgSignedLobes

namespace GdgSquarefree

/-- The unit-circle point u = exp(iφ). -/
noncomputable def gdgUnitCircle (phi : ℝ) : ℂ :=
  Complex.exp ((phi : ℂ) * Complex.I)

/-- The real block coordinate b = 2 cos φ. -/
noncomputable def gdgBlockCoord (phi : ℝ) : ℝ :=
  2 * Real.cos phi

/-- The pulled complex cover A²/Qᵍ in the reciprocal coordinate u. -/
noncomputable def gdgPulledCover (g : ℕ) (u : ℂ) : ℂ :=
  coverNumerator g ((-1 : ℂ) ^ g) u ^ 2 /
    coverQuadratic (gdgCosCoeff g : ℂ) u ^ g

/-- **Target 1.** The unit-circle point is nonzero. -/
theorem gdgUnitCircle_ne_zero (phi : ℝ) :
    gdgUnitCircle phi ≠ 0 :=
  Complex.exp_ne_zero _

/-- **Target 2.** Reciprocal sum is the real block coordinate (Euler). -/
theorem gdgUnitCircle_add_inv_eq_blockCoord (phi : ℝ) :
    gdgUnitCircle phi + (gdgUnitCircle phi)⁻¹ =
      (gdgBlockCoord phi : ℂ) := by
  simp only [gdgUnitCircle, gdgBlockCoord]
  rw [← Complex.exp_neg]
  push_cast
  rw [Complex.cos]
  ring_nf

/-- **Target 3.** The quadratic denominator on the unit circle. -/
theorem coverQuadratic_gdgUnitCircle {g : ℕ} (phi : ℝ) :
    coverQuadratic (gdgCosCoeff g : ℂ) (gdgUnitCircle phi) =
      gdgUnitCircle phi *
        (gdgInteriorDenominator g phi : ℂ) := by
  have hu : gdgUnitCircle phi ≠ 0 := gdgUnitCircle_ne_zero phi
  have h2 := gdgUnitCircle_add_inv_eq_blockCoord phi
  have hD : ((gdgInteriorDenominator g phi : ℝ) : ℂ) =
      ((gdgBlockCoord phi : ℝ) : ℂ) + ((gdgCosCoeff g : ℝ) : ℂ) := by
    simp only [gdgInteriorDenominator, gdgBlockCoord, gdgCosCoeff, gdgTheta]
    push_cast
    ring
  rw [hD, ← h2, coverQuadratic]
  field_simp
  ring

/-- **Target 4.** The squared cover numerator on the unit circle. -/
theorem coverNumerator_sq_gdgUnitCircle {g : ℕ} (phi : ℝ) :
    coverNumerator g ((-1 : ℂ) ^ g) (gdgUnitCircle phi) ^ 2 =
      (gdgUnitCircle phi) ^ g *
        ((2 * Real.cos ((g : ℝ) * phi) -
            2 * ((-1 : ℝ) ^ g) : ℝ) : ℂ) := by
  have hpow : (gdgUnitCircle phi) ^ g = gdgUnitCircle ((g : ℝ) * phi) := by
    simp only [gdgUnitCircle]
    rw [← Complex.exp_nat_mul]
    push_cast
    ring_nf
  have hv : gdgUnitCircle ((g : ℝ) * phi) ≠ 0 :=
    gdgUnitCircle_ne_zero _
  have hsum := gdgUnitCircle_add_inv_eq_blockCoord ((g : ℝ) * phi)
  have heps : (((-1 : ℝ) ^ g : ℝ) : ℂ) = (-1 : ℂ) ^ g := by
    push_cast
    ring
  have heps2 : ((-1 : ℂ) ^ g) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have hcast : ((2 * Real.cos ((g : ℝ) * phi) - 2 * ((-1 : ℝ) ^ g) : ℝ) : ℂ) =
      (gdgUnitCircle ((g : ℝ) * phi) + (gdgUnitCircle ((g : ℝ) * phi))⁻¹) -
        2 * (-1 : ℂ) ^ g := by
    rw [hsum, ← heps]
    simp only [gdgBlockCoord]
    push_cast
    ring
  rw [coverNumerator, hpow, hcast]
  field_simp
  linear_combination (gdgUnitCircle ((g : ℝ) * phi)) ^ 2 * heps2

/-- **Target 5.** The pulled cover on the unit circle is the signed pullback. -/
theorem gdgPulledCover_gdgUnitCircle_eq_signed {g : ℕ} (phi : ℝ) :
    gdgPulledCover g (gdgUnitCircle phi) =
      (gdgSignedInterior g phi : ℂ) := by
  have hu : gdgUnitCircle phi ≠ 0 := gdgUnitCircle_ne_zero phi
  rw [gdgPulledCover, coverNumerator_sq_gdgUnitCircle,
    coverQuadratic_gdgUnitCircle, mul_pow,
    mul_div_mul_left _ _ (pow_ne_zero g hu), gdgSignedInterior]
  push_cast
  ring

/-- **Target 6.** Derivative of the pulled complex cover (exact free factor). -/
theorem gdgPulledCover_hasDerivAt {g : ℕ} (hg : 1 ≤ g) {u : ℂ}
    (hQ : coverQuadratic (gdgCosCoeff g : ℂ) u ≠ 0) :
    HasDerivAt (gdgPulledCover g)
      (-(g : ℂ) * coverNumerator g ((-1 : ℂ) ^ g) u *
          criticalTetranomial g (gdgCosCoeff g : ℂ)
            ((-1 : ℂ) ^ g) u /
        coverQuadratic (gdgCosCoeff g : ℂ) u ^ (g + 1)) u := by
  obtain ⟨k, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
  have hpowd : HasDerivAt
      (fun z : ℂ => (-1 : ℂ) ^ (k + 1) * z ^ (k + 1))
      ((-1 : ℂ) ^ (k + 1) * (((k + 1 : ℕ) : ℂ) * u ^ k)) u := by
    simpa using (hasDerivAt_pow (k + 1) u).const_mul ((-1 : ℂ) ^ (k + 1))
  have hA : HasDerivAt (fun z : ℂ => coverNumerator (k + 1) ((-1 : ℂ) ^ (k + 1)) z)
      (-((-1 : ℂ) ^ (k + 1) * (((k + 1 : ℕ) : ℂ) * u ^ k))) u :=
    hpowd.const_sub 1
  have hlin : HasDerivAt (fun z : ℂ => 1 + ((gdgCosCoeff (k + 1) : ℝ) : ℂ) * z)
      ((gdgCosCoeff (k + 1) : ℝ) : ℂ) u := by
    simpa using
      (((hasDerivAt_id u).const_mul (((gdgCosCoeff (k + 1) : ℝ) : ℂ))).const_add (1 : ℂ))
  have hsqd : HasDerivAt (fun z : ℂ => z ^ 2) (2 * u) u := by
    simpa using hasDerivAt_pow 2 u
  have hQd : HasDerivAt (fun z : ℂ => coverQuadratic (gdgCosCoeff (k + 1) : ℂ) z)
      ((gdgCosCoeff (k + 1) : ℂ) + 2 * u) u := hlin.add hsqd
  have hdiv := (hA.pow 2).div (hQd.pow (k + 1)) (pow_ne_zero _ hQ)
  have hfun : gdgPulledCover (k + 1) =
      (fun z : ℂ => coverNumerator (k + 1) ((-1 : ℂ) ^ (k + 1)) z) ^ 2 /
        (fun z : ℂ => coverQuadratic (gdgCosCoeff (k + 1) : ℂ) z) ^ (k + 1) := by
    funext z
    simp [gdgPulledCover]
  rw [hfun]
  refine hdiv.congr_deriv ?_
  have hkey := coverDerivativeNumerator_eq_criticalTetranomial
    (g := k + 1) (by omega) ((gdgCosCoeff (k + 1) : ℝ) : ℂ) ((-1 : ℂ) ^ (k + 1)) u
  simp only [Pi.pow_apply, Nat.add_sub_cancel] at hkey ⊢
  rw [div_eq_div_iff (pow_ne_zero _ (pow_ne_zero _ hQ)) (pow_ne_zero _ hQ)]
  linear_combination
    (coverNumerator (k + 1) ((-1 : ℂ) ^ (k + 1)) u *
      coverQuadratic (gdgCosCoeff (k + 1) : ℂ) u ^ (k + 1 + 1) *
      coverQuadratic (gdgCosCoeff (k + 1) : ℂ) u ^ k) * hkey

/-- **Target 7a.** Derivative of the block coordinate. -/
theorem gdgBlockCoord_hasDerivAt (phi : ℝ) :
    HasDerivAt gdgBlockCoord (-2 * Real.sin phi) phi := by
  have h := (Real.hasDerivAt_cos phi).const_mul (2 : ℝ)
  have hfun : gdgBlockCoord = fun x : ℝ => 2 * Real.cos x := rfl
  rw [hfun]
  exact h.congr_deriv (by ring)

/-- **Target 7b.** The block-coordinate derivative is nonzero on the retained
interior. -/
theorem gdgBlockCoord_deriv_ne_zero_on_prePole {g : ℕ}
    (hg : 5 ≤ g) {phi : ℝ}
    (hphi : phi ∈ Set.Ioo 0 (Real.pi - gdgTheta g)) :
    -2 * Real.sin phi ≠ 0 := by
  have hth : 0 < gdgTheta g := gdgTheta_pos (by omega)
  have hlt : phi < Real.pi := lt_of_lt_of_le hphi.2 (by linarith)
  have hsin : 0 < Real.sin phi :=
    Real.sin_pos_of_pos_of_lt_pi hphi.1 hlt
  intro h
  nlinarith

/-- **Target 8.** A stationary signed point gives an actual free-factor root
with both channel factors nonzero. -/
theorem criticalTetranomial_gdgUnitCircle_eq_zero_of_stationary
    {g : ℕ} (hg : 5 ≤ g) {phi : ℝ}
    (hden : gdgInteriorDenominator g phi ≠ 0)
    (hval : gdgSignedInterior g phi ≠ 0)
    (hstat : HasDerivAt (gdgSignedInterior g) 0 phi) :
    criticalTetranomial g (gdgCosCoeff g : ℂ) ((-1 : ℂ) ^ g)
        (gdgUnitCircle phi) = 0 ∧
      coverNumerator g ((-1 : ℂ) ^ g) (gdgUnitCircle phi) ≠ 0 ∧
      coverQuadratic (gdgCosCoeff g : ℂ) (gdgUnitCircle phi) ≠ 0 := by
  have hu : gdgUnitCircle phi ≠ 0 := gdgUnitCircle_ne_zero phi
  have hDne : ((gdgInteriorDenominator g phi : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hden
  have hQ : coverQuadratic (gdgCosCoeff g : ℂ) (gdgUnitCircle phi) ≠ 0 := by
    rw [coverQuadratic_gdgUnitCircle]
    exact mul_ne_zero hu hDne
  have hQpow : coverQuadratic (gdgCosCoeff g : ℂ) (gdgUnitCircle phi) ^ (g + 1) ≠ 0 :=
    pow_ne_zero _ hQ
  have hvalC : gdgPulledCover g (gdgUnitCircle phi) ≠ 0 := by
    rw [gdgPulledCover_gdgUnitCircle_eq_signed]
    exact Complex.ofReal_ne_zero.mpr hval
  have hA : coverNumerator g ((-1 : ℂ) ^ g) (gdgUnitCircle phi) ≠ 0 := by
    intro h
    apply hvalC
    rw [gdgPulledCover, h]
    simp
  have hcirc : HasDerivAt gdgUnitCircle (Complex.I * gdgUnitCircle phi) phi := by
    have h1 : HasDerivAt (fun t : ℝ => ((t : ℂ) * Complex.I)) Complex.I phi := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := phi)).mul_const Complex.I
    have h2 := h1.cexp
    have hfun : gdgUnitCircle = fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I) := rfl
    rw [hfun]
    refine h2.congr_deriv ?_
    simp [mul_comm]
  have hpull := gdgPulledCover_hasDerivAt (g := g) (by omega) hQ
  have hcomp := hpull.scomp phi hcirc
  have heqf : (gdgPulledCover g ∘ gdgUnitCircle) =
      fun t : ℝ => ((gdgSignedInterior g t : ℝ) : ℂ) := by
    funext t
    exact gdgPulledCover_gdgUnitCircle_eq_signed t
  rw [heqf] at hcomp
  have hreal : HasDerivAt (fun t : ℝ => ((gdgSignedInterior g t : ℝ) : ℂ)) 0 phi := by
    simpa using hstat.ofReal_comp
  have huniq := hcomp.unique hreal
  rw [smul_eq_mul] at huniq
  have hIu : Complex.I * gdgUnitCircle phi ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero hu
  have hzero :
      -(g : ℂ) * coverNumerator g ((-1 : ℂ) ^ g) (gdgUnitCircle phi) *
          criticalTetranomial g (gdgCosCoeff g : ℂ) ((-1 : ℂ) ^ g)
            (gdgUnitCircle phi) /
        coverQuadratic (gdgCosCoeff g : ℂ) (gdgUnitCircle phi) ^ (g + 1) = 0 :=
    (mul_eq_zero.mp huniq).resolve_left hIu
  rw [div_eq_zero_iff] at hzero
  have hnum := hzero.resolve_right hQpow
  have hgne : (-(g : ℂ)) ≠ 0 := by
    have : (g : ℂ) ≠ 0 := by
      have : (0 : ℕ) < g := by omega
      exact_mod_cast Nat.cast_ne_zero.mpr (by omega : g ≠ 0)
    simpa using this
  have hG :
      criticalTetranomial g (gdgCosCoeff g : ℂ) ((-1 : ℂ) ^ g)
        (gdgUnitCircle phi) = 0 := by
    rcases mul_eq_zero.mp hnum with h | h
    · exact absurd ((mul_eq_zero.mp h).resolve_left hgne) hA
    · exact h
  exact ⟨hG, hA, hQ⟩

/-- Left endpoints of natural lobes with a nonnegative offset are nonnegative. -/
private theorem gdgBridge_lobeLeft_nonneg {g j : ℕ} (hg : 1 ≤ g)
    {offset : ℝ} (hoff : 0 ≤ offset) :
    0 ≤ gdgLobeLeft g j offset := by
  have hth : 0 < gdgTheta g := gdgTheta_pos hg
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  simp only [gdgLobeLeft]
  nlinarith

/-- On the retained interior the block coordinate lies strictly between
`-gdgCosCoeff g` and `2`, by strict antitonicity of cosine on `[0, π]`. -/
private theorem gdgBlockCoord_mem_Ioo_of_prePole {g : ℕ} (hg : 5 ≤ g) {phi : ℝ}
    (h0 : 0 < phi) (hlt : phi < Real.pi - gdgTheta g) :
    gdgBlockCoord phi ∈ Set.Ioo (-gdgCosCoeff g) 2 := by
  have hth : 0 < gdgTheta g := gdgTheta_pos (by omega)
  have hthlt : gdgTheta g < Real.pi / 2 := gdgTheta_lt_pi_div_two hg
  have hpi := Real.pi_pos
  have hmem : phi ∈ Set.Icc 0 Real.pi := ⟨h0.le, by linarith⟩
  have hmem0 : (0 : ℝ) ∈ Set.Icc 0 Real.pi := ⟨le_rfl, hpi.le⟩
  have hmem2 : Real.pi - gdgTheta g ∈ Set.Icc 0 Real.pi := ⟨by linarith, by linarith⟩
  have h1 : Real.cos phi < Real.cos 0 := Real.strictAntiOn_cos hmem0 hmem h0
  have h2 : Real.cos (Real.pi - gdgTheta g) < Real.cos phi :=
    Real.strictAntiOn_cos hmem hmem2 hlt
  rw [Real.cos_pi_sub] at h2
  rw [Real.cos_zero] at h1
  have hcos : gdgCosCoeff g = 2 * Real.cos (gdgTheta g) := by
    simp only [gdgCosCoeff, gdgTheta]
  simp only [Set.mem_Ioo, gdgBlockCoord, hcos]
  constructor <;> linarith

/-- **Target 9.** Every retained even lobe produces a located free root. -/
theorem exists_even_retained_lobe_criticalTetranomial_unitCircle_root
    {g j : ℕ} (hg : 5 ≤ g) (hEven : Even g)
    (hj : j ∈ gdgRetainedLobeIndices g) :
    ∃ phi ∈ Set.Ioo
        (gdgLobeLeft g j 0)
        (gdgLobeRight g j 0),
      criticalTetranomial g (gdgCosCoeff g : ℂ) ((-1 : ℂ) ^ g)
          (gdgUnitCircle phi) = 0 ∧
      coverNumerator g ((-1 : ℂ) ^ g) (gdgUnitCircle phi) ≠ 0 ∧
      coverQuadratic (gdgCosCoeff g : ℂ) (gdgUnitCircle phi) ≠ 0 ∧
      gdgBlockCoord phi ∈ Set.Ioo (-gdgCosCoeff g) 2 := by
  obtain ⟨phi, hphi, hstat⟩ :=
    exists_even_retained_lobe_hasDerivAt_gdgSignedInterior_zero hg hEven hj
  have hleft0 : 0 ≤ gdgLobeLeft g j 0 :=
    gdgBridge_lobeLeft_nonneg (g := g) (j := j) (by omega) le_rfl
  have hright : gdgLobeRight g j 0 < Real.pi - gdgTheta g :=
    (gdgEven_mem_iff_lobeRight_lt_pole hg hEven).mp hj
  have hdenpos : 0 < gdgInteriorDenominator g phi :=
    gdgInteriorDenominator_pos_on_Icc hg hleft0 hright phi
      (Set.Ioo_subset_Icc_self hphi)
  have hval : gdgSignedInterior g phi ≠ 0 :=
    ne_of_lt (gdgSignedInterior_neg_on_even_retained_lobeInterior hg hEven hj hphi)
  obtain ⟨hG, hA, hQ⟩ :=
    criticalTetranomial_gdgUnitCircle_eq_zero_of_stationary hg
      (ne_of_gt hdenpos) hval hstat
  refine ⟨phi, hphi, hG, hA, hQ, ?_⟩
  exact gdgBlockCoord_mem_Ioo_of_prePole hg (lt_of_le_of_lt hleft0 hphi.1)
    (lt_trans hphi.2 hright)

/-- **Target 10.** Every retained odd lobe produces a located free root. -/
theorem exists_odd_retained_lobe_criticalTetranomial_unitCircle_root
    {g j : ℕ} (hg : 5 ≤ g) (hOdd : Odd g)
    (hj : j ∈ gdgRetainedLobeIndices g) :
    ∃ phi ∈ Set.Ioo
        (gdgLobeLeft g j ((1 : ℝ) / 2))
        (gdgLobeRight g j ((1 : ℝ) / 2)),
      criticalTetranomial g (gdgCosCoeff g : ℂ) ((-1 : ℂ) ^ g)
          (gdgUnitCircle phi) = 0 ∧
      coverNumerator g ((-1 : ℂ) ^ g) (gdgUnitCircle phi) ≠ 0 ∧
      coverQuadratic (gdgCosCoeff g : ℂ) (gdgUnitCircle phi) ≠ 0 ∧
      gdgBlockCoord phi ∈ Set.Ioo (-gdgCosCoeff g) 2 := by
  obtain ⟨phi, hphi, hstat⟩ :=
    exists_odd_retained_lobe_hasDerivAt_gdgSignedInterior_zero hg hOdd hj
  have hleft0 : 0 ≤ gdgLobeLeft g j ((1 : ℝ) / 2) :=
    gdgBridge_lobeLeft_nonneg (g := g) (j := j) (by omega) (by norm_num)
  have hright : gdgLobeRight g j ((1 : ℝ) / 2) < Real.pi - gdgTheta g :=
    (gdgOdd_mem_iff_lobeRight_lt_pole hg hOdd).mp hj
  have hdenpos : 0 < gdgInteriorDenominator g phi :=
    gdgInteriorDenominator_pos_on_Icc hg hleft0 hright phi
      (Set.Ioo_subset_Icc_self hphi)
  have hval : gdgSignedInterior g phi ≠ 0 :=
    ne_of_gt (gdgSignedInterior_pos_on_odd_retained_lobeInterior hg hOdd hj hphi)
  obtain ⟨hG, hA, hQ⟩ :=
    criticalTetranomial_gdgUnitCircle_eq_zero_of_stationary hg
      (ne_of_gt hdenpos) hval hstat
  refine ⟨phi, hphi, hG, hA, hQ, ?_⟩
  exact gdgBlockCoord_mem_Ioo_of_prePole hg (lt_of_le_of_lt hleft0 hphi.1)
    (lt_trans hphi.2 hright)

end GdgSquarefree
