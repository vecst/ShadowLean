import RequestProject.SphericalProductDifferential

/- Specification only: the Goal definitions below are unproved propositions.
Coordinate Frechet derivatives do not by themselves identify a sphere connection,
parallel transport, an intrinsic distance, or a covariant Hessian. -/
namespace SphericalProofRequest7A2

open SphericalProofRequest7A1

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]

noncomputable def radius (p : Real × V) : Real := Real.sqrt (euclideanSquare p)

noncomputable def polarAngle (p : Real × V) : Real := Real.arccos (p.1 / radius p)

noncomputable def vectorLog (p : Real × V) : V :=
  (polarAngle p / ‖p.2‖) • p.2

noncomputable def fullLog (p : Real × V) : Real × V := (scalarLog p, vectorLog p)

noncomputable def radialProjection (e : V) : V →L[Real] V :=
  (innerSL Real e).smulRight e

noncomputable def transverseProjection (e : V) : V →L[Real] V :=
  ContinuousLinearMap.id Real V - radialProjection e

noncomputable def ambientRadial (e : V) : (Real × V) →L[Real] Real :=
  (innerSL Real e).comp (ContinuousLinearMap.snd Real Real V)

noncomputable def logDerivative (r : Real) (e : V) : (Real × V) →L[Real] (Real × V) :=
  (((Real.cos r) • ContinuousLinearMap.fst Real Real V) +
    (Real.sin r) • ambientRadial e).prod
  ((((-Real.sin r) • ContinuousLinearMap.fst Real Real V +
    (Real.cos r) • ambientRadial e).smulRight e) +
    (r / Real.sin r) • ((transverseProjection e).comp (ContinuousLinearMap.snd Real Real V)))

noncomputable def compositionDerivative (r : Real) (e : V) : V →L[Real] (Real × V) :=
  (0 : V →L[Real] Real).prod
    (radialProjection e + (r * Real.cos r / Real.sin r) • transverseProjection e)

-- G1: identify the upper-half-plane principal polar branch, not just an acos symbol.
def GoalPolarBranch (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V] : Prop :=
  ∀ p : Real × V, 0 < ‖p.2‖ →
    0 < radius p ∧ -1 < p.1 / radius p ∧ p.1 / radius p < 1 ∧
    0 < polarAngle p ∧ polarAngle p < Real.pi ∧
    Real.cos (polarAngle p) = p.1 / radius p ∧
    Real.sin (polarAngle p) = ‖p.2‖ / radius p ∧
    (∀ θ : Real, 0 < θ → θ < Real.pi → Real.cos θ = p.1 / radius p → θ = polarAngle p)

-- G2: the full logarithm has the required value at the actual radial base point.
def GoalBaseValue (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V] : Prop :=
  ∀ (r : Real) (e : V), 0 < r → r < Real.pi → ‖e‖ = 1 →
    fullLog (basePoint r e) = (0, r • e)

-- G3: full ambient derivative, including the nonzero scalar radial derivative.
def GoalLogDerivative (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V] : Prop :=
  ∀ (r : Real) (e : V), 0 < r → r < Real.pi → ‖e‖ = 1 →
    HasFDerivAt (fullLog : Real × V → Real × V) (logDerivative r e) (basePoint r e)

-- G4: differentiate the actual product followed by the actual full logarithm.
def GoalCompositionDerivative (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V] : Prop :=
  ∀ (r : Real) (e : V), 0 < r → r < Real.pi → ‖e‖ = 1 →
    HasFDerivAt (fun Y : V => fullLog (productMap r e Y)) (compositionDerivative r e) 0

-- G5: radial action, transverse action, and a nonvacuous actual-composition equator test.
def GoalActionsAndEquator : Prop :=
  (∀ (r : Real) (e : EuclideanSpace Real (Fin 2)),
    0 < r → r < Real.pi → ‖e‖ = 1 →
    compositionDerivative r e e = (0, e) ∧
    (∀ W, inner Real e W = 0 →
      compositionDerivative r e W = (0, (r * Real.cos r / Real.sin r) • W))) ∧
  (∃ e W : EuclideanSpace Real (Fin 2),
    ‖e‖ = 1 ∧ ‖W‖ = 1 ∧ inner Real e W = 0 ∧
    fderiv Real (fun Y => fullLog (productMap (Real.pi / 2) e Y)) 0 W = (0, 0))


/-! ### Supporting lemmas -/

omit [InnerProductSpace Real V] in
/-- On the domain `‖p.2‖ > 0` the Euclidean square is strictly positive. -/
lemma euclideanSquare_pos {p : Real × V} (hp : 0 < ‖p.2‖) : 0 < euclideanSquare p := by
  have h : 0 < ‖p.2‖ ^ 2 := by positivity
  have h2 : 0 ≤ p.1 ^ 2 := sq_nonneg _
  simpa [euclideanSquare] using add_pos_of_nonneg_of_pos h2 h

omit [InnerProductSpace Real V] in
/-- The Euclidean radius is positive off the axis. -/
lemma radius_pos {p : Real × V} (hp : 0 < ‖p.2‖) : 0 < radius p :=
  Real.sqrt_pos.mpr (euclideanSquare_pos hp)

omit [InnerProductSpace Real V] in
/-- The square of the radius recovers the Euclidean square. -/
lemma radius_sq (p : Real × V) (hp : 0 ≤ euclideanSquare p) :
    radius p ^ 2 = euclideanSquare p := Real.sq_sqrt hp

omit [InnerProductSpace Real V] in
/-- Strict bound of the scalar coordinate by the radius, off the axis. -/
lemma abs_lt_radius {p : Real × V} (hp : 0 < ‖p.2‖) : |p.1| < radius p := by
  have hpos := radius_pos hp
  have hsq : radius p ^ 2 = p.1 ^ 2 + ‖p.2‖ ^ 2 :=
    radius_sq p (euclideanSquare_pos hp).le
  have h : p.1 ^ 2 < radius p ^ 2 := by nlinarith [sq_nonneg ‖p.2‖, hp]
  rw [abs_lt]
  constructor <;> nlinarith

/-- The vector part of a base point has norm `sin r`. -/
lemma norm_basePoint_snd {r : Real} {e : V} (hs : 0 ≤ Real.sin r) (he : ‖e‖ = 1) :
    ‖(basePoint r e).2‖ = Real.sin r := by
  simp [basePoint, norm_smul, Real.norm_eq_abs, he, abs_of_nonneg hs]

/-- Base points lie on the Euclidean unit quadric. -/
lemma euclideanSquare_basePoint (r : Real) {e : V} (he : ‖e‖ = 1) :
    euclideanSquare (basePoint r e) = 1 := by
  have h : ‖Real.sin r • e‖ ^ 2 = Real.sin r ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, he, mul_one, sq_abs]
  simp only [euclideanSquare, basePoint, h]
  exact Real.cos_sq_add_sin_sq r

/-- Base points have unit radius. -/
lemma radius_basePoint (r : Real) {e : V} (he : ‖e‖ = 1) : radius (basePoint r e) = 1 := by
  simp [radius, euclideanSquare_basePoint r he]

/-- Strict bounds on `cos r` for `0 < r < π`. -/
lemma abs_cos_lt_one {r : Real} (hr : 0 < r) (hrpi : r < Real.pi) : |Real.cos r| < 1 := by
  have hsin : 0 < Real.sin r := Real.sin_pos_of_pos_of_lt_pi hr hrpi
  have hpy : Real.cos r ^ 2 + Real.sin r ^ 2 = 1 := Real.cos_sq_add_sin_sq r
  have h : Real.cos r ^ 2 < 1 := by nlinarith
  rw [abs_lt]
  constructor <;> nlinarith

-- Requested theorems.
theorem polar_branch : GoalPolarBranch V := by
  intro p hp
  have hpos : 0 < radius p := radius_pos hp
  have habs : |p.1| < radius p := abs_lt_radius hp
  have hlt : p.1 < radius p := (abs_lt.mp habs).2
  have hgt : -radius p < p.1 := (abs_lt.mp habs).1
  have hu1 : -1 < p.1 / radius p := by
    rw [lt_div_iff₀ hpos]; linarith
  have hu2 : p.1 / radius p < 1 := by
    rw [div_lt_one hpos]; exact hlt
  refine ⟨hpos, hu1, hu2, Real.arccos_pos.mpr hu2, Real.arccos_lt_pi.mpr hu1,
    Real.cos_arccos hu1.le hu2.le, ?_, ?_⟩
  · have hsq : radius p ^ 2 = p.1 ^ 2 + ‖p.2‖ ^ 2 :=
      radius_sq p (euclideanSquare_pos hp).le
    have hne : radius p ≠ 0 := ne_of_gt hpos
    have key : 1 - (p.1 / radius p) ^ 2 = (‖p.2‖ / radius p) ^ 2 := by
      field_simp
      nlinarith [hsq]
    rw [polarAngle, Real.sin_arccos, key, Real.sqrt_sq (by positivity)]
  · intro θ hθ0 hθπ hcos
    rw [polarAngle, ← hcos, Real.arccos_cos hθ0.le hθπ.le]

theorem base_value : GoalBaseValue V := by
  intro r e hr hrpi he
  have hsin : 0 < Real.sin r := Real.sin_pos_of_pos_of_lt_pi hr hrpi
  have hrad : radius (basePoint r e) = 1 := radius_basePoint r he
  have hnv : ‖(basePoint r e).2‖ = Real.sin r := norm_basePoint_snd hsin.le he
  have hθ : polarAngle (basePoint r e) = r := by
    rw [polarAngle, hrad, div_one]
    exact Real.arccos_cos hr.le hrpi.le
  have hslog : scalarLog (basePoint r e) = 0 := by
    have : Real.sqrt (euclideanSquare (basePoint r e)) = 1 := hrad
    rw [scalarLog, this, Real.log_one]
  refine Prod.ext hslog ?_
  show vectorLog (basePoint r e) = r • e
  rw [vectorLog, hθ, hnv]
  show (r / Real.sin r) • (Real.sin r • e) = r • e
  rw [smul_smul, div_mul_cancel₀ _ (ne_of_gt hsin)]

/-- Frechet derivative of the norm composed with a map, at a point where the value is nonzero. -/
lemma hasFDerivAt_norm_comp {W : Type*} [NormedAddCommGroup W] [NormedSpace Real W]
    {f : W → V} {f' : W →L[Real] V} {x : W} (hf : HasFDerivAt f f' x) (h0 : f x ≠ 0) :
    HasFDerivAt (fun y => ‖f y‖) ((‖f x‖⁻¹) • (innerSL Real (f x)).comp f') x := by
  have hsq : HasFDerivAt (fun y => ‖f y‖ ^ 2) (2 • (innerSL Real (f x)).comp f') x := hf.norm_sq
  have hnorm0 : ‖f x‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  have hne : ‖f x‖ ^ 2 ≠ 0 := pow_ne_zero 2 hnorm0
  have hs : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (‖f x‖ ^ 2))) (‖f x‖ ^ 2) :=
    Real.hasDerivAt_sqrt hne
  have hcomp : HasFDerivAt (fun y => Real.sqrt (‖f y‖ ^ 2))
      ((1 / (2 * Real.sqrt (‖f x‖ ^ 2))) • (2 • (innerSL Real (f x)).comp f')) x :=
    hs.comp_hasFDerivAt x hsq
  have hfun : (fun y => Real.sqrt (‖f y‖ ^ 2)) = fun y => ‖f y‖ := by
    funext y; exact Real.sqrt_sq (norm_nonneg _)
  rw [hfun, Real.sqrt_sq (norm_nonneg (f x))] at hcomp
  refine hcomp.congr_fderiv ?_
  ext y
  simp only [smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, one_div]
  field_simp

theorem log_derivative : GoalLogDerivative V := by
  intro r e hr hrpi he
  have hsin : 0 < Real.sin r := Real.sin_pos_of_pos_of_lt_pi hr hrpi
  have hsn : Real.sin r ≠ 0 := ne_of_gt hsin
  have hpy : Real.cos r ^ 2 + Real.sin r ^ 2 = 1 := Real.cos_sq_add_sin_sq r
  set p0 : Real × V := basePoint r e with hp0def
  have hfst0 : p0.1 = Real.cos r := rfl
  have hsnd0 : p0.2 = Real.sin r • e := rfl
  have hnv : ‖p0.2‖ = Real.sin r := norm_basePoint_snd hsin.le he
  have hq0 : euclideanSquare p0 = 1 := euclideanSquare_basePoint r he
  have hrad0 : radius p0 = 1 := radius_basePoint r he
  have hv0 : p0.2 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnv
    exact hsn hnv.symm
  have hfstD : HasFDerivAt (fun p : Real × V => p.1) (ContinuousLinearMap.fst Real Real V) p0 :=
    hasFDerivAt_fst
  have hsndD : HasFDerivAt (fun p : Real × V => p.2) (ContinuousLinearMap.snd Real Real V) p0 :=
    hasFDerivAt_snd
  -- derivative of the norm of the vector part
  have hnormD : HasFDerivAt (fun p : Real × V => ‖p.2‖) (ambientRadial e) p0 := by
    refine (hasFDerivAt_norm_comp hsndD hv0).congr_fderiv ?_
    rw [hnv]
    refine ContinuousLinearMap.ext fun dp => ?_
    simp only [smul_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, ContinuousLinearMap.coe_snd', innerSL_apply_apply, smul_eq_mul,
      ambientRadial, hsnd0, real_inner_smul_left]
    field_simp
  -- derivative of the Euclidean square
  have hQD : HasFDerivAt euclideanSquare
      ((2 * Real.cos r) • ContinuousLinearMap.fst Real Real V +
        (2 * Real.sin r) • ambientRadial e) p0 := by
    have h1 : HasFDerivAt (fun p : Real × V => p.1 ^ 2)
        (((2 : ℕ) • p0.1 ^ (2 - 1)) • ContinuousLinearMap.fst Real Real V) p0 := hfstD.pow 2
    have h2 : HasFDerivAt (fun p : Real × V => ‖p.2‖ ^ 2)
        (2 • (innerSL Real p0.2).comp (ContinuousLinearMap.snd Real Real V)) p0 := hsndD.norm_sq
    have h3 := h1.add h2
    refine h3.congr_fderiv ?_
    refine ContinuousLinearMap.ext fun dp => ?_
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.coe_snd', innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul,
      Nat.cast_ofNat, ambientRadial, hfst0, hsnd0, real_inner_smul_left]
    ring
  -- derivative of the radius
  have hRadD : HasFDerivAt radius
      ((Real.cos r) • ContinuousLinearMap.fst Real Real V +
        (Real.sin r) • ambientRadial e) p0 := by
    have hne : euclideanSquare p0 ≠ 0 := by rw [hq0]; norm_num
    have hs : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (euclideanSquare p0)))
        (euclideanSquare p0) := Real.hasDerivAt_sqrt hne
    have hcomp : HasFDerivAt (fun p : Real × V => Real.sqrt (euclideanSquare p))
        ((1 / (2 * Real.sqrt (euclideanSquare p0))) •
          ((2 * Real.cos r) • ContinuousLinearMap.fst Real Real V +
            (2 * Real.sin r) • ambientRadial e)) p0 := hs.comp_hasFDerivAt p0 hQD
    have hcomp' : HasFDerivAt radius
        ((1 / (2 * Real.sqrt (euclideanSquare p0))) •
          ((2 * Real.cos r) • ContinuousLinearMap.fst Real Real V +
            (2 * Real.sin r) • ambientRadial e)) p0 := hcomp
    refine hcomp'.congr_fderiv ?_
    rw [hq0, Real.sqrt_one]
    refine ContinuousLinearMap.ext fun dp => ?_
    simp only [smul_apply, add_apply, smul_eq_mul]
    ring
  -- derivative of the scalar logarithm
  have hLogD : HasFDerivAt scalarLog
      ((Real.cos r) • ContinuousLinearMap.fst Real Real V +
        (Real.sin r) • ambientRadial e) p0 := by
    have hne : radius p0 ≠ 0 := by rw [hrad0]; norm_num
    have hs : HasDerivAt Real.log (radius p0)⁻¹ (radius p0) := Real.hasDerivAt_log hne
    have hcomp : HasFDerivAt (fun p : Real × V => Real.log (radius p))
        ((radius p0)⁻¹ • ((Real.cos r) • ContinuousLinearMap.fst Real Real V +
          (Real.sin r) • ambientRadial e)) p0 := hs.comp_hasFDerivAt p0 hRadD
    have hcomp' : HasFDerivAt scalarLog
        ((radius p0)⁻¹ • ((Real.cos r) • ContinuousLinearMap.fst Real Real V +
          (Real.sin r) • ambientRadial e)) p0 := hcomp
    refine hcomp'.congr_fderiv ?_
    rw [hrad0, inv_one, one_smul]
  -- derivative of the cosine coordinate `p.1 / radius p`
  have hUD : HasFDerivAt (fun p : Real × V => p.1 / radius p)
      ((Real.sin r ^ 2) • ContinuousLinearMap.fst Real Real V -
        (Real.cos r * Real.sin r) • ambientRadial e) p0 := by
    have hne : radius p0 ≠ 0 := by rw [hrad0]; norm_num
    have hinv0 : HasDerivAt (fun t : Real => t⁻¹) (-(radius p0 ^ 2)⁻¹) (radius p0) :=
      hasDerivAt_inv hne
    have hinv : HasFDerivAt (fun p : Real × V => (radius p)⁻¹)
        ((-(radius p0 ^ 2)⁻¹) • ((Real.cos r) • ContinuousLinearMap.fst Real Real V +
          (Real.sin r) • ambientRadial e)) p0 := hinv0.comp_hasFDerivAt p0 hRadD
    have hmul := hfstD.mul hinv
    have hfun : ((fun p : Real × V => p.1) * fun p : Real × V => (radius p)⁻¹)
        = fun p : Real × V => p.1 / radius p := by
      funext p; simp [div_eq_mul_inv]
    rw [hfun] at hmul
    refine hmul.congr_fderiv ?_
    refine ContinuousLinearMap.ext fun dp => ?_
    simp only [add_apply, sub_apply, smul_apply, ContinuousLinearMap.coe_fst',
      smul_eq_mul, hrad0, hfst0, inv_one, one_pow]
    linear_combination (-dp.1) * hpy
  -- derivative of the polar angle
  have hu0 : p0.1 / radius p0 = Real.cos r := by rw [hrad0, hfst0, div_one]
  have habs : |Real.cos r| < 1 := abs_cos_lt_one hr hrpi
  have hne1 : p0.1 / radius p0 ≠ 1 := by rw [hu0]; intro h; rw [h] at habs; simp at habs
  have hnem1 : p0.1 / radius p0 ≠ -1 := by
    rw [hu0]; intro h; rw [h] at habs; simp at habs
  have hThetaD : HasFDerivAt polarAngle
      ((-Real.sin r) • ContinuousLinearMap.fst Real Real V +
        (Real.cos r) • ambientRadial e) p0 := by
    have harc : HasDerivAt Real.arccos (-(1 / Real.sqrt (1 - (p0.1 / radius p0) ^ 2)))
        (p0.1 / radius p0) := Real.hasDerivAt_arccos hnem1 hne1
    have hcomp : HasFDerivAt (fun p : Real × V => Real.arccos (p.1 / radius p))
        ((-(1 / Real.sqrt (1 - (p0.1 / radius p0) ^ 2))) •
          ((Real.sin r ^ 2) • ContinuousLinearMap.fst Real Real V -
            (Real.cos r * Real.sin r) • ambientRadial e)) p0 :=
      HasDerivAt.comp_hasFDerivAt (h₂ := Real.arccos) p0 harc hUD
    have hcomp' : HasFDerivAt polarAngle
        ((-(1 / Real.sqrt (1 - (p0.1 / radius p0) ^ 2))) •
          ((Real.sin r ^ 2) • ContinuousLinearMap.fst Real Real V -
            (Real.cos r * Real.sin r) • ambientRadial e)) p0 := hcomp
    refine hcomp'.congr_fderiv ?_
    have hsq : Real.sqrt (1 - (p0.1 / radius p0) ^ 2) = Real.sin r := by
      rw [hu0, show (1 : Real) - Real.cos r ^ 2 = Real.sin r ^ 2 by linarith]
      exact Real.sqrt_sq hsin.le
    rw [hsq]
    refine ContinuousLinearMap.ext fun dp => ?_
    simp only [smul_apply, sub_apply, add_apply, smul_eq_mul, one_div]
    field_simp
    ring
  -- value of the polar angle at the base point
  have hTheta0 : polarAngle p0 = r := by
    rw [polarAngle, hu0]
    exact Real.arccos_cos hr.le hrpi.le
  -- derivative of the coefficient `polarAngle / ‖p.2‖`
  have hGD : HasFDerivAt (fun p : Real × V => polarAngle p / ‖p.2‖)
      ((-1 : Real) • ContinuousLinearMap.fst Real Real V +
        ((Real.cos r * Real.sin r - r) / Real.sin r ^ 2) • ambientRadial e) p0 := by
    have hinv0 : HasDerivAt (fun t : Real => t⁻¹) (-(‖p0.2‖ ^ 2)⁻¹) ‖p0.2‖ :=
      hasDerivAt_inv (by rw [hnv]; exact hsn)
    have hinv : HasFDerivAt (fun p : Real × V => ‖p.2‖⁻¹)
        ((-(‖p0.2‖ ^ 2)⁻¹) • ambientRadial e) p0 := hinv0.comp_hasFDerivAt p0 hnormD
    have hmul := hThetaD.mul hinv
    have hfun : ((polarAngle : Real × V → Real) * fun p : Real × V => ‖p.2‖⁻¹)
        = fun p : Real × V => polarAngle p / ‖p.2‖ := by
      funext p; simp [div_eq_mul_inv]
    rw [hfun] at hmul
    refine hmul.congr_fderiv ?_
    refine ContinuousLinearMap.ext fun dp => ?_
    simp only [add_apply, smul_apply, ContinuousLinearMap.coe_fst',
      smul_eq_mul, hnv, hTheta0]
    field_simp
    ring
  -- derivative of the vector logarithm
  have hVecD : HasFDerivAt vectorLog
      ((((-Real.sin r) • ContinuousLinearMap.fst Real Real V +
        (Real.cos r) • ambientRadial e).smulRight e) +
        (r / Real.sin r) • ((transverseProjection e).comp
          (ContinuousLinearMap.snd Real Real V))) p0 := by
    have hs := hGD.smul hsndD
    have hfun : (fun p : Real × V => polarAngle p / ‖p.2‖) • (fun p : Real × V => p.2)
        = vectorLog := by
      funext p; rfl
    rw [hfun] at hs
    refine hs.congr_fderiv ?_
    refine ContinuousLinearMap.ext fun dp => ?_
    have hval : polarAngle p0 / ‖p0.2‖ = r / Real.sin r := by rw [hTheta0, hnv]
    rw [hval]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_comp, Function.comp_apply,
      hsnd0, transverseProjection,
      radialProjection, sub_apply, ContinuousLinearMap.id_apply,
      innerSL_apply_apply, ambientRadial, smul_eq_mul, smul_smul]
    match_scalars
    all_goals field_simp
    all_goals ring
  exact hLogD.prodMk hVecD

/-- The product map sends the origin to the base point (7A.1's helper is private). -/
lemma productMap_zero' (r : Real) (e : V) : productMap r e 0 = basePoint r e := by
  simp [productMap, expCoordinates, SpinFactor.mul, basePoint]

theorem composition_derivative : GoalCompositionDerivative V := by
  intro r e hr hrpi he
  have hsin : 0 < Real.sin r := Real.sin_pos_of_pos_of_lt_pi hr hrpi
  have hsn : Real.sin r ≠ 0 := ne_of_gt hsin
  have hpy : Real.cos r ^ 2 + Real.sin r ^ 2 = 1 := Real.cos_sq_add_sin_sq r
  have hp : HasFDerivAt (productMap r e) (productDerivative r e) 0 :=
    product_derivative r e hr hrpi he
  have hl : HasFDerivAt (fullLog : Real × V → Real × V) (logDerivative r e)
      (productMap r e 0) := by
    rw [productMap_zero']
    exact log_derivative r e hr hrpi he
  have hcomp := hl.comp 0 hp
  refine hcomp.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun W => ?_
  refine Prod.ext ?_ ?_
  · simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, logDerivative,
      productDerivative, compositionDerivative, ContinuousLinearMap.prod_apply,
      add_apply, smul_apply,
      ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.id_apply, ambientRadial, ContinuousLinearMap.coe_snd',
      innerSL_apply_apply, real_inner_smul_right, smul_eq_mul,
      zero_apply]
    ring
  · simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, logDerivative,
      productDerivative, compositionDerivative, ContinuousLinearMap.prod_apply,
      add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.id_apply,
      ambientRadial, ContinuousLinearMap.coe_snd', innerSL_apply_apply,
      real_inner_smul_right, smul_eq_mul, transverseProjection, radialProjection,
      sub_apply, ContinuousLinearMap.coe_comp]
    match_scalars
    all_goals field_simp
    all_goals linear_combination (inner Real e W * Real.sin r) * hpy

theorem actions_and_equator : GoalActionsAndEquator := by
  constructor
  · intro r e _ _ he
    have hee : (inner Real e e : Real) = 1 := by
      rw [real_inner_self_eq_norm_sq, he, one_pow]
    constructor
    · refine Prod.ext rfl ?_
      simp only [compositionDerivative, ContinuousLinearMap.prod_apply,
        add_apply, smul_apply,
        radialProjection, transverseProjection, ContinuousLinearMap.smulRight_apply,
        sub_apply, ContinuousLinearMap.id_apply, innerSL_apply_apply,
        hee, one_smul, sub_self, smul_zero, add_zero]
    · intro W hW
      refine Prod.ext rfl ?_
      simp only [compositionDerivative, ContinuousLinearMap.prod_apply,
        add_apply, smul_apply,
        radialProjection, transverseProjection, ContinuousLinearMap.smulRight_apply,
        sub_apply, ContinuousLinearMap.id_apply, innerSL_apply_apply,
        hW, zero_smul, sub_zero, zero_add]
  · refine ⟨EuclideanSpace.single 0 1, EuclideanSpace.single 1 1, ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · simp [EuclideanSpace.inner_single_left]
    · have he : ‖(EuclideanSpace.single (0 : Fin 2) (1 : Real))‖ = 1 := by simp
      have hperp : inner Real (EuclideanSpace.single (0 : Fin 2) (1 : Real))
          (EuclideanSpace.single (1 : Fin 2) (1 : Real)) = 0 := by
        simp [EuclideanSpace.inner_single_left]
      have hd := composition_derivative (Real.pi / 2) (EuclideanSpace.single (0 : Fin 2) (1 : Real))
        (by positivity) (by linarith [Real.pi_pos]) he
      rw [hd.fderiv]
      refine Prod.ext ?_ ?_
      · simp [compositionDerivative]
      · simp [compositionDerivative, radialProjection, transverseProjection, hperp,
          Real.cos_pi_div_two]

end SphericalProofRequest7A2
