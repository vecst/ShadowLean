import RequestProject.SphericalAngularPotential
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

/-!
# Spherical repair 7B.5: the intrinsic length distance of the ambient unit sphere

This module proves the four Goal propositions stated below, with the definitions and Goal
statements unchanged from the reviewed specification.

* `angular_control` (G1): `angularSeparation p q = arccos ⟪p, q⟫` satisfies the triangle
  inequality on ambient unit vectors, and admits a *uniform* local comparison with the ambient
  chord: for every `epsilon > 0` there is a single `delta > 0`, chosen before the pair, with
  `angularSeparation p q ≤ (1 + epsilon) * ‖p - q‖` for all unit `p, q` whose chord is below
  `delta`.  Equal endpoints are included; no division by a vanishing chord occurs.
* `path_lower_bound` (G2): every competitor `gamma` that is merely continuous on `[0, 1]`,
  unit-valued there and joins `p` to `q` has metric curve length
  `curveELength gamma = eVariationOn gamma (Icc 0 1)` at least `angularSeparation p q`.  No
  differentiability, rectifiability, monotonicity, hemisphere or pole-avoidance hypothesis is
  used: paths of infinite variation are covered by `le_top`, and paths crossing the poles or
  backtracking are covered because only continuity and unit norm enter the argument.
* `radial_minimizer` (G3): for unit `e` and `0 ≤ r ≤ π` the actual curve
  `radialArc e r t = radialCurve e (r * t)` is an admissible competitor, its metric curve
  length is computed (not stipulated) to be `r` from the Lipschitz bound
  `‖radialCurve e a - radialCurve e b‖ ≤ |a - b|`, and it attains the infimum
  `spherePathEDist north (radialCurve e r)`, the lower bound coming from G2 applied to every
  competitor.  The endpoints `r = 0` and `r = π` are included.
* `north_distance` (G4): for unit `p` with `-1 < height p` the path infimum equals
  `ENNReal.ofReal (arccos (height p))`, is finite, and the 7B.4 potential `angularPotential p`
  equals half the square of its real value.  The north pole is included (through the constant
  path, which needs no unit direction); the antipode is excluded, since for a zero-dimensional
  `V` the antipodal path class is empty and the infimum is `⊤`.

Scope caveats.  No metric or `MetricSpace` instance is installed on the sphere, and
`spherePathEDist` is not identified with the chord distance inherited by the subtype — indeed
G3 and the equator sanity check below distinguish the path distance `π / 2` from the chord
`√2`.  Equality with Mathlib's bundled `Manifold.riemannianEDist`, bundled tangent space and
Levi-Civita identification, and metric recovery all remain open.  G4's value at the north pole
does not extend the 7B.4 ambient gradient/Hessian differentiability statements to that pole:
those still require `-1 < height p < 1`.
-/

namespace SphericalProofRequest7B5

open SphericalProofRequest7B1 SphericalProofRequest7B2 SphericalProofRequest7B4

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]

noncomputable def angularSeparation (p q : Ambient V) : Real :=
  Real.arccos (inner Real p q)

-- Metric curve length: supremum of finite sums of ambient L2 chord lengths.
-- No derivative or angular distance is used to define this length.
noncomputable def curveELength (gamma : Real → Ambient V) : ENNReal :=
  eVariationOn gamma (Set.Icc (0 : Real) 1)

-- Only the restriction to [0,1] matters. All continuous sphere paths compete.
def IsSpherePath (p q : Ambient V) (gamma : Real → Ambient V) : Prop :=
  ContinuousOn gamma (Set.Icc (0 : Real) 1) ∧
  (∀ t ∈ Set.Icc (0 : Real) 1, ‖gamma t‖ = 1) ∧ gamma 0 = p ∧ gamma 1 = q

-- An empty path class has infimum infinity; do not convert to Real prematurely.
noncomputable def spherePathEDist (p q : Ambient V) : ENNReal :=
  ⨅ (gamma : Real → Ambient V) (_ : IsSpherePath p q gamma), curveELength gamma

noncomputable def radialArc (e : V) (r : Real) (t : Real) : Ambient V :=
  radialCurve e (r * t)

-- G1: the local comparison needed to pass from chord partitions to angles.
def GoalAngularControl (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V] : Prop :=
  (∀ p q z : Ambient V, ‖p‖ = 1 → ‖q‖ = 1 → ‖z‖ = 1 →
    angularSeparation p z ≤ angularSeparation p q + angularSeparation q z) ∧
  (∀ epsilon : Real, 0 < epsilon → ∃ delta : Real, 0 < delta ∧
    ∀ p q : Ambient V, ‖p‖ = 1 → ‖q‖ = 1 → ‖p - q‖ < delta →
      angularSeparation p q ≤ (1 + epsilon) * ‖p - q‖)

-- G2: every continuous competitor, including nonrectifiable and pole-crossing paths.
def GoalPathLowerBound (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V] : Prop :=
  ∀ (p q : Ambient V) (gamma : Real → Ambient V), IsSpherePath p q gamma →
    ENNReal.ofReal (angularSeparation p q) ≤ curveELength gamma

-- G3: an actual curve attains the bound, including r=0 and r=pi.
def GoalRadialMinimizer (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V] : Prop :=
  ∀ (e : V), ‖e‖ = 1 → ∀ r : Real, 0 ≤ r → r ≤ Real.pi →
    IsSpherePath north (radialCurve e r) (radialArc e r) ∧
    curveELength (radialArc e r) = ENNReal.ofReal r ∧
    spherePathEDist north (radialCurve e r) = ENNReal.ofReal r

-- G4: identify the existing potential using the independently defined path infimum.
-- The north pole is included. The antipode is excluded in this arbitrary-V statement.
def GoalNorthDistance (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V] : Prop :=
  ∀ p : Ambient V, ‖p‖ = 1 → -1 < height p →
    spherePathEDist north p = ENNReal.ofReal (Real.arccos (height p)) ∧
    spherePathEDist north p ≠ ⊤ ∧
    angularPotential p = ((spherePathEDist north p).toReal) ^ 2 / 2

/-! ### Elementary spherical trigonometry of the ambient chord -/

/-- The north pole is a unit ambient vector. -/
lemma norm_north : ‖(north : Ambient V)‖ = 1 := by
  have h : ‖(north : Ambient V)‖ ^ 2 = 1 := by
    rw [north, norm_toAmbient_sq]
    simp [SphericalProofRequest7A1.euclideanSquare]
  nlinarith [norm_nonneg (north : Ambient V)]

/-- The squared chord between two unit ambient vectors. -/
lemma norm_sub_sq_unit {p q : Ambient V} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) :
    ‖p - q‖ ^ 2 = 2 - 2 * (inner Real p q : Real) := by
  rw [← real_inner_self_eq_norm_sq, inner_sub_sub_self]
  simp [hp, hq, real_inner_comm p q]
  ring

lemma angularSeparation_nonneg (p q : Ambient V) : 0 ≤ angularSeparation p q :=
  Real.arccos_nonneg _

lemma angularSeparation_le_pi (p q : Ambient V) : angularSeparation p q ≤ Real.pi :=
  Real.arccos_le_pi _

/-- On unit vectors the angular separation is the arccosine branch inverse of the inner
product. -/
lemma cos_angularSeparation {p q : Ambient V} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) :
    Real.cos (angularSeparation p q) = (inner Real p q : Real) := by
  have h := abs_real_inner_le_norm p q
  rw [hp, hq, abs_le] at h
  exact Real.cos_arccos (by linarith [h.1]) (by linarith [h.2])

/-- The chord of two unit ambient vectors is `2 sin(θ/2)` for `θ` their angular separation. -/
lemma norm_sub_eq_two_sin_half {p q : Ambient V} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) :
    ‖p - q‖ = 2 * Real.sin (angularSeparation p q / 2) := by
  have hs : 0 ≤ Real.sin (angularSeparation p q / 2) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith [angularSeparation_nonneg p q]
    · linarith [angularSeparation_le_pi p q, Real.pi_pos]
  have hsq : ‖p - q‖ ^ 2 = (2 * Real.sin (angularSeparation p q / 2)) ^ 2 := by
    rw [norm_sub_sq_unit hp hq, ← cos_angularSeparation hp hq]
    have h2 := Real.cos_two_mul_eq_one_sub (angularSeparation p q / 2)
    rw [show 2 * (angularSeparation p q / 2) = angularSeparation p q by ring] at h2
    rw [h2]; ring
  nlinarith [norm_nonneg (p - q), hs]

/-- On unit vectors the angular separation is Mathlib's unoriented angle. -/
lemma angularSeparation_eq_angle {p q : Ambient V} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) :
    angularSeparation p q = InnerProductGeometry.angle p q := by
  rw [InnerProductGeometry.angle, angularSeparation, hp, hq]
  norm_num

/-- The spherical triangle inequality for the angular separation. -/
lemma angularSeparation_triangle {p q z : Ambient V} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hz : ‖z‖ = 1) :
    angularSeparation p z ≤ angularSeparation p q + angularSeparation q z := by
  rw [angularSeparation_eq_angle hp hz, angularSeparation_eq_angle hp hq,
    angularSeparation_eq_angle hq hz]
  exact InnerProductGeometry.angle_le_angle_add_angle p q z

/-- The angular separation of a unit vector from itself vanishes. -/
lemma angularSeparation_self {p : Ambient V} (hp : ‖p‖ = 1) : angularSeparation p p = 0 := by
  rw [angularSeparation, real_inner_self_eq_norm_sq, hp]
  norm_num

/-- Uniform local comparison of angle and chord, in the one-variable form. -/
lemma angle_le_chord_of_small {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ delta : Real, 0 < delta ∧ ∀ theta : Real, 0 ≤ theta → theta ≤ Real.pi →
      2 * Real.sin (theta / 2) < delta → theta ≤ (1 + epsilon) * (2 * Real.sin (theta / 2)) := by
  set u0 : Real := min (Real.pi / 2) (Real.sqrt (6 * epsilon / (1 + epsilon))) with hu0
  have hpos : 0 < u0 := lt_min (by positivity) (Real.sqrt_pos.2 (by positivity))
  have hu0le : u0 ≤ Real.pi / 2 := min_le_left _ _
  have hsin0 : 0 < Real.sin u0 :=
    Real.sin_pos_of_pos_of_lt_pi hpos (lt_of_le_of_lt hu0le (by linarith [Real.pi_pos]))
  refine ⟨2 * Real.sin u0, by linarith, ?_⟩
  intro theta h0 hpi hlt
  set u : Real := theta / 2 with hu
  have hu_nonneg : 0 ≤ u := by rw [hu]; linarith
  have hu_le : u ≤ Real.pi / 2 := by rw [hu]; linarith
  have hlt' : Real.sin u < Real.sin u0 := by linarith
  have huu0 : u < u0 := by
    by_contra hc
    rw [not_lt] at hc
    have := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ u0) hu_le hc
    linarith
  rcases eq_or_lt_of_le hu_nonneg with hz | hz
  · have hs0 : Real.sin u = 0 := by rw [← hz]; simp
    have hth : theta = 0 := by rw [hu] at hz; linarith
    rw [hth]
    rw [hu] at hs0
    rw [hs0]; norm_num
  · have hs : u - u ^ 3 / 6 < Real.sin u := Real.sin_gt_sub_cube hz
    have hu2 : u ^ 2 < 6 * epsilon / (1 + epsilon) := by
      have h1 : u < Real.sqrt (6 * epsilon / (1 + epsilon)) :=
        lt_of_lt_of_le huu0 (min_le_right _ _)
      nlinarith [Real.sq_sqrt (by positivity : (0:Real) ≤ 6 * epsilon / (1 + epsilon)),
        Real.sqrt_nonneg (6 * epsilon / (1 + epsilon))]
    rw [lt_div_iff₀ (by linarith : (0:Real) < 1 + epsilon)] at hu2
    have hkey : 1 < (1 + epsilon) * (1 - u ^ 2 / 6) := by nlinarith
    have hfin : u ≤ (1 + epsilon) * Real.sin u := by nlinarith
    rw [hu] at hfin
    linarith

/-! ### G1 -/

/-- G1.  The angular separation of ambient unit vectors satisfies the spherical triangle
inequality, and is uniformly comparable with the ambient chord at small chords: the positive
`delta` is produced from `epsilon` alone, before the pair `p, q` is given. -/
theorem angular_control : GoalAngularControl V := by
  refine ⟨fun p q z hp hq hz => angularSeparation_triangle hp hq hz, ?_⟩
  intro epsilon hepsilon
  obtain ⟨delta, hdelta, hmain⟩ := angle_le_chord_of_small hepsilon
  refine ⟨delta, hdelta, ?_⟩
  intro p q hp hq hlt
  have hchord := norm_sub_eq_two_sin_half hp hq
  have := hmain (angularSeparation p q) (angularSeparation_nonneg p q)
    (angularSeparation_le_pi p q) (by rw [← hchord]; exact hlt)
  rw [← hchord] at this
  exact this

/-! ### G2: the length of any continuous competitor dominates the endpoint angle -/

/-- Chained triangle inequality along a finite sequence of unit vectors. -/
lemma angularSeparation_chain (f : ℕ → Ambient V) (hf : ∀ i, ‖f i‖ = 1) (n : ℕ) :
    angularSeparation (f 0) (f n) ≤ ∑ i ∈ Finset.range n, angularSeparation (f i) (f (i + 1)) := by
  induction n with
  | zero => simp [angularSeparation_self (hf 0)]
  | succ n ih =>
      rw [Finset.sum_range_succ]
      exact le_trans (angularSeparation_triangle (hf 0) (hf n) (hf (n + 1)))
        (by linarith)

/-- The uniform partition of `[0,1]` into `n` pieces, clamped so that it is globally monotone
and stays inside `[0,1]`. -/
noncomputable def uniformPartition (n : ℕ) (i : ℕ) : Real := min ((i : Real) / n) 1

lemma uniformPartition_mem (n i : ℕ) : uniformPartition n i ∈ Set.Icc (0 : Real) 1 := by
  constructor
  · exact le_min (by positivity) (by norm_num)
  · exact min_le_right _ _

lemma uniformPartition_monotone (n : ℕ) : Monotone (uniformPartition n) := by
  intro i j hij
  apply min_le_min _ (le_refl 1)
  have : (i : Real) ≤ (j : Real) := by exact_mod_cast hij
  gcongr

lemma uniformPartition_zero (n : ℕ) : uniformPartition n 0 = 0 := by
  simp [uniformPartition]

lemma uniformPartition_last {n : ℕ} (hn : 0 < n) : uniformPartition n n = 1 := by
  have hn' : (n : Real) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have h : ((n : Real) / n) = 1 := by field_simp
  simp [uniformPartition, h]

lemma uniformPartition_step {n : ℕ} (hn : 0 < n) (i : ℕ) :
    uniformPartition n (i + 1) - uniformPartition n i ≤ 1 / n := by
  have hn' : (n : Real) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hnpos : (0 : Real) < n := by positivity
  have hstep : ((i : Real) + 1) / n - (i : Real) / n = 1 / n := by
    field_simp
    ring
  have hmono : (i : Real) / n ≤ ((i : Real) + 1) / n := by
    gcongr
    linarith
  unfold uniformPartition
  push_cast
  rcases le_total (((i : Real) + 1) / n) 1 with h1 | h1
  · rw [min_eq_left h1, min_eq_left (le_trans hmono h1)]
    linarith
  · rw [min_eq_right h1]
    rcases le_total ((i : Real) / n) 1 with h2 | h2
    · rw [min_eq_left h2]; linarith
    · rw [min_eq_right h2]
      simp only [sub_self]
      positivity

omit [InnerProductSpace Real V] in
/-- The real chord sum over any monotone sequence in `[0,1]` is bounded by the metric curve
length. -/
lemma chord_sum_le_length {gamma : Real → Ambient V} {u : ℕ → Real} (hu : Monotone u)
    (humem : ∀ i, u i ∈ Set.Icc (0 : Real) 1) (n : ℕ) (hfin : curveELength gamma ≠ ⊤) :
    ∑ i ∈ Finset.range n, ‖gamma (u i) - gamma (u (i + 1))‖ ≤ (curveELength gamma).toReal := by
  have hsum : ∑ i ∈ Finset.range n, edist (gamma (u (i + 1))) (gamma (u i)) ≤
      curveELength gamma := eVariationOn.sum_le hu humem
  have hcast : ∑ i ∈ Finset.range n, edist (gamma (u (i + 1))) (gamma (u i)) =
      ENNReal.ofReal (∑ i ∈ Finset.range n, ‖gamma (u i) - gamma (u (i + 1))‖) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => norm_nonneg _)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [edist_dist, dist_comm, dist_eq_norm]
  rw [hcast] at hsum
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).1 hsum

/-- The key real estimate behind G2: for a finite-length competitor the endpoint angle is at
most `(1 + epsilon)` times the length, for every positive `epsilon`. -/
lemma angularSeparation_le_length_toReal {p q : Ambient V} {gamma : Real → Ambient V}
    (hpath : IsSpherePath p q gamma) (hfin : curveELength gamma ≠ ⊤)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    angularSeparation p q ≤ (1 + epsilon) * (curveELength gamma).toReal := by
  obtain ⟨hcont, hnorm, h0, h1⟩ := hpath
  obtain ⟨-, hcomp⟩ := angular_control (V := V)
  obtain ⟨delta, hdelta, hcomp⟩ := hcomp epsilon hepsilon
  -- uniform continuity of `gamma` on the compact interval
  have hunif : UniformContinuousOn gamma (Set.Icc (0 : Real) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hcont
  rw [Metric.uniformContinuousOn_iff] at hunif
  obtain ⟨eta, heta, hunif⟩ := hunif delta hdelta
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / eta)
  have hnpos : 0 < n := by
    by_contra hc
    rw [not_lt, Nat.le_zero] at hc
    rw [hc] at hn
    simp at hn
    have : 0 < 1 / eta := by positivity
    linarith
  have hnR : (0 : Real) < n := by exact_mod_cast hnpos
  have hstep : (1 : Real) / n < eta := by
    rw [div_lt_iff₀ hnR]
    rw [div_lt_iff₀ heta] at hn
    linarith
  set u := uniformPartition n with hudef
  set f : ℕ → Ambient V := fun i => gamma (u i) with hfdef
  have hfnorm : ∀ i, ‖f i‖ = 1 := fun i => hnorm _ (uniformPartition_mem n i)
  have hchain := angularSeparation_chain f hfnorm n
  have hf0 : f 0 = p := by rw [hfdef]; simp [hudef, uniformPartition_zero, h0]
  have hfn : f n = q := by rw [hfdef]; simp [hudef, uniformPartition_last hnpos, h1]
  rw [hf0, hfn] at hchain
  have hterm : ∀ i ∈ Finset.range n,
      angularSeparation (f i) (f (i + 1)) ≤ (1 + epsilon) * ‖f i - f (i + 1)‖ := by
    intro i _
    apply hcomp _ _ (hfnorm i) (hfnorm (i + 1))
    rw [← dist_eq_norm]
    apply hunif _ (uniformPartition_mem n i) _ (uniformPartition_mem n (i + 1))
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg]
    · exact lt_of_le_of_lt (uniformPartition_step hnpos i) hstep
    · have := uniformPartition_monotone n (Nat.le_succ i)
      linarith
  have hsum1 : ∑ i ∈ Finset.range n, angularSeparation (f i) (f (i + 1)) ≤
      (1 + epsilon) * ∑ i ∈ Finset.range n, ‖f i - f (i + 1)‖ := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hsum2 : ∑ i ∈ Finset.range n, ‖f i - f (i + 1)‖ ≤ (curveELength gamma).toReal :=
    chord_sum_le_length (uniformPartition_monotone n) (uniformPartition_mem n) n hfin
  have hpos : (0 : Real) ≤ 1 + epsilon := by linarith
  calc angularSeparation p q ≤ ∑ i ∈ Finset.range n, angularSeparation (f i) (f (i + 1)) := hchain
    _ ≤ (1 + epsilon) * ∑ i ∈ Finset.range n, ‖f i - f (i + 1)‖ := hsum1
    _ ≤ (1 + epsilon) * (curveELength gamma).toReal := by
        exact mul_le_mul_of_nonneg_left hsum2 hpos

/-- G2.  Every competitor that is only assumed continuous and unit-valued on `[0,1]` — in
particular competitors of infinite variation, competitors that cross the poles and
nowhere-differentiable competitors — has metric curve length at least the angular separation
of its endpoints. -/
theorem path_lower_bound : GoalPathLowerBound V := by
  intro p q gamma hpath
  by_cases hfin : curveELength gamma = ⊤
  · rw [hfin]; exact le_top
  rw [ENNReal.ofReal_le_iff_le_toReal hfin]
  set L := (curveELength gamma).toReal with hL
  have hLnonneg : 0 ≤ L := ENNReal.toReal_nonneg
  by_contra hc
  rw [not_le] at hc
  set A := angularSeparation p q with hA
  have hgap : 0 < A - L := by linarith
  have hepsilon : 0 < (A - L) / (L + 1) := by positivity
  have := angularSeparation_le_length_toReal hpath hfin hepsilon
  rw [← hA, ← hL] at this
  have hexp : (1 + (A - L) / (L + 1)) * L = L + (A - L) * L / (L + 1) := by
    field_simp
  rw [hexp] at this
  have hfrac : (A - L) * L / (L + 1) < A - L := by
    rw [div_lt_iff₀ (by linarith : (0:Real) < L + 1)]
    nlinarith
  linarith

/-! ### G3: the radial arc is an actual minimizer -/

/-- The inner product of two points of the same radial great circle. -/
lemma inner_radialCurve {e : V} (he : ‖e‖ = 1) (a b : Real) :
    (inner Real (radialCurve e a) (radialCurve e b) : Real) = Real.cos (a - b) := by
  rw [radialCurve_apply, radialCurve_apply, inner_toAmbient]
  simp [real_inner_smul_left, real_inner_smul_right, he, Real.cos_sub]
  ring

/-- The radial great circle is `1`-Lipschitz in its parameter: the chord never exceeds the
parameter difference. -/
lemma norm_radialCurve_sub_le {e : V} (he : ‖e‖ = 1) (a b : Real) :
    ‖radialCurve e a - radialCurve e b‖ ≤ |a - b| := by
  have hsq : ‖radialCurve e a - radialCurve e b‖ ^ 2 = 2 - 2 * Real.cos (a - b) := by
    rw [norm_sub_sq_unit (norm_radialCurve e he a) (norm_radialCurve e he b),
      inner_radialCurve he]
  have hhalf := Real.cos_two_mul_eq_one_sub ((a - b) / 2)
  rw [show 2 * ((a - b) / 2) = a - b by ring] at hhalf
  have hbound : |Real.sin ((a - b) / 2)| ≤ |(a - b) / 2| := Real.abs_sin_le_abs
  have habs : |(a - b) / 2| = |a - b| / 2 := by
    rw [abs_div]; norm_num
  rw [habs] at hbound
  have hsq2 : Real.sin ((a - b) / 2) ^ 2 ≤ (|a - b| / 2) ^ 2 := by
    have h1 : |Real.sin ((a - b) / 2)| ^ 2 = Real.sin ((a - b) / 2) ^ 2 := sq_abs _
    nlinarith [abs_nonneg (Real.sin ((a - b) / 2)), abs_nonneg (a - b)]
  have : ‖radialCurve e a - radialCurve e b‖ ^ 2 ≤ |a - b| ^ 2 := by
    rw [hsq, hhalf]
    nlinarith [sq_abs (a - b)]
  nlinarith [norm_nonneg (radialCurve e a - radialCurve e b), abs_nonneg (a - b)]

lemma continuous_radialCurve {e : V} (he : ‖e‖ = 1) : Continuous (radialCurve e) := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro a b
  rw [dist_eq_norm, Real.dist_eq]
  simpa using norm_radialCurve_sub_le he a b

lemma lipschitz_radialArc {e : V} (he : ‖e‖ = 1) {r : Real} (hr : 0 ≤ r) :
    LipschitzWith (Real.toNNReal r) (radialArc e r) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  rw [dist_eq_norm, Real.dist_eq, radialArc, radialArc]
  have h := norm_radialCurve_sub_le he (r * a) (r * b)
  have : |r * a - r * b| = r * |a - b| := by
    rw [show r * a - r * b = r * (a - b) by ring, abs_mul, abs_of_nonneg hr]
  rw [this] at h
  rw [Real.coe_toNNReal r hr]
  exact h

/-- The metric curve length of the radial arc is exactly its parameter length `r`. -/
lemma curveELength_radialArc_le {e : V} (he : ‖e‖ = 1) {r : Real} (hr : 0 ≤ r) :
    curveELength (radialArc e r) ≤ ENNReal.ofReal r := by
  have hid : eVariationOn (id : Real → Real) (Set.Icc (0:Real) 1) = ENNReal.ofReal 1 := by
    have hmono := (monotone_id.monotoneOn (Set.univ : Set Real)).eVariationOn_eq
      (a := (0:Real)) (b := 1) (Set.mem_univ _) (Set.mem_univ _)
    rw [Set.univ_inter] at hmono
    rw [hmono]
    norm_num
  have hcomp := (lipschitz_radialArc he hr).lipschitzOnWith.comp_eVariationOn_le
    (g := (id : Real → Real)) (s := Set.Icc (0:Real) 1) (Set.mapsTo_univ _ _)
  rw [hid] at hcomp
  have : (radialArc e r ∘ (id : Real → Real)) = radialArc e r := rfl
  rw [this] at hcomp
  refine le_trans hcomp ?_
  rw [ENNReal.ofReal_one, mul_one]
  simp [ENNReal.ofReal, Real.toNNReal]

lemma isSpherePath_radialArc {e : V} (he : ‖e‖ = 1) (r : Real) :
    IsSpherePath north (radialCurve e r) (radialArc e r) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (((continuous_radialCurve he).comp (continuous_const.mul continuous_id)).continuousOn)
  · intro t _
    exact norm_radialCurve e he _
  · rw [radialArc, mul_zero, radialCurve, north]
    simp [SphericalProofRequest7A1.basePoint]
  · rw [radialArc, mul_one]

lemma angularSeparation_north_radialCurve (e : V) {r : Real} (h0 : 0 ≤ r)
    (hpi : r ≤ Real.pi) : angularSeparation north (radialCurve e r) = r := by
  rw [angularSeparation,
    show (inner Real (north : Ambient V) (radialCurve e r) : Real) = height (radialCurve e r) from
      rfl, height_radialCurve, Real.arccos_cos h0 hpi]

/-- G3.  For a unit direction `e` and `0 ≤ r ≤ π` the concrete curve `radialArc e r` is an
admissible competitor, its metric curve length is computed to be `r`, and it attains the
infimum defining `spherePathEDist`.  Both endpoints `r = 0` and `r = π` are covered. -/
theorem radial_minimizer : GoalRadialMinimizer V := by
  intro e he r h0 hpi
  have hpath := isSpherePath_radialArc he r
  have hlower : ENNReal.ofReal r ≤ curveELength (radialArc e r) := by
    have := path_lower_bound (V := V) north (radialCurve e r) (radialArc e r) hpath
    rwa [angularSeparation_north_radialCurve e h0 hpi] at this
  have hlen : curveELength (radialArc e r) = ENNReal.ofReal r :=
    le_antisymm (curveELength_radialArc_le he h0) hlower
  refine ⟨hpath, hlen, ?_⟩
  apply le_antisymm
  · refine le_trans (iInf_le_of_le (radialArc e r) (iInf_le _ hpath)) ?_
    rw [hlen]
  · refine le_iInf₂ ?_
    intro gamma hgamma
    have := path_lower_bound (V := V) north (radialCurve e r) gamma hgamma
    rwa [angularSeparation_north_radialCurve e h0 hpi] at this

/-! ### G4: the path distance from the north pole and the angular potential -/

/-- The constant path shows that the north pole is at path distance zero from itself. -/
lemma spherePathEDist_north_self : spherePathEDist (north : Ambient V) north = 0 := by
  apply le_antisymm _ (zero_le)
  have hpath : IsSpherePath (north : Ambient V) north (fun _ => north) := by
    refine ⟨continuousOn_const, fun t _ => norm_north, rfl, rfl⟩
  refine le_trans (iInf_le_of_le (fun _ => (north : Ambient V)) (iInf_le _ hpath)) ?_
  rw [curveELength]
  exact le_of_eq (eVariationOn.constant_on (by simp [Set.Subsingleton]))

/-- A unit ambient vector of height one is the north pole. -/
lemma eq_north_of_height_one {p : Ambient V} (hp : ‖p‖ = 1) (hh : height p = 1) :
    p = north := by
  set x : Real × V := WithLp.ofLp p with hx
  have hpx : toAmbient x = p := toAmbient_ofLp p
  have h1 : x.1 = 1 := by rw [← hh, ← hpx, height_toAmbient]
  have hnorm : x.1 ^ 2 + ‖x.2‖ ^ 2 = 1 := by
    have := norm_toAmbient_sq x
    rw [hpx, hp] at this
    simpa [SphericalProofRequest7A1.euclideanSquare] using this.symm
  have h2 : ‖x.2‖ = 0 := by nlinarith [norm_nonneg x.2]
  have h3 : x.2 = 0 := by simpa using h2
  rw [← hpx, north]
  congr 1
  exact Prod.ext h1 h3

/-- Away from the poles, a unit ambient vector is an actual radial arc endpoint for the
normalized direction of its horizontal part. -/
lemma exists_radial_normal_form {p : Ambient V} (hp : ‖p‖ = 1) (hlow : -1 < height p)
    (hhigh : height p < 1) :
    ∃ e : V, ‖e‖ = 1 ∧ p = radialCurve e (Real.arccos (height p)) := by
  set x : Real × V := WithLp.ofLp p with hx
  have hpx : toAmbient x = p := toAmbient_ofLp p
  have h1 : x.1 = height p := by rw [← hpx, height_toAmbient]
  have hnorm : x.1 ^ 2 + ‖x.2‖ ^ 2 = 1 := by
    have := norm_toAmbient_sq x
    rw [hpx, hp] at this
    simpa [SphericalProofRequest7A1.euclideanSquare] using this.symm
  have hx2pos : 0 < ‖x.2‖ := by
    rcases eq_or_lt_of_le (norm_nonneg x.2) with h | h
    · exfalso
      rw [h1] at hnorm
      nlinarith
    · exact h
  set r := Real.arccos (height p) with hr
  have hcos : Real.cos r = height p := Real.cos_arccos (by linarith) (by linarith)
  have hsin : Real.sin r = ‖x.2‖ := by
    rw [hr, Real.sin_arccos]
    rw [← h1]
    have : 1 - x.1 ^ 2 = ‖x.2‖ ^ 2 := by linarith
    rw [this, Real.sqrt_sq (norm_nonneg _)]
  refine ⟨‖x.2‖⁻¹ • x.2, ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm]
    field_simp
  · rw [radialCurve_apply, ← hpx]
    congr 1
    refine Prod.ext ?_ ?_
    · simpa using (h1.trans hcos.symm)
    · rw [hsin, smul_smul, mul_inv_cancel₀ (ne_of_gt hx2pos), one_smul]

/-- G4.  For a unit ambient vector strictly above the antipode, the intrinsic path distance
from the north pole is `arccos (height p)`, it is finite, and the 7B.4 angular potential is
half its square.  The north pole itself is included, through the constant path. -/
theorem north_distance : GoalNorthDistance V := by
  intro p hp hlow
  have hle : height p ≤ 1 := by
    have := real_inner_le_norm (north : Ambient V) p
    rw [norm_north, hp] at this
    simpa [height] using this
  have hmain : spherePathEDist north p = ENNReal.ofReal (Real.arccos (height p)) := by
    rcases eq_or_lt_of_le hle with heq | hlt
    · have hpn : p = north := eq_north_of_height_one hp heq
      rw [heq, Real.arccos_one, hpn, spherePathEDist_north_self]
      simp
    · obtain ⟨e, he, hpe⟩ := exists_radial_normal_form hp hlow hlt
      have h0 : 0 ≤ Real.arccos (height p) := Real.arccos_nonneg _
      have hpi : Real.arccos (height p) ≤ Real.pi := Real.arccos_le_pi _
      have hkey := (radial_minimizer (V := V) e he (Real.arccos (height p)) h0 hpi).2.2
      rw [← hpe] at hkey
      exact hkey
  refine ⟨hmain, ?_, ?_⟩
  · rw [hmain]; exact ENNReal.ofReal_ne_top
  · rw [hmain, ENNReal.toReal_ofReal (Real.arccos_nonneg _), angularPotential]

/-! ### Concrete sanity checks in a one-dimensional Euclidean model

`V = EuclideanSpace ℝ (Fin 1)` with `e = EuclideanSpace.single 0 1` gives an actual unit
direction, hence an actual great circle through the north pole, its equator point and its
antipode. -/

section Concrete

/-- The chosen concrete unit direction. -/
noncomputable def testDir : EuclideanSpace Real (Fin 1) := EuclideanSpace.single 0 1

lemma norm_testDir : ‖testDir‖ = 1 := by
  rw [testDir, PiLp.norm_single]
  norm_num

/-- The north pole is at path distance zero from itself; the radial arc at `r = 0` is the
constant path at the north pole. -/
lemma test_north :
    radialCurve testDir 0 = (north : Ambient (EuclideanSpace Real (Fin 1))) ∧
      spherePathEDist (north : Ambient (EuclideanSpace Real (Fin 1)))
        (radialCurve testDir 0) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [radialCurve, north]
    simp [SphericalProofRequest7A1.basePoint]
  · have := (radial_minimizer testDir norm_testDir 0 le_rfl Real.pi_pos.le).2.2
    rw [this]
    simp

/-- At the equator the intrinsic path distance is `π / 2`, strictly larger than the ambient
chord `√2` between the same two points. -/
lemma test_equator :
    spherePathEDist (north : Ambient (EuclideanSpace Real (Fin 1)))
        (radialCurve testDir (Real.pi / 2)) = ENNReal.ofReal (Real.pi / 2) ∧
      ‖(north : Ambient (EuclideanSpace Real (Fin 1))) - radialCurve testDir (Real.pi / 2)‖ =
        Real.sqrt 2 := by
  refine ⟨(radial_minimizer testDir norm_testDir (Real.pi / 2) (by positivity)
      (by linarith [Real.pi_pos])).2.2, ?_⟩
  have hinner : (inner Real (north : Ambient (EuclideanSpace Real (Fin 1)))
      (radialCurve testDir (Real.pi / 2)) : Real) = 0 := by
    rw [show (inner Real (north : Ambient (EuclideanSpace Real (Fin 1)))
        (radialCurve testDir (Real.pi / 2)) : Real) =
      height (radialCurve testDir (Real.pi / 2)) from rfl,
      height_radialCurve, Real.cos_pi_div_two]
  have hsq := norm_sub_sq_unit (p := (north : Ambient (EuclideanSpace Real (Fin 1))))
    (q := radialCurve testDir (Real.pi / 2)) norm_north
    (norm_radialCurve testDir norm_testDir _)
  rw [hinner] at hsq
  have h2 : ‖(north : Ambient (EuclideanSpace Real (Fin 1))) -
      radialCurve testDir (Real.pi / 2)‖ ^ 2 = 2 := by rw [hsq]; ring
  have h3 := congrArg Real.sqrt h2
  rwa [Real.sqrt_sq (norm_nonneg _)] at h3

/-- At the antipode, where an actual unit direction exists, the intrinsic path distance is
`π`. -/
lemma test_antipode :
    spherePathEDist (north : Ambient (EuclideanSpace Real (Fin 1)))
      (radialCurve testDir Real.pi) = ENNReal.ofReal Real.pi :=
  (radial_minimizer testDir norm_testDir Real.pi Real.pi_pos.le le_rfl).2.2

/-- The G4 potential at the north pole vanishes, consistently with distance zero. -/
lemma test_north_potential :
    angularPotential (north : Ambient (EuclideanSpace Real (Fin 1))) = 0 ∧
      spherePathEDist (north : Ambient (EuclideanSpace Real (Fin 1))) north = 0 := by
  have hh : height (north : Ambient (EuclideanSpace Real (Fin 1))) = 1 := by
    rw [height, north, inner_toAmbient]
    simp
  refine ⟨?_, spherePathEDist_north_self⟩
  rw [angularPotential, hh, Real.arccos_one]
  norm_num

end Concrete

end SphericalProofRequest7B5
