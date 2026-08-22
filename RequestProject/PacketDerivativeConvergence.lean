/-
Analytic derivative bridge, Phase A3C: Taylor certificate, explicit derivative
error, and packet convergence.

Phase A3A connected the cyclic packet to the ordinary unwrapped stencil under
the exact anti-wrap condition r < g and proved exact response on centered
polynomials. Phase A3B proved an explicit error estimate from a nodewise
Taylor-remainder certificate. This file closes the analytic bridge: under global
C^(r+1) regularity and a global uniform bound C on the absolute (r+1)-st
iterated derivative, it constructs the A3B certificate from Lagrange remainder,
specializes to the r-th analytic derivative, proves h -> 0 convergence on the
punctured neighborhood, and transfers everything through the r < g no-wrap
bridge to the complex cyclic packet.

The global-regularity and global-bound hypotheses are deliberate: they give a
clean first complete theorem with no hidden neighborhood selector. This is NOT a
local compact-interval statement.
-/
import RequestProject.PacketDerivativeRemainder
import Mathlib.Analysis.Calculus.Taylor

open scoped BigOperators Topology

namespace ResidueSlices

noncomputable def derivativeJet (f : ℝ → ℝ) (x : ℝ) (m : ℕ) : ℝ :=
  iteratedDeriv m f x / (Nat.factorial m : ℝ)

noncomputable def normalizedForwardDiffPacket {g : ℕ} [NeZero g]
    (r : ℕ) (f : ℝ → ℝ) (x h : ℝ) : ℂ :=
  forwardDiffPacket r (@realSamplePacket g _ f x h) / (h : ℂ) ^ r

theorem factorial_mul_derivativeJet (r : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    (Nat.factorial r : ℝ) * derivativeJet f x r =
      iteratedDeriv r f x := by
  unfold derivativeJet
  have hfac : (Nat.factorial r : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero r
  field_simp

theorem centeredJetPolynomial_derivativeJet_eq_taylor
    (r : ℕ) (f : ℝ → ℝ) (x y : ℝ) :
    centeredJetPolynomial r (derivativeJet f x) x y =
      taylorWithinEval f r Set.univ x y := by
  rw [taylor_within_apply]
  unfold centeredJetPolynomial derivativeJet
  refine Finset.sum_congr rfl ?_
  intro m _
  rw [iteratedDerivWithin_univ, smul_eq_mul]
  ring

/-- Auxiliary: on a set with unique differentiability containing the base point,
the Mathlib Taylor polynomial of a globally `C^(r+1)` function agrees with the
centered polynomial of the analytic derivative jet. -/
private theorem taylorWithinEval_eq_centeredJetPolynomial_derivativeJet
    {r : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ (r + 1) f)
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s) {x : ℝ} (hx : x ∈ s) (y : ℝ) :
    taylorWithinEval f r s x y =
      centeredJetPolynomial r (derivativeJet f x) x y := by
  rw [taylor_within_apply]
  unfold centeredJetPolynomial derivativeJet
  refine Finset.sum_congr rfl ?_
  intro m hm
  have hmr : m ≤ r + 1 := le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))
    (Nat.le_succ r)
  have hle : (m : WithTop ℕ∞) ≤ ((r + 1 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast hmr
  rw [iteratedDerivWithin_eq_iteratedDeriv hs ((hf.of_le hle).contDiffAt) hx,
    smul_eq_mul]
  ring

/-- Auxiliary: the Lagrange remainder bound at a node strictly to the right of
the base point. -/
private theorem abs_sub_centeredJetPolynomial_derivativeJet_le_of_lt
    {r : ℕ} {f : ℝ → ℝ} {x y C : ℝ} (hxy : x < y)
    (hf : ContDiff ℝ (r + 1) f)
    (hC : ∀ z : ℝ, |iteratedDeriv (r + 1) f z| ≤ C) :
    |f y - centeredJetPolynomial r (derivativeJet f x) x y| ≤
      C * |y - x| ^ (r + 1) / (Nat.factorial (r + 1) : ℝ) := by
  obtain ⟨z, -, hEq⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv hxy.ne hf.contDiffOn
  rw [Set.uIcc_of_le hxy.le] at hEq
  rw [taylorWithinEval_eq_centeredJetPolynomial_derivativeJet hf
      (s := Set.Icc x y) (uniqueDiffOn_Icc hxy)
      (Set.left_mem_Icc.mpr hxy.le)] at hEq
  rw [hEq, abs_div, abs_mul, abs_pow,
    abs_of_pos (show (0 : ℝ) < (Nat.factorial (r + 1) : ℝ) by positivity)]
  gcongr
  exact hC z

/-- Auxiliary: the Lagrange remainder bound at an arbitrary node, obtained from
the right-hand case by reflection through the base point. -/
private theorem abs_sub_centeredJetPolynomial_derivativeJet_le
    {r : ℕ} {f : ℝ → ℝ} {x y C : ℝ}
    (hf : ContDiff ℝ (r + 1) f)
    (hC : ∀ z : ℝ, |iteratedDeriv (r + 1) f z| ≤ C) :
    |f y - centeredJetPolynomial r (derivativeJet f x) x y| ≤
      C * |y - x| ^ (r + 1) / (Nat.factorial (r + 1) : ℝ) := by
  rcases lt_trichotomy y x with hlt | heq | hgt
  · -- reflect: apply the right-hand case to `F z = f (2x - z)` at `2x - y`.
    set F : ℝ → ℝ := fun z => f (2 * x - z) with hFdef
    have hFc : ContDiff ℝ (r + 1) F :=
      hf.comp (contDiff_const.sub contDiff_id)
    have hFd : ∀ (m : ℕ) (t : ℝ),
        iteratedDeriv m F t = (-1 : ℝ) ^ m * iteratedDeriv m f (2 * x - t) := by
      intro m t
      have h := congrFun (iteratedDeriv_comp_const_sub m f (2 * x)) t
      simpa [hFdef, smul_eq_mul] using h
    have hCF : ∀ z : ℝ, |iteratedDeriv (r + 1) F z| ≤ C := by
      intro z
      rw [hFd, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact hC _
    have hkey := abs_sub_centeredJetPolynomial_derivativeJet_le_of_lt
      (x := x) (y := 2 * x - y) (by linarith) hFc hCF
    have h1 : F (2 * x - y) = f y := by
      have : 2 * x - (2 * x - y) = y := by ring
      simp [hFdef, this]
    have h2 : centeredJetPolynomial r (derivativeJet F x) x (2 * x - y) =
        centeredJetPolynomial r (derivativeJet f x) x y := by
      unfold centeredJetPolynomial derivativeJet
      refine Finset.sum_congr rfl ?_
      intro m _
      have hsq : ((-1 : ℝ) ^ m) * ((-1 : ℝ) ^ m) = 1 := by
        rw [← mul_pow]; norm_num
      have hxx : (2 : ℝ) * x - x = x := by ring
      have hneg : (2 * x - y - x) ^ m = (-1 : ℝ) ^ m * (y - x) ^ m := by
        rw [show 2 * x - y - x = -(y - x) by ring, neg_pow]
      rw [hFd m x, hxx, hneg]
      calc (-1 : ℝ) ^ m * iteratedDeriv m f x / (Nat.factorial m : ℝ) *
              ((-1 : ℝ) ^ m * (y - x) ^ m)
          = ((-1 : ℝ) ^ m * (-1 : ℝ) ^ m) *
              (iteratedDeriv m f x / (Nat.factorial m : ℝ) * (y - x) ^ m) := by
            ring
        _ = iteratedDeriv m f x / (Nat.factorial m : ℝ) * (y - x) ^ m := by
            rw [hsq, one_mul]
    have h3 : |2 * x - y - x| = |y - x| := by
      rw [show 2 * x - y - x = -(y - x) by ring, abs_neg]
    rw [h1, h2, h3] at hkey
    exact hkey
  · -- degenerate node: both sides vanish
    have hself : centeredJetPolynomial r (derivativeJet f x) x y = f y := by
      unfold centeredJetPolynomial
      rw [heq]
      rw [Finset.sum_eq_single 0]
      · simp [derivativeJet]
      · intro m _ hm0
        rw [sub_self, zero_pow hm0, mul_zero]
      · intro h0
        exact absurd (Finset.mem_range.mpr (Nat.succ_pos r)) h0
    rw [hself, sub_self, abs_zero, heq, sub_self, abs_zero,
      zero_pow (Nat.succ_ne_zero r), mul_zero, zero_div]
  · exact abs_sub_centeredJetPolynomial_derivativeJet_le_of_lt hgt hf hC

theorem hasCenteredJetRemainderAtNodes_derivativeJet
    {r : ℕ} {f : ℝ → ℝ} {x h C : ℝ}
    (hf : ContDiff ℝ (r + 1) f)
    (hC : ∀ y : ℝ, |iteratedDeriv (r + 1) f y| ≤ C) :
    HasCenteredJetRemainderAtNodes r f (derivativeJet f x) x h C := by
  intro j _
  have hb := abs_sub_centeredJetPolynomial_derivativeJet_le
    (x := x) (y := x + (j : ℝ) * h) hf hC
  have hnode : x + (j : ℝ) * h - x = (j : ℝ) * h := by ring
  rw [hnode] at hb
  exact hb

theorem normalizedForwardDiff_iteratedDeriv_error_le
    {r : ℕ} {f : ℝ → ℝ} {x h C : ℝ}
    (hh : h ≠ 0) (hC0 : 0 ≤ C)
    (hf : ContDiff ℝ (r + 1) f)
    (hC : ∀ y : ℝ, |iteratedDeriv (r + 1) f y| ≤ C) :
    |normalizedForwardDiff r f x h - iteratedDeriv r f x| ≤
      (C / (Nat.factorial (r + 1) : ℝ)) * |h| *
        forwardDiffRemainderWeight r := by
  have hb := normalizedForwardDiff_error_le hh hC0
    (hasCenteredJetRemainderAtNodes_derivativeJet (x := x) (h := h) hf hC)
  rwa [factorial_mul_derivativeJet] at hb

theorem tendsto_normalizedForwardDiff_iteratedDeriv
    {r : ℕ} {f : ℝ → ℝ} {x C : ℝ}
    (hC0 : 0 ≤ C)
    (hf : ContDiff ℝ (r + 1) f)
    (hC : ∀ y : ℝ, |iteratedDeriv (r + 1) f y| ≤ C) :
    Filter.Tendsto (fun h : ℝ => normalizedForwardDiff r f x h)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhds (iteratedDeriv r f x)) := by
  set K : ℝ := (C / (Nat.factorial (r + 1) : ℝ)) *
    forwardDiffRemainderWeight r with hK
  have hbound : ∀ᶠ h : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
      |normalizedForwardDiff r f x h - iteratedDeriv r f x| ≤ K * |h| := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh0 : h ≠ 0 := hh
    have hb := normalizedForwardDiff_iteratedDeriv_error_le hh0 hC0 hf hC
      (x := x)
    calc |normalizedForwardDiff r f x h - iteratedDeriv r f x|
        ≤ (C / (Nat.factorial (r + 1) : ℝ)) * |h| *
            forwardDiffRemainderWeight r := hb
      _ = K * |h| := by rw [hK]; ring
  have htend : Filter.Tendsto (fun h : ℝ => K * |h|)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    have hcont : Continuous fun h : ℝ => K * |h| :=
      continuous_const.mul continuous_abs
    have h0 : Filter.Tendsto (fun h : ℝ => K * |h|) (nhds 0) (nhds 0) := by
      simpa using hcont.tendsto (0 : ℝ)
    exact h0.mono_left nhdsWithin_le_nhds
  have hzero : Filter.Tendsto
      (fun h : ℝ => |normalizedForwardDiff r f x h - iteratedDeriv r f x|)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun _ => abs_nonneg _) hbound htend
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa [Real.norm_eq_abs] using hzero

theorem normalizedForwardDiffPacket_eq
    {g r : ℕ} [NeZero g] (hrg : r < g)
    (f : ℝ → ℝ) (x h : ℝ) :
    normalizedForwardDiffPacket (g := g) r f x h =
      (normalizedForwardDiff r f x h : ℂ) := by
  unfold normalizedForwardDiffPacket normalizedForwardDiff
  rw [forwardDiffPacket_realSamplePacket_eq hrg, Complex.ofReal_div,
    Complex.ofReal_pow]

theorem normalizedForwardDiffPacket_iteratedDeriv_error_le
    {g r : ℕ} [NeZero g] (hrg : r < g)
    {f : ℝ → ℝ} {x h C : ℝ}
    (hh : h ≠ 0) (hC0 : 0 ≤ C)
    (hf : ContDiff ℝ (r + 1) f)
    (hC : ∀ y : ℝ, |iteratedDeriv (r + 1) f y| ≤ C) :
    ‖normalizedForwardDiffPacket (g := g) r f x h -
        ((iteratedDeriv r f x : ℝ) : ℂ)‖ ≤
      (C / (Nat.factorial (r + 1) : ℝ)) * |h| *
        forwardDiffRemainderWeight r := by
  rw [normalizedForwardDiffPacket_eq hrg, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  exact normalizedForwardDiff_iteratedDeriv_error_le hh hC0 hf hC

theorem tendsto_normalizedForwardDiffPacket_iteratedDeriv
    {g r : ℕ} [NeZero g] (hrg : r < g)
    {f : ℝ → ℝ} {x C : ℝ}
    (hC0 : 0 ≤ C)
    (hf : ContDiff ℝ (r + 1) f)
    (hC : ∀ y : ℝ, |iteratedDeriv (r + 1) f y| ≤ C) :
    Filter.Tendsto
      (fun h : ℝ => normalizedForwardDiffPacket (g := g) r f x h)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhds ((iteratedDeriv r f x : ℝ) : ℂ)) := by
  have hreal := tendsto_normalizedForwardDiff_iteratedDeriv (x := x) hC0 hf hC
  have hcomp : Filter.Tendsto
      (fun h : ℝ => ((normalizedForwardDiff r f x h : ℝ) : ℂ))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhds ((iteratedDeriv r f x : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.continuousAt.tendsto).comp hreal
  refine hcomp.congr ?_
  intro h
  exact (normalizedForwardDiffPacket_eq hrg f x h).symm

end ResidueSlices
