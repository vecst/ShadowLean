/-
Correlated derivative remainder, Phase A3D2: r/2 analytic coefficient and scaled
packet limit.

Phase A3D1 retained one shared Taylor coefficient beyond the target derivative
and proved the abstract normalized residual bound
  |D_(h,r) f(x) - (r! a_r + r! choose(r+1,2) a_(r+1) h)| <= (C/(r+2)!) |h|^2 W_r^(2).
This file specializes a to the analytic derivative jet from A3C: it simplifies
the exact next-term coefficient to (r/2) f^(r+1)(x), derives the A3D1 nodewise
degree-(r+2) certificate from Lagrange remainder under global C^(r+2) regularity
and a global uniform bound on f^(r+2), proves the explicit real second-order
derivative error and the scaled real limit
  (D_(h,r) f(x) - f^(r)(x))/h -> (r/2) f^(r+1)(x),
and transfers both to the normalized complex packet under r < g.

The global-regularity and global-bound hypotheses are deliberate: this is NOT a
local compact-interval theorem.
-/
import RequestProject.PacketDerivativeSecondRemainder
import RequestProject.PacketDerivativeConvergence

open scoped BigOperators Topology

namespace ResidueSlices

/-- Auxiliary: on a set with unique differentiability containing the base point,
the Mathlib Taylor polynomial of degree `r + 1` of a globally `C^(r+2)` function
agrees with the centered degree-`(r+1)` polynomial of the analytic derivative
jet.  (This reproduces, one degree higher, the corresponding private helper of
Phase A3C.) -/
private theorem taylorWithinEval_eq_centeredJetPolynomial_derivativeJet_succ
    {r : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ (r + 2) f)
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s) {x : ℝ} (hx : x ∈ s) (y : ℝ) :
    taylorWithinEval f (r + 1) s x y =
      centeredJetPolynomial (r + 1) (derivativeJet f x) x y := by
  rw [taylor_within_apply]
  unfold centeredJetPolynomial derivativeJet
  refine Finset.sum_congr rfl ?_
  intro m hm
  have hmr : m ≤ r + 2 := le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))
    (Nat.le_succ (r + 1))
  have hle : (m : WithTop ℕ∞) ≤ ((r + 2 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast hmr
  have hle' : (m : WithTop ℕ∞) ≤ (r : WithTop ℕ∞) + 2 := by
    simpa using hle
  rw [iteratedDerivWithin_eq_iteratedDeriv hs ((hf.of_le hle').contDiffAt) hx,
    smul_eq_mul]
  ring

/-- Auxiliary: the degree-`(r+2)` Lagrange remainder bound at a node strictly to
the right of the base point. -/
private theorem abs_sub_centeredJetPolynomial_derivativeJet_succ_le_of_lt
    {r : ℕ} {f : ℝ → ℝ} {x y C : ℝ} (hxy : x < y)
    (hf : ContDiff ℝ (r + 2) f)
    (hC : ∀ z : ℝ, |iteratedDeriv (r + 2) f z| ≤ C) :
    |f y - centeredJetPolynomial (r + 1) (derivativeJet f x) x y| ≤
      C * |y - x| ^ (r + 2) / (Nat.factorial (r + 2) : ℝ) := by
  have hf' : ContDiff ℝ (((r + 1 : ℕ) : WithTop ℕ∞) + 1) f := by
    refine hf.of_le ?_
    push_cast
    exact le_of_eq (by ring)
  obtain ⟨z, -, hEq⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (n := r + 1) hxy.ne hf'.contDiffOn
  rw [Set.uIcc_of_le hxy.le] at hEq
  rw [taylorWithinEval_eq_centeredJetPolynomial_derivativeJet_succ hf
      (s := Set.Icc x y) (uniqueDiffOn_Icc hxy)
      (Set.left_mem_Icc.mpr hxy.le)] at hEq
  rw [hEq, abs_div, abs_mul, abs_pow,
    abs_of_pos (show (0 : ℝ) < (Nat.factorial (r + 1 + 1) : ℝ) by positivity)]
  gcongr
  exact hC z

/-- Auxiliary: the degree-`(r+2)` Lagrange remainder bound at an arbitrary node,
obtained from the right-hand case by reflection through the base point. -/
private theorem abs_sub_centeredJetPolynomial_derivativeJet_succ_le
    {r : ℕ} {f : ℝ → ℝ} {x y C : ℝ}
    (hf : ContDiff ℝ (r + 2) f)
    (hC : ∀ z : ℝ, |iteratedDeriv (r + 2) f z| ≤ C) :
    |f y - centeredJetPolynomial (r + 1) (derivativeJet f x) x y| ≤
      C * |y - x| ^ (r + 2) / (Nat.factorial (r + 2) : ℝ) := by
  rcases lt_trichotomy y x with hlt | heq | hgt
  · -- reflect: apply the right-hand case to `F z = f (2x - z)` at `2x - y`.
    set F : ℝ → ℝ := fun z => f (2 * x - z) with hFdef
    have hFc : ContDiff ℝ (r + 2) F :=
      hf.comp (contDiff_const.sub contDiff_id)
    have hFd : ∀ (m : ℕ) (t : ℝ),
        iteratedDeriv m F t = (-1 : ℝ) ^ m * iteratedDeriv m f (2 * x - t) := by
      intro m t
      have h := congrFun (iteratedDeriv_comp_const_sub m f (2 * x)) t
      simpa [hFdef, smul_eq_mul] using h
    have hCF : ∀ z : ℝ, |iteratedDeriv (r + 2) F z| ≤ C := by
      intro z
      rw [hFd, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact hC _
    have hkey := abs_sub_centeredJetPolynomial_derivativeJet_succ_le_of_lt
      (x := x) (y := 2 * x - y) (by linarith) hFc hCF
    have h1 : F (2 * x - y) = f y := by
      have h2xy : 2 * x - (2 * x - y) = y := by ring
      simp [hFdef, h2xy]
    have h2 : centeredJetPolynomial (r + 1) (derivativeJet F x) x (2 * x - y) =
        centeredJetPolynomial (r + 1) (derivativeJet f x) x y := by
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
    have hself : centeredJetPolynomial (r + 1) (derivativeJet f x) x y = f y := by
      unfold centeredJetPolynomial
      rw [heq]
      rw [Finset.sum_eq_single 0]
      · simp [derivativeJet]
      · intro m _ hm0
        rw [sub_self, zero_pow hm0, mul_zero]
      · intro h0
        exact absurd (Finset.mem_range.mpr (Nat.succ_pos (r + 1))) h0
    rw [hself, sub_self, abs_zero, heq, sub_self, abs_zero,
      zero_pow (Nat.succ_ne_zero (r + 1)), mul_zero, zero_div]
  · exact abs_sub_centeredJetPolynomial_derivativeJet_succ_le_of_lt hgt hf hC

theorem factorial_choose_mul_derivativeJet_succ
    (r : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    (Nat.factorial r : ℝ) * (Nat.choose (r + 1) 2 : ℝ) *
        derivativeJet f x (r + 1) =
      (r : ℝ) / 2 * iteratedDeriv (r + 1) f x := by
  unfold derivativeJet
  have hchoose : ((Nat.choose (r + 1) 2 : ℕ) : ℝ) = ((r : ℝ) + 1) * (r : ℝ) / 2 := by
    rw [Nat.cast_choose_two]
    push_cast
    ring
  have hfac : ((Nat.factorial (r + 1) : ℕ) : ℝ)
      = ((r : ℝ) + 1) * (Nat.factorial r : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have h1 : ((r : ℝ) + 1) ≠ 0 := by positivity
  have h2 : ((Nat.factorial r : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)
  rw [hchoose, hfac]
  field_simp

theorem hasCenteredJetSecondRemainderAtNodes_derivativeJet
    {r : ℕ} {f : ℝ → ℝ} {x h C : ℝ}
    (hf : ContDiff ℝ (r + 2) f)
    (hC : ∀ y : ℝ, |iteratedDeriv (r + 2) f y| ≤ C) :
    HasCenteredJetSecondRemainderAtNodes r f
      (derivativeJet f x) x h C := by
  intro j _
  have hb := abs_sub_centeredJetPolynomial_derivativeJet_succ_le
    (x := x) (y := x + (j : ℝ) * h) hf hC
  have hnode : x + (j : ℝ) * h - x = (j : ℝ) * h := by ring
  rw [hnode] at hb
  exact hb

theorem normalizedForwardDiff_iteratedDeriv_second_error_le
    {r : ℕ} {f : ℝ → ℝ} {x h C : ℝ}
    (hh : h ≠ 0) (hC0 : 0 ≤ C)
    (hf : ContDiff ℝ (r + 2) f)
    (hC : ∀ y : ℝ, |iteratedDeriv (r + 2) f y| ≤ C) :
    |normalizedForwardDiff r f x h - iteratedDeriv r f x -
        ((r : ℝ) / 2 * h * iteratedDeriv (r + 1) f x)| ≤
      (C / (Nat.factorial (r + 2) : ℝ)) * |h| ^ 2 *
        forwardDiffSecondRemainderWeight r := by
  have hb := normalizedForwardDiff_second_error_le hh hC0
    (hasCenteredJetSecondRemainderAtNodes_derivativeJet (x := x) (h := h) hf hC)
  have hcoeff : (Nat.factorial r : ℝ) * (Nat.choose (r + 1) 2 : ℝ) *
      derivativeJet f x (r + 1) * h =
        (r : ℝ) / 2 * h * iteratedDeriv (r + 1) f x := by
    rw [factorial_choose_mul_derivativeJet_succ]
    ring
  rw [factorial_mul_derivativeJet, hcoeff] at hb
  have hrearrange : normalizedForwardDiff r f x h - iteratedDeriv r f x -
      ((r : ℝ) / 2 * h * iteratedDeriv (r + 1) f x)
      = normalizedForwardDiff r f x h -
        (iteratedDeriv r f x + (r : ℝ) / 2 * h * iteratedDeriv (r + 1) f x) := by
    ring
  rw [hrearrange]
  exact hb

theorem tendsto_scaled_normalizedForwardDiff_error
    {r : ℕ} {f : ℝ → ℝ} {x C : ℝ}
    (hC0 : 0 ≤ C)
    (hf : ContDiff ℝ (r + 2) f)
    (hC : ∀ y : ℝ, |iteratedDeriv (r + 2) f y| ≤ C) :
    Filter.Tendsto
      (fun h : ℝ =>
        (normalizedForwardDiff r f x h - iteratedDeriv r f x) / h)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhds ((r : ℝ) / 2 * iteratedDeriv (r + 1) f x)) := by
  set K : ℝ := (C / (Nat.factorial (r + 2) : ℝ)) *
    forwardDiffSecondRemainderWeight r with hK
  have hbound : ∀ᶠ h : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
      |(normalizedForwardDiff r f x h - iteratedDeriv r f x) / h -
        (r : ℝ) / 2 * iteratedDeriv (r + 1) f x| ≤ K * |h| := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh0 : h ≠ 0 := hh
    have hb := normalizedForwardDiff_iteratedDeriv_second_error_le hh0 hC0 hf hC
      (x := x)
    have hkey : (normalizedForwardDiff r f x h - iteratedDeriv r f x) / h -
        (r : ℝ) / 2 * iteratedDeriv (r + 1) f x
        = (normalizedForwardDiff r f x h - iteratedDeriv r f x -
            ((r : ℝ) / 2 * h * iteratedDeriv (r + 1) f x)) / h := by
      field_simp
    rw [hkey, abs_div, div_le_iff₀ (abs_pos.mpr hh0)]
    calc |normalizedForwardDiff r f x h - iteratedDeriv r f x -
            ((r : ℝ) / 2 * h * iteratedDeriv (r + 1) f x)|
        ≤ (C / (Nat.factorial (r + 2) : ℝ)) * |h| ^ 2 *
            forwardDiffSecondRemainderWeight r := hb
      _ = K * |h| * |h| := by rw [hK]; ring
  have htend : Filter.Tendsto (fun h : ℝ => K * |h|)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    have hcont : Continuous fun h : ℝ => K * |h| :=
      continuous_const.mul continuous_abs
    have h0 : Filter.Tendsto (fun h : ℝ => K * |h|) (nhds 0) (nhds 0) := by
      simpa using hcont.tendsto (0 : ℝ)
    exact h0.mono_left nhdsWithin_le_nhds
  have hzero : Filter.Tendsto
      (fun h : ℝ => |(normalizedForwardDiff r f x h - iteratedDeriv r f x) / h -
        (r : ℝ) / 2 * iteratedDeriv (r + 1) f x|)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun _ => abs_nonneg _) hbound htend
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa [Real.norm_eq_abs] using hzero

theorem normalizedForwardDiffPacket_iteratedDeriv_second_error_le
    {g r : ℕ} [NeZero g] (hrg : r < g)
    {f : ℝ → ℝ} {x h C : ℝ}
    (hh : h ≠ 0) (hC0 : 0 ≤ C)
    (hf : ContDiff ℝ (r + 2) f)
    (hC : ∀ y : ℝ, |iteratedDeriv (r + 2) f y| ≤ C) :
    ‖normalizedForwardDiffPacket (g := g) r f x h -
        ((iteratedDeriv r f x : ℝ) : ℂ) -
        ((((r : ℝ) / 2 * h * iteratedDeriv (r + 1) f x : ℝ)) : ℂ)‖ ≤
      (C / (Nat.factorial (r + 2) : ℝ)) * |h| ^ 2 *
        forwardDiffSecondRemainderWeight r := by
  rw [normalizedForwardDiffPacket_eq hrg, ← Complex.ofReal_sub,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact normalizedForwardDiff_iteratedDeriv_second_error_le hh hC0 hf hC

theorem tendsto_scaled_normalizedForwardDiffPacket_error
    {g r : ℕ} [NeZero g] (hrg : r < g)
    {f : ℝ → ℝ} {x C : ℝ}
    (hC0 : 0 ≤ C)
    (hf : ContDiff ℝ (r + 2) f)
    (hC : ∀ y : ℝ, |iteratedDeriv (r + 2) f y| ≤ C) :
    Filter.Tendsto
      (fun h : ℝ =>
        (normalizedForwardDiffPacket (g := g) r f x h -
          ((iteratedDeriv r f x : ℝ) : ℂ)) / (h : ℂ))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhds ((((r : ℝ) / 2 * iteratedDeriv (r + 1) f x : ℝ)) : ℂ)) := by
  have hreal := tendsto_scaled_normalizedForwardDiff_error (x := x) hC0 hf hC
  have hcomp : Filter.Tendsto
      (fun h : ℝ =>
        (((normalizedForwardDiff r f x h - iteratedDeriv r f x) / h : ℝ) : ℂ))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhds ((((r : ℝ) / 2 * iteratedDeriv (r + 1) f x : ℝ)) : ℂ)) :=
    (Complex.continuous_ofReal.continuousAt.tendsto).comp hreal
  refine hcomp.congr ?_
  intro h
  rw [Complex.ofReal_div, Complex.ofReal_sub, normalizedForwardDiffPacket_eq hrg]

end ResidueSlices
