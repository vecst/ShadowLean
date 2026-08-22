/-
Analytic derivative bridge, Phase A3B: explicit nodewise Taylor-remainder
certificate.

Phase A3A established the ordinary unwrapped order-r forward difference, its h^r
normalization, the exact r < g no-wrap packet bridge, and exact response on
centered polynomials through degree r. This file turns that exact polynomial
response into a reusable error certificate: the full absolute stencil weight
(no hidden constant), a nodewise centered Taylor-remainder predicate with the
standard (r+1)! denominator, the stencil error expressed exactly as the signed
sum of node remainders, an explicit unnormalized remainder bound, and its
h^r-normalized O(|h|) form.

This phase does NOT assume differentiability and does NOT prove h -> 0
convergence. Phase A3C will use Mathlib's Taylor theorem to construct the
nodewise certificate from an (r+1)-derivative bound and specialize the top jet
coefficient to the r-th derivative.
-/
import RequestProject.PacketDerivativeUnwrapped

open scoped BigOperators

namespace ResidueSlices

noncomputable def forwardDiffRemainderWeight (r : ℕ) : ℝ :=
  Finset.sum (Finset.range (r + 1)) (fun j =>
    (Nat.choose r j : ℝ) * (j : ℝ) ^ (r + 1))

def HasCenteredJetRemainderAtNodes (r : ℕ) (f : ℝ → ℝ)
    (a : ℕ → ℝ) (x h C : ℝ) : Prop :=
  ∀ j ∈ Finset.range (r + 1),
    |f (x + (j : ℝ) * h) -
        centeredJetPolynomial r a x (x + (j : ℝ) * h)| ≤
      C * |(j : ℝ) * h| ^ (r + 1) /
        (Nat.factorial (r + 1) : ℝ)

theorem forwardDiffRemainderWeight_nonneg (r : ℕ) :
    0 ≤ forwardDiffRemainderWeight r := by
  unfold forwardDiffRemainderWeight
  refine Finset.sum_nonneg ?_
  intro j _
  have h1 : (0 : ℝ) ≤ (Nat.choose r j : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ (j : ℝ) ^ (r + 1) := pow_nonneg (Nat.cast_nonneg _) _
  exact mul_nonneg h1 h2

theorem unwrappedForwardDiff_sub_jet_eq_remainder_sum
    (r : ℕ) (f : ℝ → ℝ) (a : ℕ → ℝ) (x h : ℝ) :
    unwrappedForwardDiff r f x h -
        (Nat.factorial r : ℝ) * a r * h ^ r =
      Finset.sum (Finset.range (r + 1)) (fun j =>
        (forwardDiffCoeff r j : ℝ) *
          (f (x + (j : ℝ) * h) -
            centeredJetPolynomial r a x (x + (j : ℝ) * h))) := by
  have hsplit : Finset.sum (Finset.range (r + 1)) (fun j =>
      (forwardDiffCoeff r j : ℝ) *
        (f (x + (j : ℝ) * h) -
          centeredJetPolynomial r a x (x + (j : ℝ) * h)))
      = Finset.sum (Finset.range (r + 1)) (fun j =>
          (forwardDiffCoeff r j : ℝ) * f (x + (j : ℝ) * h))
        - Finset.sum (Finset.range (r + 1)) (fun j =>
          (forwardDiffCoeff r j : ℝ) *
            centeredJetPolynomial r a x (x + (j : ℝ) * h)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  rw [hsplit]
  have hf : Finset.sum (Finset.range (r + 1)) (fun j =>
      (forwardDiffCoeff r j : ℝ) * f (x + (j : ℝ) * h))
      = unwrappedForwardDiff r f x h := rfl
  have hp : Finset.sum (Finset.range (r + 1)) (fun j =>
      (forwardDiffCoeff r j : ℝ) *
        centeredJetPolynomial r a x (x + (j : ℝ) * h))
      = unwrappedForwardDiff r (centeredJetPolynomial r a x) x h := rfl
  rw [hf, hp, unwrappedForwardDiff_centeredJetPolynomial]

theorem unwrappedForwardDiff_error_le
    {r : ℕ} {f : ℝ → ℝ} {a : ℕ → ℝ} {x h C : ℝ}
    (hC : 0 ≤ C)
    (hrem : HasCenteredJetRemainderAtNodes r f a x h C) :
    |unwrappedForwardDiff r f x h -
        (Nat.factorial r : ℝ) * a r * h ^ r| ≤
      (C * |h| ^ (r + 1) /
          (Nat.factorial (r + 1) : ℝ)) *
        forwardDiffRemainderWeight r := by
  -- `hC` is part of the requested interface; the bound itself needs only `hrem`.
  have _hCnonneg : (0 : ℝ) ≤ C := hC
  rw [unwrappedForwardDiff_sub_jet_eq_remainder_sum r f a x h]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have habsCoeff : ∀ j : ℕ,
      |(forwardDiffCoeff r j : ℝ)| = (Nat.choose r j : ℝ) := by
    intro j
    unfold forwardDiffCoeff
    push_cast
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Nat.choose r j : ℝ))]
  have hterm : ∀ j ∈ Finset.range (r + 1),
      |(forwardDiffCoeff r j : ℝ) *
        (f (x + (j : ℝ) * h) -
          centeredJetPolynomial r a x (x + (j : ℝ) * h))| ≤
      (C * |h| ^ (r + 1) / (Nat.factorial (r + 1) : ℝ)) *
        ((Nat.choose r j : ℝ) * (j : ℝ) ^ (r + 1)) := by
    intro j hj
    rw [abs_mul, habsCoeff j]
    have hb := hrem j hj
    have habs : |(j : ℝ) * h| ^ (r + 1)
        = (j : ℝ) ^ (r + 1) * |h| ^ (r + 1) := by
      rw [abs_mul, mul_pow, abs_of_nonneg (Nat.cast_nonneg j : (0:ℝ) ≤ (j : ℝ))]
    rw [habs] at hb
    have hcnn : (0 : ℝ) ≤ (Nat.choose r j : ℝ) := Nat.cast_nonneg _
    calc (Nat.choose r j : ℝ) *
            |f (x + (j : ℝ) * h) -
              centeredJetPolynomial r a x (x + (j : ℝ) * h)|
        ≤ (Nat.choose r j : ℝ) *
            (C * ((j : ℝ) ^ (r + 1) * |h| ^ (r + 1)) /
              (Nat.factorial (r + 1) : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hb hcnn
      _ = (C * |h| ^ (r + 1) / (Nat.factorial (r + 1) : ℝ)) *
            ((Nat.choose r j : ℝ) * (j : ℝ) ^ (r + 1)) := by
          ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  unfold forwardDiffRemainderWeight
  rw [Finset.mul_sum]

theorem normalizedForwardDiff_sub_jet_eq_div
    (r : ℕ) (f : ℝ → ℝ) (a : ℕ → ℝ) (x : ℝ)
    {h : ℝ} (hh : h ≠ 0) :
    normalizedForwardDiff r f x h -
        (Nat.factorial r : ℝ) * a r =
      (unwrappedForwardDiff r f x h -
          (Nat.factorial r : ℝ) * a r * h ^ r) / h ^ r := by
  have hpow : h ^ r ≠ 0 := pow_ne_zero _ hh
  unfold normalizedForwardDiff
  field_simp

theorem normalizedForwardDiff_error_le
    {r : ℕ} {f : ℝ → ℝ} {a : ℕ → ℝ} {x h C : ℝ}
    (hh : h ≠ 0) (hC : 0 ≤ C)
    (hrem : HasCenteredJetRemainderAtNodes r f a x h C) :
    |normalizedForwardDiff r f x h -
        (Nat.factorial r : ℝ) * a r| ≤
      (C / (Nat.factorial (r + 1) : ℝ)) * |h| *
        forwardDiffRemainderWeight r := by
  have hpow : (0 : ℝ) < |h| ^ r := pow_pos (abs_pos.mpr hh) r
  rw [normalizedForwardDiff_sub_jet_eq_div r f a x hh, abs_div, abs_pow]
  rw [div_le_iff₀ hpow]
  refine le_trans (unwrappedForwardDiff_error_le hC hrem) (le_of_eq ?_)
  rw [pow_succ]
  ring

end ResidueSlices
