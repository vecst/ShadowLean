/-
Correlated derivative remainder, Phase A3D1: exact next Taylor term and O(h^2)
certificate.

The A3B certificate bounds each degree-r Taylor remainder independently in
absolute value; numerical stress testing showed this is conservative at high
order because it discards the signed correlation between stencil nodes. This
file retains ONE additional common Taylor coefficient: the absolute stencil
weight for degree-(r+2) residuals, a nodewise certificate relative to a shared
centered jet through degree r+1, the exact order-r stencil response to the
degree-(r+1) centered monomial and to the full jet through r+1, the remaining
error as a signed sum of degree-(r+2) node residuals, and explicit unnormalized
and normalized O(h^2) error bounds.

Finite algebra plus an abstract nodewise certificate: NO iteratedDeriv, ContDiff,
Taylor's theorem, g, or packet convergence. Phase A3D2 will specialize a to the
derivative jet, simplify the next-term coefficient choose(r+1,2) to r/2, and
transfer to the complex packet.
-/
import RequestProject.PacketDerivativeRemainder

open scoped BigOperators

namespace ResidueSlices

noncomputable def forwardDiffSecondRemainderWeight (r : ℕ) : ℝ :=
  Finset.sum (Finset.range (r + 1)) (fun j =>
    (Nat.choose r j : ℝ) * (j : ℝ) ^ (r + 2))

def HasCenteredJetSecondRemainderAtNodes (r : ℕ) (f : ℝ → ℝ)
    (a : ℕ → ℝ) (x h C : ℝ) : Prop :=
  ∀ j ∈ Finset.range (r + 1),
    |f (x + (j : ℝ) * h) -
        centeredJetPolynomial (r + 1) a x (x + (j : ℝ) * h)| ≤
      C * |(j : ℝ) * h| ^ (r + 2) /
        (Nat.factorial (r + 2) : ℝ)

theorem forwardDiffSecondRemainderWeight_nonneg (r : ℕ) :
    0 ≤ forwardDiffSecondRemainderWeight r := by
  unfold forwardDiffSecondRemainderWeight
  refine Finset.sum_nonneg ?_
  intro j _
  have h1 : (0 : ℝ) ≤ (Nat.choose r j : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ (j : ℝ) ^ (r + 2) := pow_nonneg (Nat.cast_nonneg _) _
  exact mul_nonneg h1 h2

theorem unwrappedForwardDiff_centeredMonomial_succ
    (r : ℕ) (x h : ℝ) :
    unwrappedForwardDiff r (fun y => (y - x) ^ (r + 1)) x h =
      (Nat.factorial r : ℝ) * (Nat.choose (r + 1) 2 : ℝ) *
        h ^ (r + 1) := by
  unfold unwrappedForwardDiff
  have hmom : (Finset.sum (Finset.range (r + 1)) (fun j =>
      (forwardDiffCoeff r j : ℝ) * (j : ℝ) ^ (r + 1)))
      = (Nat.factorial r : ℝ) * (Nat.choose (r + 1) 2 : ℝ) := by
    have h0 := forwardDiff_moment_eq_factorial_mul_stirlingSecond r (r + 1)
    rw [Nat.stirlingSecond_succ_self_left r] at h0
    have hcast := congrArg (fun z : ℤ => (z : ℝ)) h0
    push_cast at hcast
    exact hcast
  have hrw : (Finset.sum (Finset.range (r + 1)) (fun j =>
      (forwardDiffCoeff r j : ℝ) * ((x + (j : ℝ) * h) - x) ^ (r + 1)))
      = h ^ (r + 1) * Finset.sum (Finset.range (r + 1)) (fun j =>
        (forwardDiffCoeff r j : ℝ) * (j : ℝ) ^ (r + 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  rw [hrw, hmom]
  ring

theorem unwrappedForwardDiff_centeredJetPolynomial_succ
    (r : ℕ) (a : ℕ → ℝ) (x h : ℝ) :
    unwrappedForwardDiff r (centeredJetPolynomial (r + 1) a x) x h =
      (Nat.factorial r : ℝ) * a r * h ^ r +
        (Nat.factorial r : ℝ) * (Nat.choose (r + 1) 2 : ℝ) *
          a (r + 1) * h ^ (r + 1) := by
  have hsplit : unwrappedForwardDiff r (centeredJetPolynomial (r + 1) a x) x h
      = unwrappedForwardDiff r (centeredJetPolynomial r a x) x h +
        a (r + 1) * unwrappedForwardDiff r (fun y => (y - x) ^ (r + 1)) x h := by
    unfold unwrappedForwardDiff
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _
    have hnode : centeredJetPolynomial (r + 1) a x (x + (j : ℝ) * h)
        = centeredJetPolynomial r a x (x + (j : ℝ) * h) +
          a (r + 1) * ((x + (j : ℝ) * h) - x) ^ (r + 1) := by
      unfold centeredJetPolynomial
      rw [Finset.sum_range_succ]
    rw [hnode]
    ring
  rw [hsplit, unwrappedForwardDiff_centeredJetPolynomial,
    unwrappedForwardDiff_centeredMonomial_succ]
  ring

theorem normalizedForwardDiff_centeredJetPolynomial_succ
    (r : ℕ) (a : ℕ → ℝ) (x : ℝ) {h : ℝ} (hh : h ≠ 0) :
    normalizedForwardDiff r (centeredJetPolynomial (r + 1) a x) x h =
      (Nat.factorial r : ℝ) * a r +
        (Nat.factorial r : ℝ) * (Nat.choose (r + 1) 2 : ℝ) *
          a (r + 1) * h := by
  have hpow : h ^ r ≠ 0 := pow_ne_zero _ hh
  unfold normalizedForwardDiff
  rw [unwrappedForwardDiff_centeredJetPolynomial_succ, pow_succ]
  field_simp

theorem unwrappedForwardDiff_sub_secondJet_eq_remainder_sum
    (r : ℕ) (f : ℝ → ℝ) (a : ℕ → ℝ) (x h : ℝ) :
    unwrappedForwardDiff r f x h -
        ((Nat.factorial r : ℝ) * a r * h ^ r +
          (Nat.factorial r : ℝ) * (Nat.choose (r + 1) 2 : ℝ) *
            a (r + 1) * h ^ (r + 1)) =
      Finset.sum (Finset.range (r + 1)) (fun j =>
        (forwardDiffCoeff r j : ℝ) *
          (f (x + (j : ℝ) * h) -
            centeredJetPolynomial (r + 1) a x
              (x + (j : ℝ) * h))) := by
  have hsplit : Finset.sum (Finset.range (r + 1)) (fun j =>
      (forwardDiffCoeff r j : ℝ) *
        (f (x + (j : ℝ) * h) -
          centeredJetPolynomial (r + 1) a x (x + (j : ℝ) * h)))
      = Finset.sum (Finset.range (r + 1)) (fun j =>
          (forwardDiffCoeff r j : ℝ) * f (x + (j : ℝ) * h))
        - Finset.sum (Finset.range (r + 1)) (fun j =>
          (forwardDiffCoeff r j : ℝ) *
            centeredJetPolynomial (r + 1) a x (x + (j : ℝ) * h)) := by
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
        centeredJetPolynomial (r + 1) a x (x + (j : ℝ) * h))
      = unwrappedForwardDiff r (centeredJetPolynomial (r + 1) a x) x h := rfl
  rw [hf, hp, unwrappedForwardDiff_centeredJetPolynomial_succ]

theorem unwrappedForwardDiff_second_error_le
    {r : ℕ} {f : ℝ → ℝ} {a : ℕ → ℝ} {x h C : ℝ}
    (hC : 0 ≤ C)
    (hrem : HasCenteredJetSecondRemainderAtNodes r f a x h C) :
    |unwrappedForwardDiff r f x h -
        ((Nat.factorial r : ℝ) * a r * h ^ r +
          (Nat.factorial r : ℝ) * (Nat.choose (r + 1) 2 : ℝ) *
            a (r + 1) * h ^ (r + 1))| ≤
      (C * |h| ^ (r + 2) /
          (Nat.factorial (r + 2) : ℝ)) *
        forwardDiffSecondRemainderWeight r := by
  -- `hC` is part of the requested interface; the bound itself needs only `hrem`.
  have _hCnonneg : (0 : ℝ) ≤ C := hC
  rw [unwrappedForwardDiff_sub_secondJet_eq_remainder_sum r f a x h]
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
          centeredJetPolynomial (r + 1) a x (x + (j : ℝ) * h))| ≤
      (C * |h| ^ (r + 2) / (Nat.factorial (r + 2) : ℝ)) *
        ((Nat.choose r j : ℝ) * (j : ℝ) ^ (r + 2)) := by
    intro j hj
    rw [abs_mul, habsCoeff j]
    have hb := hrem j hj
    have habs : |(j : ℝ) * h| ^ (r + 2)
        = (j : ℝ) ^ (r + 2) * |h| ^ (r + 2) := by
      rw [abs_mul, mul_pow, abs_of_nonneg (Nat.cast_nonneg j : (0:ℝ) ≤ (j : ℝ))]
    rw [habs] at hb
    have hcnn : (0 : ℝ) ≤ (Nat.choose r j : ℝ) := Nat.cast_nonneg _
    calc (Nat.choose r j : ℝ) *
            |f (x + (j : ℝ) * h) -
              centeredJetPolynomial (r + 1) a x (x + (j : ℝ) * h)|
        ≤ (Nat.choose r j : ℝ) *
            (C * ((j : ℝ) ^ (r + 2) * |h| ^ (r + 2)) /
              (Nat.factorial (r + 2) : ℝ)) :=
          mul_le_mul_of_nonneg_left hb hcnn
      _ = (C * |h| ^ (r + 2) / (Nat.factorial (r + 2) : ℝ)) *
            ((Nat.choose r j : ℝ) * (j : ℝ) ^ (r + 2)) := by
          ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  unfold forwardDiffSecondRemainderWeight
  rw [Finset.mul_sum]

theorem normalizedForwardDiff_sub_secondJet_eq_div
    (r : ℕ) (f : ℝ → ℝ) (a : ℕ → ℝ) (x : ℝ)
    {h : ℝ} (hh : h ≠ 0) :
    normalizedForwardDiff r f x h -
        ((Nat.factorial r : ℝ) * a r +
          (Nat.factorial r : ℝ) * (Nat.choose (r + 1) 2 : ℝ) *
            a (r + 1) * h) =
      (unwrappedForwardDiff r f x h -
        ((Nat.factorial r : ℝ) * a r * h ^ r +
          (Nat.factorial r : ℝ) * (Nat.choose (r + 1) 2 : ℝ) *
            a (r + 1) * h ^ (r + 1))) / h ^ r := by
  have hpow : h ^ r ≠ 0 := pow_ne_zero _ hh
  unfold normalizedForwardDiff
  rw [eq_div_iff hpow, sub_mul, div_mul_cancel₀ _ hpow, pow_succ]
  ring

theorem normalizedForwardDiff_second_error_le
    {r : ℕ} {f : ℝ → ℝ} {a : ℕ → ℝ} {x h C : ℝ}
    (hh : h ≠ 0) (hC : 0 ≤ C)
    (hrem : HasCenteredJetSecondRemainderAtNodes r f a x h C) :
    |normalizedForwardDiff r f x h -
        ((Nat.factorial r : ℝ) * a r +
          (Nat.factorial r : ℝ) * (Nat.choose (r + 1) 2 : ℝ) *
            a (r + 1) * h)| ≤
      (C / (Nat.factorial (r + 2) : ℝ)) * |h| ^ 2 *
        forwardDiffSecondRemainderWeight r := by
  have hpow : (0 : ℝ) < |h| ^ r := pow_pos (abs_pos.mpr hh) r
  rw [normalizedForwardDiff_sub_secondJet_eq_div r f a x hh, abs_div, abs_pow]
  rw [div_le_iff₀ hpow]
  refine le_trans (unwrappedForwardDiff_second_error_le hC hrem) (le_of_eq ?_)
  rw [pow_add]
  ring

end ResidueSlices
