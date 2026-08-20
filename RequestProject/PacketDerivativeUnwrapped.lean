/-
Analytic derivative bridge, Phase A3A: unwrapped scaled stencil, no-wrap packet
bridge, and exact polynomial response.

PacketDerivativeJet proves exact cyclic Fourier and Stirling-moment identities
but has no physical sampling scale and no theorem relating the cyclic packet to
an ordinary unwrapped finite-difference stencil. This file builds that finite
algebraic foundation: the real unwrapped order-r forward difference at base
point x and step h, its h^r normalization, a real-into-complex ZMod g sampling
packet via the canonical representative q.val, the no-wrap bridge (r < g), exact
annihilation of centered monomials below degree r with exact r! response at
degree r, and the packaged response for an arbitrary centered jet polynomial.

This phase is exact finite algebra: NO Taylor remainder estimate, NO h -> 0
convergence (those are Phases A3B/A3C and build on centeredJetPolynomial).
-/
import RequestProject.PacketDerivativeJet

namespace ResidueSlices

noncomputable def unwrappedForwardDiff (r : ℕ) (f : ℝ → ℝ)
    (x h : ℝ) : ℝ :=
  Finset.sum (Finset.range (r + 1)) (fun j =>
    (forwardDiffCoeff r j : ℝ) * f (x + (j : ℝ) * h))

noncomputable def normalizedForwardDiff (r : ℕ) (f : ℝ → ℝ)
    (x h : ℝ) : ℝ :=
  unwrappedForwardDiff r f x h / h ^ r

noncomputable def realSamplePacket {g : ℕ} [NeZero g]
    (f : ℝ → ℝ) (x h : ℝ) (q : ZMod g) : ℂ :=
  (f (x + (q.val : ℝ) * h) : ℂ)

noncomputable def centeredJetPolynomial (r : ℕ) (a : ℕ → ℝ)
    (x y : ℝ) : ℝ :=
  Finset.sum (Finset.range (r + 1)) (fun m =>
    a m * (y - x) ^ m)

theorem forwardDiffPacket_realSamplePacket_eq
    {g r : ℕ} [NeZero g] (hrg : r < g)
    (f : ℝ → ℝ) (x h : ℝ) :
    forwardDiffPacket r (@realSamplePacket g _ f x h) =
      (unwrappedForwardDiff r f x h : ℂ) := by
  unfold forwardDiffPacket realSamplePacket unwrappedForwardDiff
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hjr : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hjg : j < g := lt_of_le_of_lt hjr hrg
  have hval : (j : ZMod g).val = j := ZMod.val_natCast_of_lt hjg
  rw [hval]
  push_cast
  ring

theorem unwrappedForwardDiff_centeredMonomial_vanish
    {r m : ℕ} (hm : m < r) (x h : ℝ) :
    unwrappedForwardDiff r (fun y => (y - x) ^ m) x h = 0 := by
  unfold unwrappedForwardDiff
  have hmom : (Finset.sum (Finset.range (r + 1)) (fun j =>
      (forwardDiffCoeff r j : ℝ) * (j : ℝ) ^ m)) = 0 := by
    have h0 := forwardDiff_moment_vanish (r := r) (m := m) hm
    have hcast : ((Finset.sum (Finset.range (r + 1)) (fun j =>
        forwardDiffCoeff r j * (j : ℤ) ^ m) : ℤ) : ℝ) = 0 := by
      rw [h0]; norm_num
    push_cast at hcast
    exact hcast
  have hrw : (Finset.sum (Finset.range (r + 1)) (fun j =>
      (forwardDiffCoeff r j : ℝ) * ((x + (j : ℝ) * h) - x) ^ m))
      = h ^ m * Finset.sum (Finset.range (r + 1)) (fun j =>
        (forwardDiffCoeff r j : ℝ) * (j : ℝ) ^ m) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  simpa [hmom] using hrw

theorem unwrappedForwardDiff_centeredMonomial_top
    (r : ℕ) (x h : ℝ) :
    unwrappedForwardDiff r (fun y => (y - x) ^ r) x h =
      (Nat.factorial r : ℝ) * h ^ r := by
  unfold unwrappedForwardDiff
  have hmom : (Finset.sum (Finset.range (r + 1)) (fun j =>
      (forwardDiffCoeff r j : ℝ) * (j : ℝ) ^ r)) = (Nat.factorial r : ℝ) := by
    have h0 := forwardDiff_top_moment r
    have hcast : ((Finset.sum (Finset.range (r + 1)) (fun j =>
        forwardDiffCoeff r j * (j : ℤ) ^ r) : ℤ) : ℝ) = (Nat.factorial r : ℝ) := by
      rw [h0]; norm_num
    push_cast at hcast
    exact hcast
  have hrw : (Finset.sum (Finset.range (r + 1)) (fun j =>
      (forwardDiffCoeff r j : ℝ) * ((x + (j : ℝ) * h) - x) ^ r))
      = h ^ r * Finset.sum (Finset.range (r + 1)) (fun j =>
        (forwardDiffCoeff r j : ℝ) * (j : ℝ) ^ r) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  rw [hrw, hmom, mul_comm]

theorem normalizedForwardDiff_centeredMonomial_vanish
    {r m : ℕ} (hm : m < r) (x h : ℝ) :
    normalizedForwardDiff r (fun y => (y - x) ^ m) x h = 0 := by
  unfold normalizedForwardDiff
  rw [unwrappedForwardDiff_centeredMonomial_vanish hm, zero_div]

theorem normalizedForwardDiff_centeredMonomial_top
    (r : ℕ) (x : ℝ) {h : ℝ} (hh : h ≠ 0) :
    normalizedForwardDiff r (fun y => (y - x) ^ r) x h =
      (Nat.factorial r : ℝ) := by
  unfold normalizedForwardDiff
  rw [unwrappedForwardDiff_centeredMonomial_top]
  field_simp

theorem unwrappedForwardDiff_centeredJetPolynomial
    (r : ℕ) (a : ℕ → ℝ) (x h : ℝ) :
    unwrappedForwardDiff r (centeredJetPolynomial r a x) x h =
      (Nat.factorial r : ℝ) * a r * h ^ r := by
  have hlin : unwrappedForwardDiff r (centeredJetPolynomial r a x) x h
      = Finset.sum (Finset.range (r + 1)) (fun m =>
          a m * unwrappedForwardDiff r (fun y => (y - x) ^ m) x h) := by
    unfold unwrappedForwardDiff centeredJetPolynomial
    have hswap : ∀ j : ℕ, (forwardDiffCoeff r j : ℝ) *
        Finset.sum (Finset.range (r + 1)) (fun m => a m * ((x + (j : ℝ) * h) - x) ^ m)
        = Finset.sum (Finset.range (r + 1)) (fun m =>
            a m * ((forwardDiffCoeff r j : ℝ) * ((x + (j : ℝ) * h) - x) ^ m)) := by
      intro j
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro m _
      ring
    simp only [hswap]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro m _
    rw [Finset.mul_sum]
  rw [hlin, Finset.sum_range_succ]
  have hzero : Finset.sum (Finset.range r) (fun m =>
      a m * unwrappedForwardDiff r (fun y => (y - x) ^ m) x h) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro m hm
    rw [unwrappedForwardDiff_centeredMonomial_vanish (Finset.mem_range.mp hm), mul_zero]
  rw [hzero, unwrappedForwardDiff_centeredMonomial_top, zero_add]
  ring

theorem normalizedForwardDiff_centeredJetPolynomial
    (r : ℕ) (a : ℕ → ℝ) (x : ℝ) {h : ℝ} (hh : h ≠ 0) :
    normalizedForwardDiff r (centeredJetPolynomial r a x) x h =
      (Nat.factorial r : ℝ) * a r := by
  unfold normalizedForwardDiff
  rw [unwrappedForwardDiff_centeredJetPolynomial]
  field_simp

end ResidueSlices
