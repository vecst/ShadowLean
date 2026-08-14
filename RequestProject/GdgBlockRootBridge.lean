/-
gd_g completion roadmap, Phase 4F — the BLOCK ROOT BRIDGE.

Phase 3B (`RequestProject.GdgCriticalBridge`) produced, inside every retained
natural lobe, a located witness `phi` with

  * `criticalTetranomial g (gdgCosCoeff g) ((-1)^g) (exp (i phi)) = 0`,
  * `coverQuadratic (gdgCosCoeff g) (exp (i phi)) ≠ 0`,
  * `gdgBlockCoord phi ∈ Ioo (-gdgCosCoeff g) 2`.

Phase 4C (`GdgForcedQuadratic`) peeled the forced quadratic channel, Phase 4D
(`GdgReciprocalResidual`) removed the odd fixed factor `X - 1`, and Phase 4E
(`GdgBlockDescent`) descended the parity-correct residual `R_g` to the block
polynomial `B_g` in the coordinate `b = u + u⁻¹`.

This module transports each Phase 3B witness through those interfaces:
`H_g(exp(i phi)) = 0`, then `R_g(exp(i phi)) = 0` (cancelling the linear factor
`X - 1` in the odd case, which is legitimate exactly because the strict bound
`gdgBlockCoord phi < 2` forces `exp(i phi) ≠ 1`), and finally
`B_g (gdgBlockCoord phi) = 0`.  Since `gdgBlockCoord phi = 2 cos phi` is
strictly antitone on `[0, π]` and distinct retained lobes are ordered in `phi`,
the resulting block roots are pairwise distinct, giving an injective family of
block roots indexed by the retained natural lobes.

It does NOT claim exterior existence, degree exhaustion, uniqueness inside a
lobe, all roots real, squarefreeness of the block polynomial, critical-value
separation, monodromy, or solvability.
-/
import RequestProject.GdgBlockDescent
import RequestProject.GdgCriticalBridge

namespace GdgSquarefree

open Polynomial

/-! ### Target 1: the strict block bound excludes the reciprocal fixed point -/

/-- **Target 1.** A strict block bound `gdgBlockCoord phi < 2` forces the
unit-circle point to differ from the reciprocal fixed point `u = 1`. -/
theorem gdgUnitCircle_ne_one_of_blockCoord_lt_two
    {phi : ℝ} (hphi : gdgBlockCoord phi < 2) :
    gdgUnitCircle phi ≠ 1 := by
  intro hone
  have hsum := gdgUnitCircle_add_inv_eq_blockCoord phi
  have hC : ((gdgBlockCoord phi : ℝ) : ℂ) = 2 := by
    rw [← hsum, hone]
    norm_num
  have hR : gdgBlockCoord phi = 2 := by exact_mod_cast hC
  rw [hR] at hphi
  exact lt_irrefl 2 hphi

/-! ### Target 2: the channel quotient vanishes at the witness -/

/-- **Target 2.** A nonsingular root of the critical tetranomial on the unit
circle is a root of the Phase 4C channel quotient `H_g`. -/
theorem gdgChannelQuotientPolynomial_gdgUnitCircle_eq_zero
    {g : ℕ} (hg : 5 ≤ g) {phi : ℝ}
    (hG : criticalTetranomial g (gdgCosCoeff g : ℂ) ((-1 : ℂ) ^ g)
        (gdgUnitCircle phi) = 0)
    (hQ : coverQuadratic (gdgCosCoeff g : ℂ) (gdgUnitCircle phi) ≠ 0) :
    (gdgChannelQuotientPolynomial g).eval (gdgUnitCircle phi) = 0 := by
  have hQpoly : (gdgQuadraticPolynomial g).eval (gdgUnitCircle phi) ≠ 0 := by
    rw [gdgQuadraticPolynomial_eval]
    exact hQ
  refine (gdgChannelQuotient_eval_eq_zero_iff hg hQpoly).mpr ?_
  rw [gdgCriticalPolynomial_eval]
  exact hG

/-! ### Targets 3–4: passing to the parity-correct residual -/

set_option linter.unusedVariables false in
/-- **Target 3.** For even `g` the parity-correct residual is the channel
quotient itself. -/
theorem gdgReciprocalResidualPolynomial_gdgUnitCircle_eq_zero_of_even
    {g : ℕ} (hg : 5 ≤ g) (hEven : Even g) {phi : ℝ}
    (hH : (gdgChannelQuotientPolynomial g).eval (gdgUnitCircle phi) = 0) :
    (gdgReciprocalResidualPolynomial g).eval (gdgUnitCircle phi) = 0 := by
  rw [gdgReciprocalResidualPolynomial, if_neg (Nat.not_odd_iff_even.mpr hEven)]
  exact hH

/-- **Target 4.** For odd `g` the fixed linear factor `X - 1` is cancelled,
legitimately, because the strict block bound gives `exp (i phi) ≠ 1`. -/
theorem gdgReciprocalResidualPolynomial_gdgUnitCircle_eq_zero_of_odd
    {g : ℕ} (hg : 5 ≤ g) (hOdd : Odd g) {phi : ℝ}
    (hH : (gdgChannelQuotientPolynomial g).eval (gdgUnitCircle phi) = 0)
    (hblock : gdgBlockCoord phi < 2) :
    (gdgReciprocalResidualPolynomial g).eval (gdgUnitCircle phi) = 0 := by
  have hne : gdgUnitCircle phi ≠ 1 :=
    gdgUnitCircle_ne_one_of_blockCoord_lt_two hblock
  have hfac := congrArg (fun p : Polynomial ℂ => p.eval (gdgUnitCircle phi))
    (gdgXSubOne_mul_oddResidual hg hOdd)
  simp only [eval_mul, eval_sub, eval_X, eval_C] at hfac
  rw [hH] at hfac
  have hlin : gdgUnitCircle phi - 1 ≠ 0 := sub_ne_zero.mpr hne
  rw [gdgReciprocalResidualPolynomial, if_pos hOdd]
  exact (mul_eq_zero.mp hfac).resolve_left hlin

/-! ### Target 5: the block polynomial vanishes at the block coordinate -/

/-- **Target 5.** A residual root on the unit circle descends to a root of the
Phase 4E block polynomial at the real block coordinate. -/
theorem gdgBlockCriticalPolynomial_gdgUnitCircle_eq_zero
    {g : ℕ} (hg : 5 ≤ g) {phi : ℝ}
    (hR : (gdgReciprocalResidualPolynomial g).eval (gdgUnitCircle phi) = 0) :
    (gdgBlockCriticalPolynomial g).eval (gdgBlockCoord phi : ℂ) = 0 := by
  have h := gdgBlockCriticalPolynomial_root_of_residual_root hg hR
  rwa [gdgUnitCircle_add_inv_eq_blockCoord] at h

/-! ### Targets 6–7: strict antitonicity of the block coordinate -/

/-- **Target 6.** The block coordinate `b = 2 cos phi` is strictly antitone on
`[0, π]`. -/
theorem gdgBlockCoord_strictAntiOn :
    StrictAntiOn gdgBlockCoord (Set.Icc 0 Real.pi) := by
  intro x hx y hy hxy
  have h := Real.strictAntiOn_cos hx hy hxy
  simp only [gdgBlockCoord]
  linarith

/-- **Target 7.** Ordered points of `[0, π]` have distinct block coordinates. -/
theorem gdgBlockCoord_ne_of_lt
    {phi psi : ℝ} (hphi0 : 0 ≤ phi) (hpsipi : psi ≤ Real.pi)
    (hlt : phi < psi) :
    gdgBlockCoord phi ≠ gdgBlockCoord psi := by
  have hphipi : phi ≤ Real.pi := le_trans hlt.le hpsipi
  have hpsi0 : 0 ≤ psi := le_trans hphi0 hlt.le
  have h := gdgBlockCoord_strictAntiOn ⟨hphi0, hphipi⟩ ⟨hpsi0, hpsipi⟩ hlt
  exact ne_of_gt h

/-! ### Targets 8–9: located block roots from retained lobes -/

/-- **Target 8.** Every retained even lobe produces a located root of the block
polynomial. -/
theorem exists_even_retained_lobe_blockCriticalPolynomial_root
    {g j : ℕ} (hg : 5 ≤ g) (hEven : Even g)
    (hj : j ∈ gdgRetainedLobeIndices g) :
    ∃ phi ∈ Set.Ioo
        (gdgLobeLeft g j 0)
        (gdgLobeRight g j 0),
      (gdgBlockCriticalPolynomial g).eval (gdgBlockCoord phi : ℂ) = 0 ∧
      gdgBlockCoord phi ∈ Set.Ioo (-gdgCosCoeff g) 2 := by
  obtain ⟨phi, hphi, hG, _hA, hQ, hblock⟩ :=
    exists_even_retained_lobe_criticalTetranomial_unitCircle_root hg hEven hj
  refine ⟨phi, hphi, ?_, hblock⟩
  exact gdgBlockCriticalPolynomial_gdgUnitCircle_eq_zero hg
    (gdgReciprocalResidualPolynomial_gdgUnitCircle_eq_zero_of_even hg hEven
      (gdgChannelQuotientPolynomial_gdgUnitCircle_eq_zero hg hG hQ))

/-- **Target 9.** Every retained odd lobe produces a located root of the block
polynomial. -/
theorem exists_odd_retained_lobe_blockCriticalPolynomial_root
    {g j : ℕ} (hg : 5 ≤ g) (hOdd : Odd g)
    (hj : j ∈ gdgRetainedLobeIndices g) :
    ∃ phi ∈ Set.Ioo
        (gdgLobeLeft g j ((1 : ℝ) / 2))
        (gdgLobeRight g j ((1 : ℝ) / 2)),
      (gdgBlockCriticalPolynomial g).eval (gdgBlockCoord phi : ℂ) = 0 ∧
      gdgBlockCoord phi ∈ Set.Ioo (-gdgCosCoeff g) 2 := by
  obtain ⟨phi, hphi, hG, _hA, hQ, hblock⟩ :=
    exists_odd_retained_lobe_criticalTetranomial_unitCircle_root hg hOdd hj
  refine ⟨phi, hphi, ?_, hblock⟩
  exact gdgBlockCriticalPolynomial_gdgUnitCircle_eq_zero hg
    (gdgReciprocalResidualPolynomial_gdgUnitCircle_eq_zero_of_odd hg hOdd
      (gdgChannelQuotientPolynomial_gdgUnitCircle_eq_zero hg hG hQ) hblock.2)

/-! ### Targets 10–11: distinct lobes give distinct block coordinates -/

/-- The explicit ordering of two natural lobes with the same offset. -/
private theorem gdgLobeRight_le_lobeLeft_of_lt {g j k : ℕ} (hg : 1 ≤ g)
    (hjk : j < k) (offset : ℝ) :
    gdgLobeRight g j offset ≤ gdgLobeLeft g k offset := by
  have hth : 0 < gdgTheta g := gdgTheta_pos hg
  have hjk' : ((j : ℝ) + 1) ≤ (k : ℝ) := by exact_mod_cast hjk
  simp only [gdgLobeRight, gdgLobeLeft]
  nlinarith

set_option linter.unusedVariables false in
/-- **Target 10.** Distinct retained even lobes give distinct block
coordinates. -/
theorem gdgBlockCoord_ne_of_even_retained_lobes
    {g j k : ℕ} (hg : 5 ≤ g) (hEven : Even g)
    (hj : j ∈ gdgRetainedLobeIndices g)
    (hk : k ∈ gdgRetainedLobeIndices g) (hjk : j < k)
    {phi psi : ℝ}
    (hphi : phi ∈ Set.Ioo
      (gdgLobeLeft g j 0) (gdgLobeRight g j 0))
    (hpsi : psi ∈ Set.Ioo
      (gdgLobeLeft g k 0) (gdgLobeRight g k 0)) :
    gdgBlockCoord phi ≠ gdgBlockCoord psi := by
  have hth : 0 < gdgTheta g := gdgTheta_pos (by omega)
  have hleft : (0 : ℝ) ≤ gdgLobeLeft g j 0 := by
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    simp only [gdgLobeLeft]
    nlinarith
  have hord : gdgLobeRight g j 0 ≤ gdgLobeLeft g k 0 :=
    gdgLobeRight_le_lobeLeft_of_lt (by omega) hjk 0
  have hkpole : gdgLobeRight g k 0 < Real.pi - gdgTheta g :=
    (gdgEven_mem_iff_lobeRight_lt_pole hg hEven).mp hk
  refine gdgBlockCoord_ne_of_lt (le_trans hleft hphi.1.le) ?_ ?_
  · linarith [hpsi.2]
  · linarith [hphi.2, hpsi.1]

set_option linter.unusedVariables false in
/-- **Target 11.** Distinct retained odd lobes give distinct block
coordinates. -/
theorem gdgBlockCoord_ne_of_odd_retained_lobes
    {g j k : ℕ} (hg : 5 ≤ g) (hOdd : Odd g)
    (hj : j ∈ gdgRetainedLobeIndices g)
    (hk : k ∈ gdgRetainedLobeIndices g) (hjk : j < k)
    {phi psi : ℝ}
    (hphi : phi ∈ Set.Ioo
      (gdgLobeLeft g j ((1 : ℝ) / 2))
      (gdgLobeRight g j ((1 : ℝ) / 2)))
    (hpsi : psi ∈ Set.Ioo
      (gdgLobeLeft g k ((1 : ℝ) / 2))
      (gdgLobeRight g k ((1 : ℝ) / 2))) :
    gdgBlockCoord phi ≠ gdgBlockCoord psi := by
  have hth : 0 < gdgTheta g := gdgTheta_pos (by omega)
  have hleft : (0 : ℝ) ≤ gdgLobeLeft g j ((1 : ℝ) / 2) := by
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    simp only [gdgLobeLeft]
    nlinarith
  have hord : gdgLobeRight g j ((1 : ℝ) / 2) ≤ gdgLobeLeft g k ((1 : ℝ) / 2) :=
    gdgLobeRight_le_lobeLeft_of_lt (by omega) hjk ((1 : ℝ) / 2)
  have hkpole : gdgLobeRight g k ((1 : ℝ) / 2) < Real.pi - gdgTheta g :=
    (gdgOdd_mem_iff_lobeRight_lt_pole hg hOdd).mp hk
  refine gdgBlockCoord_ne_of_lt (le_trans hleft hphi.1.le) ?_ ?_
  · linarith [hpsi.2]
  · linarith [hphi.2, hpsi.1]

/-! ### Targets 12–13: the injective family of retained-lobe block roots -/

/-- **Target 12.** For even `g` the retained natural lobes carry an injective
family of block roots. -/
theorem exists_even_retained_lobe_blockRoot_embedding
    {g : ℕ} (hg : 5 ≤ g) (hEven : Even g) :
    ∃ phi : {j // j ∈ gdgRetainedLobeIndices g} → ℝ,
      (∀ j, phi j ∈ Set.Ioo
        (gdgLobeLeft g j.1 0)
        (gdgLobeRight g j.1 0)) ∧
      (∀ j, (gdgBlockCriticalPolynomial g).eval
        (gdgBlockCoord (phi j) : ℂ) = 0) ∧
      Function.Injective (fun j => gdgBlockCoord (phi j)) := by
  choose phi hmem hroot _hIoo using fun j : {j // j ∈ gdgRetainedLobeIndices g} =>
    exists_even_retained_lobe_blockCriticalPolynomial_root hg hEven j.2
  refine ⟨phi, hmem, hroot, ?_⟩
  intro a b hab
  simp only at hab
  rcases lt_trichotomy a.1 b.1 with h | h | h
  · exact absurd hab
      (gdgBlockCoord_ne_of_even_retained_lobes hg hEven a.2 b.2 h
        (hmem a) (hmem b))
  · exact Subtype.ext h
  · exact absurd hab.symm
      (gdgBlockCoord_ne_of_even_retained_lobes hg hEven b.2 a.2 h
        (hmem b) (hmem a))

/-- **Target 13.** For odd `g` the retained natural lobes carry an injective
family of block roots.  At `g = 5` the index subtype is empty and the statement
is a valid empty-domain embedding. -/
theorem exists_odd_retained_lobe_blockRoot_embedding
    {g : ℕ} (hg : 5 ≤ g) (hOdd : Odd g) :
    ∃ phi : {j // j ∈ gdgRetainedLobeIndices g} → ℝ,
      (∀ j, phi j ∈ Set.Ioo
        (gdgLobeLeft g j.1 ((1 : ℝ) / 2))
        (gdgLobeRight g j.1 ((1 : ℝ) / 2))) ∧
      (∀ j, (gdgBlockCriticalPolynomial g).eval
        (gdgBlockCoord (phi j) : ℂ) = 0) ∧
      Function.Injective (fun j => gdgBlockCoord (phi j)) := by
  choose phi hmem hroot _hIoo using fun j : {j // j ∈ gdgRetainedLobeIndices g} =>
    exists_odd_retained_lobe_blockCriticalPolynomial_root hg hOdd j.2
  refine ⟨phi, hmem, hroot, ?_⟩
  intro a b hab
  simp only at hab
  rcases lt_trichotomy a.1 b.1 with h | h | h
  · exact absurd hab
      (gdgBlockCoord_ne_of_odd_retained_lobes hg hOdd a.2 b.2 h
        (hmem a) (hmem b))
  · exact Subtype.ext h
  · exact absurd hab.symm
      (gdgBlockCoord_ne_of_odd_retained_lobes hg hOdd b.2 a.2 h
        (hmem b) (hmem a))

end GdgSquarefree
