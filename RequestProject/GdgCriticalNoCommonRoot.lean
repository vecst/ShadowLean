/-
gd_g completion roadmap, Phase 4A — the functional NO-COMMON-ROOT wrapper.

The hard analytic candidate exclusion is already proved by
`gdgCandidateB_not_tetranomial_root`. This module exposes the short missing
wrapper: for every g ≥ 5 the specialized critical tetranomial and its declared
derivative have NO common root. This is the functional no-common-root API a later
polynomial layer will reuse.

Does NOT introduce a `Polynomial` object and does NOT assert
`Polynomial.Squarefree`; and makes no claim about exact degree, reciprocal-pair
counting, block descent, all roots real, lobe uniqueness, critical-value
separation, monodromy, or a Galois group.

Proof routes (statements verbatim; standard axioms only):

* T1 gdgCriticalTetranomial_at_zero: unfold criticalTetranomial at u = 0; from
  5 ≤ g the exponents g-1 and g are positive, so u^(g-1) = u^g = 0 (zero_pow),
  leaving a = gdgCosCoeff g.
* T2 gdgCriticalTetranomial_root_ne_zero: if u = 0, rewrite hG by T1 to get
  (gdgCosCoeff g : ℂ) = 0, contradicting gdgCosCoeff_pos hg via
  Complex.ofReal_ne_zero.
* T3 gdgCriticalTetranomial_deriv_ne_zero_of_root: by_contra the derivative is 0;
  u ≠ 0 by T2; gdgCandidateB_eq_common_root_reciprocal gives
  u + u⁻¹ = (gdgCandidateB g : ℂ); multiply by u ≠ 0 to get exactly
  u^2 - (gdgCandidateB g : ℂ) * u + 1 = 0 (middle -B, constant +1); then
  gdgCandidateB_not_tetranomial_root hg with that quadratic gives
  criticalTetranomial ≠ 0, contradicting hG. Reuse the existing exclusion; do not
  reprove it.
* T4 gdgCriticalTetranomial_no_common_root: short wrapper — assume the conjunction
  and apply T3.

Certification: no sorry/admit/new axiom/unsafe/implemented_by; no weakening; keep
the exact specialization a = gdgCosCoeff g, epsilon = (-1 : ℂ)^g; keep both
equations visible in T4 (no custom predicate); u ≠ 0 derived not assumed; run
module, Main, audit --wfail (v4.33.0-rc2); report #print axioms per public theorem.
This completes the functional no-common-root wrapper only — NOT the polynomial
definition, Polynomial.Squarefree, degree, reciprocal descent, root count, or
uniqueness per lobe.
-/
import Mathlib
import RequestProject.GdgCriticalCandidateLocation

namespace GdgSquarefree

/-- **Target 1.** The specialized critical tetranomial at zero equals the cosine
coefficient. -/
theorem gdgCriticalTetranomial_at_zero {g : ℕ} (hg : 5 ≤ g) :
    criticalTetranomial g (gdgCosCoeff g : ℂ)
        ((-1 : ℂ) ^ g) 0 =
      (gdgCosCoeff g : ℂ) := by
  have h1 : g - 1 ≠ 0 := by omega
  have h2 : g ≠ 0 := by omega
  unfold criticalTetranomial
  rw [zero_pow h1, zero_pow h2]
  ring

/-- **Target 2.** Every specialized tetranomial root is nonzero. -/
theorem gdgCriticalTetranomial_root_ne_zero {g : ℕ} (hg : 5 ≤ g)
    {u : ℂ}
    (hG : criticalTetranomial g (gdgCosCoeff g : ℂ)
        ((-1 : ℂ) ^ g) u = 0) :
    u ≠ 0 := by
  intro hu
  rw [hu, gdgCriticalTetranomial_at_zero hg] at hG
  exact (Complex.ofReal_ne_zero.mpr (ne_of_gt (gdgCosCoeff_pos hg))) hG

/-- **Target 3.** The derivative is nonzero at every specialized root. -/
theorem gdgCriticalTetranomial_deriv_ne_zero_of_root
    {g : ℕ} (hg : 5 ≤ g) {u : ℂ}
    (hG : criticalTetranomial g (gdgCosCoeff g : ℂ)
        ((-1 : ℂ) ^ g) u = 0) :
    criticalTetranomialDeriv g (gdgCosCoeff g : ℂ)
        ((-1 : ℂ) ^ g) u ≠ 0 := by
  intro hG'
  have hu : u ≠ 0 := gdgCriticalTetranomial_root_ne_zero hg hG
  have hrec : u + u⁻¹ = (gdgCandidateB g : ℂ) :=
    gdgCandidateB_eq_common_root_reciprocal hg hu hG hG'
  have hquad : u ^ 2 - (gdgCandidateB g : ℂ) * u + 1 = 0 := by
    field_simp at hrec
    linear_combination hrec
  exact gdgCandidateB_not_tetranomial_root hg hu hquad hG

/-- **Target 4.** The specialized critical tetranomial and its derivative have no
common root. -/
theorem gdgCriticalTetranomial_no_common_root
    {g : ℕ} (hg : 5 ≤ g) {u : ℂ} :
    ¬ (
      criticalTetranomial g (gdgCosCoeff g : ℂ)
          ((-1 : ℂ) ^ g) u = 0 ∧
      criticalTetranomialDeriv g (gdgCosCoeff g : ℂ)
          ((-1 : ℂ) ^ g) u = 0) := by
  rintro ⟨hG, hG'⟩
  exact gdgCriticalTetranomial_deriv_ne_zero_of_root hg hG hG'

end GdgSquarefree
