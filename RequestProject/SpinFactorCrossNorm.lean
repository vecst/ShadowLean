/-
Target statements for Aristotle: the algebraic core of the quadratic-space
shadow calculus (the spin-factor Jordan algebra) and the Cross-Norm Identity,
following `shadow_spin_factor.tex` (Prop. [Closed-form associator],
Cor. [Jordan identity]) and `cross_norm_identity_shadow.tex`
(Prop. [Cross-Norm Identity]).

Everything here is finite exact algebra — no analysis and no matrices.
The bilinear form `B` is arbitrary (symmetry is assumed only where actually
needed), so one development simultaneously covers the elliptic
(B negative definite), hyperbolic (B positive definite), Gram-matrix
coordinate, and degenerate/parabolic cases from the papers.

Every theorem below is a requested result. Minor Mathlib-name adjustments
(e.g. the exact spelling of the symmetry predicate) are fine; please keep
the mathematical content of each statement.
-/
import Mathlib

open scoped BigOperators

namespace SpinFactor

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (B : LinearMap.BilinForm ℝ V)

/-- The shadow (spin-factor) product on `ℝ ⊕ V` attached to a bilinear
form `B`:  `(s, u) ∘_B (t, v) = (s·t + B(u,v), s·v + t·u)`. -/
def mul (x y : ℝ × V) : ℝ × V :=
  (x.1 * y.1 + B x.2 y.2, x.1 • y.2 + y.1 • x.2)

/-- Shadow conjugate `(s, α) ↦ (s, −α)`. -/
def conj (x : ℝ × V) : ℝ × V := (x.1, -x.2)

/-- Generic norm `q_B(s, u) = s² − B(u, u)`. -/
def q (x : ℝ × V) : ℝ := x.1 ^ 2 - B x.2 x.2

/-
`(1, 0)` is a two-sided identity for the shadow product.
-/
theorem one_mul (x : ℝ × V) : mul B ((1 : ℝ), (0 : V)) x = x := by
  simp +decide [ mul ]

theorem mul_one (x : ℝ × V) : mul B x ((1 : ℝ), (0 : V)) = x := by
  unfold mul;
  aesop

/-- Commutativity of the shadow product (uses symmetry of `B`). -/
theorem mul_comm (hB : B.IsSymm) (x y : ℝ × V) :
    mul B x y = mul B y x := by
  apply Prod.ext
  · dsimp [mul]
    rw [hB.eq]
    ac_rfl
  · dsimp [mul]
    ac_rfl

/-
**Generic-norm relation**: the product of an element with its shadow
conjugate is scalar, with scalar part the generic norm.  The vector part
cancels exactly; no symmetry hypothesis is needed.
-/
theorem mul_conj (x : ℝ × V) : mul B x (conj x) = (q B x, 0) := by
  simp +decide [ mul, q, conj ];
  ring

/-
**Cross-Norm Identity** (`cross_norm_identity_shadow.tex`, Prop. 1):
the conjugate product taken in the OPPOSITE-signature algebra (form `−B`)
recovers the cross-norm `s² + B(u,u)` of the current signature.
-/
theorem cross_norm_identity (x : ℝ × V) :
    mul (-B) x (conj x) = (x.1 ^ 2 + B x.2 x.2, 0) := by
      unfold mul conj; simp +decide ; ring;

/-
Signature-indexed form matching the paper's notation: for a signature
scalar `σ` (the paper takes `σ = ±1`), the conjugate product in signature
`σ` yields `s² − σ·B(u,u)`.  Instantiating at `−σ` gives the cross-norm
`s² + σ·B(u,u)` — normalization via a single opposite-signature product.
-/
theorem signed_mul_conj (σ : ℝ) (x : ℝ × V) :
    mul (σ • B) x (conj x) = (x.1 ^ 2 - σ * B x.2 x.2, 0) := by
      unfold mul conj; simp +decide ; ring;

/-
**Closed-form associator** (`shadow_spin_factor.tex`,
Prop. [Closed-form associator]; equivalently the local rotation packet of
`tree_indexed_shadow.tex`): the associator is purely vectorial,
`(x∘y)∘z − x∘(y∘z) = (0, B(u,v)·w − B(v,w)·u)`.
No symmetry hypothesis is needed.
-/
theorem associator_eq (x y z : ℝ × V) :
    mul B (mul B x y) z - mul B x (mul B y z)
      = ((0 : ℝ), B x.2 y.2 • z.2 - B y.2 z.2 • x.2) := by
        unfold mul;
        simp +decide [mul_add, add_mul, mul_assoc, smul_smul, sub_eq_add_neg];
        constructor <;> abel_nf;
        · ring;
        · module

/-
Third powers associate: `(x∘x)∘x = x∘(x∘x)` (immediate from
`associator_eq` at `y = z = x`).
-/
theorem mul_self_assoc (x : ℝ × V) :
    mul B (mul B x x) x = mul B x (mul B x x) := by
      unfold mul;
      simp +decide [ add_smul, mul_add, add_assoc, add_comm, add_left_comm ];
      ring

/-
**Jordan identity** (`shadow_spin_factor.tex`, Cor. [Jordan identity]):
`(x∘x)∘(x∘y) = x∘((x∘x)∘y)`. The stated symmetry hypothesis is retained
from the requested result, although the exact expansion shows that this
particular identity holds without it.
-/
theorem jordan_identity (_hB : B.IsSymm) (x y : ℝ × V) :
    mul B (mul B x x) (mul B x y) = mul B x (mul B (mul B x x) y) := by
      unfold mul;
      simp +decide [add_comm, add_left_comm, add_assoc, mul_left_comm];
      constructor <;> norm_num [ add_smul, smul_smul ] <;> ring;
      module

/-
Optional stretch goals, if the above goes smoothly:

1. Package the product as an algebra structure: for symmetric `B`, define a
   type synonym carrying `mul` as its `Mul`, give it the appropriate
   non-associative ring instances, and derive Mathlib's `IsCommJordan`
   instance — connecting the development to Mathlib's Jordan vocabulary.

2. Full power-associativity: with powers defined by `x^(n+1) = x ∘ x^n`,
   prove `x^a ∘ x^b = x^(a+b)` for symmetric `B`.

3. Gram-coordinate corollary: instantiate `V = Fin m → ℝ` with
   `B(α,β) = αᵀ G β` for a symmetric matrix `G`, recovering the coordinate
   statements of `cross_norm_identity_shadow.tex` exactly as stated there.
-/

end SpinFactor