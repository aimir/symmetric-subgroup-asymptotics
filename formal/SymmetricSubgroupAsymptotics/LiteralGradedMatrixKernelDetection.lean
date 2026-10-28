import SymmetricSubgroupAsymptotics.CFSGGradedMatrixSupport
import Mathlib.Algebra.Lie.Basic
import Mathlib.LinearAlgebra.Basis.Basic

/-! Literal grading separates root coefficients over EVERY coefficient
ring. A double-bracket detector with a unit coordinate then detects the
scalar of a root image, without an arbitrary-root Cartan-column formula.
No field-weight separation or characteristic restriction is used. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.LiteralGradedMatrixKernelDetection
open CFSGGradedMatrixSupport

/-- Distinct nonzero lattice degrees have disjoint literal entry supports.
The extra degree-zero matrix is retained; it need not be zero. -/
theorem component_smul_eq_zero
    {I J W R : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    [AddCommGroup W] [CommRing R]
    (weight : I → W) (degree : J → W) (hinj : Function.Injective degree)
    (hne : ∀ k, degree k ≠ 0) (M : J → Matrix I I R)
    (hM : ∀ k, Supported weight (fun w => w + degree k) (M k))
    (C : Matrix I I R) (hC : Supported weight id C)
    (c : J → R) (hsum : (∑ k, c k • M k) + C = 0) (k : J) :
    c k • M k = 0 := by
  classical
  apply Matrix.ext
  intro i j
  by_cases hij : weight i = weight j + degree k
  · have hCij : C i j = 0 := by
      apply hC i j
      intro he
      apply hne k
      apply add_left_cancel (a := weight j)
      calc
        weight j + degree k = weight i := hij.symm
        _ = weight j + 0 := by simpa only [Function.id_def, add_zero] using he
    have hother : ∀ l ∈ (Finset.univ : Finset J), l ≠ k → c l * M l i j = 0 := by
      intro l _ hl
      have hzero : M l i j = 0 := by
        apply hM l i j
        intro he
        have hd : degree l = degree k := add_left_cancel (he.symm.trans hij)
        exact hl (hinj hd)
      rw [hzero, mul_zero]
    have hentry := congrArg (fun N : Matrix I I R => N i j) hsum
    simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.zero_apply] at hentry
    rw [Finset.sum_eq_single k hother (by simp), hCij, add_zero] at hentry
    exact hentry
  · change c k * M k i j = 0
    rw [hM k i j hij, mul_zero]

/-- A normalized root/opposite-root bracket and a unit simple-root
coordinate detect a root scalar. This is characteristic-free: the unit
coefficient is 1 or -1 before coefficient reduction. -/
theorem scalar_eq_zero_of_double_bracket
    {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    (X Y E : L) (entry : L →ₗ[R] R) (hentry : entry E = 1)
    (epsilon : R) (hepsilon : epsilon = 1 ∨ epsilon = -1)
    (hbracket : ⁅⁅X, Y⁆, E⁆ = epsilon • E)
    (c : R) (hzero : c • X = 0) : c = 0 := by
  have h : c • ⁅⁅X, Y⁆, E⁆ = 0 := by
    rw [← smul_lie, ← smul_lie, hzero, zero_lie, zero_lie]
  rw [hbracket, smul_smul] at h
  have hc := congrArg entry h
  simp only [map_smul, hentry, map_zero, smul_eq_mul, mul_one] at hc
  rcases hepsilon with hepsilon | hepsilon
  · simpa only [hepsilon, mul_one] using hc
  · simpa only [hepsilon, mul_neg, mul_one, neg_eq_zero] using hc

end SymmetricSubgroupAsymptotics.LiteralGradedMatrixKernelDetection
