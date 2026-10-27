import SymmetricSubgroupAsymptotics.CFSGOrthogonalDCartanIntrinsicEquiv
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDInvariantForm
import SymmetricSubgroupAsymptotics.CFSGIntegralSquareZeroOperators
import Mathlib.Tactic.NoncommRing

/-! The literal intrinsic D matrix lattice: skew-adjoint integer matrices
whose upper-left diagonal has even sum. This is a genuine submodule of
FULL integer matrices, not a redefinition of the original source lattice. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIntrinsicIntegralLattice
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDCartanParityLattice
variable (r : ℕ)

def diagonal : Mat ℤ r→ₗ[ℤ](Fin r→ℤ) where
  toFun M i:=M (.inl i) (.inl i)
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

def lattice : Submodule ℤ (Mat ℤ r) :=
  (skewAdjointMatricesLieSubalgebra (gram ℤ r)).toSubmodule ⊓
    (evenSum r).comap (diagonal r)

theorem mem_lattice (M : Mat ℤ r) : M∈lattice r ↔
    M∈skewAdjointMatricesLieSubalgebra (gram ℤ r) ∧ diagonal r M∈evenSum r := Iff.rfl

def upperTrace : Mat ℤ r→ₗ[ℤ]ℤ :=
  (CFSGOrthogonalDCartanIntrinsicCoordinates.total r).comp (diagonal r)

theorem mem_parity_iff (M : Mat ℤ r) : diagonal r M∈evenSum r ↔
    ∃ z : ℤ,upperTrace r M=2*z := Iff.rfl

/-- Sandwiching three skew-adjoint matrices in the symmetric pattern
E*X*E remains skew-adjoint, without dividing two. -/
theorem sandwich_mem (E X : Mat ℤ r)
    (hE : E∈skewAdjointMatricesLieSubalgebra (gram ℤ r))
    (hX : X∈skewAdjointMatricesLieSubalgebra (gram ℤ r)) :
    E*X*E∈skewAdjointMatricesLieSubalgebra (gram ℤ r) := by
  rw [mem_skewAdjointMatricesLieSubalgebra,mem_skewAdjointMatricesSubmodule] at hE hX ⊢
  change E.transpose*gram ℤ r=gram ℤ r*(-E) at hE
  change X.transpose*gram ℤ r=gram ℤ r*(-X) at hX
  change (E*X*E).transpose*gram ℤ r=gram ℤ r*(-(E*X*E))
  simp only [Matrix.transpose_mul]
  calc
    E.transpose*(X.transpose*E.transpose)*gram ℤ r=
        E.transpose*X.transpose*(E.transpose*gram ℤ r) := by noncomm_ring
    _=E.transpose*X.transpose*(gram ℤ r*(-E)) := by rw [hE]
    _=E.transpose*(X.transpose*gram ℤ r)*(-E) := by noncomm_ring
    _=E.transpose*(gram ℤ r*(-X))*(-E) := by rw [hX]
    _=(E.transpose*gram ℤ r)*(-X)*(-E) := by noncomm_ring
    _=(gram ℤ r*(-E))*(-X)*(-E) := by rw [hE]
    _=gram ℤ r*(-(E*X*E)) := by noncomm_ring

/-- Every divided-power coefficient preserves the orthogonal equation.
The remaining parity condition is deliberately not hidden in this lemma. -/
theorem operator_mem_orthogonal (E X : Mat ℤ r)
    (hE : E∈skewAdjointMatricesLieSubalgebra (gram ℤ r))
    (hX : X∈skewAdjointMatricesLieSubalgebra (gram ℤ r)) (k : ℕ) :
    CFSGIntegralSquareZeroOperators.operator ℤ E k X∈
      skewAdjointMatricesLieSubalgebra (gram ℤ r) := by
  by_cases hk : 3 ≤ k
  · rw [CFSGIntegralSquareZeroOperators.operator_large ℤ E X k hk]
    exact (skewAdjointMatricesLieSubalgebra (gram ℤ r)).zero_mem
  · have hlt : k < 3:=by omega
    interval_cases k
    · simpa only [CFSGIntegralSquareZeroOperators.operator_zero] using hX
    · rw [CFSGIntegralSquareZeroOperators.operator_one]
      exact (skewAdjointMatricesLieSubalgebra (gram ℤ r)).lie_mem hE hX
    · rw [CFSGIntegralSquareZeroOperators.operator_two]
      exact (skewAdjointMatricesLieSubalgebra (gram ℤ r)).neg_mem (sandwich_mem r E X hE hX)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIntrinsicIntegralLattice
