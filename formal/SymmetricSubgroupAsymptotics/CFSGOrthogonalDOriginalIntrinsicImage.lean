import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIntrinsicRootOperatorParity
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIntegralRealization
import SymmetricSubgroupAsymptotics.CFSGSerreSquareZeroInvariantIntegralLattice

/-! The SAME original integral D lattice actually realizes inside the
intrinsic parity lattice. Generator membership and every literal divided
root operator are proved; no image-containment premise is retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalIntrinsicImage
open CFSG.Models.Chevalley CFSGOrthogonalDSerreMatrices
open CFSGOrthogonalDCartanParityLattice CFSGOrthogonalDIntrinsicIntegralLattice
variable (r : ℕ) (hr : 4 ≤ r)

private theorem root_diagonal (neg : Bool) (i j : Fin r) :
    rootMatrix ℤ r neg i (.inl j) (.inl j)=0 := by
  by_cases hi : i.val+1 < r
  · have hne : i≠(⟨i.val+1,hi⟩ : Fin r) := by
      intro h
      have hh:=congrArg Fin.val h
      change i.val=i.val+1 at hh
      omega
    cases neg <;>
      simp [rootMatrix,negative,positive,hi,Matrix.transpose_apply,Matrix.single_apply,
        hne,Ne.symm hne,eq_comm] <;>
        (intro hij; subst j; exact hne)
  · cases neg <;>
      simp [rootMatrix,negative,positive,hi,Matrix.transpose_apply,Matrix.single_apply]

include hr in
theorem generator_mem (g : CartanMatrix.Generators (Fin r)) :
    integerGenerator r g∈lattice r := by
  cases g with
  | H i =>
    refine ⟨(skewAdjointMatricesLieSubalgebra (gram ℤ r)).lie_mem
      (positive_mem_orthogonal ℤ r i) (negative_mem_orthogonal ℤ r i),?_⟩
    exact column_mem r hr i
  | E i =>
    refine ⟨positive_mem_orthogonal ℤ r i,?_⟩
    have hz : diagonal r (positive ℤ r i)=0 := by
      funext j
      exact root_diagonal r false i j
    change diagonal r (positive ℤ r i) ∈ evenSum r
    rw [hz]
    exact (evenSum r).zero_mem
  | F i =>
    refine ⟨negative_mem_orthogonal ℤ r i,?_⟩
    have hz : diagonal r (negative ℤ r i)=0 := by
      funext j
      exact root_diagonal r true i j
    change diagonal r (negative ℤ r i) ∈ evenSum r
    rw [hz]
    exact (evenSum r).zero_mem

theorem realization_mem (x : integralLattice (CartanMatrix.D r)) :
    integralOrthogonalRepresentation r hr x∈lattice r := by
  apply CFSGSerreSquareZeroInvariantIntegralLattice.integral_image_mem
    (realizationData r hr) (lattice r)
  · exact generator_mem r hr
  · intro neg i k X hX
    have he : CFSGSerreSquareZeroMatrix.integerRoot (realizationData r hr) neg i=
        rootMatrix ℤ r neg i := by cases neg <;> rfl
    rw [he]
    exact CFSGOrthogonalDIntrinsicRootOperatorParity.root_operator_mem r hr neg i k X hX

def realization : integralLattice (CartanMatrix.D r)→ₗ[ℤ]lattice r :=
  (integralOrthogonalRepresentation r hr).codRestrict (lattice r) (realization_mem r hr)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalIntrinsicImage
