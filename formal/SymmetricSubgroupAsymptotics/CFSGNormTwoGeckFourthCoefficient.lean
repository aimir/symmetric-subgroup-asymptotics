import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckLieForm
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckGramEntries
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNegative

/-! The fourth root-conjugation coefficient vanishes on the SAME actual
Geck Lie algebra, for both signs. It is not asserted on all matrices. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFourthCoefficient
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoGeckQuadratic CFSGNormTwoGeckNegative CFSGGeckOppositionAlgEquiv
open CFSGNormTwoGeckLieForm CFSGNormTwoGeckGramEntries
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    (hd : ∀ i,A i i=2) (ho : ∀ i j,i≠j→A i j≤0)
local notation "b" => coordinateBase A hd hs hp ho

theorem positive_fourth_coefficient_zero
    (X : Matrix ((b).support⊕Roots A) ((b).support⊕Roots A) ℚ)
    (hX : X∈RootPairing.GeckConstruction.lieAlgebra b) (i : (b).support) :
    secondMatrix A hs hp b i*X*secondMatrix A hs hp b i=0 := by
  have hz := opposite_entry_zero A hs hp b X (mem_form A hs hp hd ho hX) i
  simp only [secondMatrix,Matrix.single_mul_mul_single,hz,mul_zero,zero_mul,
    Matrix.single_zero]

theorem opposition_involutive (X : Matrix ((b).support⊕Roots A) ((b).support⊕Roots A) ℚ) :
    opposition b (opposition b X)=X := by
  change RootPairing.GeckConstruction.ωConj b (RootPairing.GeckConstruction.ωConj b X)=X
  exact (RootPairing.GeckConstruction.ωConj b).symm_apply_apply X

theorem negative_fourth_coefficient_zero
    (X : Matrix ((b).support⊕Roots A) ((b).support⊕Roots A) ℚ)
    (hX : X∈RootPairing.GeckConstruction.lieAlgebra b) (i : (b).support) :
    negativeSecondMatrix A hs hp b i*X*negativeSecondMatrix A hs hp b i=0 := by
  have hop : opposition b X∈RootPairing.GeckConstruction.lieAlgebra b :=
    RootPairing.GeckConstruction.ωConj_mem_of_mem hX
  have hz := positive_fourth_coefficient_zero A hs hp hd ho (opposition b X) hop i
  have hh := congrArg (opposition b) hz
  simp only [map_mul,map_zero] at hh
  rw [opposition_involutive A hs hp hd ho X] at hh
  exact hh

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFourthCoefficient
