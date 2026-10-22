import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckCoordinateForm
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckGramEntries
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNegative

/-! Abstract-base staging of the actual height-form calculation. The only
extra condition is the scalar sign of each simple root; the coordinate-base
construction has already proved that sign from its original integer lattice.
Keeping the base abstract avoids computing its support during type inference. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckBasedForm
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoGeckHeightData CFSGNormTwoGeckStepMatrices CFSGNormTwoGeckGram
open CFSGNormTwoGeckQuadratic CFSGNormTwoGeckNegative CFSGGeckOppositionAlgEquiv
open CFSGNormTwoGeckCoordinateForm CFSGNormTwoGeckGramEntries
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    (b : (rootPairing A hs hp).Base) (hsimple : ∀ i : b.support,rootSign A i= -1)

include hsimple

theorem E_mem_form (i : b.support) :
    RootPairing.GeckConstruction.e i∈skewAdjointMatricesLieSubalgebra (gram A hs hp b) := by
  rw [mem_skewAdjointMatricesLieSubalgebra,mem_skewAdjointMatricesSubmodule]
  change (RootPairing.GeckConstruction.e i).transpose*gram A hs hp b=
    gram A hs hp b*(-RootPairing.GeckConstruction.e i)
  rw [mul_neg,eq_neg_iff_add_eq_zero,E_eq_step A hs hp b i]
  exact step_skew_of_sign A hs hp b i i (hsimple i)

theorem F_mem_form (i : b.support) :
    RootPairing.GeckConstruction.f i∈skewAdjointMatricesLieSubalgebra (gram A hs hp b) := by
  rw [mem_skewAdjointMatricesLieSubalgebra,mem_skewAdjointMatricesSubmodule]
  change (RootPairing.GeckConstruction.f i).transpose*gram A hs hp b=
    gram A hs hp b*(-RootPairing.GeckConstruction.f i)
  rw [mul_neg,eq_neg_iff_add_eq_zero,F_eq_step A hs hp b i]
  exact step_skew_of_sign A hs hp b (negativeIndex A hs hp i) i
    ((rootSign_negative A hs hp i).trans (hsimple i))

theorem mem_form {X : Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ}
    (hX : X∈RootPairing.GeckConstruction.lieAlgebra b) :
    X∈skewAdjointMatricesLieSubalgebra (gram A hs hp b) := by
  have hle : RootPairing.GeckConstruction.lieAlgebra b≤
      skewAdjointMatricesLieSubalgebra (gram A hs hp b) := by
    unfold RootPairing.GeckConstruction.lieAlgebra
    apply LieSubalgebra.lieSpan_le.mpr
    intro Y hY
    rcases hY with (hY|hY)|hY
    · obtain ⟨i,rfl⟩ := hY
      rw [←RootPairing.GeckConstruction.lie_e_f_same i]
      exact (skewAdjointMatricesLieSubalgebra (gram A hs hp b)).lie_mem
        (E_mem_form A hs hp b hsimple i) (F_mem_form A hs hp b hsimple i)
    · obtain ⟨i,rfl⟩ := hY
      exact E_mem_form A hs hp b hsimple i
    · obtain ⟨i,rfl⟩ := hY
      exact F_mem_form A hs hp b hsimple i
  exact hle hX

theorem positive_fourth_coefficient_zero
    (X : Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ)
    (hX : X∈RootPairing.GeckConstruction.lieAlgebra b) (i : b.support) :
    secondMatrix A hs hp b i*X*secondMatrix A hs hp b i=0 := by
  have hz := opposite_entry_zero A hs hp b X (mem_form A hs hp b hsimple hX) i
  simp only [secondMatrix,Matrix.single_mul_mul_single,hz,mul_zero,zero_mul,Matrix.single_zero]

theorem negative_fourth_coefficient_zero
    (X : Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ)
    (hX : X∈RootPairing.GeckConstruction.lieAlgebra b) (i : b.support) :
    negativeSecondMatrix A hs hp b i*X*negativeSecondMatrix A hs hp b i=0 := by
  have hop : opposition b X∈RootPairing.GeckConstruction.lieAlgebra b :=
    RootPairing.GeckConstruction.ωConj_mem_of_mem hX
  have hz := positive_fourth_coefficient_zero A hs hp b hsimple (opposition b X) hop i
  have hh := congrArg (opposition b) hz
  simp only [map_mul,map_zero] at hh
  have hi : opposition b (opposition b X)=X :=
    (RootPairing.GeckConstruction.ωConj b).symm_apply_apply X
  rw [hi] at hh
  exact hh

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckBasedForm
