import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumnInstaller

/-! Faithfulness converts a complete family of 26 sparse kernel
certificates into equality of the literal original Model words. No
ordinary F4 simplicity and no original-automorphism lift is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalMiddleWeylCertificateEquality
open CFSGSerreQuadraticMatrix CFSGFFourSerreMatrices
open CFSGFFourE6MiddleWeylCoordinateSteps CFSGFFourE6NormMatrixAction
open CFSGFFourE6MiddleWeylBasisLabels CFSGFFourE6MiddleWeylColumnCertificate
open CFSGFFourE6MiddleWeylColumnInstaller CFSGFFourOriginalMiddleWeylColumnAction
open CFSGFFourOriginalFoldedEquivalence

theorem matrixAction_injective (K : Type) [Field K] [Finite K] [CharP K 2] :
    Function.Injective (matrixAction K) := by
  intro g h he
  apply normMatrixAction_injective K
  ext j k
  obtain ⟨a,rfl⟩ := basisIndex_bijective.2 j
  obtain ⟨b,rfl⟩ := basisIndex_bijective.2 k
  exact congrArg (fun M : Matrix (Fin 26) (Fin 26) K=>M a b) he

theorem original_words_eq_of_certificates (K : Type) [Field K] [Finite K] [CharP K 2]
    (certificates : ∀k : Fin 26,ColumnCertificate k) :
    originalLeftWord K=originalRightWord K := by
  apply (modelEquivFolded K).injective
  apply matrixAction_injective K
  apply Matrix.ext_of_mulVec_single
  intro k
  exact original_word_column_eq_of_certificate K k (certificates k)

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalMiddleWeylCertificateEquality
