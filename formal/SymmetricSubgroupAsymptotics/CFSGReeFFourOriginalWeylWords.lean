import SymmetricSubgroupAsymptotics.CFSGFFourOriginalGeneratedEquivalence
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleRootCovariance

/-! Literal original F4 Weyl words, their exact folded E6 values, and
the actual exceptional automorphism's letter reversal. No exceptional
root-duality identification or ordinary simplicity is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalWeylWords
open CFSG.Models.Chevalley CFSGFFourOriginalMiddleWords CFSGFFourE6RelativeWords
open CFSGSerreQuadraticWeylWord CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoGeckIntegralWord CFSGTwistedE6RelativeWeylOrbits
open CFSGTwistedE6FixedWordClassification
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGReeFFourFieldParameters CFSGReeFFourOriginalAutomorphism CFSGReeFFourMiddleRootCovariance

def modelWeylWord (K : Type) [Field K] [Finite K] [CharP K 2] :
    List (Fin 4)→Model CartanMatrix.F₄ K
  | []=>1
  | i::w=>weyl K i*modelWeylWord K w

theorem rawHom_modelWeylWord (K : Type) [Field K] [Finite K] [CharP K 2]
    (w : List (Fin 4)) :
    rawHom K (modelWeylWord K w)=canonicalWord CFSGFFourSerreMatrices.realizationData K w := by
  induction w with
  | nil=>exact map_one (rawHom K)
  | cons i w ih=>
    simp only [modelWeylWord,map_mul,rawHom_weyl,ih,canonicalWord]

theorem rawHom_modelWeylWord_relative (K : Type) [Field K] [Finite K] [CharP K 2]
    (w : List (Fin 4)) :
    rawHom K (modelWeylWord K w)=
      wordUnit CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
        E6Base E6Index K (expandRelative w) := by
  have h := (rawHom_modelWeylWord K w).trans (foldedWord_eq_relativeWord K w)
  simpa only [word_eq_canonicalWord] using h

theorem ree_modelWeylWord (m : ℕ) (w : List (Fin 4)) :
    reeAutomorphism m (modelWeylWord (Field m) w)=
      modelWeylWord (Field m) (w.map CFSG.Models.reverseNode) := by
  induction w with
  | nil=>exact map_one (reeAutomorphism m)
  | cons i w ih=>simp only [modelWeylWord,map_mul,ree_weyl,ih,List.map_cons]

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalWeylWords
