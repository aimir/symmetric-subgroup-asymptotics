import SymmetricSubgroupAsymptotics.CFSGFFourOriginalFoldedEquivalence
import SymmetricSubgroupAsymptotics.CFSGFFourE6ExceptionalFoldedAutomorphism

/-! The exceptional automorphism of the literal ORIGINAL F4 Model in
every finite characteristic-two field. The proved parameter-preserving
source/folded equivalence transports the checked norm/quotient action.
All signed original parameters are retained. Ordinary F4 simplicity is
not assumed, including over the Tits defining field of two elements.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalExceptionalModel
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration
open CFSGFFourOriginalFoldedEquivalence CFSGFFourE6ExceptionalFoldedAutomorphism
open CFSGFFourE6NormQuotientActionRange CFSGFFourE6CharacteristicTwoNormImage
variable (K:Type) [Field K] [Finite K] [CharP K 2]

def exceptionalModelEquiv : MulAut (Model CartanMatrix.F₄ K) :=
  (modelEquivFolded K).trans ((exceptionalFoldedEquiv K).trans (modelEquivFolded K).symm)

theorem exceptionalModelEquiv_intertwines (g:Model CartanMatrix.F₄ K) :
    modelEquivFolded K (exceptionalModelEquiv K g)=
      exceptionalFoldedEquiv K (modelEquivFolded K g) :=
  (modelEquivFolded K).apply_symm_apply _

theorem exceptionalModelEquiv_root (neg:Bool) (i:Fin 4) (t:K) :
    exceptionalModelEquiv K (modelRoot CartanMatrix.F₄ K neg i t)=
      modelRoot CartanMatrix.F₄ K neg (reversedNode i) (exceptionalParameter i t) := by
  apply (modelEquivFolded K).injective
  rw [exceptionalModelEquiv_intertwines,modelEquivFolded_root,modelEquivFolded_root]
  exact exceptionalFoldedEquiv_root K neg i t

theorem exceptionalModelEquiv_twice_root (neg:Bool) (i:Fin 4) (t:K) :
    exceptionalModelEquiv K (exceptionalModelEquiv K (modelRoot CartanMatrix.F₄ K neg i t))=
      modelRoot CartanMatrix.F₄ K neg i (t^2) := by
  rw [exceptionalModelEquiv_root,exceptionalModelEquiv_root]
  fin_cases i <;> rfl

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalExceptionalModel
