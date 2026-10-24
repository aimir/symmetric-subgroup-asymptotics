import SymmetricSubgroupAsymptotics.CFSGFFourOriginalParameterizedTorus
import SymmetricSubgroupAsymptotics.CFSGFFourE6GeneratedOriginalProjection

/-! An unconditional characteristic-two equivalence from the same
original F4 Model to the literal diagram-fixed generated subgroup.
This combines proved source faithfulness and the proved folded subgroup
equality, without ordinary projective simplicity or an automorphism lift. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalGeneratedEquivalence
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration
open CFSGFFourOriginalFoldedEquivalence CFSGFFourOriginalMiddleWords
open CFSGFFourOriginalParameterizedTorus CFSGFFourE6GeneratedOriginalProjection
open CFSGFFourE6SimpleGeneratedParameters CFSGFFourE6FixedGeneratedGroup
open CFSGFFourE6RelativeTorus CFSGTwistedE6GeckRelativeRootGenerated
variable (K : Type) [Field K] [Finite K] [CharP K 2]

def modelEquivGenerated : Model CartanMatrix.F₄ K≃*fixedRootGenerated K (RingEquiv.refl K) :=
  (modelEquivFolded K).trans (foldedEquiv K).symm

theorem modelEquivGenerated_val (g : Model CartanMatrix.F₄ K) :
    (modelEquivGenerated K g).val=rawHom K g := rfl

theorem modelEquivGenerated_root (neg : Bool) (i : Fin 4) (a : K) :
    modelEquivGenerated K (modelRoot CartanMatrix.F₄ K neg i a)=
      simpleInGenerated K neg i (Multiplicative.ofAdd a) := by
  apply Subtype.ext
  rw [modelEquivGenerated_val,rawHom_root,simpleInGenerated_val,folded_root_eq_orbitParameter]
  fin_cases i <;> rfl

theorem modelEquivGenerated_parameterTorus (i : Fin 4) (a : Kˣ) :
    modelEquivGenerated K (parameterTorus K i a)=torusInGenerated K i a := by
  apply Subtype.ext
  rw [modelEquivGenerated_val,rawHom_parameterTorus]

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalGeneratedEquivalence
