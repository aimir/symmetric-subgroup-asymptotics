import SymmetricSubgroupAsymptotics.Selected1071QuotientPackets
import SymmetricSubgroupAsymptotics.Selected1071KernelSignature
import SymmetricSubgroupAsymptotics.FiniteKernelQuotientWordGraph

/-! The bounded selected graph binds the literal twelve-point target to the
quotient by the same displayed original central kernel. -/
set_option autoImplicit false
set_option maxRecDepth 8192
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1071QuotientGraph

local instance : Fintype originalKernel := Fintype.ofFinite _
local instance : originalKernel.subtype.range.Normal := by
  rw [Subgroup.range_subtype]
  infer_instance

def originalState (i : Fin 192) : Original := ((word i).map source).prod

theorem originalState_val (i : Fin 192) : (originalState i).val=sourceState i := by
  change Original.subtype (((word i).map source).prod)=sourceState i
  rw [map_list_prod]
  simp only [List.map_map,sourceState,source,Function.comp_def]
  rfl

def actualQuotientGraph : FiniteKernelQuotientWordGraph (I := Fin 192)
    originalKernel.subtype source targetGenerators originalCode where
  word := word
  identity := 0
  identity_source := by
    apply Subtype.ext
    change (originalState 0).val=1
    rw [originalState_val]
    apply Equiv.ext
    intro x
    exact identity_source x
  identity_target := by
    change targetState 0=1
    apply Equiv.ext
    intro x
    exact identity_target x
  step := step
  step_residue i j := kernelElement (stepResidue i j)
  step_source i j := by
    apply Subtype.ext
    change (originalState (step i j)).val*kernelElements (stepResidue i j)=
      (originalState i).val*sourceGenerators j
    rw [originalState_val,originalState_val]
    apply Equiv.ext
    intro x
    exact all_step_source i j x
  step_target i j := by
    apply Equiv.ext
    intro x
    exact all_step_target i j x
  inverse := inverse
  inverse_residue i := kernelElement (inverseResidue i)
  inverse_source i := by
    apply Subtype.ext
    change (originalState (inverse i)).val*kernelElements (inverseResidue i)=
      (originalState i).val⁻¹
    rw [originalState_val,originalState_val]
    apply Equiv.ext
    intro x
    exact all_inverse_source i x
  inverse_target i := by
    apply Equiv.ext
    intro x
    exact all_inverse_target i x
  target_word_injective := targetState_injective
  signature_injective := by
    intro i j h
    apply cosetSignature_injective
    change FiniteKernelCosetSignature.signature originalKernel.subtype originalCode
      (originalState i)=FiniteKernelCosetSignature.signature originalKernel.subtype
        originalCode (originalState j) at h
    rw [actual_signature_eq,actual_signature_eq] at h
    simpa only [originalFourSignature,cosetSignature,originalState_val] using h

/-- Exactness of the finite target graph is a theorem about the original
quotient, rather than a statement about metadata labels. -/
def selectedQuotientEquivalence :
    actualQuotientGraph.certificate.Source ≃* actualQuotientGraph.certificate.Target :=
  actualQuotientGraph.equivalence

end SymmetricSubgroupAsymptotics.Selected1071QuotientGraph
