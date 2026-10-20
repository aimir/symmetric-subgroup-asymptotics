import SymmetricSubgroupAsymptotics.Selected1542QuotientStructurePackets
import SymmetricSubgroupAsymptotics.Selected1542KernelSignature
import SymmetricSubgroupAsymptotics.FiniteKernelQuotientWordGraph

/-! The bounded selected graph binds the literal twelve-point target to the
quotient by the same displayed original central kernel. -/
set_option autoImplicit false
set_option maxRecDepth 8192
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1542QuotientStructure

local instance : Fintype originalPreimage := Fintype.ofFinite _
local instance : originalPreimage.subtype.range.Normal := by
  rw [Subgroup.range_subtype]
  infer_instance

def originalState (i : Fin 48) : Original := ((word i).map source).prod

theorem originalState_val (i : Fin 48) : (originalState i).val=sourceState i := by
  change Original.subtype (((word i).map source).prod)=sourceState i
  rw [map_list_prod]
  simp only [List.map_map,sourceState,source,Function.comp_def]
  rfl

def actualQuotientGraph : FiniteKernelQuotientWordGraph (I := Fin 48)
    originalPreimage.subtype source targetGenerators originalCode where
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
  step_residue i j := preimageTable.chart (stepResidue i j)
  step_source i j := by
    apply Subtype.ext
    change (originalState (step i j)).val*preimageElements (stepResidue i j)=
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
  inverse_residue i := preimageTable.chart (inverseResidue i)
  inverse_source i := by
    apply Subtype.ext
    change (originalState (inverse i)).val*preimageElements (inverseResidue i)=
      (originalState i).val⁻¹
    rw [originalState_val,originalState_val]
    apply Equiv.ext
    intro x
    exact all_inverse_source i x
  inverse_target i := by
    apply Equiv.ext
    intro x
    exact all_inverse_target i x
  target_word_injective := by
    intro i j h
    change targetState i=targetState j at h
    apply all_target_code_injective i j
    rw [←all_target_code i,←all_target_code j,h]
  signature_injective := by
    intro i j h
    apply all_signature_injective i j
    change FiniteKernelCosetSignature.signature originalPreimage.subtype originalCode
      (originalState i)=FiniteKernelCosetSignature.signature originalPreimage.subtype
        originalCode (originalState j) at h
    rw [actual_signature_eq,actual_signature_eq] at h
    have hs : cosetSignature i=cosetSignature j := by
      simpa only [indexedSignature,cosetSignature,originalState_val] using h
    rw [←all_signature i,←all_signature j]
    exact hs


/-- Exactness of the finite target graph is a theorem about the original
quotient, rather than a statement about metadata labels. -/
def selectedQuotientEquivalence :
    actualQuotientGraph.certificate.Source ≃* actualQuotientGraph.certificate.Target :=
  actualQuotientGraph.equivalence

end SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
