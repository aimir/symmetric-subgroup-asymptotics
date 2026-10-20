import SymmetricSubgroupAsymptotics.Row182OriginalBlockKernel
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

set_option autoImplicit false
set_option maxRecDepth 8192
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row182OriginalBlockKernel

abbrev component := (blockFrame.kernelCoordinate 0).range

private theorem source_le_component : Row182QuotientWordGraph.certificate.Source ≤ component := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  refine ⟨kernelGenerators j, ?_⟩
  apply Equiv.ext
  exact coordinate_zero_checked j

def componentState (i : Fin 360) : component :=
  ⟨(Row182QuotientWordGraph.certificate.sourceElement i : Equiv.Perm (Fin 6)),
    source_le_component (Row182QuotientWordGraph.certificate.sourceElement i).property⟩

private theorem componentState_val (i : Fin 360) :
    (componentState i : Equiv.Perm (Fin 6)) = Row182QuotientWordGraph.sourceState i :=
  Row182QuotientWordGraph.certificate.sourceElement_val i

private theorem reference_pair_reaches : ∀ x y : Fin 6, x ≠ y →
    ∃ i : Fin 360, Row182QuotientWordGraph.sourceState i 0 = x ∧
      Row182QuotientWordGraph.sourceState i 1 = y := by
  decide +kernel

theorem component_two_pretransitive : MulAction.IsMultiplyPretransitive component (Fin 6) 2 := by
  apply MulAction.is_two_pretransitive_iff.mpr
  intro a b c d hab hcd
  obtain ⟨i, hi0, hi1⟩ := reference_pair_reaches a b hab
  obtain ⟨j, hj0, hj1⟩ := reference_pair_reaches c d hcd
  let p := componentState i
  let q := componentState j
  have hp0 : p • (0 : Fin 6) = a := by
    change (componentState i : Equiv.Perm (Fin 6)) 0 = a
    rw [componentState_val]
    exact hi0
  have hp1 : p • (1 : Fin 6) = b := by
    change (componentState i : Equiv.Perm (Fin 6)) 1 = b
    rw [componentState_val]
    exact hi1
  have hq0 : q • (0 : Fin 6) = c := by
    change (componentState j : Equiv.Perm (Fin 6)) 0 = c
    rw [componentState_val]
    exact hj0
  have hq1 : q • (1 : Fin 6) = d := by
    change (componentState j : Equiv.Perm (Fin 6)) 1 = d
    rw [componentState_val]
    exact hj1
  have hpa : p⁻¹ • a = (0 : Fin 6) := by rw [← hp0]; simp
  have hpb : p⁻¹ • b = (1 : Fin 6) := by rw [← hp1]; simp
  exact ⟨q * p⁻¹, by simpa only [mul_smul, hpa] using hq0,
    by simpa only [mul_smul, hpb] using hq1⟩

instance component_primitive : MulAction.IsPreprimitive component (Fin 6) :=
  MulAction.isPreprimitive_of_is_two_pretransitive component_two_pretransitive

end SymmetricSubgroupAsymptotics.Row182OriginalBlockKernel
