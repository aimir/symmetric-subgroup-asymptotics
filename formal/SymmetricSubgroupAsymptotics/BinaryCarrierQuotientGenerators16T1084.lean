import SymmetricSubgroupAsymptotics.BinaryCarrierDerivedOrder16T1084
import SymmetricSubgroupAsymptotics.BinaryCarrierDerived16T1084
import SymmetricSubgroupAsymptotics.PrimeAbelianizationGeneratorCoordinates

/-! Six coordinates for the canonical binary evaluation quotient of the
literal 16T1084 action. The original generator zero is the actual derived
row seven. Its evaluation vanishes, so the remaining six evaluations span
the quotient. All seven generators remain in the original ambient group;
no generation claim for the reduced group tuple is made. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierQuotientGenerators16T1084

abbrev Original := BinaryCarrierDerivedOrder16T1084.Original
abbrev Input := Fin 6 → ZMod 2
abbrev V := PrimeAbelianization 2 Original

/-- The full original tuple, including the redundant quotient coordinate. -/
def ambientGenerators : Fin 7 → Original :=
  closureGenerators BinaryActionData16.node1084Generators

/-- Only the quotient-coordinate tuple drops the first original generator. -/
def reducedGenerators (i : Fin 6) : Original := ambientGenerators i.succ

private theorem generator_zero_pointwise : ∀ x : Fin 16,
    BinaryActionData16.node1084Generators 0 x =
      BinaryCarrierDerivedOrder16T1084.ambientRows 7 x := by
  decide +kernel

/-- Literal equality inside the same original permutation closure. -/
theorem generator_zero_eq_derived_row :
    ambientGenerators 0 =
      BinaryCarrierDerivedOrder16T1084.certificate.cayley.elements 7 := by
  apply Subtype.ext
  change BinaryActionData16.node1084Generators 0 =
    (BinaryCarrierDerivedOrder16T1084.certificate.cayley.elements 7 :
      Equiv.Perm (Fin 16))
  rw [BinaryCarrierDerivedOrder16T1084.certificate_elements_coe]
  exact Equiv.ext generator_zero_pointwise

theorem generator_zero_mem_commutator :
    ambientGenerators 0 ∈ commutator Original := by
  rw [generator_zero_eq_derived_row]
  rw [← BinaryCarrierDerivedOrder16T1084.certificate.subgroup_eq_commutator]
  exact (BinaryCarrierDerivedOrder16T1084.certificate.cayley.mem_closure_iff _).mpr
    ⟨7, rfl⟩

/-- This zero is in the actual canonical evaluation quotient. -/
theorem evaluation_generator_zero :
    primeAbelianizationMap 2 Original (Additive.ofMul (ambientGenerators 0)) = 0 := by
  have h : ambientGenerators 0 ∈ (primeAbelianizationGroupMap 2 Original).ker := by
    rw [BinaryCarrierDerived16T1084.evaluationKernel_eq_commutator]
    exact generator_zero_mem_commutator
  exact h

/-- Removing the proved-zero evaluation preserves the span of all seven
original evaluations; the smaller tuple need not generate the group. -/
theorem evaluation_reduced_span :
    Submodule.span (ZMod 2) (Set.range (fun i : Fin 6 =>
      primeAbelianizationMap 2 Original (Additive.ofMul (reducedGenerators i)))) = ⊤ := by
  apply top_unique
  rw [← primeEvaluation_span_eq_top_of_generates 2 ambientGenerators
    (closureGenerators_full BinaryActionData16.node1084Generators)]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  refine Fin.cases ?_ (fun j => ?_) i
  · change primeAbelianizationMap 2 Original (Additive.ofMul (ambientGenerators 0)) ∈ _
    rw [evaluation_generator_zero]
    exact Submodule.zero_mem _
  · exact Submodule.subset_span ⟨j, rfl⟩

/-- The actual six-coordinate linear spanning map. -/
def generatorMap : Input →ₗ[ZMod 2] V :=
  primeAbelianizationGeneratorMap 2 reducedGenerators

theorem generatorMap_apply (x : Input) :
    generatorMap x = ∑ i : Fin 6, x i •
      primeAbelianizationMap 2 Original (Additive.ofMul (reducedGenerators i)) :=
  primeAbelianizationGeneratorMap_apply 2 reducedGenerators x

@[simp] theorem generatorMap_basis (i : Fin 6) :
    generatorMap (Pi.single i 1) =
      primeAbelianizationMap 2 Original (Additive.ofMul (reducedGenerators i)) := by
  simp [generatorMap, primeAbelianizationGeneratorMap_apply, Pi.single_apply]

theorem generatorMap_surjective : Function.Surjective generatorMap := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← evaluation_reduced_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact ⟨Pi.single i 1, generatorMap_basis i⟩

end SymmetricSubgroupAsymptotics.BinaryCarrierQuotientGenerators16T1084
