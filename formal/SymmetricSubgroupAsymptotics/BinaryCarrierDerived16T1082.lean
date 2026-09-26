import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.GeneratedAction16.DataChunk027

/-! Original-generator square certificates on the literal 16T1082 closure.
The finite point equations are checked by the kernel. No order, catalogue
coverage, or ambient symmetric-group derived membership is inferred. -/
set_option autoImplicit false

namespace SymmetricSubgroupAsymptotics.BinaryCarrierDerived16T1082

def squareWords : Fin 6 → DerivedGeneratorWord (Fin 6) :=
  ![.one, .one, .one, .one,
    .mul (.comm 2 4) (.comm 4 5),
    .mul (.comm 0 3) (.comm 0 4)]

theorem squareWords_pointwise : ∀ (i : Fin 6) (x : Fin 16),
    BinaryActionData16.node1082Generators i (BinaryActionData16.node1082Generators i x) =
      (squareWords i).eval BinaryActionData16.node1082Generators x := by
  decide +kernel

theorem evaluationKernel_eq_commutator :
    (primeAbelianizationGroupMap 2
      (Subgroup.closure (Set.range BinaryActionData16.node1082Generators))).ker =
      commutator (Subgroup.closure (Set.range BinaryActionData16.node1082Generators)) :=
  binaryEvaluationKernel_permClosure_eq_commutator_of_pointwise
    BinaryActionData16.node1082Generators squareWords squareWords_pointwise

end SymmetricSubgroupAsymptotics.BinaryCarrierDerived16T1082
