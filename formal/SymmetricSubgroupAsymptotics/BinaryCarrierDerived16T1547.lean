import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.GeneratedAction16.DataChunk039

/-! Original-generator square certificates on the literal 16T1547 closure.
The finite point equations are checked by the kernel. No order, catalogue
coverage, or ambient symmetric-group derived membership is inferred. -/
set_option autoImplicit false

namespace SymmetricSubgroupAsymptotics.BinaryCarrierDerived16T1547

def squareWords : Fin 6 → DerivedGeneratorWord (Fin 6) :=
  ![.mul (.comm 1 5) (.comm 2 3),
    .mul (.comm 1 5) (.comm 2 3),
    .one,
    .one,
    .mul (.comm 0 4) (.comm 3 1),
    .comm 2 3]

theorem squareWords_pointwise : ∀ (i : Fin 6) (x : Fin 16),
    BinaryActionData16.node1547Generators i (BinaryActionData16.node1547Generators i x) =
      (squareWords i).eval BinaryActionData16.node1547Generators x := by
  decide +kernel

theorem evaluationKernel_eq_commutator :
    (primeAbelianizationGroupMap 2
      (Subgroup.closure (Set.range BinaryActionData16.node1547Generators))).ker =
      commutator (Subgroup.closure (Set.range BinaryActionData16.node1547Generators)) :=
  binaryEvaluationKernel_permClosure_eq_commutator_of_pointwise
    BinaryActionData16.node1547Generators squareWords squareWords_pointwise

end SymmetricSubgroupAsymptotics.BinaryCarrierDerived16T1547
