import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.GeneratedAction16.DataChunk034

/-! Original-generator square certificates on the literal 16T1332 closure.
The finite point equations are checked by the kernel. No order, catalogue
coverage, or ambient symmetric-group derived membership is inferred. -/
set_option autoImplicit false

namespace SymmetricSubgroupAsymptotics.BinaryCarrierDerived16T1332

def squareWords : Fin 5 → DerivedGeneratorWord (Fin 5) :=
  ![.one, .one,
    .mul (.comm 0 2) (.comm 1 2),
    .comm 1 2,
    .mul (.mul (.comm 0 4) (.comm 1 4)) (.comm 3 4)]

theorem squareWords_pointwise : ∀ (i : Fin 5) (x : Fin 16),
    BinaryActionData16.node1332Generators i (BinaryActionData16.node1332Generators i x) =
      (squareWords i).eval BinaryActionData16.node1332Generators x := by
  decide +kernel

theorem evaluationKernel_eq_commutator :
    (primeAbelianizationGroupMap 2
      (Subgroup.closure (Set.range BinaryActionData16.node1332Generators))).ker =
      commutator (Subgroup.closure (Set.range BinaryActionData16.node1332Generators)) :=
  binaryEvaluationKernel_permClosure_eq_commutator_of_pointwise
    BinaryActionData16.node1332Generators squareWords squareWords_pointwise

end SymmetricSubgroupAsymptotics.BinaryCarrierDerived16T1332
