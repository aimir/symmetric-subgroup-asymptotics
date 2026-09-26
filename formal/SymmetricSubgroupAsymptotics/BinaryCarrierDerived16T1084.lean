import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.GeneratedAction16.DataChunk027

/-! Original-generator square certificates on the literal 16T1084 closure.
The finite point equations are checked by the kernel. No order, catalogue
coverage, or ambient symmetric-group derived membership is inferred. -/
set_option autoImplicit false

namespace SymmetricSubgroupAsymptotics.BinaryCarrierDerived16T1084

def squareWords : Fin 7 → DerivedGeneratorWord (Fin 7) :=
  ![.one,
    .comm 1 2,
    .one,
    .one,
    .one,
    .mul (.comm 1 5) (.comm 2 5),
    .comm 6 2]

theorem squareWords_pointwise : ∀ (i : Fin 7) (x : Fin 16),
    BinaryActionData16.node1084Generators i (BinaryActionData16.node1084Generators i x) =
      (squareWords i).eval BinaryActionData16.node1084Generators x := by
  decide +kernel

theorem evaluationKernel_eq_commutator :
    (primeAbelianizationGroupMap 2
      (Subgroup.closure (Set.range BinaryActionData16.node1084Generators))).ker =
      commutator (Subgroup.closure (Set.range BinaryActionData16.node1084Generators)) :=
  binaryEvaluationKernel_permClosure_eq_commutator_of_pointwise
    BinaryActionData16.node1084Generators squareWords squareWords_pointwise

end SymmetricSubgroupAsymptotics.BinaryCarrierDerived16T1084
