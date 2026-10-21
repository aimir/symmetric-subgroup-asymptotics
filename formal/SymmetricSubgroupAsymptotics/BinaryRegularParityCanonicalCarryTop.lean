import SymmetricSubgroupAsymptotics.BinaryRegularSixCanonicalGenerators
import SymmetricSubgroupAsymptotics.BinaryRegular46ParityZeroOuterCarriesData
import SymmetricSubgroupAsymptotics.BinaryPairFrameConjugateTop

/-! The carry packet's literal six rows are exactly the proved sparse
canonical generators of the same original regular-K46 zero model. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace BinaryRegularParityCanonicalCarryTop
private theorem generator_points : ∀ i : Fin 6, ∀ j : Fin 16,
    BinaryRegularSixCanonicalGenerators.generators i j =
      BinaryRegular46ParityZeroOuterCarries.generatorImages i j := by decide +kernel

theorem generators_eq : BinaryRegularSixCanonicalGenerators.generators =
    BinaryRegular46ParityZeroOuterCarries.generators := by
  funext i
  exact Equiv.ext (generator_points i)
end BinaryRegularParityCanonicalCarryTop

namespace BinaryPairFrame
variable {X : Type} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16)) (E : BinaryPairFrame F.top.range (Fin 8))

theorem canonical_regular_parity_carry_top_range
    (hzero : F.top.range = E.splitAffineAction)
    (hH : E.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T3.generators))
    (hK : E.kernelSpace = BinaryRegularSixCanonicalGenerators.K.space) :
    (F.reindex E.canonicalPointLabels).top.range =
      Subgroup.closure (Set.range BinaryRegular46ParityZeroOuterCarries.generators) := by
  rw [F.reindex_top_range]
  have hh := BinaryRegularSixCanonicalGenerators.BinaryPairFrame.canonical_regular_six_closure
    E hzero hH hK
  rw [BinaryRegularParityCanonicalCarryTop.generators_eq] at hh
  exact hh

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
