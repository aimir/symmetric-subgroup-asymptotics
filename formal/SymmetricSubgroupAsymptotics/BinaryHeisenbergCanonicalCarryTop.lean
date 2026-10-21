import SymmetricSubgroupAsymptotics.BinaryHeisenbergSixCanonicalGenerators
import SymmetricSubgroupAsymptotics.BinaryHeisenberg14PhiZeroOuterCarriesData
import SymmetricSubgroupAsymptotics.BinaryPairFrameConjugateTop

/-! The carry packet's literal six rows are exactly the proved sparse
canonical generators of the same original Heisenberg-K14 zero model. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace BinaryHeisenbergCanonicalCarryTop
private theorem generator_points : ∀ i : Fin 6, ∀ j : Fin 16,
    BinaryHeisenbergSixCanonicalGenerators.generators i j =
      BinaryHeisenberg14PhiZeroOuterCarries.generatorImages i j := by decide +kernel

theorem generators_eq : BinaryHeisenbergSixCanonicalGenerators.generators =
    BinaryHeisenberg14PhiZeroOuterCarries.generators := by
  funext i
  exact Equiv.ext (generator_points i)
end BinaryHeisenbergCanonicalCarryTop

namespace BinaryPairFrame
variable {X : Type} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16)) (E : BinaryPairFrame F.top.range (Fin 8))

theorem canonical_heisenberg_carry_top_range
    (hzero : F.top.range = E.splitAffineAction)
    (hH : E.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T22.generators))
    (hK : E.kernelSpace = BinaryHeisenbergSixCanonicalGenerators.K.space) :
    (F.reindex E.canonicalPointLabels).top.range =
      Subgroup.closure (Set.range BinaryHeisenberg14PhiZeroOuterCarries.generators) := by
  rw [F.reindex_top_range]
  have hh := BinaryHeisenbergSixCanonicalGenerators.BinaryPairFrame.canonical_heisenberg_six_closure
    E hzero hH hK
  rw [BinaryHeisenbergCanonicalCarryTop.generators_eq] at hh
  exact hh

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
