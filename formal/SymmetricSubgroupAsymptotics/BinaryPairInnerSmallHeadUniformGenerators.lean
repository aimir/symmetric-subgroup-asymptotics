import SymmetricSubgroupAsymptotics.BinaryPairNaturalHeadDoubleTop
import SymmetricSubgroupAsymptotics.BinaryPairModuleLayerModelBound
import SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T3Kernel45
import SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T22Kernel12
import SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T22Kernel13
import SymmetricSubgroupAsymptotics.PGroupCoinvariantGenerators

/-! The three already checked small inner pair-layer models yield six
or four original natural-module generators one level further out.
Both original pair frames and every affine lift offset are retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16)) (E : BinaryPairFrame F.top.range (Fin 8))

private theorem uniform_generatedBy_twice_actual_top_head (hU : IsPGroup 2 U)
    (c : ℕ) (hcap : ∀ A : Subrepresentation F.coordinateTopAction,
      Module.finrank (ZMod 2) A.toRepresentation.Coinvariants ≤ c) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U X) (c + c) := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  apply pGroup_uniformSubrepresentationGeneratorBound_of_head_le hU
  intro W
  rw [representationHead_finrank_eq_coinvariants]
  exact F.naturalModuleHead_le_twice_actual_top c hcap W

theorem uniform_generatedBy_six_of_inner_regular45
    (hU : IsPGroup 2 U)
    (hH : E.top.range = BinaryRegularEightNaturalRegistry.H)
    (hK : E.kernelSpace = (BinaryRegularEightNaturalRegistry.charts 45).2.space) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U X) 6 := by
  apply F.uniform_generatedBy_twice_actual_top_head hU 3
  intro A
  exact E.naturalModuleHead_le_of_literal_pair_layer_bound
    BinaryRegularEightNaturalRegistry.H hH
    (BinaryRegularEightNaturalRegistry.charts 45).2.space hK 3
    BinaryPairLayerHead8T3Kernel45.pair_bound A

theorem uniform_generatedBy_four_of_inner_heisenberg12
    (hU : IsPGroup 2 U)
    (hH : E.top.range = BinaryHeisenbergEightNaturalHeads.H)
    (hK : E.kernelSpace = (BinaryHeisenbergEightNaturalHeads.charts 12).2.space) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U X) 4 := by
  apply F.uniform_generatedBy_twice_actual_top_head hU 2
  intro A
  exact E.naturalModuleHead_le_of_literal_pair_layer_bound
    BinaryHeisenbergEightNaturalHeads.H hH
    (BinaryHeisenbergEightNaturalHeads.charts 12).2.space hK 2
    BinaryPairLayerHead8T22Kernel12.pair_bound A

theorem uniform_generatedBy_six_of_inner_heisenberg13
    (hU : IsPGroup 2 U)
    (hH : E.top.range = BinaryHeisenbergEightNaturalHeads.H)
    (hK : E.kernelSpace = (BinaryHeisenbergEightNaturalHeads.charts 13).2.space) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U X) 6 := by
  apply F.uniform_generatedBy_twice_actual_top_head hU 3
  intro A
  exact E.naturalModuleHead_le_of_literal_pair_layer_bound
    BinaryHeisenbergEightNaturalHeads.H hH
    (BinaryHeisenbergEightNaturalHeads.charts 13).2.space hK 3
    BinaryPairLayerHead8T22Kernel13.pair_bound A

end SymmetricSubgroupAsymptotics.BinaryPairFrame
