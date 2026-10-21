import SymmetricSubgroupAsymptotics.BinaryPairModuleLayerModelBound
import SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T3Kernel45
import SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T22Kernel13
import SymmetricSubgroupAsymptotics.BinaryPairAxisNaturalModule

/-! These are UNIFORM bounds over every actual normal subaxis of the
original outer kernel. They use the checked full natural-module pair-layer
theorems, not just the head dimension of the outer kernel itself. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance innerThreeAxisBoundsPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16)) (E : BinaryPairFrame F.top.range (Fin 8))

theorem normalGen_le_three_of_inner_regular45
    (hU : IsPGroup 2 U)
    (hH : E.top.range=BinaryRegularEightNaturalRegistry.H)
    (hJ : E.kernelSpace=(BinaryRegularEightNaturalRegistry.charts 45).2.space)
    (A : Subgroup U) [A.Normal] (hA : A≤F.top.ker) : MarkedC4.normalGen A≤3 := by
  rw [F.axisNatural_normalGen A hA hU]
  exact E.naturalModuleHead_le_of_literal_pair_layer_bound
    BinaryRegularEightNaturalRegistry.H hH _ hJ 3
    BinaryPairLayerHead8T3Kernel45.pair_bound (F.axisNaturalSubrepresentation A)

theorem normalGen_le_three_of_inner_heisenberg13
    (hU : IsPGroup 2 U)
    (hH : E.top.range=BinaryHeisenbergEightNaturalHeads.H)
    (hJ : E.kernelSpace=(BinaryHeisenbergEightNaturalHeads.charts 13).2.space)
    (A : Subgroup U) [A.Normal] (hA : A≤F.top.ker) : MarkedC4.normalGen A≤3 := by
  rw [F.axisNatural_normalGen A hA hU]
  exact E.naturalModuleHead_le_of_literal_pair_layer_bound
    BinaryHeisenbergEightNaturalHeads.H hH _ hJ 3
    BinaryPairLayerHead8T22Kernel13.pair_bound (F.axisNaturalSubrepresentation A)

end SymmetricSubgroupAsymptotics.BinaryPairFrame
