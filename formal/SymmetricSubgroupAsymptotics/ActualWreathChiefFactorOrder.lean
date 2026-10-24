import SymmetricSubgroupAsymptotics.SemisimpleChartCoordinateFactorEmbedding
import SymmetricSubgroupAsymptotics.PermutationalWreathQuotient
import SymmetricSubgroupAsymptotics.FiniteGroupBinaryOrderGenerators

/-! Genuine selected-factor order charges in the original wreath kernel.
An internal simple factor is detected by one literal local-kernel
coordinate; neither chart origins nor independence of original coordinates
is assumed. The generator cost remains the factor's actual ordinary rank. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualWreathChiefFactorOrder
open PermutationalWreathProduct

variable {A D D' Q I : Type} [Group A] [Group D] [Finite D]
    [Group D'] [Group Q] [MulAction Q I]
    (rho : A →* PermutationalWreathProduct D Q I) (phi : D →* D')
    (hrho : Function.Injective rho)
    (C : SemisimpleNormalChart (Compression.kernel rho phi)) (j : C.ι)

include hrho

theorem factor_card_le_local_kernel : Nat.card (C.factor j) ≤ Nat.card phi.ker :=
  SemisimpleChartCoordinateFactorEmbedding.factor_card_le_coordinate
    (Compression.kernel rho phi) C (Compression.kernelCoordinate rho phi)
    (Compression.kernelCoordinate_joint_injective rho phi hrho) j

theorem two_pow_factor_genRank_le_local_kernel :
    2 ^ MarkedC4.genRank (C.factor j) ≤ Nat.card phi.ker :=
  (FiniteGroupBinaryOrderGenerators.two_pow_genRank_le_card (C.factor j)).trans
    (factor_card_le_local_kernel rho phi hrho C j)

theorem factor_genRank_le_of_local_card_le_two_pow (a : ℕ)
    (ha : Nat.card phi.ker ≤ 2 ^ a) : MarkedC4.genRank (C.factor j) ≤ a :=
  (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    ((two_pow_factor_genRank_le_local_kernel rho phi hrho C j).trans ha)

end SymmetricSubgroupAsymptotics.ActualWreathChiefFactorOrder
