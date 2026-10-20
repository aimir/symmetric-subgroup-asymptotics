import SymmetricSubgroupAsymptotics.BinaryEightOriginalRowActions
import SymmetricSubgroupAsymptotics.BinaryHeisenbergEightSquareCarryData

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryNaturalEightPointStabilizer8T22State12

open BinaryEightOriginalRowActions
theorem count_bound : ∀ v : Fin 8 → ZMod 2, v ∉ BinaryHeisenbergEightSquareCarry.K12 →
  Nat.card {i : Fin 32 // heisenbergRho (heisenbergRow i) v - v ∈ BinaryHeisenbergEightSquareCarry.R12} ≤ 8 := by
  simp only [BinaryHeisenbergEightSquareCarry.K12, BinaryHeisenbergEightSquareCarry.R12, BinaryRegularEightSquareCarry.annihilatorSpace, Submodule.mem_iInf, LinearMap.mem_ker]
  simp only [Nat.card_eq_fintype_card]
  decide +kernel
theorem kernel_le (D : Subgroup heisenbergH) (hD : 8 < Nat.card D)
    (K : Submodule (ZMod 2) (Fin 8 → ZMod 2))
    (hfixed : ∀ d : D, ∀ v ∈ K, heisenbergRho (d : heisenbergH) v - v ∈ BinaryHeisenbergEightSquareCarry.R12) :
    K ≤ BinaryHeisenbergEightSquareCarry.K12 :=
  submodule_le_of_small_stabilizer_rows heisenbergRow heisenbergRow_bijective heisenbergRho
    BinaryHeisenbergEightSquareCarry.K12 BinaryHeisenbergEightSquareCarry.R12 K 8 count_bound D hD hfixed

end SymmetricSubgroupAsymptotics.BinaryNaturalEightPointStabilizer8T22State12
