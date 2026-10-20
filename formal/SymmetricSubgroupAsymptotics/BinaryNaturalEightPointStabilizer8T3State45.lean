import Mathlib.Algebra.Field.ZMod
import SymmetricSubgroupAsymptotics.BinaryEightOriginalRowActions
import SymmetricSubgroupAsymptotics.BinaryRegularEightSquareCarry

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryNaturalEightPointStabilizer8T3State45

open BinaryEightOriginalRowActions
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
theorem count_bound : ∀ v : Fin 8 → ZMod 2, v ∉ BinaryRegularEightSquareCarry.K45 →
  Nat.card {i : Fin 8 // regularRho (regularRow i) v - v ∈ BinaryRegularEightSquareCarry.R45} ≤ 2 := by
  simp only [BinaryRegularEightSquareCarry.K45, BinaryRegularEightSquareCarry.R45, BinaryRegularEightSquareCarry.annihilatorSpace, Submodule.mem_iInf, LinearMap.mem_ker]
  simp only [Nat.card_eq_fintype_card]
  decide +kernel
theorem kernel_le (D : Subgroup regularH) (hD : 2 < Nat.card D)
    (K : Submodule (ZMod 2) (Fin 8 → ZMod 2))
    (hfixed : ∀ d : D, ∀ v ∈ K, regularRho (d : regularH) v - v ∈ BinaryRegularEightSquareCarry.R45) :
    K ≤ BinaryRegularEightSquareCarry.K45 :=
  submodule_le_of_small_stabilizer_rows (k := ZMod 2)
    (H := regularH) (V := Fin 8 → ZMod 2) regularRow regularRow_bijective regularRho
    BinaryRegularEightSquareCarry.K45 BinaryRegularEightSquareCarry.R45 K 2 count_bound D hD hfixed

end SymmetricSubgroupAsymptotics.BinaryNaturalEightPointStabilizer8T3State45
