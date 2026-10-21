import SymmetricSubgroupAsymptotics.BinarySplitHeisenberg14PhiZeroStabilizerCountData

/-! Four actual original rows for ONE quotient code. Pairwise scalar
images, not a full stabilizer count, are independently checked below. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinarySplitHeisenberg14PhiZeroStabilizer

def code1OrbitRows : Fin 4 → Fin 256 := ![0,32,96,160]

theorem code1_orbit_images_separated : ∀ i j : Fin 4, i ≠ j →
    rowAction (code1OrbitRows i) (sectionMap (binaryVectorOfMask 6 1)) -
      rowAction (code1OrbitRows j) (sectionMap (binaryVectorOfMask 6 1)) ∉ radical.space := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel

end SymmetricSubgroupAsymptotics.BinarySplitHeisenberg14PhiZeroStabilizer
