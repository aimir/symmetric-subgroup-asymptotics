import SymmetricSubgroupAsymptotics.BinaryEightTop30CyclicChunk0
import SymmetricSubgroupAsymptotics.BinaryEightTop30CyclicChunk1
import SymmetricSubgroupAsymptotics.BinaryEightTop30CyclicChunk2
import SymmetricSubgroupAsymptotics.BinaryEightTop30CyclicChunk3
import SymmetricSubgroupAsymptotics.BinaryEightTop30CyclicChunk4
import SymmetricSubgroupAsymptotics.BinaryEightTop30CyclicChunk5
import SymmetricSubgroupAsymptotics.BinaryEightTop30CyclicChunk6
import SymmetricSubgroupAsymptotics.BinaryEightTop30CyclicChunk7
import SymmetricSubgroupAsymptotics.BinaryInvariantChainRegistry

/-! Complete nine-state natural-module coverage for original8T30. The
finite point-orbit certificates and checked chain force completeness;
no list of normals or degree16 extensions is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryEightTop30NaturalComplete
open BinaryEightTop30CoordinateAction BinaryEightTop30NineStates
private theorem mask_lt : ∀ v : V, binaryVectorMask v < 256 := by decide +kernel

theorem point_exists (v : V) : ∃ i : Fin 9,
    (states i).toSubmodule = binaryOrbitSpan rho v := by
  have hmax := mask_lt v
  by_cases h0 : binaryVectorMask v < 32
  · exact ⟨_,BinaryEightTop30CyclicChunk0.point_span v (by omega) h0⟩
  by_cases h1 : binaryVectorMask v < 64
  · exact ⟨_,BinaryEightTop30CyclicChunk1.point_span v (by omega) h1⟩
  by_cases h2 : binaryVectorMask v < 96
  · exact ⟨_,BinaryEightTop30CyclicChunk2.point_span v (by omega) h2⟩
  by_cases h3 : binaryVectorMask v < 128
  · exact ⟨_,BinaryEightTop30CyclicChunk3.point_span v (by omega) h3⟩
  by_cases h4 : binaryVectorMask v < 160
  · exact ⟨_,BinaryEightTop30CyclicChunk4.point_span v (by omega) h4⟩
  by_cases h5 : binaryVectorMask v < 192
  · exact ⟨_,BinaryEightTop30CyclicChunk5.point_span v (by omega) h5⟩
  by_cases h6 : binaryVectorMask v < 224
  · exact ⟨_,BinaryEightTop30CyclicChunk6.point_span v (by omega) h6⟩
  exact ⟨_,BinaryEightTop30CyclicChunk7.point_span v (by omega) hmax⟩

theorem complete (W : Subrepresentation rho) : ∃ i, states i = W :=
  binaryInvariantChain_complete rho states 0 bottom_space chain point_exists W
end SymmetricSubgroupAsymptotics.BinaryEightTop30NaturalComplete
