import SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T3Kernel23Chunk0Data
import SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T3Kernel23Chunk1Data
import SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T3Kernel23Chunk2Data
import SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T3Kernel23Chunk3Data
import SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T3Kernel23Chunk4Data
import SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T3Kernel23Chunk5Data

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T3Kernel23
open BinaryRegularEightNaturalRegistry

def chunkSize : Fin 6 → ℕ := ![120,120,120,120,120,3]
def sourceIndex : (c : Fin 6) → Fin (chunkSize c) → Fin 47 :=
  (Fin.cases BinaryPairLayerHead8T3Kernel23Chunk0.sourceIndex (Fin.cases BinaryPairLayerHead8T3Kernel23Chunk1.sourceIndex (Fin.cases BinaryPairLayerHead8T3Kernel23Chunk2.sourceIndex (Fin.cases BinaryPairLayerHead8T3Kernel23Chunk3.sourceIndex (Fin.cases BinaryPairLayerHead8T3Kernel23Chunk4.sourceIndex (Fin.cases BinaryPairLayerHead8T3Kernel23Chunk5.sourceIndex (fun i : Fin 0 => Fin.elim0 i)))))))
def targetIndex : (c : Fin 6) → Fin (chunkSize c) → Fin 47 :=
  (Fin.cases BinaryPairLayerHead8T3Kernel23Chunk0.targetIndex (Fin.cases BinaryPairLayerHead8T3Kernel23Chunk1.targetIndex (Fin.cases BinaryPairLayerHead8T3Kernel23Chunk2.targetIndex (Fin.cases BinaryPairLayerHead8T3Kernel23Chunk3.targetIndex (Fin.cases BinaryPairLayerHead8T3Kernel23Chunk4.targetIndex (Fin.cases BinaryPairLayerHead8T3Kernel23Chunk5.targetIndex (fun i : Fin 0 => Fin.elim0 i)))))))
def denominatorIndex : (c : Fin 6) → Fin (chunkSize c) → Fin 47 :=
  (Fin.cases BinaryPairLayerHead8T3Kernel23Chunk0.denominatorIndex (Fin.cases BinaryPairLayerHead8T3Kernel23Chunk1.denominatorIndex (Fin.cases BinaryPairLayerHead8T3Kernel23Chunk2.denominatorIndex (Fin.cases BinaryPairLayerHead8T3Kernel23Chunk3.denominatorIndex (Fin.cases BinaryPairLayerHead8T3Kernel23Chunk4.denominatorIndex (Fin.cases BinaryPairLayerHead8T3Kernel23Chunk5.denominatorIndex (fun i : Fin 0 => Fin.elim0 i)))))))

def compatible (i j : Fin 47) : Prop := ∀ a : Fin (charts 23).1,
  ∀ b : Fin (charts i).1,
    (charts 23).2.inclusion (Pi.single a 1) * (charts i).2.inclusion (Pi.single b 1) ∈
      (charts j).2.space

theorem covered : ∀ i j : Fin 47, compatible i j →
    ∃ c : Fin 6, ∃ p : Fin (chunkSize c), sourceIndex c p = i ∧ targetIndex c p = j := by
  unfold compatible
  intro i
  fin_cases i <;> decide +kernel

theorem finite_pair_bound (c : Fin 6) (p : Fin (chunkSize c))
    (hproduct : binaryCoordinateProductSpan (charts 23).2.space
      (states (sourceIndex c p)).toSubmodule ≤ (states (targetIndex c p)).toSubmodule) :
    Module.finrank (ZMod 2) (states (sourceIndex c p)).toRepresentation.Coinvariants +
      Module.finrank (ZMod 2) ((states (targetIndex c p)).toSubmodule ⧸
        ((binaryCoordinateProductSpan (charts 23).2.space
          (states (sourceIndex c p)).toSubmodule).comap (states (targetIndex c p)).toSubmodule.subtype ⊔
            Representation.Coinvariants.ker (states (targetIndex c p)).toRepresentation)) ≤ 6 := by
  fin_cases c
  · exact BinaryPairLayerHead8T3Kernel23Chunk0.finite_pair_bound p hproduct
  · exact BinaryPairLayerHead8T3Kernel23Chunk1.finite_pair_bound p hproduct
  · exact BinaryPairLayerHead8T3Kernel23Chunk2.finite_pair_bound p hproduct
  · exact BinaryPairLayerHead8T3Kernel23Chunk3.finite_pair_bound p hproduct
  · exact BinaryPairLayerHead8T3Kernel23Chunk4.finite_pair_bound p hproduct
  · exact BinaryPairLayerHead8T3Kernel23Chunk5.finite_pair_bound p hproduct

theorem denominator_dimension_le (c : Fin 6) (p : Fin (chunkSize c))
    (hproduct : binaryCoordinateProductSpan (charts 23).2.space
      (states (sourceIndex c p)).toSubmodule ≤ (states (targetIndex c p)).toSubmodule) :
    (charts (denominatorIndex c p)).1 +
      Module.finrank (ZMod 2) ((states (targetIndex c p)).toSubmodule ⧸
        ((binaryCoordinateProductSpan (charts 23).2.space
          (states (sourceIndex c p)).toSubmodule).comap (states (targetIndex c p)).toSubmodule.subtype ⊔
            Representation.Coinvariants.ker (states (targetIndex c p)).toRepresentation)) ≤
      (charts (targetIndex c p)).1 := by
  fin_cases c
  · exact BinaryPairLayerHead8T3Kernel23Chunk0.denominator_dimension_le p hproduct
  · exact BinaryPairLayerHead8T3Kernel23Chunk1.denominator_dimension_le p hproduct
  · exact BinaryPairLayerHead8T3Kernel23Chunk2.denominator_dimension_le p hproduct
  · exact BinaryPairLayerHead8T3Kernel23Chunk3.denominator_dimension_le p hproduct
  · exact BinaryPairLayerHead8T3Kernel23Chunk4.denominator_dimension_le p hproduct
  · exact BinaryPairLayerHead8T3Kernel23Chunk5.denominator_dimension_le p hproduct

theorem wide_indices (c : Fin 6) (p : Fin (chunkSize c))
    (hnum : (charts (denominatorIndex c p)).1 + 6 ≤
      headCeiling (sourceIndex c p) + (charts (targetIndex c p)).1) :
    sourceIndex c p = 46 ∧ targetIndex c p = 45 := by
  fin_cases c
  · exact BinaryPairLayerHead8T3Kernel23Chunk0.wide_indices p hnum
  · exact BinaryPairLayerHead8T3Kernel23Chunk1.wide_indices p hnum
  · exact BinaryPairLayerHead8T3Kernel23Chunk2.wide_indices p hnum
  · exact BinaryPairLayerHead8T3Kernel23Chunk3.wide_indices p hnum
  · exact BinaryPairLayerHead8T3Kernel23Chunk4.wide_indices p hnum
  · exact BinaryPairLayerHead8T3Kernel23Chunk5.wide_indices p hnum

end SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T3Kernel23
