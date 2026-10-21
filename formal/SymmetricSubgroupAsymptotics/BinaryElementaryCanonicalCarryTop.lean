import SymmetricSubgroupAsymptotics.BinaryElementary16PhiZeroOuterCarriesDefinitions
import SymmetricSubgroupAsymptotics.BinaryPairCanonicalAffinePermutation
import SymmetricSubgroupAsymptotics.BinaryPairSplitBasisGeneration
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryCharts
import SymmetricSubgroupAsymptotics.BinaryPairFrameConjugateTop

/-! The elementary carry packet's four rows generate precisely the same
original constant-kernel zero model in canonical point coordinates. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace BinaryElementaryCanonicalCarryTop
private abbrev P := binaryEightCanonicalPairFrame
abbrev K := BinaryRegularEightNaturalRegistry.chart23
private def topRows : Fin 4 → Equiv.Perm (Fin 8) :=
  ![1,BinaryMenuCayley8T3.generators 0,BinaryMenuCayley8T3.generators 1,
    BinaryMenuCayley8T3.generators 2]
private def offsetMasks : Fin 4 → ℕ := ![255,0,0,0]
private theorem row_points : ∀ i : Fin 4, ∀ x : Fin 16,
    P.affinePermutation (topRows i) (binaryVectorOfMask 8 (offsetMasks i)) x =
      BinaryElementary16PhiZeroOuterCarries.generators i x := by decide +kernel
private theorem flip_points : ∀ j : Fin 1, ∀ x : Fin 16,
    P.physicalFlip (K.inclusion (Pi.single j 1)) x =
      BinaryElementary16PhiZeroOuterCarries.generators 0 x := by decide +kernel
private theorem top_points : ∀ j : Fin 3, ∀ x : Fin 16,
    P.affinePermutation (BinaryMenuCayley8T3.generators j) 0 x =
      BinaryElementary16PhiZeroOuterCarries.generators ⟨1+j.val,by omega⟩ x := by decide +kernel
private theorem offsets_mem : ∀ i : Fin 4,
    binaryVectorOfMask 8 (offsetMasks i) ∈ K.space := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel
private theorem topRows_mem : ∀ i : Fin 4,
    topRows i ∈ Subgroup.closure (Set.range BinaryMenuCayley8T3.generators) := by
  intro i
  fin_cases i
  · exact Subgroup.one_mem _
  · exact Subgroup.subset_closure ⟨0,rfl⟩
  · exact Subgroup.subset_closure ⟨1,rfl⟩
  · exact Subgroup.subset_closure ⟨2,rfl⟩
end BinaryElementaryCanonicalCarryTop

namespace BinaryPairFrame
open BinaryElementaryCanonicalCarryTop
variable {Y : Type} {V : Subgroup (Equiv.Perm Y)} (E : BinaryPairFrame V (Fin 8))

theorem canonical_elementary_four_closure
    (hzero : V = E.splitAffineAction)
    (hH : E.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T3.generators))
    (hK : E.kernelSpace = K.space) :
    V.map E.canonicalPointLabels.permCongrHom =
      Subgroup.closure (Set.range BinaryElementary16PhiZeroOuterCarries.generators) := by
  let C := Subgroup.closure (Set.range BinaryElementary16PhiZeroOuterCarries.generators)
  let e := E.canonicalPointLabels.permCongrHom
  have hgen (i : Fin 4) : BinaryElementary16PhiZeroOuterCarries.generators i ∈ C :=
    Subgroup.subset_closure ⟨i,rfl⟩
  apply le_antisymm
  · have hle : E.splitAffineAction ≤ C.comap e := by
      apply E.splitAffineAction_le_of_kernel_basis_and_top (C.comap e) K hK
        BinaryMenuCayley8T3.generators hH.symm
      · intro j
        change e (E.physicalFlip (K.inclusion (Pi.single j 1))) ∈ C
        rw [show e (E.physicalFlip (K.inclusion (Pi.single j 1))) =
            binaryEightCanonicalPairFrame.physicalFlip (K.inclusion (Pi.single j 1)) from
              E.canonical_affinePermutation _ _]
        rw [show binaryEightCanonicalPairFrame.physicalFlip (K.inclusion (Pi.single j 1)) =
            BinaryElementary16PhiZeroOuterCarries.generators 0 from Equiv.ext (flip_points j)]
        exact hgen 0
      · intro j
        change e (E.affinePermutation (BinaryMenuCayley8T3.generators j) 0) ∈ C
        rw [E.canonical_affinePermutation,
          show binaryEightCanonicalPairFrame.affinePermutation (BinaryMenuCayley8T3.generators j) 0 =
            BinaryElementary16PhiZeroOuterCarries.generators ⟨1+j.val,by omega⟩ from
              Equiv.ext (top_points j)]
        exact hgen _
    rintro p ⟨a,ha,rfl⟩
    exact hle (hzero ▸ ha)
  · apply (Subgroup.closure_le _).mpr
    rintro p ⟨i,rfl⟩
    have ht : topRows i ∈ E.top.range := by rw [hH];exact topRows_mem i
    have ha : binaryVectorOfMask 8 (offsetMasks i) ∈ E.kernelSpace := by
      rw [hK];exact offsets_mem i
    refine ⟨E.affinePermutation (topRows i) (binaryVectorOfMask 8 (offsetMasks i)),?_,?_⟩
    · have hm : E.affinePermutation (topRows i) (binaryVectorOfMask 8 (offsetMasks i)) ∈
          E.splitAffineAction := Subgroup.subset_closure ⟨⟨_,ht⟩,_,ha,rfl⟩
      exact (congrArg (fun C : Subgroup (Equiv.Perm Y) =>
        E.affinePermutation (topRows i) (binaryVectorOfMask 8 (offsetMasks i)) ∈ C) hzero).mpr hm
    · exact (E.canonical_affinePermutation _ _).trans (Equiv.ext (row_points i))

variable {X : Type} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16)) (E' : BinaryPairFrame F.top.range (Fin 8))

theorem canonical_elementary_carry_top_range
    (hzero : F.top.range = E'.splitAffineAction)
    (hH : E'.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T3.generators))
    (hK : E'.kernelSpace = K.space) :
    (F.reindex E'.canonicalPointLabels).top.range =
      Subgroup.closure (Set.range BinaryElementary16PhiZeroOuterCarries.generators) := by
  rw [F.reindex_top_range]
  exact E'.canonical_elementary_four_closure hzero hH hK

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
