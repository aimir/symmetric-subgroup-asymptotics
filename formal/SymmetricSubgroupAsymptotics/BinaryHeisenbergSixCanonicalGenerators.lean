import SymmetricSubgroupAsymptotics.BinaryPairCanonicalAffinePermutation
import SymmetricSubgroupAsymptotics.BinaryPairSplitBasisGeneration
import SymmetricSubgroupAsymptotics.BinaryHeisenbergEightNaturalHeads
import SymmetricSubgroupAsymptotics.BinaryHeisenbergEightSquareCarryData

/-! The Heisenberg-K14 zero model has six literal canonical generators.
Three sparse kernel-basis words and the four retained original top
involutions establish completeness on the same original points. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryHeisenbergSixCanonicalGenerators
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private abbrev P := binaryEightCanonicalPairFrame
abbrev K := BinaryRegularEightNaturalRegistry.chart40

def topRows : Fin 6 → Equiv.Perm (Fin 8) :=
  ![1,1,BinaryHeisenbergEightSquareCarry.originalSelected 0,
    BinaryHeisenbergEightSquareCarry.originalSelected 1,
    BinaryHeisenbergEightSquareCarry.originalSelected 2,
    BinaryHeisenbergEightSquareCarry.originalSelected 3]
def offsetMasks : Fin 6 → ℕ := ![135,102,0,0,0,0]
def generators (i : Fin 6) : Equiv.Perm (Fin 16) :=
  P.affinePermutation (topRows i) (binaryVectorOfMask 8 (offsetMasks i))
private def kernelWords : Fin 3 → Equiv.Perm (Fin 16) :=
  ![generators 0,generators 1,
    generators 0 * generators 1 *
      (generators 0 * generators 3 * (generators 0)⁻¹ * (generators 3)⁻¹)]
private theorem kernelWords_apply : ∀ j : Fin 3, ∀ x : Fin 16,
    P.physicalFlip (K.inclusion (Pi.single j 1)) x = kernelWords j x := by decide +kernel
private theorem offset_mem : ∀ i : Fin 6,
    binaryVectorOfMask 8 (offsetMasks i) ∈ K.space := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel
private theorem topRows_mem : ∀ i : Fin 6,
    topRows i ∈ Subgroup.closure (Set.range BinaryMenuCayley8T22.generators) := by
  intro i
  fin_cases i
  · exact Subgroup.one_mem _
  · exact Subgroup.one_mem _
  · exact Subgroup.subset_closure ⟨1,rfl⟩
  · exact Subgroup.subset_closure ⟨2,rfl⟩
  · exact Subgroup.subset_closure ⟨3,rfl⟩
  · exact Subgroup.subset_closure ⟨4,rfl⟩
private theorem zero_top_generator (j : Fin 4) :
    P.affinePermutation (BinaryHeisenbergEightSquareCarry.originalSelected j) 0 =
      generators ⟨2+j.val,by omega⟩ := by
  apply Equiv.ext
  intro x
  fin_cases j <;> (revert x;decide +kernel)

namespace BinaryPairFrame
variable {X : Type} {U : Subgroup (Equiv.Perm X)}
    (E : SymmetricSubgroupAsymptotics.BinaryPairFrame U (Fin 8))

theorem canonical_heisenberg_six_closure
    (hzero : U = E.splitAffineAction)
    (hH : E.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T22.generators))
    (hK : E.kernelSpace = K.space) :
    U.map E.canonicalPointLabels.permCongrHom = Subgroup.closure (Set.range generators) := by
  let C := Subgroup.closure (Set.range generators)
  let e := E.canonicalPointLabels.permCongrHom
  have hgen (i : Fin 6) : generators i ∈ C := Subgroup.subset_closure ⟨i,rfl⟩
  have hword (j : Fin 3) : kernelWords j ∈ C := by
    fin_cases j
    · exact hgen 0
    · exact hgen 1
    · exact C.mul_mem (C.mul_mem (hgen 0) (hgen 1))
        (C.mul_mem (C.mul_mem (C.mul_mem (hgen 0) (hgen 3)) (C.inv_mem (hgen 0)))
          (C.inv_mem (hgen 3)))
  apply le_antisymm
  · have hle : E.splitAffineAction ≤ C.comap e := by
      apply E.splitAffineAction_le_of_kernel_basis_and_top (C.comap e) K hK
        BinaryHeisenbergEightSquareCarry.originalSelected
        (BinaryHeisenbergEightSquareCarry.selected_closure_eq_original.trans hH.symm)
      · intro j
        change e (E.physicalFlip (K.inclusion (Pi.single j 1))) ∈ C
        rw [show e (E.physicalFlip (K.inclusion (Pi.single j 1))) =
            P.physicalFlip (K.inclusion (Pi.single j 1)) from E.canonical_affinePermutation _ _]
        rw [show P.physicalFlip (K.inclusion (Pi.single j 1)) = kernelWords j from
          Equiv.ext (kernelWords_apply j)]
        exact hword j
      · intro j
        change e (E.affinePermutation (BinaryHeisenbergEightSquareCarry.originalSelected j) 0) ∈ C
        rw [E.canonical_affinePermutation,zero_top_generator]
        exact hgen _
    rintro p ⟨a,ha,rfl⟩
    exact hle (hzero ▸ ha)
  · apply (Subgroup.closure_le _).mpr
    rintro p ⟨i,rfl⟩
    have ht : topRows i ∈ E.top.range := by rw [hH];exact topRows_mem i
    have ha : binaryVectorOfMask 8 (offsetMasks i) ∈ E.kernelSpace := by
      rw [hK];exact offset_mem i
    refine ⟨E.affinePermutation (topRows i) (binaryVectorOfMask 8 (offsetMasks i)),?_,?_⟩
    · have hm : E.affinePermutation (topRows i) (binaryVectorOfMask 8 (offsetMasks i)) ∈
          E.splitAffineAction := Subgroup.subset_closure ⟨⟨_,ht⟩,_,ha,rfl⟩
      exact (congrArg (fun C : Subgroup (Equiv.Perm X) =>
        E.affinePermutation (topRows i) (binaryVectorOfMask 8 (offsetMasks i)) ∈ C) hzero).mpr hm
    · exact E.canonical_affinePermutation _ _

end BinaryPairFrame
end SymmetricSubgroupAsymptotics.BinaryHeisenbergSixCanonicalGenerators
