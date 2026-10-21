import SymmetricSubgroupAsymptotics.BinaryRegularFullConstantTopCenter
import SymmetricSubgroupAsymptotics.BinaryPairCanonicalCoordinateAction

/-! Six actual original elements have the literal fullconstant coordinate
operators. Only the inner proved zero model is used; the outer pair source
and its arbitrary lift offsets are never split. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryRegularFullConstantOriginalCoordinateRows
local instance fullConstantOriginalRowsFactPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
open BinaryRegularSixCanonicalGenerators
private theorem top_original : ∀ i : Fin 6,topRows i=1 ∨
    ∃ j : Fin 3,topRows i=BinaryMenuCayley8T3.generators j := by decide +kernel
private theorem offsets_mem : ∀ i : Fin 6,binaryVectorOfMask 8 (offsetMasks i)∈K.space := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel
private theorem canonical_points : ∀ i : Fin 6,∀ x : Fin 16,
    binaryEightCanonicalPairFrame.affinePermutation (topRows i) (binaryVectorOfMask 8 (offsetMasks i)) x=
      BinaryRegular46FullConstantOuterCarries.generators i x := by decide +kernel

namespace BinaryPairFrame
variable {H : Subgroup (Equiv.Perm (Fin 16))} (E : SymmetricSubgroupAsymptotics.BinaryPairFrame H (Fin 8))
include E

theorem exists_actual_six_coordinate_rows
    (hzero : H=E.splitAffineAction)
    (hH : E.top.range=Subgroup.closure (Set.range BinaryMenuCayley8T3.generators))
    (hK : E.kernelSpace=K.space) :
    ∃ u : Fin 6 → H,∀ i,E.originalCoordinateRepresentation (u i)=BinaryRegularFullConstantPlaneOne.action i := by
  have ht (i : Fin 6) : topRows i∈E.top.range := by
    rw [hH]
    rcases top_original i with hi | ⟨j,hi⟩
    · rw [hi];exact Subgroup.one_mem _
    · rw [hi];exact Subgroup.subset_closure ⟨j,rfl⟩
  have ha (i : Fin 6) : binaryVectorOfMask 8 (offsetMasks i)∈E.kernelSpace := by
    rw [hK];exact offsets_mem i
  let u : Fin 6 → H := fun i => E.originalZeroRow hzero ⟨topRows i,ht i⟩
    (binaryVectorOfMask 8 (offsetMasks i)) (ha i)
  refine ⟨u,fun i => ?_⟩
  have hc : E.canonicalPointLabels.permCongrHom (u i).val=
      BinaryRegular46FullConstantOuterCarries.generators i := by
    change E.canonicalPointLabels.permCongrHom
      (E.affinePermutation (topRows i) (binaryVectorOfMask 8 (offsetMasks i)))=_
    rw [E.canonical_affinePermutation]
    exact Equiv.ext (canonical_points i)
  rw [E.originalCoordinateRepresentation_canonical,hc]
  rfl

end BinaryPairFrame
end SymmetricSubgroupAsymptotics.BinaryRegularFullConstantOriginalCoordinateRows
