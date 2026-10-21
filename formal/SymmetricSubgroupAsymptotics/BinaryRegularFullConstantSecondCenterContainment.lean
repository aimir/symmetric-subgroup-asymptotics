import SymmetricSubgroupAsymptotics.BinaryPairCanonicalCenterLine
import SymmetricSubgroupAsymptotics.BinaryRegularFullConstantCentralTopTrivial
import SymmetricSubgroupAsymptotics.BinaryPairKernelCentralQuotientBits
import SymmetricSubgroupAsymptotics.BinaryPairQuotientCentralTop

/-! The actual second centre of the original fullconstant source has
zero top image and lies in the SAME literal four-space. Arbitrary outer
lift offsets are retained throughout. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
private theorem fullconstant_line_basis_plane : ∀ j : Fin 1,
    BinaryRegularFullConstantSevenPlanes.line.inclusion (Pi.single j 1)∈
      BinaryRegularFullConstantPlaneOne.plane.space := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel
private theorem fullconstant_line_le_plane :
    BinaryRegularFullConstantSevenPlanes.line.space≤BinaryRegularFullConstantPlaneOne.plane.space :=
  BinaryRegularFullConstantSevenPlanes.line.le_of_basis_mem _ fullconstant_line_basis_plane
namespace BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16)) (E : BinaryPairFrame F.top.range (Fin 8))
    [MulAction.IsPretransitive U X]
include F E

theorem fullconstant_second_center_actual_coordinate_element
    (hU : IsPGroup 2 U)
    (hzero : F.top.range=E.splitAffineAction)
    (hH : E.top.range=Subgroup.closure (Set.range BinaryMenuCayley8T3.generators))
    (hK : E.kernelSpace=BinaryRegularSixCanonicalGenerators.K.space)
    (hspace : F.kernelSpace.map E.originalCoordinateEquiv.toLinearMap=
      BinaryRegularFullConstantPlaneOne.K.space)
    (z : U) (hz : QuotientGroup.mk' (Subgroup.center U) z∈
      Subgroup.center (U ⧸ Subgroup.center U)) :
    ∃ k : F.top.ker,(k : U)=z ∧
      E.originalCoordinateEquiv (F.bits k)∈BinaryRegularFullConstantSecondCenterSpace.room.space := by
  let e := E.originalCoordinateEquiv
  have hN : Subgroup.center U≤F.top.ker :=
    F.original_center_le_kernel_of_fullconstant_space E hU hspace
  have hA : (F.ambientAxis (Subgroup.center U)).map e.toLinearMap≤
      BinaryRegularFullConstantPlaneOne.plane.space :=
    (F.original_center_axis_le_canonical_line E).trans fullconstant_line_le_plane
  have heact (t : F.top.range) (a : Fin 16 → ZMod 2) :
      E.originalCoordinateRepresentation t (e a)-e a=e (F.coordinateTopAction t a-a) := by
    change e (F.coordinateTopAction t (e.symm (e a)))-e a=e _
    rw [e.symm_apply_apply,map_sub]
  have hdelta (a : Fin 16 → ZMod 2) (ha : a∈F.kernelSpace) :
      F.coordinateTopAction (F.top.rangeRestrict z) a-a∈F.ambientAxis (Subgroup.center U) := by
    obtain ⟨k,hk⟩ := ha
    change F.bits k.toMul=a at hk
    rw [←hk]
    exact F.central_quotient_displacement_axis (Subgroup.center U) z hz k.toMul
  have ht : F.top.rangeRestrict z=1 := by
    apply BinaryRegularFullConstantCentralTopTrivial.actual_central_top_eq_one E hzero hH hK
      (F.top.rangeRestrict z) (F.quotient_central_top_mem_center (Subgroup.center U) hN z hz)
    intro a ha
    rw [←hspace] at ha
    obtain ⟨v,hv,rfl⟩ := ha
    change E.originalCoordinateRepresentation (F.top.rangeRestrict z) (e v)-e v∈
      BinaryRegularFullConstantPlaneOne.plane.space
    rw [heact]
    exact hA ⟨_,hdelta v hv,rfl⟩
  have hzk : z∈F.top.ker := congrArg Subtype.val ht
  let k : F.top.ker := ⟨z,hzk⟩
  refine ⟨k,rfl,?_⟩
  apply BinaryRegularFullConstantSecondCenterSpace.fixed_mem_room
    (⟨e (F.bits k),?_,?_⟩ : binaryCoordinateFixedDisplacements
      BinaryRegularFullConstantPlaneOne.K BinaryRegularFullConstantPlaneOne.action
      BinaryRegularFullConstantPlaneOne.plane.space)
  · rw [←hspace]
    exact ⟨F.bits k,⟨Additive.ofMul k,rfl⟩,rfl⟩
  · obtain ⟨u,hu⟩ := BinaryRegularFullConstantOriginalCoordinateRows.BinaryPairFrame.exists_actual_six_coordinate_rows
      E hzero hH hK
    intro i
    rw [←hu,heact]
    exact hA ⟨_,F.kernel_central_quotient_bits_displacement (Subgroup.center U) k hz (u i),rfl⟩
end BinaryPairFrame
end SymmetricSubgroupAsymptotics
