import SymmetricSubgroupAsymptotics.BinaryRegularFullConstantSecondCenterContainment
import SymmetricSubgroupAsymptotics.BinaryPairCanonicalKernelAxisCards
import SymmetricSubgroupAsymptotics.BinaryNormalOrderFourContainsSmallCenter

/-! Every actual normal of order four is carried into one of seven
planes of the SAME kernel coordinates. There is no original-normal list
and no assumption that the outer extension splits. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance fullConstantNormalFourCoverPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16)) (E : BinaryPairFrame F.top.range (Fin 8))
    [MulAction.IsPretransitive U X]
include F E

theorem fullconstant_normal_four_original_coordinate_cover
    (hU : IsPGroup 2 U)
    (hzero : F.top.range=E.splitAffineAction)
    (hH : E.top.range=Subgroup.closure (Set.range BinaryMenuCayley8T3.generators))
    (hK : E.kernelSpace=BinaryRegularSixCanonicalGenerators.K.space)
    (hspace : F.kernelSpace.map E.originalCoordinateEquiv.toLinearMap=
      BinaryRegularFullConstantPlaneOne.K.space)
    (L : Subgroup U) [L.Normal] (hcard : Nat.card L=4) :
    L≤F.top.ker ∧ ∃ i : Fin 7,
      (F.ambientAxis L).map E.originalCoordinateEquiv.toLinearMap≤
        (BinaryRegularFullConstantSevenPlanes.plane i).space := by
  have hLZ := binary_normal_order_four_le_second_center hU L hcard
  have hZK := F.original_center_le_kernel_of_fullconstant_space E hU hspace
  have hLker : L≤F.top.ker := by
    intro z hz
    obtain ⟨k,hk,_⟩ := F.fullconstant_second_center_actual_coordinate_element E hU hzero hH hK hspace
      z (hLZ hz)
    exact hk ▸ k.property
  refine ⟨hLker,?_⟩
  let A := (F.ambientAxis L).map E.originalCoordinateEquiv.toLinearMap
  have hroom : A≤BinaryRegularFullConstantSecondCenterSpace.room.space := by
    rintro v ⟨a,ha,rfl⟩
    obtain ⟨k,hk,rfl⟩ := (F.mem_ambientAxis L a).mp ha
    obtain ⟨k',he,hmem⟩ := F.fullconstant_second_center_actual_coordinate_element E hU hzero hH hK hspace
      (k : U) (hLZ hk)
    have hkk : k'=k := Subtype.ext he
    simpa only [hkk] using hmem
  have hcenter := F.original_fullconstant_center_card_le_two E hU hspace
  have hZL := binary_normal_order_four_contains_center_of_card_le_two hU hcenter L hcard
  letI : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp (by
    have hc := Subgroup.card_le_card_group L
    rw [hcard] at hc
    omega)
  letI : Nontrivial (Subgroup.center U) := hU.center_nontrivial
  have hcenterCard : Nat.card (Subgroup.center U)=2 := by
    have hh : 1<Nat.card (Subgroup.center U) := Finite.one_lt_card
    omega
  let Z := (F.ambientAxis (Subgroup.center U)).map E.originalCoordinateEquiv.toLinearMap
  have hZline : Z≤BinaryRegularFullConstantSevenPlanes.line.space :=
    F.original_center_axis_le_canonical_line E
  have hZcard : Nat.card Z=2 :=
    (F.original_coordinate_axis_card_of_le_kernel E (Subgroup.center U) hZK).trans hcenterCard
  have hZE : Z=BinaryRegularFullConstantSevenPlanes.line.space := by
    have he : Z.toAddSubgroup=BinaryRegularFullConstantSevenPlanes.line.space.toAddSubgroup :=
      AddSubgroup.eq_of_le_of_card_ge hZline (by
        change Nat.card BinaryRegularFullConstantSevenPlanes.line.space≤Nat.card Z
        rw [BinaryRegularFullConstantSevenPlanes.line.card,hZcard]
        decide)
    ext v
    change v∈Z.toAddSubgroup ↔ v∈BinaryRegularFullConstantSevenPlanes.line.space.toAddSubgroup
    rw [he]
  have hline : BinaryRegularFullConstantSevenPlanes.line.space≤A := by
    rw [←hZE]
    rintro v ⟨a,ha,rfl⟩
    obtain ⟨k,hk,rfl⟩ := (F.mem_ambientAxis (Subgroup.center U) a).mp ha
    exact ⟨_,(F.mem_ambientAxis L _).mpr ⟨k,hZL hk,rfl⟩,rfl⟩
  have hAcard : Nat.card A=4 :=
    (F.original_coordinate_axis_card_of_le_kernel E L hLker).trans hcard
  exact BinaryRegularFullConstantSevenPlanes.cover A hroom hline hAcard
end SymmetricSubgroupAsymptotics.BinaryPairFrame
