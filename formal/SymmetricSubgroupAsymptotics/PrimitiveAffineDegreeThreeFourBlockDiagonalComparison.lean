import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockSignedDispatcher
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeNineCentralProductModel

/-!
# The literal diagonal four-block central-product comparison

In the one-sign branch, the kernel of the four-pair top map consists of
the simultaneous flip on all four pairs.  It is therefore central and has
order at most two.  The top image is a literal subgroup of `S₄`.

This is precisely the structural input used by the degree-nine
central-product construction.  The file applies the same construction to
the actual signed quotient `U / E`: for every literal normal quotient, its
projective image and the product of that image with `C₂` occur as two
distinct normal quotients of one faithful six-point comparator.  No finite
action catalogue or additional project-owned hypothesis enters.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

private abbrev C2 := Multiplicative (ZMod 2)

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

section ProjectiveMap

variable (hr : Nat.card block.Fibre = 3)
  (hs : Nat.card block.Points = 4)
  (hcomponent : Nat.card block.Component = 6)

private abbrev PairChart :=
  degreeThreeFourBlockPairChart block P hr hs hcomponent

/-- The actual four-point top of the literal signed quotient. -/
private abbrev DiagonalProjectiveImage :=
  (PairChart block P hr hs hcomponent).frame.top.range

/-- The literal signed quotient followed by its actual four-pair top map. -/
private def diagonalProjectiveMap :
    (preE7NonPairAction w U ⧸ E block P) →*
      DiagonalProjectiveImage block P hr hs hcomponent :=
  (PairChart block P hr hs hcomponent).frame.top.rangeRestrict.comp
    (PairChart block P hr hs hcomponent).sourceEquiv.toMonoidHom

private theorem diagonalProjectiveMap_surjective :
    Function.Surjective
      (diagonalProjectiveMap block P hr hs hcomponent) :=
  (PairChart block P hr hs hcomponent).frame.top.rangeRestrict_surjective.comp
    (PairChart block P hr hs hcomponent).sourceEquiv.surjective

/-- A kernel element of the projective map is the corresponding element of
the literal pair kernel. -/
private def diagonalProjectiveKernelToPairKernel
    (z : (diagonalProjectiveMap block P hr hs hcomponent).ker) :
    (PairChart block P hr hs hcomponent).frame.top.ker := by
  refine ⟨(PairChart block P hr hs hcomponent).sourceEquiv z.1, ?_⟩
  change (PairChart block P hr hs hcomponent).frame.top
      ((PairChart block P hr hs hcomponent).sourceEquiv z.1) = 1
  exact congrArg Subtype.val z.2

private theorem diagonalProjectiveKernelToPairKernel_injective :
    Function.Injective
      (diagonalProjectiveKernelToPairKernel block P hr hs hcomponent) := by
  intro x y hxy
  apply Subtype.ext
  apply (PairChart block P hr hs hcomponent).sourceEquiv.injective
  exact congrArg Subtype.val hxy

/-- The projective kernel is no larger than the actual diagonal pair
kernel, hence has order at most two. -/
private theorem diagonalProjectiveKernel_card_le_two
    (hdiag : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 1) :
    Nat.card (diagonalProjectiveMap block P hr hs hcomponent).ker ≤ 2 := by
  calc
    Nat.card (diagonalProjectiveMap block P hr hs hcomponent).ker ≤
        Nat.card (PairChart block P hr hs hcomponent).frame.top.ker :=
      Nat.card_le_card_of_injective
        (diagonalProjectiveKernelToPairKernel block P hr hs hcomponent)
        (diagonalProjectiveKernelToPairKernel_injective
          block P hr hs hcomponent)
    _ ≤ 2 := degreeThreeFourBlock_diagonalPairKernel_card_le_two
      block P hr hs hcomponent hdiag

/-- Constant pair bits are fixed by every top permutation.  Faithfulness of
the bit chart then makes every projective-kernel element central in the
literal signed quotient. -/
private theorem diagonalProjectiveMap_central_kernel
    (hdiag : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 1) :
    ∀ z ∈ (diagonalProjectiveMap block P hr hs hcomponent).ker,
      ∀ x : preE7NonPairAction w U ⧸ E block P, z * x = x * z := by
  let C := PairChart block P hr hs hcomponent
  have hconstant : ∀ (k : C.frame.top.ker) (i j : Fin 4),
      C.frame.bits k i = C.frame.bits k j :=
    (degreeThreeFourBlockSignedIsotype_eq_one_iff_bits_constant
      block P hr hs hcomponent).mp hdiag
  intro z hz x
  let k : C.frame.top.ker :=
    diagonalProjectiveKernelToPairKernel block P hr hs hcomponent ⟨z, hz⟩
  let u : C.action := C.sourceEquiv x
  have hkfixed : MulAut.conjNormal u k = k := by
    apply C.frame.bitsHom_injective
    apply congrArg Multiplicative.ofAdd
    funext i
    rw [C.frame.bits_conjNormal]
    exact hconstant k ((C.frame.top u)⁻¹ i) i
  have hcomm : (k : C.action) * u = u * k := by
    have hkfixed' := congrArg Subtype.val hkfixed
    change u * (k : C.action) * u⁻¹ = (k : C.action) at hkfixed'
    calc
      (k : C.action) * u = (u * (k : C.action) * u⁻¹) * u := by
        rw [hkfixed']
      _ = u * k := by simp [mul_assoc]
  change C.sourceEquiv z * C.sourceEquiv x =
    C.sourceEquiv x * C.sourceEquiv z at hcomm
  apply C.sourceEquiv.injective
  simpa only [map_mul] using hcomm

end ProjectiveMap

section Comparator

variable (hr : Nat.card block.Fibre = 3)
  (hs : Nat.card block.Points = 4)
  (hcomponent : Nat.card block.Component = 6)

/-- The actual four-point top, times one binary scalar, in the common
faithful six-point action. -/
private def diagonalProductAction :
    DiagonalProjectiveImage block P hr hs hcomponent × C2 →*
      Equiv.Perm (Fin 6) :=
  PrimitiveAffineProfile.degreeNineS4C2Action.comp
    ((DiagonalProjectiveImage block P hr hs hcomponent).subtype.prodMap
      (MonoidHom.id C2))

private theorem diagonalProductAction_injective :
    Function.Injective (diagonalProductAction block P hr hs hcomponent) := by
  intro a b hab
  have hab' := PrimitiveAffineProfile.degreeNineS4C2Action_injective hab
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun y : Equiv.Perm (Fin 4) × C2 => y.1) hab'
  · exact congrArg (fun y : Equiv.Perm (Fin 4) × C2 => y.2) hab'

/-- The fixed six-point comparator belonging to the literal four-point
top. -/
private abbrev DiagonalProductComparator :=
  (diagonalProductAction block P hr hs hcomponent).range

private def diagonalProductComparatorEquiv :
    DiagonalProjectiveImage block P hr hs hcomponent × C2 ≃*
      DiagonalProductComparator block P hr hs hcomponent :=
  MonoidHom.ofInjective
    (diagonalProductAction_injective block P hr hs hcomponent)

end Comparator

section Quotient

variable (hr : Nat.card block.Fibre = 3)
  (hs : Nat.card block.Points = 4)
  (hcomponent : Nat.card block.Component = 6)
  (hdiag : (degreeThreeFourBlockSignedIsotypeProfile
    block P hr hs hcomponent).isotypeCount = 1)
  (M : {M : Subgroup (preE7NonPairAction w U ⧸ E block P) // M.Normal})

local instance primitiveAffineDegreeThreeFourBlockDiagonalComparison_localInstance1 : M.1.Normal := M.2
local instance primitiveAffineDegreeThreeFourBlockDiagonalComparison_localInstance2 :
    (ProjectiveCentralQuotient.normalImage
      (diagonalProjectiveMap block P hr hs hcomponent)
      (diagonalProjectiveMap_surjective block P hr hs hcomponent) M).1.Normal :=
  (ProjectiveCentralQuotient.normalImage
    (diagonalProjectiveMap block P hr hs hcomponent)
    (diagonalProjectiveMap_surjective block P hr hs hcomponent) M).2

private abbrev QuotientProjectiveImage :=
  DiagonalProjectiveImage block P hr hs hcomponent ⧸
    (ProjectiveCentralQuotient.normalImage
      (diagonalProjectiveMap block P hr hs hcomponent)
      (diagonalProjectiveMap_surjective block P hr hs hcomponent) M).1

private def quotientProjectiveMap :
    ((preE7NonPairAction w U ⧸ E block P) ⧸ M.1) →*
      QuotientProjectiveImage block P hr hs hcomponent M :=
  ProjectiveCentralQuotient.map
    (diagonalProjectiveMap block P hr hs hcomponent)
    (diagonalProjectiveMap_surjective block P hr hs hcomponent) M

private def diagonalQuotientProductMap :
    DiagonalProjectiveImage block P hr hs hcomponent × C2 →*
      QuotientProjectiveImage block P hr hs hcomponent M × C2 :=
  (QuotientGroup.mk' _).prodMap (MonoidHom.id C2)

private theorem diagonalQuotientProductMap_surjective :
    Function.Surjective
      (diagonalQuotientProductMap block P hr hs hcomponent M) :=
  (QuotientGroup.mk'_surjective _).prodMap Function.surjective_id

private def diagonalQuotientBaseMap :
    DiagonalProjectiveImage block P hr hs hcomponent × C2 →*
      QuotientProjectiveImage block P hr hs hcomponent M :=
  (QuotientGroup.mk' _).comp
    (MonoidHom.fst _ C2)

private theorem diagonalQuotientBaseMap_surjective :
    Function.Surjective
      (diagonalQuotientBaseMap block P hr hs hcomponent M) := by
  intro a
  obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective _ a
  exact ⟨(p, 1), rfl⟩

private def diagonalProductAxis :
    {N : Subgroup (DiagonalProductComparator block P hr hs hcomponent) //
      N.Normal} :=
  ⟨((diagonalQuotientProductMap block P hr hs hcomponent M).comp
      (diagonalProductComparatorEquiv
        block P hr hs hcomponent).symm.toMonoidHom).ker,
    inferInstance⟩

private def diagonalBaseAxis :
    {N : Subgroup (DiagonalProductComparator block P hr hs hcomponent) //
      N.Normal} :=
  ⟨((diagonalQuotientBaseMap block P hr hs hcomponent M).comp
      (diagonalProductComparatorEquiv
        block P hr hs hcomponent).symm.toMonoidHom).ker,
    inferInstance⟩

private theorem diagonalAxes_ne :
    diagonalProductAxis block P hr hs hcomponent M ≠
      diagonalBaseAxis block P hr hs hcomponent M := by
  let e := diagonalProductComparatorEquiv block P hr hs hcomponent
  let c : C2 := Multiplicative.ofAdd 1
  have hc : c ≠ 1 := by decide
  let q : DiagonalProductComparator block P hr hs hcomponent := e (1, c)
  intro haxes
  have hbase : q ∈ (diagonalBaseAxis block P hr hs hcomponent M).1 := by
    change diagonalQuotientBaseMap block P hr hs hcomponent M (e.symm q) = 1
    simp [q, e, diagonalQuotientBaseMap]
  have hproduct :
      q ∈ (diagonalProductAxis block P hr hs hcomponent M).1 := by
    rw [haxes]
    exact hbase
  have hc1 : c = 1 := by
    have hpeq :
        diagonalQuotientProductMap block P hr hs hcomponent M (e.symm q) = 1 :=
      hproduct
    have h := congrArg Prod.snd hpeq
    simpa [q, e, diagonalProductAxis,
      diagonalQuotientProductMap] using h
  exact hc hc1

private def diagonalQuotientKernelBinaryEmbedding :
    {chi : (quotientProjectiveMap block P hr hs hcomponent M).ker →* C2 //
      Function.Injective chi} :=
  binaryEmbeddingOfCardLETwo _ (by
    calc
      Nat.card (quotientProjectiveMap
          block P hr hs hcomponent M).ker ≤
          Nat.card (diagonalProjectiveMap
            block P hr hs hcomponent).ker :=
        ProjectiveCentralQuotient.card_kernel_le
          (diagonalProjectiveMap block P hr hs hcomponent)
          (diagonalProjectiveMap_surjective block P hr hs hcomponent) M
      _ ≤ 2 := diagonalProjectiveKernel_card_le_two
        block P hr hs hcomponent hdiag)

/-- The two literal axes for one normal quotient of the diagonal signed
action. -/
private def diagonalQuotientDatum :
    CentralBinaryQuotientDatum
      (DiagonalProductComparator block P hr hs hcomponent)
      ((preE7NonPairAction w U ⧸ E block P) ⧸ M.1) where
  A := QuotientProjectiveImage block P hr hs hcomponent M
  projection := quotientProjectiveMap block P hr hs hcomponent M
  projection_surjective := ProjectiveCentralQuotient.map_surjective
    (diagonalProjectiveMap block P hr hs hcomponent)
    (diagonalProjectiveMap_surjective block P hr hs hcomponent) M
  projective_order_le := by
    calc
      Nat.card (QuotientProjectiveImage block P hr hs hcomponent M) ≤
          Nat.card (DiagonalProjectiveImage block P hr hs hcomponent) :=
        Nat.card_le_card_of_surjective _
          (QuotientGroup.mk'_surjective _)
      _ ≤ Nat.card (Equiv.Perm (Fin 4)) :=
        Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
      _ = 24 := by
        rw [Nat.card_perm]
        norm_num
  central_kernel := ProjectiveCentralQuotient.central_kernel
    (diagonalProjectiveMap block P hr hs hcomponent)
    (diagonalProjectiveMap_surjective block P hr hs hcomponent) M
    (diagonalProjectiveMap_central_kernel
      block P hr hs hcomponent hdiag)
  kernelCharacter :=
    (diagonalQuotientKernelBinaryEmbedding
      block P hr hs hcomponent hdiag M).1
  kernelCharacter_injective :=
    (diagonalQuotientKernelBinaryEmbedding
      block P hr hs hcomponent hdiag M).2
  productAxis := diagonalProductAxis block P hr hs hcomponent M
  baseAxis := diagonalBaseAxis block P hr hs hcomponent M
  axes_ne := diagonalAxes_ne block P hr hs hcomponent M
  productEquiv :=
    (QuotientGroup.quotientKerEquivOfSurjective
      ((diagonalQuotientProductMap block P hr hs hcomponent M).comp
        (diagonalProductComparatorEquiv
          block P hr hs hcomponent).symm.toMonoidHom)
      ((diagonalQuotientProductMap_surjective
          block P hr hs hcomponent M).comp
        (diagonalProductComparatorEquiv
          block P hr hs hcomponent).symm.surjective)).symm
  baseEquiv :=
    (QuotientGroup.quotientKerEquivOfSurjective
      ((diagonalQuotientBaseMap block P hr hs hcomponent M).comp
        (diagonalProductComparatorEquiv
          block P hr hs hcomponent).symm.toMonoidHom)
      ((diagonalQuotientBaseMap_surjective
          block P hr hs hcomponent M).comp
        (diagonalProductComparatorEquiv
          block P hr hs hcomponent).symm.surjective)).symm

end Quotient

/-- Catalogue-free central-product model for the actual diagonal signed
quotient. -/
noncomputable def degreeThreeFourBlockDiagonalCentralProductModel
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hdiag : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 1) :
    DegreeNineCentralProductModel
      (preE7NonPairAction w U ⧸ E block P) where
  Q := DiagonalProductComparator block P hr hs hcomponent
  quotient := fun M =>
    diagonalQuotientDatum block P hr hs hcomponent hdiag M

/-- The diagonal comparison source required by the signed-isotype
dispatcher, constructed from the literal action itself. -/
noncomputable def degreeThreeFourBlockDiagonalComparisonSource :
    DegreeThreeFourBlockDiagonalComparisonSource := by
  intro w U basePoint block P _inst hr hs hcomponent _hbinary hdiag
  exact degreeThreeFourBlockDiagonalCentralProductModel
    block P hr hs hcomponent hdiag

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
