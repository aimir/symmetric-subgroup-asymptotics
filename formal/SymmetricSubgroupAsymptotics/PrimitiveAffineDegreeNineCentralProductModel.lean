import SymmetricSubgroupAsymptotics.PrimitiveAffineProjectiveCentralQuotients
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeNineProductAction
import SymmetricSubgroupAsymptotics.DegreeNineCentralProductComparator

/-!
# The degree-nine primitive-affine central-product model

The projective map of a degree-nine affine complement has central binary
kernel.  On every literal normal quotient, its projective image together
with one binary scalar supplies the two distinct comparator axes required
by `DegreeNineCentralProductModel`.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineProfile

private abbrev C2 := Multiplicative (ZMod 2)

variable {L : Type} [Group L] [MulAction L (Fin 9)] [Finite L]
  [FaithfulSMul L (Fin 9)]

/-! ## The two quotient axes -/

section Quotient

variable (P : PrimitiveAffineProfile L (Fin 9))
  (hprimitive : MulAction.IsPreprimitive L (Fin 9)) (x : Fin 9)
  (M : {M : Subgroup (P.complement x) // M.Normal})

local instance : M.1.Normal := M.2
local instance :
    (ProjectiveCentralQuotient.normalImage
      (P.complementProjectiveRangeMap_degreeNine hprimitive x)
      (P.complementProjectiveRangeMap_degreeNine_surjective hprimitive x) M).1.Normal :=
  (ProjectiveCentralQuotient.normalImage
    (P.complementProjectiveRangeMap_degreeNine hprimitive x)
    (P.complementProjectiveRangeMap_degreeNine_surjective hprimitive x) M).2

private abbrev A := P.DegreeNineProjectiveImage hprimitive x ⧸
  (ProjectiveCentralQuotient.normalImage
    (P.complementProjectiveRangeMap_degreeNine hprimitive x)
    (P.complementProjectiveRangeMap_degreeNine_surjective hprimitive x) M).1

private def piA : (P.complement x ⧸ M.1) →* A P hprimitive x M :=
  ProjectiveCentralQuotient.map
    (P.complementProjectiveRangeMap_degreeNine hprimitive x)
    (P.complementProjectiveRangeMap_degreeNine_surjective hprimitive x) M

private def productMap :
    P.DegreeNineProjectiveImage hprimitive x × C2 →*
      A P hprimitive x M × C2 :=
  (QuotientGroup.mk' _).prodMap (MonoidHom.id C2)

private theorem productMap_surjective :
    Function.Surjective (productMap P hprimitive x M) :=
  (QuotientGroup.mk'_surjective _).prodMap Function.surjective_id

private def baseMap :
    P.DegreeNineProjectiveImage hprimitive x × C2 →*
      A P hprimitive x M :=
  (QuotientGroup.mk' _).comp (MonoidHom.fst _ C2)

private theorem baseMap_surjective :
    Function.Surjective (baseMap P hprimitive x M) := by
  intro a
  obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective _ a
  exact ⟨(p, 1), rfl⟩

private def productAxis :
    {N : Subgroup (P.DegreeNineProductComparator hprimitive x) // N.Normal} :=
  ⟨((productMap P hprimitive x M).comp
      (P.degreeNineProductComparatorEquiv hprimitive x).symm.toMonoidHom).ker,
    inferInstance⟩

private def baseAxis :
    {N : Subgroup (P.DegreeNineProductComparator hprimitive x) // N.Normal} :=
  ⟨((baseMap P hprimitive x M).comp
      (P.degreeNineProductComparatorEquiv hprimitive x).symm.toMonoidHom).ker,
    inferInstance⟩

private theorem axes_ne :
    productAxis P hprimitive x M ≠ baseAxis P hprimitive x M := by
  let e := P.degreeNineProductComparatorEquiv hprimitive x
  let c : C2 := Multiplicative.ofAdd 1
  have hc : c ≠ 1 := by decide
  let q : P.DegreeNineProductComparator hprimitive x := e (1, c)
  intro haxes
  have hbase : q ∈ (baseAxis P hprimitive x M).1 := by
    change baseMap P hprimitive x M (e.symm q) = 1
    simp [q, e, baseMap]
  have hproduct : q ∈ (productAxis P hprimitive x M).1 := by
    rw [haxes]
    exact hbase
  have hc1 : c = 1 := by
    have hpeq : productMap P hprimitive x M (e.symm q) = 1 := hproduct
    have := congrArg Prod.snd hpeq
    simpa [q, e, productAxis, productMap] using this
  exact hc hc1

private def quotientKernelBinaryEmbedding :
    {chi : (piA P hprimitive x M).ker →* C2 // Function.Injective chi} :=
  binaryEmbeddingOfCardLETwo _ (by
    calc
      Nat.card (piA P hprimitive x M).ker ≤
          Nat.card (P.complementProjectiveRangeMap_degreeNine hprimitive x).ker :=
        ProjectiveCentralQuotient.card_kernel_le
          (P.complementProjectiveRangeMap_degreeNine hprimitive x)
          (P.complementProjectiveRangeMap_degreeNine_surjective hprimitive x) M
      _ ≤ 2 := P.complementProjectiveKernel_card_le_two_degreeNine hprimitive x)

private def quotientDatum :
    CentralBinaryQuotientDatum
      (P.DegreeNineProductComparator hprimitive x) (P.complement x ⧸ M.1) where
  A := A P hprimitive x M
  projection := piA P hprimitive x M
  projection_surjective := ProjectiveCentralQuotient.map_surjective
    (P.complementProjectiveRangeMap_degreeNine hprimitive x)
    (P.complementProjectiveRangeMap_degreeNine_surjective hprimitive x) M
  projective_order_le := by
    calc
      Nat.card (A P hprimitive x M) ≤
          Nat.card (P.DegreeNineProjectiveImage hprimitive x) :=
        Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
      _ ≤ Nat.card (Equiv.Perm (Fin 4)) :=
        Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
      _ = 24 := by
        rw [Nat.card_perm]
        norm_num
  central_kernel := ProjectiveCentralQuotient.central_kernel
    (P.complementProjectiveRangeMap_degreeNine hprimitive x)
    (P.complementProjectiveRangeMap_degreeNine_surjective hprimitive x) M
    (P.complementProjectiveRangeMap_degreeNine_central_kernel hprimitive x)
  kernelCharacter := (quotientKernelBinaryEmbedding P hprimitive x M).1
  kernelCharacter_injective :=
    (quotientKernelBinaryEmbedding P hprimitive x M).2
  productAxis := productAxis P hprimitive x M
  baseAxis := baseAxis P hprimitive x M
  axes_ne := axes_ne P hprimitive x M
  productEquiv :=
    (QuotientGroup.quotientKerEquivOfSurjective
      ((productMap P hprimitive x M).comp
        (P.degreeNineProductComparatorEquiv hprimitive x).symm.toMonoidHom)
      ((productMap_surjective P hprimitive x M).comp
        (P.degreeNineProductComparatorEquiv hprimitive x).symm.surjective)).symm
  baseEquiv :=
    (QuotientGroup.quotientKerEquivOfSurjective
      ((baseMap P hprimitive x M).comp
        (P.degreeNineProductComparatorEquiv hprimitive x).symm.toMonoidHom)
      ((baseMap_surjective P hprimitive x M).comp
        (P.degreeNineProductComparatorEquiv hprimitive x).symm.surjective)).symm

end Quotient

/-- Catalogue-free degree-nine central-product data for the actual point
stabilizer of every primitive affine profile. -/
noncomputable def degreeNineCentralProductModel
    (P : PrimitiveAffineProfile L (Fin 9))
    (hprimitive : MulAction.IsPreprimitive L (Fin 9)) (x : Fin 9) :
    DegreeNineCentralProductModel (P.complement x) where
  Q := P.DegreeNineProductComparator hprimitive x
  quotient := fun M => quotientDatum P hprimitive x M

end PrimitiveAffineProfile
end SymmetricSubgroupAsymptotics
