import SymmetricSubgroupAsymptotics.BinaryPairFrameOneSignKernel
import SymmetricSubgroupAsymptotics.CentralBinaryRecursiveCompleteQuotientComparison
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignStructural
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeSignedQuotientPairFrame

/-!
# The post-four one-sign central product comparison

When every pair coordinate of the literal degree-three signed quotient has
the same sign character, the pair kernel is a central group of order at
most two.  The quotient by that kernel is the actual block top.  Adjoining
one regular binary orbit to the top therefore gives a faithful comparator
of degree `s + 2` and supplies both quotient maps needed by the global
central-binary comparison.

This construction is uniform in the number of blocks.  In particular it
applies without a finite row census at six, twelve, and eighteen blocks.
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

private abbrev OneSignFrame
    (hr : Nat.card block.Fibre = 3) :=
  degreeThreeSignedQuotientPairFrame block P hr

/-- The actual block-top image of the literal signed quotient. -/
abbrev DegreeThreePostFourOneSignTop
    (hr : Nat.card block.Fibre = 3) :=
  (OneSignFrame block P hr).top.range

/-- The literal signed quotient projected onto its actual block top. -/
def degreeThreePostFourOneSignProjectiveMap
    (hr : Nat.card block.Fibre = 3) :
    (preE7NonPairAction w U ⧸ E block P) →*
      DegreeThreePostFourOneSignTop block P hr :=
  (OneSignFrame block P hr).top.rangeRestrict.comp
    (degreeThreeSignedQuotientRangeEquiv block P).toMonoidHom

theorem degreeThreePostFourOneSignProjectiveMap_surjective
    (hr : Nat.card block.Fibre = 3) :
    Function.Surjective
      (degreeThreePostFourOneSignProjectiveMap block P hr) :=
  (OneSignFrame block P hr).top.rangeRestrict_surjective.comp
    (degreeThreeSignedQuotientRangeEquiv block P).surjective

/-- A projective-kernel element, transported to the literal pair kernel. -/
def degreeThreePostFourOneSignProjectiveKernelToPairKernel
    (hr : Nat.card block.Fibre = 3)
    (z : (degreeThreePostFourOneSignProjectiveMap block P hr).ker) :
    (OneSignFrame block P hr).top.ker := by
  refine ⟨degreeThreeSignedQuotientRangeEquiv block P z.1, ?_⟩
  exact congrArg Subtype.val z.2

theorem degreeThreePostFourOneSignProjectiveKernelToPairKernel_injective
    (hr : Nat.card block.Fibre = 3) :
    Function.Injective
      (degreeThreePostFourOneSignProjectiveKernelToPairKernel block P hr) := by
  intro x y hxy
  apply Subtype.ext
  apply (degreeThreeSignedQuotientRangeEquiv block P).injective
  exact congrArg Subtype.val hxy

/-- The one-sign projective kernel has order at most two. -/
theorem degreeThreePostFourOneSignProjectiveKernel_card_le_two
    (hr : Nat.card block.Fibre = 3)
    (hone : Nat.card (BinaryPairFrame.CoordinateSign
      (OneSignFrame block P hr)) = 1) :
    Nat.card (degreeThreePostFourOneSignProjectiveMap block P hr).ker ≤ 2 := by
  calc
    Nat.card (degreeThreePostFourOneSignProjectiveMap block P hr).ker ≤
        Nat.card (OneSignFrame block P hr).top.ker :=
      Nat.card_le_card_of_injective
        (degreeThreePostFourOneSignProjectiveKernelToPairKernel block P hr)
        (degreeThreePostFourOneSignProjectiveKernelToPairKernel_injective
          block P hr)
    _ ≤ 2 := BinaryPairFrame.top_ker_card_le_two_of_sign_count_one
      (OneSignFrame block P hr) hone

/-- The one-sign projective kernel is central in the literal signed
quotient. -/
theorem degreeThreePostFourOneSignProjectiveMap_central_kernel
    (hr : Nat.card block.Fibre = 3)
    (hone : Nat.card (BinaryPairFrame.CoordinateSign
      (OneSignFrame block P hr)) = 1) :
    ∀ z ∈ (degreeThreePostFourOneSignProjectiveMap block P hr).ker,
      ∀ x : preE7NonPairAction w U ⧸ E block P, z * x = x * z := by
  intro z hz x
  let k : (OneSignFrame block P hr).top.ker :=
    degreeThreePostFourOneSignProjectiveKernelToPairKernel
      block P hr ⟨z, hz⟩
  let u := degreeThreeSignedQuotientRangeEquiv block P x
  have hkcenter : (k : (quotientAction block P).range) ∈
      Subgroup.center ((quotientAction block P).range) :=
    BinaryPairFrame.top_ker_le_center_of_sign_count_one
      (OneSignFrame block P hr) hone k.2
  have hcomm : (k : (quotientAction block P).range) * u = u * k :=
    Subgroup.mem_center_iff.mp hkcenter u
  change degreeThreeSignedQuotientRangeEquiv block P z *
      degreeThreeSignedQuotientRangeEquiv block P x =
    degreeThreeSignedQuotientRangeEquiv block P x *
      degreeThreeSignedQuotientRangeEquiv block P z at hcomm
  apply (degreeThreeSignedQuotientRangeEquiv block P).injective
  simpa only [map_mul] using hcomm

/-- Relabel the actual block top by its finite cardinality. -/
def degreeThreePostFourOneSignTopAction
    (hr : Nat.card block.Fibre = 3) :
    DegreeThreePostFourOneSignTop block P hr →*
      Equiv.Perm (Fin (Nat.card block.Points)) :=
  (Finite.equivFin block.Points).permCongrHom.toMonoidHom.comp
    (DegreeThreePostFourOneSignTop block P hr).subtype

theorem degreeThreePostFourOneSignTopAction_injective
    (hr : Nat.card block.Fibre = 3) :
    Function.Injective (degreeThreePostFourOneSignTopAction block P hr) :=
  (Finite.equivFin block.Points).permCongrHom.injective.comp
    Subtype.val_injective

/-- Faithful disjoint action of the actual block top and one binary orbit. -/
def degreeThreePostFourOneSignComparatorAction
    (hr : Nat.card block.Fibre = 3) :
    DegreeThreePostFourOneSignTop block P hr × C2 →*
      Equiv.Perm (Fin (Nat.card block.Points + 2)) :=
  DegreeThreeFourBlockTwoSignComparator.appendC2Action
    (degreeThreePostFourOneSignTopAction block P hr)

theorem degreeThreePostFourOneSignComparatorAction_injective
    (hr : Nat.card block.Fibre = 3) :
    Function.Injective
      (degreeThreePostFourOneSignComparatorAction block P hr) :=
  DegreeThreeFourBlockTwoSignComparator.appendC2Action_injective
    (degreeThreePostFourOneSignTopAction block P hr)
    (degreeThreePostFourOneSignTopAction_injective block P hr)

/-- The two quotient maps from `top × C₂` give a global comparison for the
central binary signed quotient. -/
noncomputable def degreeThreePostFourOneSignGlobalComparison
    (hr : Nat.card block.Fibre = 3)
    (hone : Nat.card (BinaryPairFrame.CoordinateSign
      (OneSignFrame block P hr)) = 1) :
    CentralBinaryGlobalComparison
      (DegreeThreePostFourOneSignTop block P hr × C2)
      (preE7NonPairAction w U ⧸ E block P)
      (DegreeThreePostFourOneSignTop block P hr) where
  projection := degreeThreePostFourOneSignProjectiveMap block P hr
  projection_surjective :=
    degreeThreePostFourOneSignProjectiveMap_surjective block P hr
  central_kernel :=
    degreeThreePostFourOneSignProjectiveMap_central_kernel
      block P hr hone
  kernel_card_le_two :=
    degreeThreePostFourOneSignProjectiveKernel_card_le_two
      block P hr hone
  baseQuotient := MonoidHom.fst _ C2
  baseQuotient_surjective := Prod.fst_surjective
  productQuotient := MonoidHom.id _
  productQuotient_surjective := Function.surjective_id

/-- Recursive all-normal comparison for the post-four one-sign branch. -/
noncomputable def degreeThreePostFourOneSignComparison
    (hr : Nat.card block.Fibre = 3)
    (hone : Nat.card (BinaryPairFrame.CoordinateSign
      (OneSignFrame block P hr)) = 1) :
    CentralBinaryRecursiveComparison
      (DegreeThreePostFourOneSignTop block P hr × C2)
      (preE7NonPairAction w U ⧸ E block P)
      (DegreeThreePostFourOneSignTop block P hr) :=
  CentralBinaryRecursiveComparison.ofGlobal
    (degreeThreePostFourOneSignGlobalComparison block P hr hone)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
