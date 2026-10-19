import SymmetricSubgroupAsymptotics.SixPairDihedralSocles
import SymmetricSubgroupAsymptotics.NaturalFourNormalChains

/-! The displayed faithful six-point dihedral image has its literal S3
quotient with kernel of order two. No subgroup census is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.DihedralSixImageRecognition

def projection : DihedralGroup 6 →* Equiv.Perm (Fin 3) where
  toFun
    | .r i => finRotate 3 ^ i.val
    | .sr i => Equiv.swap 0 1 * finRotate 3 ^ i.val
  map_one' := rfl
  map_mul' := by
    rintro (i | i) (j | j) <;> apply Equiv.ext <;> intro x <;>
      revert i j x <;> decide +kernel

theorem projection_surjective : Function.Surjective projection := by decide +kernel
private theorem action_injective : Function.Injective SixPairDihedralSocles.dihedralMap := by
  decide +kernel

def canonicalEquiv : DihedralGroup 6 ≃* SixPairDihedralSocles.dihedralMap.range :=
  MulEquiv.ofBijective SixPairDihedralSocles.dihedralMap.rangeRestrict
    ⟨fun _ _ h => action_injective (congrArg Subtype.val h),
      SixPairDihedralSocles.dihedralMap.rangeRestrict_surjective⟩

variable {U : Subgroup (Equiv.Perm (Fin 12))} (F : BinaryPairFrame U (Fin 6))
    (himage : F.top.range=SixPairDihedralSocles.dihedralMap.range)

def equiv : F.top.range ≃* DihedralGroup 6 :=
  (MulEquiv.subgroupCongr himage).trans canonicalEquiv.symm

def topProjection : F.top.range →* Equiv.Perm (Fin 3) :=
  projection.comp (equiv F himage).toMonoidHom

theorem topProjection_surjective : Function.Surjective (topProjection F himage) :=
  projection_surjective.comp (equiv F himage).surjective

include himage in
theorem top_card : Nat.card F.top.range=12 := by
  rw [Nat.card_congr (equiv F himage).toEquiv,DihedralGroup.nat_card]

theorem topProjection_kernel_card : Nat.card (topProjection F himage).ker=2 := by
  have hquot : Nat.card (F.top.range ⧸ (topProjection F himage).ker)=6 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
      (topProjection F himage) (topProjection_surjective F himage)).toEquiv]
    rw [Nat.card_perm,Nat.card_fin]
    decide
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (topProjection F himage).ker
  rw [top_card F himage,hquot] at h
  omega

end SymmetricSubgroupAsymptotics.DihedralSixImageRecognition
