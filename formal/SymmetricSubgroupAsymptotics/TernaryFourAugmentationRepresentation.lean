import SymmetricSubgroupAsymptotics.TernaryA4InvariantSubmodules
import SymmetricSubgroupAsymptotics.AffineIrreducibleNormalGenerators
import SymmetricSubgroupAsymptotics.NaturalFourNormalChains

/-! The actual ternary augmentation representation on four labels.
The original coordinate sum is zero, with chart
`(a,b,c) ↦ (a,b,c,-a-b-c)`. Its irreducibility follows from the proved
natural-A4 invariant-submodule theorem, including in characteristic three.
Every original quotient of its A4- or S4-affine group has a normally cyclic
socle. No coprimality assumption on the complement is used. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.TernaryFourAugmentationRepresentation

open TernaryA4InvariantSubmodules

abbrev Vector := AffineModel.V 3 3
abbrev LinearGroup := AffineModel.GLV 3 3

def encode (v : Vector) : V := ![v 0,v 1,v 2,-v 0-v 1-v 2]
def decode (v : V) : Vector := ![v 0,v 1,v 2]

theorem encode_sum (v : Vector) : ∑ i, encode v i = 0 := by
  simp only [encode,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Matrix.cons_val_fin_one,Fin.sum_univ_zero,add_zero]
  ring

theorem decode_encode (v : Vector) : decode (encode v) = v := by
  funext i
  fin_cases i <;> rfl

theorem encode_decode (v : V) (hv : ∑ i, v i = 0) : encode (decode v) = v := by
  have hsum : v 0 + v 1 + v 2 + v 3 = 0 := by
    simpa only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,add_assoc] using hv
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · change -v 0-v 1-v 2 = v 3
    linear_combination -hsum

def chart : Vector ≃ₗ[Scalar] augmentation where
  toFun v := ⟨encode v,encode_sum v⟩
  invFun v := decode v.1
  left_inv := decode_encode
  right_inv v := Subtype.ext (encode_decode v.1 v.2)
  map_add' := by
    intro v w
    apply Subtype.ext
    funext i
    change encode (v+w) i = encode v i + encode w i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · change -(v 0+w 0)-(v 1+w 1)-(v 2+w 2) =
        (-v 0-v 1-v 2)+(-w 0-w 1-w 2)
      ring
  map_smul' := by
    intro a v
    apply Subtype.ext
    funext i
    change encode (a • v) i = a * encode v i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · change -(a*v 0)-(a*v 1)-(a*v 2) = a*(-v 0-v 1-v 2)
      ring

def permLinear (g : Equiv.Perm (Fin 4)) : augmentation ≃ₗ[Scalar] augmentation where
  toFun v := ⟨fun i => v.1 (g.symm i), by
    change (∑ i, v.1 (g.symm i)) = 0
    rw [Equiv.sum_comp]
    exact v.2⟩
  invFun v := ⟨fun i => v.1 (g i), by
    change (∑ i, v.1 (g i)) = 0
    rw [Equiv.sum_comp]
    exact v.2⟩
  left_inv v := Subtype.ext (funext fun i => congrArg v.1 (g.symm_apply_apply i))
  right_inv v := Subtype.ext (funext fun i => congrArg v.1 (g.apply_symm_apply i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def hom : Equiv.Perm (Fin 4) →* LinearGroup where
  toFun g := (chart.trans (permLinear g)).trans chart.symm
  map_one' := by
    apply LinearEquiv.ext
    intro v
    change chart.symm (chart v) = v
    exact chart.symm_apply_apply v
  map_mul' g h := by
    apply LinearEquiv.ext
    intro v
    change chart.symm (permLinear (g*h) (chart v)) =
      chart.symm (permLinear g (chart (chart.symm (permLinear h (chart v)))))
    rw [chart.apply_symm_apply]
    apply congrArg chart.symm
    apply Subtype.ext
    funext i
    rfl

def evenHom : alternatingGroup (Fin 4) →* LinearGroup :=
  hom.comp (alternatingGroup (Fin 4)).subtype

theorem encode_hom (g : Equiv.Perm (Fin 4)) (v : Vector) :
    encode (hom g v) = coordinateAction g (encode v) := by
  exact congrArg Subtype.val (chart.apply_symm_apply (permLinear g (chart v)))

def encodeLinear : Vector →ₗ[Scalar] V := augmentation.subtype.comp chart.toLinearMap

theorem encode_injective : Function.Injective encode :=
  Subtype.val_injective.comp chart.injective

private theorem constant_not_augmentation :
    (fun _ : Fin 4 => (1 : Scalar)) ∉ augmentation := by
  change (∑ _ : Fin 4, (1 : Scalar)) ≠ 0
  decide +kernel

/-- Any linear group containing the actual even coordinate action is
irreducible on the augmentation. -/
theorem irreducible_of_even_range_le (R : Subgroup LinearGroup)
    (hR : evenHom.range ≤ R) : AffineModel.Irreducible R := by
  classical
  intro S hS
  let K : AddSubgroup V := S.map encodeLinear.toAddMonoidHom
  have hKaug : K ≤ augmentation.toAddSubgroup := by
    rintro _ ⟨v,_,rfl⟩
    exact encode_sum v
  have hKinv : ∀ g ∈ alternatingGroup (Fin 4), ∀ v ∈ K,
      coordinateAction g v ∈ K := by
    intro g hg v hv
    obtain ⟨w,hw,rfl⟩ := hv
    refine ⟨hom g w,hS (hom g) (hR ⟨⟨g,hg⟩,rfl⟩) w hw,?_⟩
    exact encode_hom g w
  rcases additive_classification K hKinv with hb | hd | ha | ht
  · left
    apply bot_unique
    intro v hv
    have hm : encode v ∈ K := ⟨v,hv,rfl⟩
    rw [hb,AddSubgroup.mem_bot] at hm
    apply AddSubgroup.mem_bot.mpr
    apply encode_injective
    exact hm.trans (map_zero encodeLinear).symm
  · exfalso
    apply constant_not_augmentation
    apply hKaug
    rw [hd]
    intro i
    rfl
  · right
    apply top_unique
    intro v _
    have hm : encode v ∈ K := by
      rw [ha]
      exact encode_sum v
    obtain ⟨w,hw,hwv⟩ := hm
    exact encode_injective hwv ▸ hw
  · exfalso
    apply constant_not_augmentation
    apply hKaug
    rw [ht]
    exact AddSubgroup.mem_top _

abbrev alternatingLinearGroup := evenHom.range
abbrev symmetricLinearGroup := hom.range

theorem alternating_irreducible : AffineModel.Irreducible alternatingLinearGroup :=
  irreducible_of_even_range_le _ le_rfl

theorem symmetric_irreducible : AffineModel.Irreducible symmetricLinearGroup :=
  irreducible_of_even_range_le _ (by
    rintro _ ⟨g,rfl⟩
    exact ⟨g.1,rfl⟩)

theorem alternating_normal_total
    (A B : Subgroup alternatingLinearGroup) (hA : A.Normal) (hB : B.Normal) :
    A ≤ B ∨ B ≤ A :=
  normalSubgroups_total_of_surjective evenHom.rangeRestrict evenHom.rangeRestrict_surjective
    NaturalFourNormalChains.alternating_normal_total A B hA hB

theorem symmetric_normal_total
    (A B : Subgroup symmetricLinearGroup) (hA : A.Normal) (hB : B.Normal) :
    A ≤ B ∨ B ≤ A :=
  normalSubgroups_total_of_surjective hom.rangeRestrict hom.rangeRestrict_surjective
    NaturalFourNormalChains.symmetric_normal_total A B hA hB

theorem alternating_affine_normal_total :
    ∀ A B : Subgroup (AffineModel.Aff alternatingLinearGroup),
      A.Normal → B.Normal → A ≤ B ∨ B ≤ A :=
  AffineModel.normal_total_of_irreducible_complement _
    alternating_irreducible alternating_normal_total

theorem symmetric_affine_normal_total :
    ∀ A B : Subgroup (AffineModel.Aff symmetricLinearGroup),
      A.Normal → B.Normal → A ≤ B ∨ B ≤ A :=
  AffineModel.normal_total_of_irreducible_complement _
    symmetric_irreducible symmetric_normal_total

theorem alternating_socle_of_surjective {Q : Type} [Group Q]
    (pi : AffineModel.Aff alternatingLinearGroup →* Q) (hpi : Function.Surjective pi) :
    SocleNormalGeneratorBound Q 1 :=
  socleNormalGeneratorBound_one_of_normal_total
    (normalSubgroups_total_of_surjective pi hpi alternating_affine_normal_total)

theorem symmetric_socle_of_surjective {Q : Type} [Group Q]
    (pi : AffineModel.Aff symmetricLinearGroup →* Q) (hpi : Function.Surjective pi) :
    SocleNormalGeneratorBound Q 1 :=
  socleNormalGeneratorBound_one_of_normal_total
    (normalSubgroups_total_of_surjective pi hpi symmetric_affine_normal_total)

end SymmetricSubgroupAsymptotics.TernaryFourAugmentationRepresentation

end
