import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.GroupTheory.Perm.Basic

/-! An injectively labelled subgroup family stable under a specified
actual automorphism action carries its permutation representation. The
acting group may be a subgroup of the full automorphism group; no full
family-invariance premise is built into the group definition. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSubgroupFamilyAction
variable {G A X : Type*} [Group G] [Group A]
variable (phi : A →* MulAut G) (L : X → Subgroup G) (hinj : Function.Injective L)
  (hstable : ∀ a : A, ∀ x, ∃ y, L y = (L x).map (phi a).toMonoidHom)

 def image (a : A) (x : X) : X := Classical.choose (hstable a x)

 theorem label_image (a : A) (x : X) :
    L (image phi L hstable a x) = (L x).map (phi a).toMonoidHom :=
  Classical.choose_spec (hstable a x)

 include hinj in
 theorem image_one (x : X) : image phi L hstable 1 x = x := by
  apply hinj
  rw [label_image phi L hstable, map_one]
  exact Subgroup.map_id _

 include hinj in
 theorem image_mul (a b : A) (x : X) :
    image phi L hstable (a * b) x = image phi L hstable a (image phi L hstable b x) := by
  apply hinj
  rw [label_image phi L hstable, label_image phi L hstable,
    label_image phi L hstable, Subgroup.map_map, map_mul]
  rfl

 def permutation (a : A) : Equiv.Perm X where
  toFun := image phi L hstable a
  invFun := image phi L hstable a⁻¹
  left_inv x := by rw [← image_mul phi L hinj hstable, inv_mul_cancel, image_one phi L hinj hstable]
  right_inv x := by rw [← image_mul phi L hinj hstable, mul_inv_cancel, image_one phi L hinj hstable]

 def permutationHom : A →* Equiv.Perm X where
  toFun := permutation phi L hinj hstable
  map_one' := by apply Equiv.ext; exact image_one phi L hinj hstable
  map_mul' a b := by apply Equiv.ext; exact image_mul phi L hinj hstable a b

 theorem label_permutation (a : A) (x : X) :
    L (permutationHom phi L hinj hstable a x) = (L x).map (phi a).toMonoidHom :=
  label_image phi L hstable a x

end SymmetricSubgroupAsymptotics.CFSGSubgroupFamilyAction
