import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.GroupTheory.Perm.Basic

/-! An injectively labelled subgroup family stable under actual group
automorphisms carries their literal permutation representation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSubgroupFamilyPermutation
variable {G X : Type*} [Group G]
variable (L : X→Subgroup G) (hinj : Function.Injective L)
  (hstable : ∀a : MulAut G,∀x,∃y,L y=(L x).map a.toMonoidHom)

def image (a : MulAut G) (x : X) : X := Classical.choose (hstable a x)

theorem label_image (a : MulAut G) (x : X) :
    L (image L hstable a x)=(L x).map a.toMonoidHom :=
  Classical.choose_spec (hstable a x)

include hinj in
theorem image_one (x : X) : image L hstable 1 x=x := by
  apply hinj
  rw [label_image L hstable 1 x]
  change (L x).map (MonoidHom.id G)=L x
  exact Subgroup.map_id _

include hinj in
theorem image_mul (a b : MulAut G) (x : X) :
    image L hstable (a*b) x=image L hstable a (image L hstable b x) := by
  apply hinj
  rw [label_image L hstable (a*b) x,
    label_image L hstable a (image L hstable b x),label_image L hstable b x,
    Subgroup.map_map]
  rfl

def permutation (a : MulAut G) : Equiv.Perm X where
  toFun := image L hstable a
  invFun := image L hstable a⁻¹
  left_inv x := by
    rw [←image_mul L hinj hstable,inv_mul_cancel,image_one L hinj hstable]
  right_inv x := by
    rw [←image_mul L hinj hstable,mul_inv_cancel,image_one L hinj hstable]

def permutationHom : MulAut G→*Equiv.Perm X where
  toFun := permutation L hinj hstable
  map_one' := by
    apply Equiv.ext
    exact image_one L hinj hstable
  map_mul' a b := by
    apply Equiv.ext
    exact image_mul L hinj hstable a b

theorem label_permutation (a : MulAut G) (x : X) :
    L (permutationHom L hinj hstable a x)=(L x).map a.toMonoidHom :=
  label_image L hstable a x

end SymmetricSubgroupAsymptotics.CFSGSubgroupFamilyPermutation
