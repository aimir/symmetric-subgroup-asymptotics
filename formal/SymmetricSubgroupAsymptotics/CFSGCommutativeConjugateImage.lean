import SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateRestriction

/-! Conjugating an actual subgroup inside its ambient group does not
change its image under a homomorphism to a commutative group. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGCommutativeConjugateImage
variable {G C : Type*} [Group G] [CommGroup C]

theorem conjugate_map_eq (f : G→*C) (R : Subgroup G) (g : G) :
    (R.map (MulAut.conj g).toMonoidHom).map f=R.map f := by
  rw [CFSGSubgroupConjugateRestriction.map_conjugate]
  have he : (MulAut.conj (f g)).toMonoidHom=MonoidHom.id C := by
    apply MonoidHom.ext
    intro x
    change f g*x*(f g)⁻¹=x
    rw [mul_comm (f g) x,mul_assoc,mul_inv_cancel,mul_one]
  rw [he,Subgroup.map_id]

end SymmetricSubgroupAsymptotics.CFSGCommutativeConjugateImage
