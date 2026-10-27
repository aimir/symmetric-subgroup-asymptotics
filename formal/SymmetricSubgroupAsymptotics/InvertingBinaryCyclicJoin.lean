import SymmetricSubgroupAsymptotics.CFSGTwoBinaryPowerGenerators
import SymmetricSubgroupAsymptotics.AmbientCyclePowerNormalizerWitness
import Mathlib.GroupTheory.PGroup

/-! A genuine dihedral binary subgroup, allowing order four rotations.
No full generation or word recovery is inferred from these relations. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.InvertingBinaryCyclicJoin
open CFSGReduction AmbientCyclePowerNormalizerWitness
variable {G : Type*} [Group G]

theorem isPGroup_join (a z : G) (ha : a^2=1) (hz : z^4=1)
    (hinv : a*z*a⁻¹=z⁻¹) :
    IsPGroup 2 (Subgroup.zpowers a ⊔ Subgroup.zpowers z : Subgroup G) := by
  have hai : a⁻¹=a := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using ha)
  have hzi : z⁻¹=z^3 := inv_eq_of_mul_eq_one_right
    ((pow_succ' z 3).symm.trans hz)
  have hf : a*z*a⁻¹=z^3 := hinv.trans hzi
  have hb : a⁻¹*z*a=z^3 := by simpa only [hai] using hf
  have hn : Subgroup.zpowers a ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) :=
    Subgroup.zpowers_le.mpr (mem_normalizer_zpowers a z 3 3 hf hb)
  exact (zpowers_isPGroup_two_of_pow a 1 (by simpa using ha)).to_sup_of_normal_right'
    (zpowers_isPGroup_two_of_pow z 2 (by simpa using hz)) hn

theorem involution_rotation_binary (a t : G) (ha : a^2=1) (ht : t^2=1)
    (hr : (a*t)^12=1) :
    IsPGroup 2 (Subgroup.zpowers a ⊔ Subgroup.zpowers ((a*t)^3) : Subgroup G) := by
  have hai : a⁻¹=a := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using ha)
  have hti : t⁻¹=t := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using ht)
  have hz : ((a*t)^3)^4=1 := by simpa only [←pow_mul] using hr
  have hinv : a*(a*t)*a⁻¹=(a*t)⁻¹ := by
    rw [mul_inv_rev,hai,hti]
    have haa : a*a=1 := by simpa only [pow_two] using ha
    simp only [←mul_assoc,haa,one_mul]
  have hzconj : a*((a*t)^3)*a⁻¹=(((a*t)^3))⁻¹ := by
    change (MulAut.conj a) ((a*t)^3)=_
    rw [map_pow]
    change (a*(a*t)*a⁻¹)^3=_
    rw [hinv,inv_pow]
  exact isPGroup_join a ((a*t)^3) ha hz hzconj

end SymmetricSubgroupAsymptotics.InvertingBinaryCyclicJoin
