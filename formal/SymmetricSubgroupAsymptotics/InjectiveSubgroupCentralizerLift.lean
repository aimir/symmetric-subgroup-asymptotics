import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.GroupTheory.Subgroup.Centralizer

/-! Centralization lifts through a quotient on a normalized subgroup
whenever the quotient is injective on that SAME subgroup. Injectivity
on the ambient group, an automorphism lift, and a trivial full kernel
are not required. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.InjectiveSubgroupCentralizerLift

theorem commute_of_map {G H : Type*} [Group G] [Group H]
    (f : G→*H) (R : Subgroup G)
    (hf : Function.Injective (f.comp R.subtype)) (k x : G)
    (hk : k∈Subgroup.normalizer (R : Set G)) (hx : x∈R)
    (hc : Commute (f k) (f x)) : Commute k x := by
  have hconj : k*x*k⁻¹∈R := (Subgroup.mem_normalizer_iff.mp hk x).mp hx
  have hm : f (k*x*k⁻¹)=f x := by
    rw [map_mul,map_mul,map_inv]
    exact mul_inv_eq_iff_eq_mul.mpr hc
  have he : (⟨k*x*k⁻¹,hconj⟩ : R)=⟨x,hx⟩ := hf hm
  exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he)

theorem commute_map_iff {G H : Type*} [Group G] [Group H]
    (f : G→*H) (R : Subgroup G)
    (hf : Function.Injective (f.comp R.subtype)) (k x : G)
    (hk : k∈Subgroup.normalizer (R : Set G)) (hx : x∈R) :
    Commute (f k) (f x)↔Commute k x :=
  ⟨commute_of_map f R hf k x hk hx,fun h=>by
    simpa only [map_mul] using congrArg f h⟩

end SymmetricSubgroupAsymptotics.InjectiveSubgroupCentralizerLift
