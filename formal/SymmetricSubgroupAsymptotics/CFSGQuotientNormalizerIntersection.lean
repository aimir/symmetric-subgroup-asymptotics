import SymmetricSubgroupAsymptotics.CFSGCentralKernelPSubgroupReflection
import Mathlib.Algebra.Group.Subgroup.Map

/-! Actual simple-root intersection identities descend through central
quotients. Kernel containment justifies the intersection; p-element
separation justifies the FULL normalizer image. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGQuotientNormalizerIntersection
open CFSGCentralKernelPSubgroupReflection
variable {G H : Type*} [Group G] [Group H]

theorem map_inf_of_ker_le_right (f : G→*H) (U R : Subgroup G) (hker : f.ker≤R) :
    (U⊓R).map f=U.map f⊓R.map f := by
  apply le_antisymm (Subgroup.map_inf_le _ _ _)
  rintro _ ⟨⟨u,hu,rfl⟩,v,hv,he⟩
  have hk : u*v⁻¹∈f.ker := by
    change f (u*v⁻¹)=1
    rw [map_mul,map_inv,he,mul_inv_cancel]
  have hr := R.mul_mem (hker hk) hv
  have huR : u∈R := by simpa only [mul_assoc,inv_mul_cancel,mul_one] using hr
  exact ⟨u,⟨hu,huR⟩,rfl⟩

theorem normalizer_map_eq_of_central_p_separation {p : ℕ} [Fact p.Prime]
    (f : G→*H) (hf : Function.Surjective f) (P : Sylow p G)
    (hP : Function.Injective (f.comp (P : Subgroup G).subtype))
    (hker : f.ker≤Subgroup.center G) (V : Subgroup G) (hV : IsPGroup p V) :
    (Subgroup.normalizer (V : Set G)).map f=Subgroup.normalizer (V.map f : Set H) := by
  apply le_antisymm (Subgroup.le_normalizer_map f)
  intro q hq
  obtain ⟨g,rfl⟩ := hf q
  exact ⟨g,(mem_normalizer_map_iff f P hP hker V hV g).mp hq,rfl⟩

theorem opposite_normalizer_intersection_map {p : ℕ} [Fact p.Prime]
    (f : G→*H) (hf : Function.Surjective f) (P : Sylow p G)
    (hP : Function.Injective (f.comp (P : Subgroup G).subtype))
    (hker : f.ker≤Subgroup.center G) (U V R : Subgroup G) (hV : IsPGroup p V)
    (hinter : U⊓(Subgroup.normalizer (V : Set G)⊔R)=R) :
    U.map f⊓(Subgroup.normalizer (V.map f : Set H)⊔R.map f)=R.map f := by
  have hk : f.ker≤Subgroup.normalizer (V : Set G)⊔R :=
    hker.trans ((Subgroup.center_le_normalizer (V : Set G)).trans le_sup_left)
  have hh := congrArg (fun S : Subgroup G=>S.map f) hinter
  dsimp only at hh
  rw [map_inf_of_ker_le_right f U _ hk,Subgroup.map_sup,
    normalizer_map_eq_of_central_p_separation f hf P hP hker V hV] at hh
  exact hh

end SymmetricSubgroupAsymptotics.CFSGQuotientNormalizerIntersection
