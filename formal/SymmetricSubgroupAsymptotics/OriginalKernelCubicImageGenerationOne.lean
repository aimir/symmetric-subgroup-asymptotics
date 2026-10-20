import SymmetricSubgroupAsymptotics.OriginalKernelImageCubicProjectors
import SymmetricSubgroupAsymptotics.ProjectorRankSubmoduleQuotient
import SymmetricSubgroupAsymptotics.BinaryCubicProjectorIdempotents
import SymmetricSubgroupAsymptotics.CubicProjectorSchurCapacityOne
import SymmetricSubgroupAsymptotics.RepresentationGeneratorRestrictionMaschke

/-! One ambient generator from the literal elementary intersection/image:
intersection fixed rank<=1 and active rank0, actual fixed-free image<=4.
Every map is retained from the SAME original quotient. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra
namespace SymmetricSubgroupAsymptotics.OriginalKernelModuleChart

variable {Q B D H : Type} [Group Q] [Group B] [Group D] [Group H] [Finite H]
  [NeZero (Nat.card H : ZMod 2)]
  {eta : Q →* D} {A : Rep.{0} (ZMod 2) D} [Finite A]
  (E : OriginalKernelModuleChart eta A) (pi : Q →* B)

theorem generatedBy_one_of_cubic_intersection (f : H →* Q) (a : H)
    (hgen : ∀ h : H, ∃ n : ℕ, h=a^n) (ha : a^3=1)
    (hke : Module.finrank (ZMod 2) (LinearMap.range
      (1+(E.kernelIntersection pi).toRepresentation (f a)+
        ((E.kernelIntersection pi).toRepresentation (f a))^2))≤1)
    (hkf : Module.finrank (ZMod 2) (LinearMap.range
      ((E.kernelIntersection pi).toRepresentation (f a)+
        ((E.kernelIntersection pi).toRepresentation (f a))^2))≤0)
    (hcard : Nat.card (E.elementaryImageHom pi).range≤4)
    (hfix : ∀ x∈(E.elementaryImageHom pi).range,
      pi (f a)*x*(pi (f a))⁻¹=x → x=1) : RepresentationGeneratedBy A.ρ 1 := by
  let S := (E.kernelIntersection pi).toSubmodule
  let tau : Representation (ZMod 2) H A := A.ρ.comp (eta.comp f)
  let T := tau a
  let U := (E.kernelIntersection pi).toRepresentation (f a)
  let V := E.kernelImageRepresentation pi (f a)
  have hga : (f a)^3=1 := by rw [← map_pow,ha,map_one]
  have hc : T^3=1 := by change (tau a)^3=1; rw [← map_pow,ha,map_one]
  obtain ⟨hve,hvf⟩ := E.kernelImage_projector_ranks pi (f a) hga hcard hfix
  have he : Module.finrank (ZMod 2) (LinearMap.range (1+T+T^2))≤1 := by
    have hh := ProjectorRankSubmoduleQuotient.range_rank_le S
      (1+T+T^2) (1+V+V^2) (1+U+U^2)
      (BinaryCubicProjectorIdempotents.fixed T hc) (by
        intro v
        simp only [pow_two,Module.End.mul_apply,LinearMap.add_apply,Module.End.one_apply,map_add] <;> rfl) (fun _ => rfl)
    exact hh.trans (Nat.add_le_add hke (le_of_eq hve))
  have hf : Module.finrank (ZMod 2) (LinearMap.range (T+T^2))≤2 := by
    have hh := ProjectorRankSubmoduleQuotient.range_rank_le S
      (T+T^2) (V+V^2) (U+U^2)
      (BinaryCubicProjectorIdempotents.active T hc) (by
        intro v
        simp only [pow_two,Module.End.mul_apply,LinearMap.add_apply,Module.End.one_apply,map_add] <;> rfl) (fun _ => rfl)
    exact hh.trans (Nat.add_le_add hkf hvf)
  have hmem : ∀ v : tau.invariants, (v : A)∈(1+T+T^2 : Module.End (ZMod 2) A).range := by
    intro v
    refine ⟨v,?_⟩
    have hv : T v.val=v.val := v.property a
    change v.val+T v.val+T (T v.val)=v.val
    rw [hv,hv]
    have hz : v.val+v.val=0 := by
      rw [← two_smul (ZMod 2),show (2 : ZMod 2)=0 by decide,zero_smul]
    rw [hz,zero_add]
  let j := tau.invariants.subtype.codRestrict (1+T+T^2).range hmem
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : (1+T+T^2 : Module.End (ZMod 2) A).range => (z : A)) h
  have hfixed : Module.finrank (ZMod 2) tau.invariants≤1 :=
    (j.finrank_le_finrank_of_injective hj).trans he
  have ht : RepresentationGeneratedBy tau 1 :=
    CubicProjectorSchurCapacityOne.generatedBy_one tau a hgen hc hfixed hf
  exact RepresentationGeneratedBy.of_comp A.ρ (eta.comp f) ht

end SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
