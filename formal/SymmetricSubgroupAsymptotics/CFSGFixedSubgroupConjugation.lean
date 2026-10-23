import SymmetricSubgroupAsymptotics.CFSGCentralTwistedCommutatorLift
import SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateOrbitCardinality

/-! Conjugation by a genuinely fixed element commutes with taking the
fixed part of an actual subgroup. Ambient normalizer membership then
restricts to the same fixed intersection. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFixedSubgroupConjugation
open CFSGCentralTwistedCommutatorLift CFSGSubgroupConjugateOrbitCardinality
variable {G : Type*} [Group G]

theorem fixed_subgroup_map (tau : MulAut G) (g : G) (hg : tau g=g) :
    (fixedSubgroup tau).map (MulAut.conj g).toMonoidHom=fixedSubgroup tau := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    change tau (g*y*g⁻¹)=g*y*g⁻¹
    change tau y=y at hy
    rw [map_mul,map_mul,map_inv,hg,hy]
  · intro hx
    change tau x=x at hx
    refine ⟨g⁻¹*x*g,?_,?_⟩
    · change tau (g⁻¹*x*g)=g⁻¹*x*g
      rw [map_mul,map_mul,map_inv,hg,hx]
    · change g*(g⁻¹*x*g)*g⁻¹=x
      group

theorem map_inf_fixed (tau : MulAut G) (H : Subgroup G) (g : G) (hg : tau g=g) :
    (H⊓fixedSubgroup tau).map (MulAut.conj g).toMonoidHom=
      H.map (MulAut.conj g).toMonoidHom⊓fixedSubgroup tau := by
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,fixed_subgroup_map tau g hg]

theorem normalizes_inf_fixed (tau : MulAut G) (H : Subgroup G) (g : G)
    (hg : tau g=g) (hN : g∈Subgroup.normalizer (H : Set G)) :
    g∈Subgroup.normalizer ((H⊓fixedSubgroup tau : Subgroup G) : Set G) := by
  apply Subgroup.mem_normalizer_iff_conj_image_eq.mpr
  have he : (H⊓fixedSubgroup tau).map (MulAut.conj g).toMonoidHom=H⊓fixedSubgroup tau := by
    rw [map_inf_fixed tau H g hg,conjugate_eq_of_mem_normalizer H g hN]
  exact congrArg (fun S : Subgroup G=>(S : Set G)) he

end SymmetricSubgroupAsymptotics.CFSGFixedSubgroupConjugation
