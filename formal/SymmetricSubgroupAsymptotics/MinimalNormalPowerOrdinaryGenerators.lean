import SymmetricSubgroupAsymptotics.MinimalNormalInternalFactorOrdinaryGenerators
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawChart
import Mathlib.Algebra.Group.Pi.Lemmas

/-! A literal homogeneous minimal normal subgroup costs the ordinary
generating rank of one factor, regardless of its number of factors.
The coordinate factor is internally normal, and ambient conjugation
supplies its entire normal closure by minimality.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MinimalNormalPowerOrdinaryGenerators

theorem genRank_le {G T I : Type} [Group G] [Finite G] [Group T]
    [Finite T] [Nontrivial T] (E : Subgroup G) [E.Normal]
    (hE : IsMinimalNormalSubgroup E) (e : E ≃* (I → T)) (i : I) :
    MarkedC4.genRank G ≤ MarkedC4.genRank T + MarkedC4.genRank (G⧸E) := by
  let f : T →* E := e.symm.toMonoidHom.comp (MonoidHom.mulSingle (fun _ : I => T) i)
  have hf : Function.Injective f := by
    intro x y hxy
    have h := congrArg (fun a : E => e a i) hxy
    simpa only [f,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply,MonoidHom.mulSingle_apply,Pi.mulSingle_eq_same] using h
  let A : Subgroup E := f.range
  letI : A.Normal := {
    conj_mem := by
      rintro _ ⟨t,rfl⟩ x
      refine ⟨(e x i)*t*(e x i)⁻¹,?_⟩
      apply e.injective
      funext j
      by_cases hj : j=i
      · subst j
        simp only [f,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
          MulEquiv.apply_symm_apply,MonoidHom.mulSingle_apply,Pi.mulSingle_eq_same,
          map_mul,map_inv,Pi.mul_apply,Pi.inv_apply]
      · simp only [f,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
          MulEquiv.apply_symm_apply,MonoidHom.mulSingle_apply,Pi.mulSingle_eq_of_ne hj,
          map_mul,map_inv,Pi.mul_apply,Pi.inv_apply,mul_one,mul_inv_cancel]
  }
  have hA : A≠⊥ := by
    intro hbot
    obtain ⟨t,ht⟩ := exists_ne (1 : T)
    have hm : f t ∈ A := ⟨t,rfl⟩
    rw [hbot] at hm
    exact ht (hf ((Subgroup.mem_bot.mp hm).trans (map_one f).symm))
  have h := MinimalNormalInternalFactorOrdinaryGenerators.genRank_le E A hE hA
  rw [← CoprimeNilpotentProductGenerators.genRank_mulEquiv (MonoidHom.ofInjective hf)] at h
  exact h

end MinimalNormalPowerOrdinaryGenerators

namespace PrimitiveSocleRawStructure

theorem NonaffineData.genRank_le_simple_add_quotient_of_minimal
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) (hmin : IsMinimalNormalSubgroup (finiteGroupSocle G)) :
    MarkedC4.genRank G ≤ MarkedC4.genRank D.Simple +
      MarkedC4.genRank (G⧸finiteGroupSocle G) :=
  MinimalNormalPowerOrdinaryGenerators.genRank_le (finiteGroupSocle G) hmin
    D.socleEquiv ⟨0,D.factorCount_pos⟩

end PrimitiveSocleRawStructure
end SymmetricSubgroupAsymptotics
