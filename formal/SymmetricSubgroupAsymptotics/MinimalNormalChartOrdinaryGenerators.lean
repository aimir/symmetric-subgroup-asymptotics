import SymmetricSubgroupAsymptotics.MinimalNormalInternalFactorOrdinaryGenerators
import SymmetricSubgroupAsymptotics.SemisimpleNormalChart
import Mathlib.Algebra.Group.Pi.Lemmas

/-! A heterogeneous actual semisimple chart of a minimal normal subgroup
costs the genuine ordinary rank of one selected internal simple factor.
The factor's type is retained. No homogeneous-coordinate replacement,
simple two-generation, or nonabelian minimal-normal '+1' is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.MinimalNormalChartOrdinaryGenerators

theorem genRank_le_factor {G : Type} [Group G] [Finite G]
    (E : Subgroup G) [E.Normal] (hE : IsMinimalNormalSubgroup E)
    (C : SemisimpleNormalChart E) (i : C.ι) :
    MarkedC4.genRank G ≤ MarkedC4.genRank (C.factor i) + MarkedC4.genRank (G ⧸ E) := by
  classical
  letI : IsSimpleGroup (C.factor i) := C.simple i
  let f : C.factor i →* E :=
    C.equiv.symm.toMonoidHom.comp (MonoidHom.mulSingle C.factor i)
  have hf : Function.Injective f := by
    intro x y hxy
    have h := congrArg (fun a : E => C.equiv a i) hxy
    simpa only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same] using h
  let A : Subgroup E := f.range
  letI : A.Normal := {
    conj_mem := by
      rintro _ ⟨t, rfl⟩ x
      refine ⟨(C.equiv x i)*t*(C.equiv x i)⁻¹, ?_⟩
      apply C.equiv.injective
      funext j
      by_cases hj : j = i
      · subst j
        simp only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          MulEquiv.apply_symm_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same,
          map_mul, map_inv, Pi.mul_apply, Pi.inv_apply]
      · simp only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          MulEquiv.apply_symm_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hj,
          map_mul, map_inv, Pi.mul_apply, Pi.inv_apply, mul_one, mul_inv_cancel] }
  have hA : A ≠ ⊥ := by
    intro hbot
    obtain ⟨t, ht⟩ := exists_ne (1 : C.factor i)
    have hm : f t ∈ A := ⟨t, rfl⟩
    rw [hbot] at hm
    exact ht (hf ((Subgroup.mem_bot.mp hm).trans (map_one f).symm))
  have h := MinimalNormalInternalFactorOrdinaryGenerators.genRank_le E A hE hA
  rw [← CoprimeNilpotentProductGenerators.genRank_mulEquiv (MonoidHom.ofInjective hf)] at h
  exact h

theorem exists_generating_finset {G : Type} [Group G] [Finite G]
    (E : Subgroup G) [E.Normal] (hE : IsMinimalNormalSubgroup E)
    (C : SemisimpleNormalChart E) (i : C.ι) :
    ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧
      S.card ≤ MarkedC4.genRank (C.factor i) + MarkedC4.genRank (G ⧸ E) := by
  obtain ⟨S, hcard, hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨S, hgen, hcard.le.trans (genRank_le_factor E hE C i)⟩

end SymmetricSubgroupAsymptotics.MinimalNormalChartOrdinaryGenerators
