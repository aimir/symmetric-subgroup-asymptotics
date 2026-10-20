import SymmetricSubgroupAsymptotics.SolubleSocleConjugationModule
import Mathlib.RepresentationTheory.Intertwining

/-! The socle of a finite soluble group is abelian and semisimple for its
literal integral conjugation action. Surjective inflation preserves that
semisimplicity, with all primes retained in one integral module. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical IsMulCommutative MonoidAlgebra

namespace SymmetricSubgroupAsymptotics.SolubleSocleConjugationModule

variable {G : Type} [Group G] [Finite G] [IsSolvable G]

theorem minimalNormal_commutator_eq_bot (M K : Subgroup G)
    (hM : IsMinimalNormalSubgroup M) (hK : IsMinimalNormalSubgroup K) :
    ⁅M, K⁆ = ⊥ := by
  letI : M.Normal := hM.1
  letI : K.Normal := hK.1
  by_cases he : M = K
  · subst K
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (Subgroup.le_centralizer_iff_isMulCommutative.mpr
        (minimalNormal_isMulCommutative_of_isSolvable M hM))
  · have hinf : M ⊓ K = ⊥ := by
      by_contra hne
      have hi : M ⊓ K = M := hM.2.2 (M ⊓ K) inferInstance hne inf_le_left
      have hMK : M ≤ K := by rw [← hi]; exact inf_le_right
      exact he (hK.2.2 M inferInstance hM.2.1 hMK)
    exact le_antisymm ((Subgroup.commutator_le_inf (H₁ := M) (H₂ := K)).trans_eq hinf)
      bot_le

theorem socle_isMulCommutative : IsMulCommutative (finiteGroupSocle G) := by
  have hcentral (M : Subgroup G) (hM : IsMinimalNormalSubgroup M) :
      finiteGroupSocle G ≤ Subgroup.centralizer (M : Set G) := by
    letI : M.Normal := hM.1
    apply Subgroup.normalClosure_le_normal
    rintro x ⟨K, hK, hx⟩
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (minimalNormal_commutator_eq_bot K M hK hM)) hx
  apply Subgroup.le_centralizer_iff_isMulCommutative.mp
  apply Subgroup.normalClosure_le_normal
  rintro x ⟨M, hM, hx⟩
  exact (Subgroup.le_centralizer_iff.mpr (hcentral M hM)) hx

theorem socle_isSemisimple :
    letI : IsMulCommutative (finiteGroupSocle G) := socle_isMulCommutative (G := G)
    IsSemisimpleModule ℤ[G] (representation (finiteGroupSocle G)).asModule := by
  letI : IsMulCommutative (finiteGroupSocle G) := socle_isMulCommutative (G := G)
  let N := finiteGroupSocle G
  let T : Submodule ℤ[G] (representation N).asModule :=
    sSup {S | IsSimpleModule ℤ[G] S}
  apply IsSemisimpleModule.of_sSup_simples_eq_top
  change T = ⊤
  have hNT : N ≤ submoduleGroup N T := by
    apply Subgroup.normalClosure_le_normal
    rintro g ⟨M, hM, hg⟩
    letI : M.Normal := hM.1
    have hMN : M ≤ N := by
      intro m hm
      exact Subgroup.subset_normalClosure ⟨M, hM, hm⟩
    have hsimple : IsSimpleModule ℤ[G] (normalSubmodule N M) :=
      minimalNormal_isSimple N M hM hMN
    apply (mem_submoduleGroup N T (⟨g, hMN hg⟩ : N)).mpr
    have hle : normalSubmodule N M ≤ T := le_sSup
      (show normalSubmodule N M ∈
        {S : Submodule ℤ[G] (representation N).asModule | IsSimpleModule ℤ[G] S} from hsimple)
    exact hle hg
  apply top_unique
  intro v _
  exact (mem_submoduleGroup N T v.toMul).mp (hNT v.toMul.property)

/-- The integral group-algebra restriction along an actual epimorphism
retains all simple factors, without a characteristic restriction. -/
theorem semisimple_comp {A B V : Type} [Group A] [Group B]
    [AddCommGroup V] [Module ℤ V]
    (f : A →* B) (hf : Function.Surjective f) (rho : Representation ℤ B V)
    [IsSemisimpleModule ℤ[B] rho.asModule] :
    IsSemisimpleModule ℤ[A] (Representation.asModule (rho.comp f)) := by
  let phi := MonoidAlgebra.mapDomainRingHom ℤ f
  letI : RingHomSurjective phi := ⟨Finsupp.mapDomain_surjective hf⟩
  let F : Representation.asModule (rho.comp f) →ₛₗ[phi] rho.asModule := {
    toFun := fun x => x
    map_add' := fun _ _ => rfl
    map_smul' := by
      intro r x
      induction r using MonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [map_add, add_smul, ha, hb]
      | single g z =>
          simp only [phi, MonoidAlgebra.mapDomainRingHom_apply,
            MonoidAlgebra.mapDomain_single, Representation.single_smul] <;> rfl }
  exact (F.isSemisimpleModule_iff_of_bijective
    ⟨Function.injective_id, Function.surjective_id⟩).mpr inferInstance

end SymmetricSubgroupAsymptotics.SolubleSocleConjugationModule
