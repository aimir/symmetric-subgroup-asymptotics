import SymmetricSubgroupAsymptotics.CFSGGoodSylowPrime
import SymmetricSubgroupAsymptotics.CFSGTwoPSubgroupsSylowGeneration

/-! Two generating p-subgroups and one soluble Sylow normalizer produce
the actual good-Sylow witnesses. Conjugacy transports the normalizer to
the generating Sylow; the original p-subgroups need not be Sylow. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Pointwise
namespace SymmetricSubgroupAsymptotics.CFSGReduction
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem goodSylowPrime_of_two_p_subgroups_and_exists_soluble_normalizer
    (U V : Subgroup G) (hU : IsPGroup p U) (hV : IsPGroup p V) (hgen : U ⊔ V = ⊤)
    (hsol : ∃ Q : Sylow p G, IsSolvable (Subgroup.normalizer (Q : Set G))) :
    GoodSylowPrime G p := by
  obtain ⟨P, g, _, hgenerate⟩ :=
    CFSGTwoPSubgroupsSylowGeneration.exists_conjugate_sylows U V hU hV hgen
  obtain ⟨Q, hQ⟩ := hsol
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq G Q P
  let e := MulAut.conj a
  have he : (Q : Subgroup G).map e.toMonoidHom = (P : Subgroup G) := by
    have hh := congrArg (fun R : Sylow p G => (R : Subgroup G)) ha
    simpa only [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def] using hh
  let N := Subgroup.normalizer (Q : Set G)
  letI : IsSolvable N := hQ
  let b := N.equivMapOfInjective e.toMonoidHom e.injective
  have hm : IsSolvable (N.map e.toMonoidHom) :=
    solvable_of_solvable_injective (f := b.symm.toMonoidHom) b.symm.injective
  have hP : IsSolvable (Subgroup.normalizer (P : Set G)) := by
    change IsSolvable (Subgroup.normalizer ((P : Subgroup G) : Set G))
    rw [← he, ← Subgroup.map_equiv_normalizer_eq]
    exact hm
  exact ⟨Fact.out, P, g, hP, hgenerate⟩

end SymmetricSubgroupAsymptotics.CFSGReduction
