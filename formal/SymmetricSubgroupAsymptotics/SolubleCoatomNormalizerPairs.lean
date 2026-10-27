import SymmetricSubgroupAsymptotics.CFSGSylowNormalizerGeneration
import Mathlib.GroupTheory.Nilpotent

/-! A soluble maximal Sylow normalizer supplies the full simple-factor
witness needed by Suzuki's induction. This uses two normalizer conjugates,
and deliberately does not assert generation by two Sylow subgroups. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SolubleCoatomNormalizerPairs
open CFSGReduction

variable {G : Type*} [Group G] [Finite G]

theorem normalizer_soluble_of_prime_power_index {p q e : ℕ}
    [Fact p.Prime] [Fact q.Prime] (P : Sylow p G)
    (hindex : ((P : Subgroup G).subgroupOf
      (Subgroup.normalizer (P : Set G))).index = q ^ e) :
    IsSolvable (Subgroup.normalizer (P : Set G)) := by
  let N := Subgroup.normalizer (P : Set G)
  let Q : Sylow p N := P.subtype Subgroup.le_normalizer
  let S : Subgroup N := Q
  letI : S.Normal := by
    change ((P : Subgroup G).subgroupOf (Subgroup.normalizer (P : Set G))).Normal
    exact (P : Subgroup G).normal_in_normalizer
  letI : Group.IsNilpotent S := Q.isPGroup'.isNilpotent
  letI : IsSolvable S := inferInstance
  have hc : Nat.card (N ⧸ S) = q ^ e := by
    rw [← Subgroup.index_eq_card]
    exact hindex
  letI : Group.IsNilpotent (N ⧸ S) := (IsPGroup.of_card hc).isNilpotent
  letI : IsSolvable (N ⧸ S) := inferInstance
  exact solvable_of_ker_le_range S.subtype (QuotientGroup.mk' S)
    (le_of_eq (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype]))

theorem conjugates_generate_of_coatom_self_normalizing (H : Subgroup G)
    (hmax : IsCoatom H) (hself : Subgroup.normalizer (H : Set G) = H) :
    ∃ g : G, Subgroup.closure ((H : Set G) ∪
      H.map (MulAut.conj g).toMonoidHom) = ⊤ := by
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ H := by
    by_contra! h
    exact hmax.ne_top (top_unique (fun g _ => h g))
  have hjoin : H ⊔ H.map (MulAut.conj g).toMonoidHom = ⊤ := by
    rcases hmax.le_iff.mp (show H ≤ H ⊔ H.map (MulAut.conj g).toMonoidHom
      from le_sup_left) with htop | heq
    · exact htop
    · exfalso
      have hmap : H.map (MulAut.conj g).toMonoidHom ≤ H :=
        (sup_le_iff.mp (le_of_eq heq)).2
      have hgn : g ∈ Subgroup.normalizer (H : Set G) :=
        Subgroup.mem_normalizer_fintype (fun x hx =>
          hmap ⟨x, hx, by rfl⟩)
      exact hg (hself ▸ hgn)
  refine ⟨g, ?_⟩
  simpa only [Subgroup.closure_union, Subgroup.closure_eq] using hjoin

theorem sylow_normalizer_witness {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hsol : IsSolvable (Subgroup.normalizer (P : Set G)))
    (hmax : IsCoatom (Subgroup.normalizer (P : Set G))) :
    ∃ (H : Subgroup G) (g : G), IsSolvable H ∧ Intravariant H ∧
      Subgroup.normalizer (H : Set G) = H ∧
      Subgroup.closure ((H : Set G) ∪ H.map (MulAut.conj g).toMonoidHom) = ⊤ := by
  obtain ⟨g, hgen⟩ := conjugates_generate_of_coatom_self_normalizing
    (Subgroup.normalizer (P : Set G)) hmax (sylow_normalizer_self_normalizing P)
  exact ⟨_, g, hsol, sylow_normalizer_intravariant P,
    sylow_normalizer_self_normalizing P, hgen⟩

end SymmetricSubgroupAsymptotics.SolubleCoatomNormalizerPairs
