import SymmetricSubgroupAsymptotics.CFSGAlternatingThreeCycleStars

/-! Elementary support gluing on the literal natural point set. Two
supported alternating groups covering the point set generate its full
alternating group when their supports share two distinct points. The
proof uses only fixed-pair three-cycle stars, not Jordan's theorem or an
abstract recognition of a permutation representation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AlternatingSupportedOverlapGeneration
open Equiv Equiv.Perm CFSGAlternatingStarGenerators CFSGAlternatingThreeCycleStars

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem eq_top_of_two_supported_alternating
    (H : Subgroup (alternatingGroup X)) (S T : Finset X)
    (a b : X) (hab : a ≠ b)
    (haS : a ∈ S) (hbS : b ∈ S) (haT : a ∈ T) (hbT : b ∈ T)
    (hcover : S ∪ T = Finset.univ)
    (hS : (alternatingGroup.ofSubtype S).range ≤ H)
    (hT : (alternatingGroup.ofSubtype T).range ≤ H) : H = ⊤ := by
  let K : Subgroup (Perm X) := H.map (alternatingGroup X).subtype
  have supported_mem (s : Finset X)
      (hs : (alternatingGroup.ofSubtype s).range ≤ H)
      (g : Perm X) (hg : g ∈ alternatingGroup X) (hgs : g.support ⊆ s) : g ∈ K := by
    apply Subgroup.mem_map.mpr
    refine ⟨⟨g, hg⟩, hs ?_, rfl⟩
    exact (alternatingGroup.mem_range_ofSubtype_iff s ⟨g, hg⟩).mpr hgs
  have hfull : alternatingGroup X ≤ K := by
    apply alternating_le_of_star K a b hab
    intro c hca hcb
    have heven : cycle a b c ∈ alternatingGroup X :=
      (cycle_isThreeCycle a b c hab (Ne.symm hca) (Ne.symm hcb)).mem_alternatingGroup
    have hc : c ∈ S ∨ c ∈ T := by
      apply Finset.mem_union.mp
      rw [hcover]
      exact Finset.mem_univ c
    rcases hc with hcS | hcT
    · apply supported_mem S hS _ heven
      rw [cycle_support a b c hab (Ne.symm hca) (Ne.symm hcb)]
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨haS, hbS, hcS⟩
    · apply supported_mem T hT _ heven
      rw [cycle_support a b c hab (Ne.symm hca) (Ne.symm hcb)]
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨haT, hbT, hcT⟩
  apply top_unique
  intro g _
  obtain ⟨u, hu, he⟩ := Subgroup.mem_map.mp (hfull g.property)
  have hue : u = g := Subtype.ext he
  exact hue ▸ hu

end SymmetricSubgroupAsymptotics.AlternatingSupportedOverlapGeneration
