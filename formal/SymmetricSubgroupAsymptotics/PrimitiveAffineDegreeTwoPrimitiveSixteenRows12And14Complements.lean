import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRows12And14LinearRelations
import SymmetricSubgroupAsymptotics.CyclicKernelNormalGenerators
import SymmetricSubgroupAsymptotics.AlternatingSymmetricNormalChain

/-! The exact five-plane actions of the original row12/14 complements
have cyclic kernels and images S5/A5. Their ambient normal subgroups need
at most two generators by the cyclic-kernel extension theorem. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPrimitiveSixteenRows12And14Complements

open BinaryFourProjectiveSpread
open PrimitiveAffineDegreeTwoPrimitiveSixteenRows12And14LinearRelations

abbrev R12 : Subgroup LinearGroup := Subgroup.closure ({a12, b12} : Set LinearGroup)
abbrev R14 : Subgroup LinearGroup := Subgroup.closure ({a14, b14} : Set LinearGroup)

theorem a12_mem : a12 ∈ R12 := Subgroup.subset_closure (by simp)
theorem b12_mem : b12 ∈ R12 := Subgroup.subset_closure (by simp)
theorem a14_mem : a14 ∈ R14 := Subgroup.subset_closure (by simp)
theorem b14_mem : b14 ∈ R14 := Subgroup.subset_closure (by simp)

theorem stable12 : R12 ≤ InvariantEmbeddingPermutationAction.liftable planeAction (spread chart12) := by
  apply (Subgroup.closure_le _).mpr
  intro r hr
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl
  · exact ⟨alpha, a12_spread⟩
  · exact ⟨beta12, b12_spread⟩

theorem stable14 : R14 ≤ InvariantEmbeddingPermutationAction.liftable planeAction (spread chart14) := by
  apply (Subgroup.closure_le _).mpr
  intro r hr
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl
  · exact ⟨alpha, a14_spread⟩
  · exact ⟨beta14, b14_spread⟩

def projective12 : R12 →* Equiv.Perm (Fin 5) :=
  InvariantEmbeddingPermutationAction.lift (planeAction.comp R12.subtype)
    (spread chart12) (spread_injective chart12) (fun g ↦ stable12 g.2)

def projective14 : R14 →* Equiv.Perm (Fin 5) :=
  InvariantEmbeddingPermutationAction.lift (planeAction.comp R14.subtype)
    (spread chart14) (spread_injective chart14) (fun g ↦ stable14 g.2)

theorem projective12_a : projective12 ⟨a12, a12_mem⟩ = alpha :=
  InvariantEmbeddingPermutationAction.lift_eq _ _ _ _ _ _ a12_spread
theorem projective12_b : projective12 ⟨b12, b12_mem⟩ = beta12 :=
  InvariantEmbeddingPermutationAction.lift_eq _ _ _ _ _ _ b12_spread
theorem projective14_a : projective14 ⟨a14, a14_mem⟩ = alpha :=
  InvariantEmbeddingPermutationAction.lift_eq _ _ _ _ _ _ a14_spread
theorem projective14_b : projective14 ⟨b14, b14_mem⟩ = beta14 :=
  InvariantEmbeddingPermutationAction.lift_eq _ _ _ _ _ _ b14_spread

theorem projective12_intertwine (g : R12) (i : Fin 5) :
    planeAction g.1 (spread chart12 i) = spread chart12 (projective12 g i) :=
  InvariantEmbeddingPermutationAction.intertwine (planeAction.comp R12.subtype)
    (spread chart12) (spread_injective chart12) (fun r ↦ stable12 r.2) g i

theorem projective14_intertwine (g : R14) (i : Fin 5) :
    planeAction g.1 (spread chart14 i) = spread chart14 (projective14 g i) :=
  InvariantEmbeddingPermutationAction.intertwine (planeAction.comp R14.subtype)
    (spread chart14) (spread_injective chart14) (fun r ↦ stable14 r.2) g i

theorem projective12_kernel_cyclic : IsCyclic projective12.ker :=
  action_kernel_isCyclic R12.subtype Subtype.val_injective projective12 chart12
    projective12_intertwine

theorem projective14_kernel_cyclic : IsCyclic projective14.ker :=
  action_kernel_isCyclic R14.subtype Subtype.val_injective projective14 chart14
    projective14_intertwine

theorem projective12_range : projective12.range = ⊤ := by
  apply top_unique
  rw [← symmetric_generators]
  apply (Subgroup.closure_le _).mpr
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · exact ⟨⟨a12, a12_mem⟩, projective12_a⟩
  · exact ⟨⟨b12, b12_mem⟩, projective12_b⟩

theorem projective14_range_le : projective14.range ≤ alternatingGroup (Fin 5) := by
  generalize hφ : projective14 = φ
  have ha : φ ⟨a14, a14_mem⟩ ∈ alternatingGroup (Fin 5) := by
    rw [← hφ, projective14_a]
    exact alpha_even
  have hb : φ ⟨b14, b14_mem⟩ ∈ alternatingGroup (Fin 5) := by
    rw [← hφ, projective14_b]
    exact beta14_even
  have hgen : ∀ r (hr : r ∈ R14),
      φ ⟨r, hr⟩ ∈ alternatingGroup (Fin 5) := by
    intro r hr
    induction hr using Subgroup.closure_induction with
    | mem r hr =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
      rcases hr with rfl | rfl
      · exact ha
      · exact hb
    | one =>
      change φ 1 ∈ _
      rw [map_one]
      exact (alternatingGroup (Fin 5)).one_mem
    | mul r s hr hs h1 h2 =>
      change φ ((⟨r, hr⟩ : R14) * ⟨s, hs⟩) ∈ _
      rw [map_mul]
      exact (alternatingGroup (Fin 5)).mul_mem h1 h2
    | inv r hr h1 =>
      change φ ((⟨r, hr⟩ : R14)⁻¹) ∈ _
      rw [map_inv]
      exact (alternatingGroup (Fin 5)).inv_mem h1
  rintro _ ⟨g, rfl⟩
  exact hgen g.1 g.2

theorem projective14_range : projective14.range = alternatingGroup (Fin 5) := by
  apply le_antisymm projective14_range_le
  rw [← alternating_generators]
  apply (Subgroup.closure_le _).mpr
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · exact ⟨⟨a14, a14_mem⟩, projective14_a⟩
  · exact ⟨⟨b14, b14_mem⟩, projective14_b⟩

def evenProjective14 : R14 →* alternatingGroup (Fin 5) :=
  projective14.codRestrict _ (fun g ↦ projective14_range_le ⟨g, rfl⟩)

theorem evenProjective14_surjective : Function.Surjective evenProjective14 := by
  intro p
  have hp : p.1 ∈ projective14.range := by rw [projective14_range]; exact p.2
  obtain ⟨g, hg⟩ := hp
  exact ⟨g, Subtype.ext hg⟩

theorem normal_generating_pairs12 :
    ∀ N : Subgroup R12, N.Normal →
      ∃ x : Fin 2 → R12, Subgroup.normalClosure (Set.range x) = N := by
  letI := projective12_kernel_cyclic
  exact normal_generating_pairs_of_cyclic_kernel_normal_total projective12
    (MonoidHom.range_eq_top.mp projective12_range)
    (AlternatingSymmetricNormalChain.symmetric_normal_total (X := Fin 5) (by norm_num))

theorem normal_generating_pairs14 :
    ∀ N : Subgroup R14, N.Normal →
      ∃ x : Fin 2 → R14, Subgroup.normalClosure (Set.range x) = N := by
  letI : IsCyclic evenProjective14.ker := by
    have hk : evenProjective14.ker = projective14.ker := by
      ext g
      change evenProjective14 g = 1 ↔ projective14 g = 1
      exact Subtype.ext_iff
    rw [hk]
    exact projective14_kernel_cyclic
  exact normal_generating_pairs_of_cyclic_kernel_normal_total evenProjective14
    evenProjective14_surjective
    (AlternatingSymmetricNormalChain.alternating_normal_total (X := Fin 5) (by norm_num))

theorem irreducible12 : AffineModel.Irreducible R12 :=
  irreducible_of_nonzero_orbit R12 a12 a12_mem a12_orbit

theorem irreducible14 : AffineModel.Irreducible R14 :=
  irreducible_of_nonzero_orbit R14 a14 a14_mem a14_orbit

end PrimitiveAffineDegreeTwoPrimitiveSixteenRows12And14Complements
end SymmetricSubgroupAsymptotics

end
