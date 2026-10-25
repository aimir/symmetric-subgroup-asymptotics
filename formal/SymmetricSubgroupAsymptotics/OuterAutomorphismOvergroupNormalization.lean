import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex
import Mathlib.GroupTheory.Index

/-! An actual automorphism overgroup can normalize automorphisms into a
literal stabilizer without being an inner group. Its contribution is
charged by the index of a subgroup acting by inner automorphisms.
No automorphism lift, stabilizer rigidity or outer-order bound is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OuterAutomorphismOvergroupNormalization
open PrimitiveSocleRawStructure
variable {A : Type*} {G : Type} [Group A] [Group G] [Finite A] [Finite G]

theorem outer_card_le_index_mul_stabilizer
    (phi : A →* MulAut G) (N : Subgroup A)
    (hinner : ∀ a ∈ N, phi a ∈ Inner G)
    (S : Subgroup (MulAut G))
    (hcover : ∀ f : MulAut G, ∃ a : A, phi a * f ∈ S) :
    Nat.card (Outer G) ≤ N.index * Nat.card S := by
  let out : MulAut G →* Outer G := QuotientGroup.mk' (Inner G)
  let chi : A →* Outer G := out.comp phi
  have hN : N ≤ chi.ker := by
    intro a ha
    change out (phi a) = 1
    exact (QuotientGroup.eq_one_iff _).mpr (hinner a ha)
  have hrange : Nat.card chi.range ≤ N.index := by
    rw [← Subgroup.index_ker]
    exact Subgroup.index_antitone hN
  let F : chi.range × S → Outer G := fun p => p.1.val⁻¹ * out p.2.val
  have hF : Function.Surjective F := by
    intro o
    obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective (Inner G) o
    obtain ⟨a, ha⟩ := hcover f
    refine ⟨(⟨chi a, ⟨a, rfl⟩⟩, ⟨phi a * f, ha⟩), ?_⟩
    change (out (phi a))⁻¹ * out (phi a * f) = o
    rw [map_mul, inv_mul_cancel_left]
    exact hf
  have hcard : Nat.card (Outer G) ≤ Nat.card chi.range * Nat.card S := by
    simpa only [Nat.card_prod] using Nat.card_le_card_of_surjective F hF
  exact hcard.trans (Nat.mul_le_mul_right _ hrange)

end SymmetricSubgroupAsymptotics.OuterAutomorphismOvergroupNormalization
