import SymmetricSubgroupAsymptotics.C2WreathNormalCover

/-! Lift a local normal-cover epimorphism through the actual two-point
wreath product. The literal kernel is retained, and a positive uniform
normal-generator bound on the quotient is inherited without adding a slot. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace C2Wreath

open SemidirectProduct

variable {A Q : Type} [Group A] [Group Q]

def mapLocal (π : A →* Q) : W A →* W Q :=
  SemidirectProduct.map (π.prodMap π) (MonoidHom.id _)
    (by
      intro c
      rcases cases c with rfl | rfl
      · apply MonoidHom.ext
        intro v
        change (π (swapAut A 1 v).1, π (swapAut A 1 v).2) =
          swapAut Q 1 (π v.1, π v.2)
        rw [swapAut_one, swapAut_one]
      · apply MonoidHom.ext
        intro v
        change (π (swapAut A gen v).1, π (swapAut A gen v).2) =
          swapAut Q gen (π v.1, π v.2)
        rw [swapAut_gen, swapAut_gen])

theorem mapLocal_surjective (π : A →* Q) (hπ : Function.Surjective π) :
    Function.Surjective (mapLocal π) := by
  intro g
  obtain ⟨a, ha⟩ := hπ g.left.1
  obtain ⟨b, hb⟩ := hπ g.left.2
  refine ⟨⟨(a, b), g.right⟩, ?_⟩
  apply SemidirectProduct.ext
  · exact Prod.ext ha hb
  · rfl

theorem mapLocal_ker (π : A →* Q) :
    (mapLocal π).ker = (π.ker.prod π.ker).map (inl : A × A →* W A) := by
  apply le_antisymm
  · intro g hg
    have h : mapLocal π g = 1 := hg
    have ha : π g.left.1 = 1 := congrArg (fun q : W Q ↦ q.left.1) h
    have hb : π g.left.2 = 1 := congrArg (fun q : W Q ↦ q.left.2) h
    have hc : g.right = 1 := congrArg (fun q : W Q ↦ q.right) h
    refine ⟨g.left, ⟨ha, hb⟩, ?_⟩
    apply SemidirectProduct.ext
    · rfl
    · exact hc.symm
  · rintro g ⟨v, hv, rfl⟩
    apply MonoidHom.mem_ker.mpr
    apply SemidirectProduct.ext
    · exact Prod.ext hv.1 hv.2
    · rfl

theorem normal_generating_tuples_of_local_normal_cover [Nontrivial A]
    (π : A →* Q) (hπ : Function.Surjective π)
    (hcenter : Subgroup.center A = ⊥) (hker : π.ker ≠ ⊥)
    (hcover : ∀ K : Subgroup A, K.Normal → K ≠ ⊥ → π.ker ≤ K)
    {t : ℕ} (ht : 0 < t)
    (hQ : ∀ M : Subgroup (W Q), M.Normal →
      ∃ x : Fin t → W Q, Subgroup.normalClosure (Set.range x) = M) :
    ∀ N : Subgroup (W A), N.Normal →
      ∃ x : Fin t → W A, Subgroup.normalClosure (Set.range x) = N := by
  obtain ⟨a, ha, ha1⟩ := π.ker.bot_or_exists_ne_one.resolve_left hker
  have hw : (inl (a, 1) : W A) ∈ (mapLocal π).ker := by
    rw [mapLocal_ker]
    exact ⟨(a, 1), ⟨ha, π.ker.one_mem⟩, rfl⟩
  have hw1 : (inl (a, 1) : W A) ≠ 1 := by
    intro h
    exact ha1 (congrArg (fun g : W A ↦ g.left.1) h)
  apply normal_generating_tuples_of_kernel_normal_cover
    (mapLocal π) (mapLocal_surjective π hπ) (inl (a, 1)) hw hw1 ?_ ht hQ
  intro N hN hNb
  rw [mapLocal_ker]
  exact product_normal_cover hcenter π.ker hcover N hN hNb

theorem quotientSocle_of_local_normal_cover [Nontrivial A]
    (π : A →* Q) (hπ : Function.Surjective π)
    (hcenter : Subgroup.center A = ⊥) (hker : π.ker ≠ ⊥)
    (hcover : ∀ K : Subgroup A, K.Normal → K ≠ ⊥ → π.ker ≤ K)
    {t : ℕ} (ht : 0 < t)
    (hQ : ∀ M : Subgroup (W Q), M.Normal →
      ∃ x : Fin t → W Q, Subgroup.normalClosure (Set.range x) = M)
    (N : Subgroup (W A)) [N.Normal] :
    SocleNormalGeneratorBound (W A ⧸ N) t :=
  quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    (normal_generating_tuples_of_local_normal_cover π hπ hcenter hker hcover ht hQ) N

end C2Wreath
end SymmetricSubgroupAsymptotics

end
