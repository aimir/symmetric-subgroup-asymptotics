import SymmetricSubgroupAsymptotics.NormalizerSharedOrdinaryGenerators
import SymmetricSubgroupAsymptotics.CoprimeNilpotentProductGenerators
import SymmetricSubgroupAsymptotics.ZmudFaithfulCharacterInput

/-! One nontrivial internally normal factor of a minimal normal subgroup
suffices for ordinary generation, together with the original ambient
quotient. The factor need not be normal in the ambient group.
-/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.MinimalNormalInternalFactorOrdinaryGenerators

variable {G : Type} [Group G] (E : Subgroup G) (A : Subgroup E) [A.Normal]

theorem conjugate_mem (n : G) (hn : n ∈ E) (a : G)
    (ha : a ∈ A.map E.subtype) : n*a*n⁻¹ ∈ A.map E.subtype := by
  obtain ⟨a,ha,rfl⟩ := ha
  refine ⟨(⟨n,hn⟩ : E)*a*(⟨n,hn⟩ : E)⁻¹,?_,rfl⟩
  exact (inferInstance : A.Normal).conj_mem a ha ⟨n,hn⟩

theorem le_normalizer : E ≤ Subgroup.normalizer (A.map E.subtype) := by
  intro n hn
  apply Subgroup.mem_normalizer_iff.mpr
  intro a
  constructor
  · exact conjugate_mem E A n hn a
  · intro ha
    have h := conjugate_mem E A n⁻¹ (E.inv_mem hn) _ ha
    have heq : n⁻¹*(n*a*n⁻¹)*(n⁻¹)⁻¹=a := by group
    rwa [heq] at h

omit [A.Normal] in
theorem normalClosure_eq (hE : IsMinimalNormalSubgroup E) (hA : A ≠ ⊥) :
    Subgroup.normalClosure (A.map E.subtype : Set G) = E := by
  letI : E.Normal := hE.1
  have hle : A.map E.subtype ≤ E := by
    rintro x ⟨a,ha,rfl⟩
    exact a.property
  have hn : Subgroup.normalClosure (A.map E.subtype : Set G) ≠ ⊥ := by
    intro hz
    apply hA
    apply bot_unique
    intro a ha
    have hc := Subgroup.subset_normalClosure
      (show (a:G) ∈ A.map E.subtype from ⟨a,ha,rfl⟩)
    rw [hz] at hc
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hc))
  exact hE.2.2 _ inferInstance hn (Subgroup.normalClosure_le_normal hle)

theorem genRank_le [Finite G] [E.Normal] (hE : IsMinimalNormalSubgroup E) (hA : A ≠ ⊥) :
    MarkedC4.genRank G ≤ MarkedC4.genRank A + MarkedC4.genRank (G⧸E) := by
  letI : E.Normal := hE.1
  have h := NormalizerSharedOrdinaryGenerators.genRank_le E (A.map E.subtype)
    (le_normalizer E A) (normalClosure_eq E A hE hA)
  rw [← CoprimeNilpotentProductGenerators.genRank_mulEquiv
    (A.equivMapOfInjective E.subtype Subtype.val_injective)] at h
  exact h

end SymmetricSubgroupAsymptotics.MinimalNormalInternalFactorOrdinaryGenerators
