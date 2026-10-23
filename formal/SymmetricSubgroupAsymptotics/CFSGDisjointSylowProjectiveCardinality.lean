import SymmetricSubgroupAsymptotics.CFSGCentralKernelPSubgroups

/-! Two disjoint Sylow p-subgroups survive the actual central quotient,
including their mutual intersection. The central p-element argument is
explicit; separate injectivity alone is not used to separate images. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGDisjointSylowProjectiveCardinality
variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]

theorem central_quotient_injective (P Q : Sylow p G)
    (hPQ : (P : Subgroup G) ⊓ (Q : Subgroup G) = ⊥) :
    Function.Injective ((QuotientGroup.mk' (Subgroup.center G)).comp
      (P : Subgroup G).subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro z hz
  have hc : z.val ∈ Subgroup.center G := (QuotientGroup.eq_one_iff z.val).mp hz
  obtain ⟨a,ha⟩ := P.isPGroup' z
  have hzQ : z.val ∈ Q := CFSGCentralKernelPElements.central_p_element_mem Q z.val hc
    ⟨a,congrArg Subtype.val ha⟩
  have hm : z.val ∈ (P : Subgroup G) ⊓ (Q : Subgroup G) := ⟨z.property,hzQ⟩
  rw [hPQ,Subgroup.mem_bot] at hm
  exact Subgroup.mem_bot.mpr (Subtype.ext hm)

theorem card_mul_le_central_quotient [Finite (G ⧸ Subgroup.center G)]
    (P Q : Sylow p G) (hPQ : (P : Subgroup G) ⊓ (Q : Subgroup G) = ⊥) :
    Nat.card P * Nat.card Q ≤ Nat.card (G ⧸ Subgroup.center G) :=
  CFSGCentralKernelPElements.disjoint_p_subgroups_card_mul_le
    (QuotientGroup.mk' (Subgroup.center G)) P (central_quotient_injective P Q hPQ)
    (by rw [QuotientGroup.ker_mk']) (P : Subgroup G) (Q : Subgroup G)
    P.isPGroup' Q.isPGroup' hPQ

end SymmetricSubgroupAsymptotics.CFSGDisjointSylowProjectiveCardinality
