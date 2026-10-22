import SymmetricSubgroupAsymptotics.CFSGCentralKernelPSubgroups

/-! Disjoint actual Sylow subgroups survive the central quotient.
A central p-element belongs to both Sylows, hence is trivial. This
counts opposite unipotents without assuming projective faithfulness. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGDisjointSylowProjectiveOrder
open CFSGCentralKernelPElements
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem quotient_center_sylow_injective (P Q : Sylow p G)
    (hPQ : (P : Subgroup G) ⊓ (Q : Subgroup G) = ⊥) :
    Function.Injective ((QuotientGroup.mk' (Subgroup.center G)).comp
      (P : Subgroup G).subtype) := by
  apply (((QuotientGroup.mk' (Subgroup.center G)).comp
    (P : Subgroup G).subtype).ker_eq_bot_iff).mp
  apply bot_unique
  intro x hx
  change x = 1
  apply Subtype.ext
  have hz : x.val ∈ Subgroup.center G :=
    (QuotientGroup.eq_one_iff x.val).mp hx
  obtain ⟨k, hk⟩ := P.isPGroup' x
  have hxQ : x.val ∈ Q := central_p_element_mem Q x.val hz
    ⟨k, congrArg Subtype.val hk⟩
  have hh : x.val ∈ (P : Subgroup G) ⊓ (Q : Subgroup G) := ⟨x.property, hxQ⟩
  simpa only [hPQ, Subgroup.mem_bot] using hh

theorem quotient_center_card_lower (P Q : Sylow p G)
    (hPQ : (P : Subgroup G) ⊓ (Q : Subgroup G) = ⊥) :
    Nat.card P ^ 2 ≤ Nat.card (G ⧸ Subgroup.center G) := by
  let f := QuotientGroup.mk' (Subgroup.center G)
  have hker : f.ker ≤ Subgroup.center G := by
    intro z hz
    exact (QuotientGroup.eq_one_iff z).mp hz
  have hh := disjoint_p_subgroups_card_mul_le f P
    (quotient_center_sylow_injective P Q hPQ) hker
    (P : Subgroup G) (Q : Subgroup G) P.isPGroup' Q.isPGroup' hPQ
  have hc : Nat.card Q = Nat.card P := Nat.card_congr (Q.equiv P).toEquiv
  simpa only [hc, pow_two] using hh

end SymmetricSubgroupAsymptotics.CFSGDisjointSylowProjectiveOrder
