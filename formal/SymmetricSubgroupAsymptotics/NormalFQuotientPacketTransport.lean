import SymmetricSubgroupAsymptotics.NormalFEquivalenceTransport

/-! Transport a quotient-wide normal-F packet through one actual group
isomorphism. The denominator, chosen normal subgroup, and both logarithmic
invariants follow that same quotient equivalence. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NormalFEquivalenceTransport
open MarkedC4.RDTNormalFInterface MarkedC4.ActualNormalFMarkedPeel
variable {G H : Type} [Group G] [Finite G] [Group H] [Finite H]

theorem quotient_packet_of_equiv (e : G ≃* H) (a b c : ℝ)
    (hpacket : ∀ (M : Subgroup H) [M.Normal],
      (¬∀ x y : H ⧸ M,x*y=y*x) →
      ∃ F : Subgroup (H ⧸ M),F.Normal ∧
        commutatorLog F+a*centralLog F≤b ∧ centralLog F≤c)
    (N : Subgroup G) [N.Normal]
    (hnonab : ¬∀ x y : G ⧸ N,x*y=y*x) :
    ∃ F : Subgroup (G ⧸ N),F.Normal ∧
      commutatorLog F+a*centralLog F≤b ∧ centralLog F≤c := by
  let M := N.map e.toMonoidHom
  letI : M.Normal := Subgroup.Normal.map inferInstance _ e.surjective
  let q : G ⧸ N ≃* H ⧸ M := QuotientGroup.congr N M e rfl
  have hH : ¬∀ x y : H ⧸ M,x*y=y*x := by
    intro hcomm
    apply hnonab
    intro x y
    apply q.injective
    simpa only [map_mul] using hcomm (q x) (q y)
  obtain ⟨F,hF,hcost,hcenter⟩ := hpacket M hH
  letI := hF
  refine ⟨F.map q.symm.toMonoidHom,
    Subgroup.Normal.map hF _ q.symm.surjective,?_,?_⟩
  · simpa only [commutatorLog_map,centralLog_map] using hcost
  · simpa only [centralLog_map] using hcenter

end SymmetricSubgroupAsymptotics.NormalFEquivalenceTransport
