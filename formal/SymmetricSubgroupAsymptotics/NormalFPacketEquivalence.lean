import SymmetricSubgroupAsymptotics.NormalFEquivalenceTransport

/-! Both actual normal-F invariants are transported through one quotient
equivalence. No replacement of the selected proper normal is made. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
open MarkedC4.ActualNormalFMarkedPeel NormalFEquivalenceTransport

theorem normalF_packet_of_equiv
    {G H : Type} [Group G] [Group H] [Finite G] [Finite H]
    (e : G ≃* H) (c b z : ℝ)
    (h : ∃ F : Subgroup G, F.Normal ∧
      commutatorLog F + c * centralLog F ≤ b ∧ centralLog F ≤ z) :
    ∃ F : Subgroup H, F.Normal ∧
      commutatorLog F + c * centralLog F ≤ b ∧ centralLog F ≤ z := by
  obtain ⟨F,hF,hcost,hcenter⟩ := h
  letI := hF
  let W := F.map e.toMonoidHom
  letI : W.Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
  refine ⟨W,inferInstance,?_,?_⟩
  · simpa only [W,commutatorLog_map,centralLog_map] using hcost
  · simpa only [W,centralLog_map] using hcenter

end SymmetricSubgroupAsymptotics
