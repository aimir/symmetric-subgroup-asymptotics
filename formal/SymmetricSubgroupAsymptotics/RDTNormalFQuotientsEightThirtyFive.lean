import SymmetricSubgroupAsymptotics.RDTNormalFSelectedEightThirtyFive
import SymmetricSubgroupAsymptotics.NormalFEquivalenceTransport
import SymmetricSubgroupAsymptotics.GeneratedCarrierNormal8T35.QuotientProfiles

/-! Every actual nonabelian quotient of the original Sylow128 carrier
has its retained excess-one normal-F packet. No quotient table or
classification premise is imported. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.RDTNormalFQuotientsEightThirtyFive
open BinaryCarrierNormal8T35
open MarkedC4.RDTNormalFInterface MarkedC4.ActualNormalFMarkedPeel
local instance : Group Source := BinaryMenuCayley8T35.group

private theorem top_numeric (i : Fin 28) (hi : i≠0) (hd : derivedLog i≠0) :
    derivedLog i+centerLog i≤4 ∧ centerLog i≤2 := by
  revert i
  decide +kernel

theorem nonzero_state_top_bounds (i : Fin 28) (hi : i≠0)
    (hnonab : ¬∀ x y : Source ⧸ (states i).kernel,x*y=y*x) :
    commutatorLog (⊤ : Subgroup (Source ⧸ (states i).kernel))+
      centralLog (⊤ : Subgroup (Source ⧸ (states i).kernel))≤4 ∧
      centralLog (⊤ : Subgroup (Source ⧸ (states i).kernel))≤2 := by
  have hd : derivedLog i≠0 := by
    intro hz
    have hb : commutator (Source ⧸ (states i).kernel)=⊥ :=
      Subgroup.card_eq_one.mp (by rw [source_quotient_derived_card,hz]; rfl)
    apply hnonab
    intro x y
    apply commutatorElement_eq_one_iff_mul_comm.mp
    have hm := Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    change ⁅x,y⁆∈commutator (Source ⧸ (states i).kernel) at hm
    simpa only [hb,Subgroup.mem_bot] using hm
  have hc : commutatorLog (⊤ : Subgroup (Source ⧸ (states i).kernel))=(derivedLog i : ℝ) := by
    change Real.logb 2 (Nat.card (commutator (Source ⧸ (states i).kernel)) : ℝ)=_
    rw [source_quotient_derived_card,Nat.cast_pow]
    norm_num [Real.logb_pow]
  have hz : centralLog (⊤ : Subgroup (Source ⧸ (states i).kernel))=(centerLog i : ℝ) := by
    simp only [centralLog,targetCentralizer,Subgroup.coe_top,Subgroup.centralizer_univ]
    rw [source_quotient_center_card,Nat.cast_pow]
    norm_num [Real.logb_pow]
  rw [hc,hz]
  exact ⟨by exact_mod_cast (top_numeric i hi hd).1,by exact_mod_cast (top_numeric i hi hd).2⟩

theorem quotient_packet (N : Subgroup Source) [N.Normal]
    (hnonab : ¬∀ x y : Source ⧸ N,x*y=y*x) :
    ∃ F : Subgroup (Source ⧸ N),F.Normal ∧
      commutatorLog F+centralLog F≤4 ∧ centralLog F≤2 := by
  by_cases hN : N=⊥
  · subst N
    let e : Source ≃* (Source ⧸ (⊥ : Subgroup Source)) := QuotientGroup.quotientBot.symm
    let F := N12.kernel.map e.toMonoidHom
    refine ⟨F,Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective,?_,?_⟩
    · simpa only [F,NormalFEquivalenceTransport.commutatorLog_map,
        NormalFEquivalenceTransport.centralLog_map] using
        RDTNormalFSelectedEightThirtyFive.retained_log_bounds.1
    · simpa only [F,NormalFEquivalenceTransport.centralLog_map] using
        RDTNormalFSelectedEightThirtyFive.retained_log_bounds.2
  · obtain ⟨i,hi⟩ := complete N
    have hi0 : i≠0 := by
      intro hz
      apply hN
      rw [←hi,hz]
      exact registry.bottom_kernel
    subst N
    exact ⟨⊤,inferInstance,(nonzero_state_top_bounds i hi0 hnonab).1,
      (nonzero_state_top_bounds i hi0 hnonab).2⟩

end SymmetricSubgroupAsymptotics.RDTNormalFQuotientsEightThirtyFive
