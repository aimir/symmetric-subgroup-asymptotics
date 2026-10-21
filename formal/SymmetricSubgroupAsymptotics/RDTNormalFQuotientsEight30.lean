import SymmetricSubgroupAsymptotics.NormalFEquivalenceTransport
import SymmetricSubgroupAsymptotics.RDTNormalFProfiles8T30Quotients

/-! The same literal centre/derived profiles control every actual nonabelian
quotient of the original64-element source8T30. No normal subgroup is
rediscovered and no quotient is replaced by an abstract comparison group. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.RDTNormalFQuotientsEight30
open BinaryNormal8T30
open MarkedC4.RDTNormalFInterface MarkedC4.ActualNormalFMarkedPeel
local instance : Group Source := BinaryMenuCayley8T30.group

private theorem numeric (i : Fin 13) (hd : derivedLog i≠0) :
    derivedLog i+centerLog i≤4 ∧ centerLog i≤2 := by
  revert i
  decide +kernel

theorem state_top_bounds (i : Fin 13)
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
  exact ⟨by exact_mod_cast (numeric i hd).1,by exact_mod_cast (numeric i hd).2⟩

theorem quotient_packet (N : Subgroup Source) [N.Normal]
    (hnonab : ¬∀ x y : Source ⧸ N,x*y=y*x) :
    ∃ F : Subgroup (Source ⧸ N),F.Normal ∧
      commutatorLog F+centralLog F≤4 ∧ centralLog F≤2 := by
  obtain ⟨i,rfl⟩ := complete N
  exact ⟨⊤,inferInstance,(state_top_bounds i hnonab).1,(state_top_bounds i hnonab).2⟩

end SymmetricSubgroupAsymptotics.RDTNormalFQuotientsEight30
