import SymmetricSubgroupAsymptotics.Selected1542SecondCenter
import SymmetricSubgroupAsymptotics.Selected1542SecondPlane
import SymmetricSubgroupAsymptotics.CubicKernelCentralMonolith

/-! The second actual monolithic layer is N8/Z2 in the original quotient.
The center exclusion receipts and cubic orbit replace a normal census. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1542QuotientStructure

theorem secondAxis_le_binaryKernel : secondAxis≤firstQuotientBinaryKernel := by
  rintro _ ⟨g,hg,rfl⟩
  have ht : originalToTarget g=1 := by
    apply MonoidHom.mem_ker.mp
    rw [originalToTarget_ker]
    exact normal_le_preimage hg
  change firstQuotientCubic (QuotientGroup.mk' originalFirstAxis g)=1
  rw [firstQuotientCubic_apply]
  change ActualRepeatedAlternatingCentralCoordinates.top targetAlternating 0 (originalToTarget g)=1
  rw [ht,map_one]

theorem secondPlane_injective : Function.Injective secondPlane := by
  intro i j hij
  have h : QuotientGroup.mk' originalFirstAxis
      (normalOriginal (secondPlaneIndex i)*(normalOriginal (secondPlaneIndex j))⁻¹)=1 := by
    rw [map_mul,map_inv]
    change secondPlane i*(secondPlane j)⁻¹=1
    rw [hij,mul_inv_cancel]
  apply secondPlane_distinct i j
  rcases (mkFirst_eq_one_iff _).mp h with h | h
  · have he := mul_inv_eq_one.mp h
    exact Or.inl (fun p => congrArg (fun g : Original => g.val p) he)
  · have he := mul_inv_eq_iff_eq_mul.mp h
    have hc : originalCentralInvolution*normalOriginal (secondPlaneIndex j)=
        normalOriginal (secondPlaneIndex j)*originalCentralInvolution :=
      (Subgroup.mem_center_iff.mp originalCentralInvolution_central _).symm
    rw [hc] at he
    exact Or.inr (fun p => congrArg (fun g : Original => g.val p) he)

theorem secondAxis_noncentral : ∃ a d : FirstQuotient, d∈secondAxis ∧ a*d≠d*a := by
  refine ⟨firstQuotientCubicLift,secondPlane 0,secondPlane_mem 0,?_⟩
  intro h
  have he : firstQuotientCubicLift*secondPlane 0*firstQuotientCubicLift⁻¹=secondPlane 0 := by
    rw [h,mul_assoc,mul_inv_cancel,mul_one]
  have hv : secondPlane 1=secondPlane 0 := (secondPlane_cycle_actual 0).symm.trans he
  have hidx : (1 : Fin 3)=0 := secondPlane_injective hv
  exact (by decide : (1 : Fin 3)≠0) hidx

/-- Every nontrivial normal in Original/Z2 contains the same actual N8/Z2. -/
theorem original_second_monolith (N : Subgroup FirstQuotient)
    (hN : N.Normal) (hne : N≠⊥) : secondAxis≤N :=
  normal_cover_of_cubic_kernel_central_monolith firstQuotientCubic
    firstQuotientBinaryKernel_isPGroup secondAxis secondAxis_minimalNormal
    secondAxis_le_binaryKernel firstQuotient_kernel_center_le_secondAxis secondAxis_noncentral N hN hne

end SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
