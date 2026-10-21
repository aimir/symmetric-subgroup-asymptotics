import SymmetricSubgroupAsymptotics.BinaryHeisenbergFullSplitTransport
import SymmetricSubgroupAsymptotics.RDTNormalFHeisenbergFullProperAxes
import SymmetricSubgroupAsymptotics.RDTNormalFHeisenbergUnitOneAxisEnvelope
import SymmetricSubgroupAsymptotics.RDTNormalFHeisenbergLowHeadUnit
import SymmetricSubgroupAsymptotics.BinaryHeisenbergFullJointAxisAlternatives
import SymmetricSubgroupAsymptotics.NormalFPacketEquivalence

/-! Every original normal quotient of a full-kernel rank-five Heisenberg
pair action has the unit packet. Two axes use the actual proper normal F;
the other thirteen use the joint whole-quotient envelope. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
open BinaryHeisenbergEightNaturalHeads
open BinaryRegularEightNaturalRegistry (chart0 chart1 chart23 chart45)
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8))

theorem heisenberg_full_kernel_unit_normalF_packet
    (hU : IsPGroup 2 U) (hrank : 5 ≤ MarkedC4.genRank U)
    (hH : F.top.range = H) (hK : F.kernelSpace = chart1.space)
    (hR : F.ambientAxis (primeRelativeRadical 2 F.top.ker) = chart45.space)
    (N : Subgroup U) [N.Normal]
    (hnonab : ¬ ∀ a b : U ⧸ N, a * b = b * a) :
    ∃ W : Subgroup (U ⧸ N), W.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog W +
        MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 8 ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 4 := by
  let eH : H ≃* F.top.range := (MulEquiv.subgroupCongr hH).symm
  let A := F.sharedOriginalAxis rho eH (fun _ _ => rfl) N
  have hspecial (haxis : F.ambientAxis N = chart0.space ∨
      F.ambientAxis N = chart23.space) :
      ∃ W : Subgroup (U ⧸ N), W.Normal ∧
        MarkedC4.ActualNormalFMarkedPeel.commutatorLog W +
          MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 8 ∧
        MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 4 := by
    have hfull : F.kernelSpace = ⊤ := hK.trans BinaryHeisenbergFullProperAxisZero.full_space
    let e := F.heisenbergFullSplitEquiv hH hfull
    let M := N.comap e.toMonoidHom
    letI : M.Normal := inferInstance
    have hmap : M.map e.toMonoidHom = N := by
      ext u
      constructor
      · rintro ⟨g,hg,rfl⟩
        exact hg
      · intro hu
        exact ⟨e.symm u,by
          change e (e.symm u) ∈ N
          simpa only [e.apply_symm_apply] using hu, e.apply_symm_apply u⟩
    let eqQ := QuotientGroup.congr M N e hmap
    have hp : ∃ W : Subgroup (BinaryHeisenbergFullSplitModel.Model ⧸ M), W.Normal ∧
        MarkedC4.ActualNormalFMarkedPeel.commutatorLog W +
          (1 : ℝ) * MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 8 ∧
        MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 4 := by
      rcases haxis with h0|hc
      · have hm (v : V) : (SemidirectProduct.inl (Multiplicative.ofAdd v) :
            BinaryHeisenbergFullSplitModel.Model) ∈ M ↔ v ∈ chart0.space := by
          change e _ ∈ N ↔ _
          rw [F.heisenbergFullSplitEquiv_inl_mem_iff,h0]
        simpa only [one_mul] using BinaryHeisenbergFullSplitModel.zero_axis_unit_packet M hm
      · have hm (v : V) : (SemidirectProduct.inl (Multiplicative.ofAdd v) :
            BinaryHeisenbergFullSplitModel.Model) ∈ M ↔ v ∈ chart23.space := by
          change e _ ∈ N ↔ _
          rw [F.heisenbergFullSplitEquiv_inl_mem_iff,hc]
        simpa only [one_mul] using BinaryHeisenbergFullSplitModel.constant_axis_unit_packet M hm
    simpa only [one_mul] using normalF_packet_of_equiv eqQ 1 8 4 hp
  rcases BinaryHeisenbergFullJointAxisAlternatives.all_axes A with h0|hc|he
  · exact hspecial (Or.inl h0)
  · exact hspecial (Or.inr hc)
  · obtain ⟨hu,hd⟩ := F.heisenberg_rank_five_derived_le_kernel_card hU hrank hH
    rw [hK,chart1.card] at hu hd
    exact F.heisenberg_unit_normalF_of_one_doubled_axis_envelope hU hH
      chart1.space chart45.space hK.symm
      (chart45.le_of_basis_mem _ (by decide +kernel))
      (F.radical_coordinate_le_derived chart45.space hR) 128
      (by simpa using hd) (by rw [chart45.card]; decide)
      (by rw [chart45.card]; norm_num at hu ⊢; omega) N he hnonab

end SymmetricSubgroupAsymptotics.BinaryPairFrame
