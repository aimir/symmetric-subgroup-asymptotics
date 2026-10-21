import SymmetricSubgroupAsymptotics.BinaryHeisenbergFourteenThirteenZeroFlip
import SymmetricSubgroupAsymptotics.BinaryPairIntervalPreimageNormalF
import SymmetricSubgroupAsymptotics.BinaryPairSmallInvariantLowerLayer
import SymmetricSubgroupAsymptotics.BinaryPairLargeKernelCenter
import SymmetricSubgroupAsymptotics.BinaryPairOriginalKernelCoordinateCard
import SymmetricSubgroupAsymptotics.NormalOrderTwo

/-! The actual Heisenberg14 / thirteen-dimensional outer kernel has a
proper normal-F packet for every SAME original normal of order at most
two. Centrality, zero top image, and the required strict invariant interval
are derived internally. Neither inner nor outer extension is split. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance heisenbergFourteenThirteenNormalFPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16)) (E : BinaryPairFrame F.top.range (Fin 8))
    [MulAction.IsPretransitive U X]

theorem heisenberg14_thirteen_small_normalF_packet
    (hU : IsPGroup 2 U)
    (hH : E.top.range=Subgroup.closure (Set.range BinaryMenuCayley8T22.generators))
    (hJ : E.kernelSpace=BinaryRegularEightNaturalRegistry.chart40.space)
    (hSum : (E.pairSumModuleLayer (F.axisNaturalSubrepresentation F.top.ker)).toSubmodule=
      BinaryRegularEightNaturalRegistry.chart33.space)
    (hLow : (E.pairConstantModuleLayer (F.axisNaturalSubrepresentation F.top.ker)).toSubmodule=⊤)
    (N : Subgroup U) [N.Normal] (hcard : Nat.card N≤2) :
    ∃ D : Subgroup (U ⧸ N),D.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog D+
        MarkedC4.ActualNormalFMarkedPeel.centralLog D≤16 ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog D≤8 := by
  letI : MulAction.IsPretransitive F.top.range (Fin 16) := F.top_pretransitive
  letI : MulAction.IsPretransitive E.top.range (Fin 8) := E.top_pretransitive
  let V := F.axisNaturalSubrepresentation F.top.ker
  let S : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) E.top.range (Fin 8)) :=
    E.descendPairLayer (E.pairSumModuleLayer V)
  have hSdim : Module.finrank (ZMod 2) S.toSubmodule=5 := by
    change Module.finrank (ZMod 2) (E.pairSumModuleLayer V).toSubmodule=5
    rw [hSum]
    exact BinaryRegularEightNaturalRegistry.chart33.finrank
  have hK : F.kernelSpace=S.toSubmodule.comap E.pairSum := by
    have he := E.pairModule_eq_pairSum_preimage_of_constant_top V hLow
    change F.ambientAxis F.top.ker=(E.pairSumModuleLayer V).toSubmodule.comap E.pairSum at he
    rw [F.original_ambientAxis_kernel] at he
    exact he
  have hdK : Module.finrank (ZMod 2) F.kernelSpace=13 := by
    have hd := E.pairModuleLayers_finrank V
    change Module.finrank (ZMod 2) (F.ambientAxis F.top.ker)=
      Module.finrank (ZMod 2) S.toSubmodule+
        Module.finrank (ZMod 2) (E.pairConstantModuleLayer V).toSubmodule at hd
    have hl : Module.finrank (ZMod 2) (E.pairConstantModuleLayer V).toSubmodule=8 := by
      rw [hLow]
      simp
    rw [F.original_ambientAxis_kernel,hSdim,hl] at hd
    omega
  have hNZ : N≤Subgroup.center U := by
    have hp : 0<Nat.card N := Nat.card_pos
    rcases (show Nat.card N=1 ∨ Nat.card N=2 from by omega) with hone|htwo
    · rw [Subgroup.card_eq_one.mp hone]
      exact bot_le
    · exact NormalOrderTwo.le_center N htwo
  have hN : N≤F.top.ker := hNZ.trans
    (F.original_center_le_kernel_of_half_lt hU (0 : Fin 16) (by omega))
  have hsmall : Module.finrank (ZMod 2) (F.ambientAxis N)≤1 := by
    have ha : Nat.card (F.ambientAxis N)≤2 := by
      rw [F.axis_card_eq_kernel_intersection N,inf_eq_right.mpr hN]
      exact hcard
    have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.ambientAxis N)
    rw [Nat.card_zmod] at he
    rw [he] at ha
    by_contra hh
    have hb := Nat.pow_le_pow_right (by decide : 0<2)
      (show 2≤Module.finrank (ZMod 2) (F.ambientAxis N) from by omega)
    norm_num at hb
    omega
  let W := F.axisNaturalSubrepresentation N
  let A : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) E.top.range (Fin 8)) :=
    E.descendPairLayer (E.pairConstantModuleLayer W)
  have hWlower : W.toSubmodule≤E.pairSum.ker := by
    apply E.small_invariant_subrepresentation_le_pairSum_kernel (F.top_isPGroup hU) 0 W
    change Module.finrank (ZMod 2) (F.ambientAxis N)≤Module.finrank (ZMod 2) E.kernelSpace
    rw [hJ,BinaryRegularEightNaturalRegistry.chart40.finrank]
    omega
  have haxis : F.ambientAxis N=A.toSubmodule.map E.pairConstant := by
    apply le_antisymm
    · intro v hv
      obtain ⟨a,ha⟩ := E.pairConstant_pairSum_exact_linear.ge (hWlower hv)
      refine ⟨a,?_,ha⟩
      change E.pairConstant a=v at ha
      change E.pairConstant a∈W.toSubmodule
      rw [ha]
      exact hv
    · rintro _ ⟨a,ha,rfl⟩
      exact ha
  have hAdim : Module.finrank (ZMod 2) A.toSubmodule≤1 := by
    have hd := E.pairModuleLayers_finrank W
    change Module.finrank (ZMod 2) W.toSubmodule=
      Module.finrank (ZMod 2) (E.pairSumModuleLayer W).toSubmodule+
        Module.finrank (ZMod 2) A.toSubmodule at hd
    change Module.finrank (ZMod 2) W.toSubmodule≤1 at hsmall
    omega
  have honeS : (fun _ : Fin 8 => (1 : ZMod 2))∈S.toSubmodule := by
    apply pGroup_permutation_subrepresentation_contains_one (E.top_isPGroup (F.top_isPGroup hU)) 0 S
    intro he
    rw [he,Module.finrank_zero_of_subsingleton] at hSdim
    omega
  have hconstant (a : A.toSubmodule) (i : Fin 8) : a.val i=a.val 0 := by
    have ha : E.pairConstant a.val∈F.ambientAxis N := a.property
    obtain ⟨k,hk,hbits⟩ := (F.mem_ambientAxis N (E.pairConstant a.val)).mp ha
    have hc := F.central_kernel_bits_constant k (hNZ hk) (E.frame (i,0)) (E.frame (0,0))
    rw [hbits] at hc
    simpa only [E.pairConstant_frame] using hc
  have hAle : A.toSubmodule≤S.toSubmodule := by
    intro a ha
    have he : a=a 0 • (fun _ : Fin 8 => (1 : ZMod 2)) := by
      funext i
      simpa only [Pi.smul_apply,smul_eq_mul,mul_one] using hconstant ⟨a,ha⟩ i
    rw [he]
    exact S.toSubmodule.smul_mem (a 0) honeS
  have hAS : A.toSubmodule<S.toSubmodule := by
    apply lt_of_le_of_ne hAle
    intro he
    have hd : Module.finrank (ZMod 2) A.toSubmodule=
        Module.finrank (ZMod 2) S.toSubmodule :=
      congrArg (fun P : Submodule (ZMod 2) (Fin 8 → ZMod 2) =>
        Module.finrank (ZMod 2) P) he
    have hf := hAdim
    rw [hd,hSdim] at hf
    omega
  have hKchart : F.kernelSpace=BinaryRegularEightNaturalRegistry.chart33.space.comap E.pairSum := by
    change F.kernelSpace=(E.pairSumModuleLayer V).toSubmodule.comap E.pairSum at hK
    rw [hSum] at hK
    exact hK
  obtain ⟨z,hzbits,hzcentral,hzero⟩ :=
    BinaryHeisenbergFourteenThirteenZeroFlip.BinaryPairFrame.exists_actual_zero_constant_flip
      F E hH hJ hKchart
  obtain ⟨D,hD,hcost,hcenter⟩ := F.interval_preimage_normalF_packet (w := 8) E hU (0 : Fin 8)
    A S hK hAS (by omega) z hzbits hzcentral hzero N hN haxis
  exact ⟨D,hD,by norm_num at hcost ⊢;exact hcost,hcenter⟩
end SymmetricSubgroupAsymptotics.BinaryPairFrame
