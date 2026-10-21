import SymmetricSubgroupAsymptotics.BinaryRegular45TwelveZeroFlip
import SymmetricSubgroupAsymptotics.BinaryPairIntervalPreimageNormalF
import SymmetricSubgroupAsymptotics.BinaryPairFullConstantOriginalState
import SymmetricSubgroupAsymptotics.BinaryPairOriginalKernelCoordinateCard
import SymmetricSubgroupAsymptotics.BinaryPairModuleLayerTopTransport

/-! The retained regular45 / twelve-dimensional outer-kernel sector
has an actual proper normal-F packet at the original zero denominator.
Only the selected double-commutator lift is made pure; neither extension
is assumed split. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance regular45TwelveNormalFPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16)) (E : BinaryPairFrame F.top.range (Fin 8))
    [MulAction.IsPretransitive U X]

theorem regular45_twelve_zero_normalF_packet
    (hU : IsPGroup 2 U)
    (hH : E.top.range=Subgroup.closure (Set.range BinaryMenuCayley8T3.generators))
    (hJ : E.kernelSpace=BinaryRegularEightNaturalRegistry.chart45.space)
    (hSum : (E.pairSumModuleLayer (F.axisNaturalSubrepresentation F.top.ker)).toSubmodule=
      (BinaryRegularEightNaturalRegistry.charts 46).2.space)
    (hLow : (E.pairConstantModuleLayer (F.axisNaturalSubrepresentation F.top.ker)).toSubmodule=⊤) :
    ∃ D : Subgroup (U ⧸ (⊥ : Subgroup U)),D.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog D+
        MarkedC4.ActualNormalFMarkedPeel.centralLog D≤16 ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog D≤8 := by
  letI : MulAction.IsPretransitive F.top.range (Fin 16) := F.top_pretransitive
  let W := F.axisNaturalSubrepresentation F.top.ker
  let S : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) E.top.range (Fin 8)) :=
    E.descendPairLayer (E.pairSumModuleLayer W)
  have hK : F.kernelSpace=S.toSubmodule.comap E.pairSum := by
    have he := E.pairModule_eq_pairSum_preimage_of_constant_top W hLow
    change F.ambientAxis F.top.ker=(E.pairSumModuleLayer W).toSubmodule.comap E.pairSum at he
    rw [F.original_ambientAxis_kernel] at he
    exact he
  have hL : (E.pairConstantModuleLayer W).toSubmodule=
      (BinaryRegularEightNaturalRegistry.charts 1).2.space := by
    rw [hLow]
    symm
    apply Submodule.eq_top_of_finrank_eq
    rw [(BinaryRegularEightNaturalRegistry.charts 1).2.finrank]
    change 8=Module.finrank (ZMod 2) (Fin 8 → ZMod 2)
    simp
  have hState := E.regular_fullconstant_layers_original_state W hSum hL
  obtain ⟨z,hzbits,hzcentral,hzero⟩ :=
    BinaryRegular45TwelveZeroFlip.BinaryPairFrame.exists_actual_zero_constant_flip F E hH hJ hState
  have hSdim : Module.finrank (ZMod 2) S.toSubmodule=4 := by
    change Module.finrank (ZMod 2) (E.pairSumModuleLayer W).toSubmodule=4
    rw [hSum]
    exact (BinaryRegularEightNaturalRegistry.charts 46).2.finrank
  have hAS : (⊥ : Submodule (ZMod 2) (Fin 8 → ZMod 2))<S.toSubmodule := by
    apply bot_lt_iff_ne_bot.mpr
    intro he
    rw [he,Module.finrank_zero_of_subsingleton] at hSdim
    omega
  have haxis : F.ambientAxis (⊥ : Subgroup U)=
      (⊥ : Submodule (ZMod 2) (Fin 8 → ZMod 2)).map E.pairConstant := by
    rw [Submodule.map_bot]
    apply le_antisymm ?_ bot_le
    intro v hv
    obtain ⟨k,hk,hv⟩ := (F.mem_ambientAxis (⊥ : Subgroup U) v).mp hv
    have he : k=1 := Subtype.ext (Subgroup.mem_bot.mp hk)
    change v=0
    rw [←hv,he]
    exact congrArg Multiplicative.toAdd F.bitsHom.map_one
  have hp := F.interval_preimage_normalF_packet (w := 8) E hU (0 : Fin 8)
    (⊥ : Subrepresentation (permutationFunctionRepresentation (ZMod 2) E.top.range (Fin 8)))
    S hK hAS (by
      change 2*Module.finrank (ZMod 2) (⊥ : Submodule (ZMod 2) (Fin 8 → ZMod 2))<8
      norm_num) z hzbits hzcentral hzero (⊥ : Subgroup U) bot_le haxis
  rcases hp with ⟨D,hD,hcost,hcenter⟩
  have hnum : (8 : ℝ)+(8 : ℝ)≤16 := by norm_num
  exact ⟨D,hD,hcost.trans hnum,hcenter⟩

end SymmetricSubgroupAsymptotics.BinaryPairFrame
