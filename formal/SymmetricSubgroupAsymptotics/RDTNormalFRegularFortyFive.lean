import SymmetricSubgroupAsymptotics.BinaryRegularFortyFiveAllDerivedAxes
import SymmetricSubgroupAsymptotics.BinaryRegularFortyFiveDerivedAxis
import SymmetricSubgroupAsymptotics.BinaryPairSharedQuotientCenterBound
import SymmetricSubgroupAsymptotics.DerivedIntersectionQuotientCenter
import SymmetricSubgroupAsymptotics.SmallDerivedNormalFBounds

/-! Every original rank-six regular-K45 extension, with arbitrary original
lift offsets, has the normal-F packet for ALL nonabelian normal quotients.
The finite calculation uses only the complete invariant-axis registry,
restricted to proper subspaces of the original derived axis. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8)) [MulAction.IsPretransitive U X]

theorem regular45_quotient_center_le_eight
    (hU : IsPGroup 2 U) (hrank : 6 ≤ MarkedC4.genRank U)
    (hH : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T3.generators))
    (hK : F.kernelSpace = BinaryRegularEightSquareCarry.K45)
    (hR : F.ambientAxis (primeRelativeRadical 2 F.top.ker) = BinaryRegularEightSquareCarry.R45)
    (N : Subgroup U) [N.Normal]
    (hnonab : ¬ ∀ a b : U ⧸ N, a * b = b * a) :
    Nat.card (Subgroup.center (U ⧸ N)) ≤ 8 := by
  let L := N ⊓ commutator U
  let e : BinaryRegularEightNaturalRegistry.H ≃* F.top.range :=
    (MulEquiv.subgroupCongr hH).symm
  have he : ∀ g v, BinaryRegularEightNaturalRegistry.rho g v =
      F.coordinateTopAction (e g) v := fun _ _ => rfl
  let A := F.sharedOriginalAxis BinaryRegularEightNaturalRegistry.rho e he L
  have hd := F.regular45_derived_axis hU hrank hH hK hR
  have hDker : commutator U ≤ F.top.ker := by
    rw [hd]
    exact F.coordinateSubgroup_le_kernel _
  have hLker : L ≤ F.top.ker := inf_le_right.trans hDker
  have hcoord : F.coordinateSubgroup A.toSubmodule = L := by
    change F.coordinateSubgroup (F.ambientAxis L) = L
    rw [F.coordinateSubgroup_ambientAxis, inf_eq_right.mpr hLker]
  have hAle : A.toSubmodule ≤ BinaryRegularEightSquareCarry.R45 := by
    intro v hv
    obtain ⟨k, hk, rfl⟩ := (F.mem_ambientAxis L v).mp hv
    have hm : (k : U) ∈ F.coordinateSubgroup BinaryRegularEightSquareCarry.R45 :=
      hd ▸ hk.2
    exact (F.kernel_mem_coordinateSubgroup _ k).mp hm
  have hproper : A.toSubmodule ≠ BinaryRegularEightSquareCarry.R45 := by
    intro hEq
    have hle : commutator U ≤ N := by
      rw [hd, ← hEq, hcoord]
      exact inf_le_left
    letI : IsMulCommutative (U ⧸ N) :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hle
    exact hnonab (fun a b => mul_comm' a b)
  have hdim : Module.finrank (ZMod 2) A.toSubmodule ≤ 3 := by
    have hlt := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hAle hproper)
    have hdR : Module.finrank (ZMod 2) BinaryRegularEightSquareCarry.R45 = 4 := by
      rw [← BinaryRegularEightNaturalRegistry.radical45_space]
      exact (BinaryRegularEightNaturalRegistry.radicalCharts 45).2.finrank
    rw [hdR] at hlt
    omega
  have hchart : BinaryRegularEightNaturalRegistry.chart45.space = F.kernelSpace := by
    change (BinaryRegularEightNaturalRegistry.states 45).toSubmodule = F.kernelSpace
    exact BinaryRegularEightNaturalRegistry.kernel45_space.trans hK.symm
  have hRK : BinaryRegularEightSquareCarry.R45 ≤ F.kernelSpace := by
    rw [← hR]
    exact F.ambientAxis_le_kernelSpace _
  have hc := F.shared_quotient_center_card_le
    BinaryRegularEightNaturalRegistry.rho e he
    BinaryRegularEightNaturalRegistry.chart45.space hchart
    A (hAle.trans (hRK.trans_eq hchart.symm)) 8
    (BinaryRegularFortyFiveAllDerivedAxes.coordinate_capacity A hAle hdim)
  let eq : (U ⧸ F.coordinateSubgroup
      (F.sharedSubrepresentation BinaryRegularEightNaturalRegistry.rho e he A).toSubmodule) ≃*
      (U ⧸ L) := QuotientGroup.quotientMulEquivOfEq hcoord
  have hcard := Nat.card_congr (RDTDegreeEightExceptionalTransport.centerEquiv eq).toEquiv
  exact (quotient_center_card_le_derived_intersection N).trans (hcard.symm.trans_le hc)

theorem regular45_five_quarters_normalF_packet
    (hU : IsPGroup 2 U) (hrank : 6 ≤ MarkedC4.genRank U)
    (hH : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T3.generators))
    (hK : F.kernelSpace = BinaryRegularEightSquareCarry.K45)
    (hR : F.ambientAxis (primeRelativeRadical 2 F.top.ker) = BinaryRegularEightSquareCarry.R45)
    (N : Subgroup U) [N.Normal]
    (hnonab : ¬ ∀ a b : U ⧸ N, a * b = b * a) :
    ∃ V : Subgroup (U ⧸ N), V.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog V +
        (5 / 4 : ℝ) * MarkedC4.ActualNormalFMarkedPeel.centralLog V ≤ 8 ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog V ≤ 4 := by
  have hD := F.regular45_derived_axis hU hrank hH hK hR
  have hRle : BinaryRegularEightSquareCarry.R45 ≤ F.kernelSpace := by
    rw [← hR]
    exact F.ambientAxis_le_kernelSpace _
  have hd : Nat.card (commutator (U ⧸ N)) ≤ 16 := by
    have hcard : Nat.card (commutator U) = 16 := by
      rw [hD, F.coordinateSubgroup_card _ hRle,
        ← BinaryRegularEightNaturalRegistry.radical45_space]
      exact (BinaryRegularEightNaturalRegistry.radicalCharts 45).2.card
    exact (SmallDerivedNormalFBounds.quotient_derived_card_le N).trans_eq hcard
  have hz := F.regular45_quotient_center_le_eight hU hrank hH hK hR N hnonab
  have hlog (n k : ℕ) (hn : 0 < n) (hk : n ≤ 2 ^ k) :
      Real.logb 2 (n : ℝ) ≤ k := by
    apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2)
      (by exact_mod_cast hn)).mpr
    simpa only [Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat] using
      (show (n : ℝ) ≤ (2 ^ k : ℕ) by exact_mod_cast hk)
  have hdlog : MarkedC4.ActualNormalFMarkedPeel.commutatorLog (⊤ : Subgroup (U ⧸ N)) ≤ 4 := by
    simpa using hlog _ 4 Nat.card_pos hd
  have hzlog : MarkedC4.ActualNormalFMarkedPeel.centralLog (⊤ : Subgroup (U ⧸ N)) ≤ 3 := by
    simpa only [MarkedC4.ActualNormalFMarkedPeel.centralLog,
      MarkedC4.RDTNormalFInterface.targetCentralizer, Subgroup.coe_top,
      Subgroup.centralizer_univ, Nat.cast_ofNat] using hlog _ 3 Nat.card_pos hz
  exact ⟨⊤, inferInstance, by linarith, by linarith⟩

end SymmetricSubgroupAsymptotics.BinaryPairFrame
