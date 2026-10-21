import SymmetricSubgroupAsymptotics.BinaryElementary32DerivedDenominators
import SymmetricSubgroupAsymptotics.BinaryElementary32FiniteCapacity
import SymmetricSubgroupAsymptotics.DerivedThirtyTwoNormalFBound

/-! The actual elementary-top rank-ten source is reduced to finite scalar
capacities on the same original derived chart. The exposed capacities are
intermediate finite obligations, not replacement literature assumptions. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
open MarkedC4.ActualNormalFMarkedPeel MarkedC4.RDTNormalFInterface
local instance elementaryNormalFInstallerFactPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16))

include F

theorem elementary_rank_ten_packet_of_hyperplane_capacities
    [MulAction.IsPretransitive U X]
    (hU : IsPGroup 2 U) (hhigh : 10≤MarkedC4.genRank U)
    (hpow : ∀ t : F.top.range,t^2=1)
    (hfinite : ∀ c : Fin 32,c≠0 →
      BinaryElementary32FiniteCapacity.capacity
        (binaryFiveHyperplane BinaryElementaryPhiZeroIntrinsicRadical.radical c)≤512)
    (N : Subgroup U) [N.Normal]
    (hnonab : ¬ ∀ a b : U ⧸ N,a*b=b*a) :
    ∃ V : Subgroup (U ⧸ N), V.Normal ∧
      commutatorLog V+(5/4 : ℝ)*centralLog V≤16 ∧ centralLog V≤8 := by
  obtain ⟨E,hzero,hH,hK,hS,hgen,hker,htop⟩ :=
    F.rank_ten_elementary_original_kernel_model hU hhigh hpow
  obtain ⟨hd,hcoord,hderived⟩ := F.elementary_rank_ten_derived_coordinate_radical
    hU hpow E hzero hH hK hS hgen hker htop
  obtain ⟨u,hu,hb⟩ := F.exists_bijective_original_elementary_coordinate_words E hpow hzero hH hK
  have hwhole : F.ambientAxis F.top.ker=F.kernelSpace := by
    apply le_antisymm (F.ambientAxis_le_kernelSpace F.top.ker)
    rintro v ⟨a,rfl⟩
    exact (F.bits_mem_ambientAxis F.top.ker a.toMul).mpr a.toMul.property
  have hspace : F.kernelSpace.map E.originalCoordinateEquiv.toLinearMap=
      (BinaryElementary16GraphHeadRigidity.stateChart 0).space := by
    change (F.ambientAxis F.top.ker).map E.originalCoordinateEquiv.toLinearMap=_ at hS
    rwa [hwhole] at hS
  have hsourceCenter : Nat.card (Subgroup.center U)≤32 := by
    have hc := Nat.card_le_card_of_injective
      (fun z : Subgroup.center U => (z : U) • F.frame (0,0))
      (transitive_center_evaluation_injective (F.frame (0,0)))
    have hdegree : Nat.card X=32 := by simpa only [Nat.card_fin] using F.card_points
    exact hc.trans_eq hdegree
  apply derived_thirty_two_normalF_packet hderived hsourceCenter ?_ N hnonab
  intro L _ _hLzero hLproper
  have hLab : ¬ ∀ a b : U ⧸ L,a*b=b*a := by
    intro hcomm
    letI : IsMulCommutative (U ⧸ L) := ⟨⟨hcomm⟩⟩
    have hDL : commutator U≤L :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
    exact (not_le_of_gt hLproper) hDL
  obtain ⟨c,hc,hA⟩ := F.elementary_derived_denominator_hyperplane E hd hcoord L hLab
  have hLA : L ⊓ commutator U=L := inf_eq_left.mpr hLproper.le
  rw [hLA] at hA
  have hcapacity := F.kernel_center_card_mul_le_original_coordinate_capacity E L
    (BinaryElementary16GraphHeadRigidity.stateChart 0).space
    (binaryFiveHyperplane BinaryElementaryPhiZeroIntrinsicRadical.radical c) hspace hA
  exact hcapacity.trans ((BinaryElementary32FiniteCapacity.original_capacity_le
    E.originalCoordinateRepresentation u hu hb _).trans (hfinite c hc))

end SymmetricSubgroupAsymptotics.BinaryPairFrame
