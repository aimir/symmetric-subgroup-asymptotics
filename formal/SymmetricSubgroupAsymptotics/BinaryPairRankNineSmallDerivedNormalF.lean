import SymmetricSubgroupAsymptotics.BinaryPairSecondCenterRoom
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoRankNineQuotientCenters
import SymmetricSubgroupAsymptotics.BinaryNormalUpperCentralSeries
import SymmetricSubgroupAsymptotics.DerivedOneThousandTwentyFourUnitBound
import SymmetricSubgroupAsymptotics.TransitiveNonabelianCenterBound

/-! A uniform low-derived consumer for the remaining rank-nine source
sectors. The sole geometric branch is triggered only above derived512;
its large actual kernel bounds the SAME original second centre and hence
all original order-two denominators. No normal-subgroup census is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
open MarkedC4.ActualNormalFMarkedPeel
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X] (F : BinaryPairFrame U (Fin 16))
include F

theorem rank_nine_small_derived_all_normal_unit
    (hU : IsPGroup 2 U) (hrank : MarkedC4.genRank U=9)
    (hderived : Nat.card (commutator U)≤1024)
    (hlarge : 512<Nat.card (commutator U) →
      10≤Module.finrank (ZMod 2) F.kernelSpace)
    (hnon : ¬∀ t : F.top.range,t^2=1)
    (N : Subgroup U) [N.Normal] (hnonab : ¬∀ a b : U ⧸ N,a*b=b*a) :
    ∃ V : Subgroup (U ⧸ N),V.Normal ∧
      commutatorLog V+centralLog V≤16 ∧ centralLog V≤8 := by
  have hdegree : Nat.card X=32 := by simpa only [Nat.card_fin] using F.card_points
  have hcenter : Nat.card (Subgroup.center U)≤32 := by
    have hc := Nat.card_le_card_of_injective
      (fun z : Subgroup.center U => (z : U) • F.frame (0,0))
      (transitive_center_evaluation_injective (F.frame (0,0)))
    exact hc.trans_eq hdegree
  apply derived_one_thousand_twenty_four_unit_packet hU hderived hcenter
    (fun L _ hnc => F.rank_nine_nonabelian_quotient_center_card_le_256 hU hrank L hnc)
    ?_ N hnonab
  intro L _ _ htwo hbig
  have hZtwo := F.original_second_center_card_le_sixteen_of_large_nonelementary_kernel
    hU (hlarge hbig) (fun hs => hnon
      (BinarySquareActionStructure.squaresActTrivially_iff_pow_two.mp hs))
  have hc := binary_normal_quotient_center_card_mul_le_upperCentralSeries_of_card_le
    hU 1 L (by rw [htwo];norm_num)
  norm_num only [Nat.reduceAdd] at hc
  have hh := hc.trans hZtwo
  rw [htwo] at hh
  omega

end SymmetricSubgroupAsymptotics.BinaryPairFrame
