import SymmetricSubgroupAsymptotics.BinaryPairSecondCenterCoarseRoom
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoRankNineQuotientCenters
import SymmetricSubgroupAsymptotics.BinaryNormalUpperCentralSeries
import SymmetricSubgroupAsymptotics.DerivedOneThousandTwentyFourUnitBound
import SymmetricSubgroupAsymptotics.TransitiveNonabelianCenterBound
import SymmetricSubgroupAsymptotics.PGroupElementaryAbelianizationRank

/-! A nine-dimensional actual kernel suffices for the remaining rank-nine
1024-derived source. The joint second-centre estimate retains its actual
top image instead of requiring that image to vanish. All original normal
denominators remain literal. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
open MarkedC4.ActualNormalFMarkedPeel
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X] (F : BinaryPairFrame U (Fin 16))
include F

theorem rank_nine_coarse_derived_all_normal_unit
    (hU : IsPGroup 2 U) (hrank : MarkedC4.genRank U=9)
    (hderived : Nat.card (commutator U)≤1024)
    (hlarge : 512<Nat.card (commutator U) →
      9≤Module.finrank (ZMod 2) F.kernelSpace)
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
  have hZtwo := F.original_second_center_card_le_256_of_nine_dim_nonelementary_kernel
    hU (hlarge hbig) (fun hs => hnon
      (BinarySquareActionStructure.squaresActTrivially_iff_pow_two.mp hs))
  have hc := binary_normal_quotient_center_card_mul_le_upperCentralSeries_of_card_le
    hU 1 L (by rw [htwo];norm_num)
  norm_num only [Nat.reduceAdd] at hc
  have hh := hc.trans hZtwo
  rw [htwo] at hh
  omega

end SymmetricSubgroupAsymptotics.BinaryPairFrame

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance coarseNormalFOrderPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
open MarkedC4.ActualNormalFMarkedPeel
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X] (F : BinaryPairFrame U (Fin 16))
include F

theorem rank_nine_order_budget_top_1024_all_normal_unit
    (hU : IsPGroup 2 U) (hrank : MarkedC4.genRank U=9)
    (hderived : Nat.card (commutator U)≤1024) (htop : Nat.card F.top.range≤1024)
    (hnon : ¬∀ t : F.top.range,t^2=1)
    (N : Subgroup U) [N.Normal] (hnonab : ¬∀ a b : U ⧸ N,a*b=b*a) :
    ∃ V : Subgroup (U ⧸ N),V.Normal ∧
      commutatorLog V+centralLog V≤16 ∧ centralLog V≤8 := by
  have hdegree : Nat.card X=32 := by simpa only [Nat.card_fin] using F.card_points
  have hexp := binary_degree_thirty_two_rank_nine_abelianization_exponent U hU hdegree hrank
  have hAb : Nat.card (Abelianization U)=512 := by
    rw [pGroup_abelianization_card_eq_pow_genRank 2 hU hexp,hrank]
    decide
  have hc := (commutator U).card_mul_index
  change Nat.card (commutator U)*Nat.card (Abelianization U)=Nat.card U at hc
  rw [hAb] at hc
  apply F.rank_nine_coarse_derived_all_normal_unit hU hrank hderived ?_ hnon N hnonab
  intro hbig
  by_contra hn
  have hk : Module.finrank (ZMod 2) F.kernelSpace≤8 := by omega
  have hK : Nat.card F.kernelSpace≤256 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.kernelSpace)
    rw [Nat.card_zmod] at hh
    rw [hh]
    exact (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) hk).trans_eq (by decide)
  have hu := Nat.mul_le_mul hK htop
  rw [F.kernelSpace_card_mul_top] at hu
  omega
end SymmetricSubgroupAsymptotics.BinaryPairFrame
