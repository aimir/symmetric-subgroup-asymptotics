import SymmetricSubgroupAsymptotics.BinaryHeisenbergPhiZeroCentralLineActual
import SymmetricSubgroupAsymptotics.BinaryPairOriginalKernelCoordinateCard
import SymmetricSubgroupAsymptotics.BinaryPairRankSixTopQuotientCenter
import SymmetricSubgroupAsymptotics.DerivedTwoFiftySixNormalFBound
import SymmetricSubgroupAsymptotics.PGroupGeneratorAbelianizationOrder
import SymmetricSubgroupAsymptotics.TransitiveNonabelianCenterBound

/-! Every original nonabelian quotient of the rank-ten Heisenberg phi-zero
source has the exact five-quarter packet. Only one original constant-line
capacity is finite; larger derived denominators use the universal actual
rank-six-top quotient-centre bound. No outer split or offset choice occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance heisenbergThirtyTwoNormalFProofPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
open MarkedC4.ActualNormalFMarkedPeel
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16)) (E : BinaryPairFrame F.top.range (Fin 8))
    [MulAction.IsPretransitive U X]
include F E

theorem heisenberg_rank_ten_all_normalF_packet
    (hU : IsPGroup 2 U) (hhigh : 10≤MarkedC4.genRank U)
    (hTopRank : 6≤MarkedC4.genRank F.top.range)
    (hzero : F.top.range=E.splitAffineAction)
    (hH : E.top.range=Subgroup.closure (Set.range BinaryMenuCayley8T22.generators))
    (hK : E.kernelSpace=BinaryHeisenbergSixCanonicalGenerators.K.space)
    (hS : (E.originalCoordinateSubrepresentation (F.axisNaturalSubrepresentation F.top.ker)).toSubmodule=
      (BinaryHeisenberg14GraphHeadRigidity.stateChart 0).space)
    (N : Subgroup U) [N.Normal] (hnonab : ¬∀ a b : U ⧸ N,a*b=b*a) :
    ∃ V : Subgroup (U ⧸ N),V.Normal ∧
      commutatorLog V+(5/4 : ℝ)*centralLog V≤16 ∧ centralLog V≤8 := by
  have hdegree : Nat.card X=32 := by simpa only [Nat.card_fin] using F.card_points
  have hAb : Nat.card (Abelianization U)=1024 := by
    have hu := twoGroup_transitive_abelianization_card_le_quarter_add_two U hU
    rw [hdegree] at hu
    norm_num at hu
    have hl := (Nat.pow_le_pow_right (by decide : 0<2) hhigh).trans
      (pGroup_pow_genRank_le_abelianization_card 2 hU)
    norm_num at hl
    omega
  have htopcard : Nat.card F.top.range=256 := by
    rw [E.card_of_original_zero_frame hzero,hK,hH,
      BinaryHeisenbergSixCanonicalGenerators.K.card,BinaryMenuCayley8T22.exact_card]
    norm_num
  have hkcard : Nat.card F.kernelSpace=1024 :=
    F.kernelSpace_card_of_original_coordinate_state E (BinaryHeisenberg14GraphHeadRigidity.stateChart 0) hS
  have hUcard : Nat.card U=262144 := by
    have hh := F.kernelSpace_card_mul_top
    rw [hkcard,htopcard] at hh
    omega
  have hderived : Nat.card (commutator U)≤256 := by
    have hh := (commutator U).card_mul_index
    change Nat.card (commutator U)*Nat.card (Abelianization U)=Nat.card U at hh
    rw [hAb,hUcard] at hh
    omega
  have hsourceCenter : Nat.card (Subgroup.center U)≤32 := by
    have hc := Nat.card_le_card_of_injective
      (fun z : Subgroup.center U => (z : U) • F.frame (0,0))
      (transitive_center_evaluation_injective (F.frame (0,0)))
    exact hc.trans_eq hdegree
  apply derived_two_fifty_six_normalF_packet hU hderived hsourceCenter
    (fun L _ hnon => F.rank_six_top_nonabelian_quotient_center_card_le_256 hU hTopRank L hnon)
    ?_ N hnonab
  intro L _ _ htwo
  exact (BinaryHeisenbergPhiZeroCentralLineActual.BinaryPairFrame.normal_order_two_quotient_center_card_le_four
    F E hU hzero hH hK hS L htwo).trans (by decide)
end SymmetricSubgroupAsymptotics.BinaryPairFrame
