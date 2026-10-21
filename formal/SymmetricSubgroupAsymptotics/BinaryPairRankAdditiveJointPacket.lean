import SymmetricSubgroupAsymptotics.BinaryRankAdditiveNormalFJointOnly
import SymmetricSubgroupAsymptotics.BinaryPairActualKernelImageBounds
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoRankNineQuotientCenters

/-! Actual-frame installer for the retained rank-additive joint bound.
Both quotient factors use the original denominator. The retained top is
the actual image of that top, identified by its literal quotient kernel;
the full original rank-nine abelianization and quotient centre bound are
supplied by their proved theorems. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
open MarkedC4.ActualNormalFMarkedPeel
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X] (F : BinaryPairFrame U (Fin 16))
include F

theorem rank_nine_rank_additive_joint_normalF_packet
    (hU : IsPGroup 2 U) (hrank : MarkedC4.genRank U=9)
    (hadd : MarkedC4.genRank U=
      MarkedC4.normalGen F.top.ker+MarkedC4.genRank F.top.range)
    (d a t : ℕ)
    (hbound : ∀ (A : Subgroup U) [A.Normal],A≤F.top.ker → MarkedC4.normalGen A≤d)
    (hjoint : ∀ (M : Subgroup F.top.range) [M.Normal],
      Nat.card (commutator (F.top.range ⧸ M))*
        Nat.card (Subgroup.center (F.top.range ⧸ M))≤2^t)
    (hcost : d+a+t≤MarkedC4.normalGen F.top.ker+16)
    (N : Subgroup U) [N.Normal] (hN : N≤commutator U)
    (himage : Nat.card (F.top.ker.map (QuotientGroup.mk' N))≤2^a)
    (hnonab : ¬∀ x y : U ⧸ N,x*y=y*x) :
    ∃ V : Subgroup (U ⧸ N),V.Normal ∧
      commutatorLog V+centralLog V≤16 ∧ centralLog V≤8 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let beta := F.top.rangeRestrict
  have hbeta : Function.Surjective beta := F.top.rangeRestrict_surjective
  have hpowers : ∀ k : beta.ker,(k : U)^2=1 := by
    intro k
    exact F.physical_kernel_pow_two
      ⟨k.val,by simpa only [beta,MonoidHom.ker_rangeRestrict] using k.property⟩
  have hdegree : Nat.card X=32 := by simpa only [Nat.card_fin] using F.card_points
  have hexp := binary_degree_thirty_two_rank_nine_abelianization_exponent U hU hdegree hrank
  have hrankadd : MarkedC4.genRank U=
      MarkedC4.normalGen beta.ker+MarkedC4.genRank F.top.range := by
    simpa only [beta,MonoidHom.ker_rangeRestrict] using hadd
  have hbound' (A : Subgroup U) [A.Normal] (hA : A≤beta.ker) :
      MarkedC4.normalGen A≤d :=
    hbound A (by simpa only [beta,MonoidHom.ker_rangeRestrict] using hA)
  have hker := F.zeroCutBase_kernel_eq_actual_kernel_image N
  have hker' : (F.zeroCutBase N).ker=beta.ker.map (QuotientGroup.mk' N) := by
    simpa only [beta,MonoidHom.ker_rangeRestrict] using hker
  let e : F.top.range ⧸ (F.sectionTopQuotient N).ker ≃*
      U ⧸ (F.top.ker⊔N) := QuotientGroup.quotientKerEquivOfSurjective
        (F.sectionTopQuotient N) (F.sectionTopQuotient_surjective N)
  have hjoint' : Nat.card (commutator (U ⧸ (F.top.ker⊔N)))*
      Nat.card (Subgroup.center (U ⧸ (F.top.ker⊔N)))≤2^t := by
    rw [←Nat.card_congr (RDTDegreeEightExceptionalTransport.derivedEquiv e).toEquiv,
      ←Nat.card_congr (RDTDegreeEightExceptionalTransport.centerEquiv e).toEquiv]
    exact hjoint (F.sectionTopQuotient N).ker
  have hcenter : Nat.card (Subgroup.center (U ⧸ N))≤2^8 := by
    exact F.rank_nine_nonabelian_quotient_center_card_le_256 hU hrank N hnonab
  apply binary_rank_additive_normalF_top_unit_criterion_of_quotient_center
    hU beta hbeta hpowers hexp hrankadd (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N)
    (by simpa only [QuotientGroup.ker_mk'] using hN)
    d a t 16 8 hbound' (F.zeroCutBase N) (F.zeroCutBase_surjective N) hker'
  · simpa only [beta,MonoidHom.ker_rangeRestrict] using himage
  · exact hjoint'
  · simpa only [beta,MonoidHom.ker_rangeRestrict] using hcost
  · exact hcenter

end SymmetricSubgroupAsymptotics.BinaryPairFrame
