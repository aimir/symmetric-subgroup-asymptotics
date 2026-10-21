import SymmetricSubgroupAsymptotics.BinaryPairRankAdditiveJointPacket

/-! For the SAME original N contained in the actual pair kernel, the
retained top is the original top itself. Its source joint bound is used;
no uniform bound on unrelated top quotients is substituted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
open MarkedC4.ActualNormalFMarkedPeel
local instance rankAdditiveKernelNormalPacketPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X] (F : BinaryPairFrame U (Fin 16))

theorem rank_nine_rank_additive_kernel_normalF_packet
    (hU : IsPGroup 2 U) (hrank : MarkedC4.genRank U=9)
    (hadd : MarkedC4.genRank U=
      MarkedC4.normalGen F.top.ker+MarkedC4.genRank F.top.range)
    (d a t : ℕ)
    (hbound : ∀ (A : Subgroup U) [A.Normal],A≤F.top.ker → MarkedC4.normalGen A≤d)
    (hjoint : Nat.card (commutator F.top.range)*Nat.card (Subgroup.center F.top.range)≤2^t)
    (hcost : d+a+t≤MarkedC4.normalGen F.top.ker+16)
    (N : Subgroup U) [N.Normal] (hN : N≤F.top.ker) (hND : N≤commutator U)
    (himage : Nat.card (F.top.ker.map (QuotientGroup.mk' N))≤2^a)
    (hnonab : ¬∀ x y : U ⧸ N,x*y=y*x) :
    ∃ V : Subgroup (U ⧸ N),V.Normal ∧
      commutatorLog V+centralLog V≤16 ∧ centralLog V≤8 := by
  let beta := F.top.rangeRestrict
  have hbeta : Function.Surjective beta := F.top.rangeRestrict_surjective
  have hNbeta : N≤beta.ker := by
    simpa only [beta,MonoidHom.ker_rangeRestrict] using hN
  let q := QuotientGroup.mk' N
  let f : (U ⧸ N) →* F.top.range := QuotientGroup.lift N beta hNbeta
  have hf : Function.Surjective f := by
    intro b
    obtain ⟨u,rfl⟩ := hbeta b
    exact ⟨q u,rfl⟩
  have hfker : f.ker=beta.ker.map q := by
    ext x
    obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective N x
    change beta u=1 ↔ q u∈beta.ker.map q
    constructor
    · intro hu
      exact ⟨u,hu,rfl⟩
    · rintro ⟨v,hv,he⟩
      have hh := congrArg f he
      change beta v=beta u at hh
      exact hh.symm.trans hv
  have hpowers : ∀ k : beta.ker,(k : U)^2=1 := by
    intro k
    exact F.physical_kernel_pow_two
      ⟨k.val,by simpa only [beta,MonoidHom.ker_rangeRestrict] using k.property⟩
  have hdegree : Nat.card X=32 := by simpa only [Nat.card_fin] using F.card_points
  have hexp := binary_degree_thirty_two_rank_nine_abelianization_exponent U hU hdegree hrank
  have hrankadd : MarkedC4.genRank U=
      MarkedC4.normalGen beta.ker+MarkedC4.genRank F.top.range := by
    simpa only [beta,MonoidHom.ker_rangeRestrict] using hadd
  have hbound' (A : Subgroup U) [A.Normal] (hA : A≤beta.ker) : MarkedC4.normalGen A≤d :=
    hbound A (by simpa only [beta,MonoidHom.ker_rangeRestrict] using hA)
  have hcenter : Nat.card (Subgroup.center (U ⧸ N))≤2^8 :=
    F.rank_nine_nonabelian_quotient_center_card_le_256 hU hrank N hnonab
  apply binary_rank_additive_normalF_top_unit_criterion_of_quotient_center
    hU beta hbeta hpowers hexp hrankadd q (QuotientGroup.mk'_surjective N)
    (by simpa only [q,QuotientGroup.ker_mk'] using hND)
    d a t 16 8 hbound' f hf hfker
  · simpa only [beta,MonoidHom.ker_rangeRestrict] using himage
  · exact hjoint
  · simpa only [beta,MonoidHom.ker_rangeRestrict] using hcost
  · exact hcenter

end SymmetricSubgroupAsymptotics.BinaryPairFrame
