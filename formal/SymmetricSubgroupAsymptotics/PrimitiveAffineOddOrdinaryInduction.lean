import SymmetricSubgroupAsymptotics.PrimitiveAffineOrdinaryGeneratorRank
import SymmetricSubgroupAsymptotics.AbelianAutomorphismInversionPairs
import SymmetricSubgroupAsymptotics.PermutationOrdinarySmallerActions

/-! Odd-prime primitive affine ordinary-generator induction. The actual
point stabilizer acts on inverse pairs of nonidentity translations;
its literal kernel has rank at most one. Rounded smaller-action bounds
then give the exact half-degree bound whenever the degree is at least nine. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineOddOrdinaryInduction
open AbelianAutomorphismInversionPairs PermutationOrdinarySmallerActions

variable {G X : Type} [Group G] [Finite G] [Finite X] [Nontrivial X]
    [MulAction G X] [FaithfulSMul G X] (P : PrimitiveAffineProfile G X)

theorem translation_inverse_ne_self (hp : P.p≠2) (v : P.V) (hv : v≠1) : v⁻¹≠v := by
  intro he
  have hcop : P.p.Coprime 2 := (Nat.coprime_primes P.p_prime Nat.prime_two).mpr hp
  have hpow : v^2=(1:P.V)^2 := by
    calc
      v^2=v*v := pow_two v
      _=v*v⁻¹ := congrArg (fun z=>v*z) he.symm
      _=1 := mul_inv_cancel v
      _=(1:P.V)^2 := (one_pow 2).symm
  exact hv ((P.V_pgroup.powEquiv hcop).injective hpow)

theorem two_mul_genRank_le_degree (hprimitive : MulAction.IsPreprimitive G X)
    (hp : P.p≠2) (hn : 9≤Nat.card X) (hbelow : SmallerActionBound (Nat.card X)) :
    2*MarkedC4.genRank G≤Nat.card X := by
  letI : IsMulCommutative P.V := P.isMulCommutative hprimitive
  let x : X := Classical.arbitrary X
  let H := P.complement x
  let φ : H→*MulAut P.V := P.complementAction x
  have hφ : Function.Injective φ := P.complementAction_injective x
  let F : H→*Equiv.Perm (PairCarrier P.V) := pairAction φ
  let Q : Subgroup (Equiv.Perm (PairCarrier P.V)) := F.range
  letI : Finite Q := Finite.of_surjective F.rangeRestrict F.rangeRestrict_surjective
  have hpair : 2*Nat.card (PairCarrier P.V)≤Nat.card X-1 := by
    have hh := two_mul_pairCard_le (V:=P.V) (translation_inverse_ne_self P hp)
    simpa only [P.card_eq x] using hh
  have hQ : 2*MarkedC4.genRank Q≤Nat.card (PairCarrier P.V)+1 :=
    rounded_rank_of_smaller (Nat.card X) hbelow Q (PairCarrier P.V) (by omega)
  have hK : MarkedC4.genRank F.ker≤1 := kernel_genRank_le_one φ hφ
  have hquot : MarkedC4.genRank (H⧸F.ker)=MarkedC4.genRank Q :=
    CoprimeNilpotentProductGenerators.genRank_mulEquiv (QuotientGroup.quotientKerEquivRange F)
  have hH : MarkedC4.genRank H≤1+MarkedC4.genRank Q := by
    have hh := MarkedC4.genRank_le_of_normal F.ker
    rw [hquot] at hh
    exact hh.trans (Nat.add_le_add_right hK _)
  have hG := P.genRank_le_complement_add_one hprimitive x
  change MarkedC4.genRank G≤MarkedC4.genRank H+1 at hG
  omega

theorem exists_half_degree_generators (hprimitive : MulAction.IsPreprimitive G X)
    (hp : P.p≠2) (hn : 9≤Nat.card X) (hbelow : SmallerActionBound (Nat.card X)) :
    ∃S:Finset G,Subgroup.closure (S:Set G)=⊤ ∧ 2*S.card≤Nat.card X := by
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G:=G)
  refine ⟨S,hgen,?_⟩
  rw [hS]
  exact two_mul_genRank_le_degree P hprimitive hp hn hbelow

end SymmetricSubgroupAsymptotics.PrimitiveAffineOddOrdinaryInduction
