import SymmetricSubgroupAsymptotics.FrattiniSurjectiveOrdinaryGenerators
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCentralCommutators
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryHeisenbergPrime
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperCardinality
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRadicalUpperEmbedding
import SymmetricSubgroupAsymptotics.PrimeFieldBasisOrdinaryGenerators
import SymmetricSubgroupAsymptotics.PrimeFrattini
import SymmetricSubgroupAsymptotics.CoprimeNilpotentProductGenerators

/-! The literal central parameter kernel is Frattini in the SAME
unitary radical, all fields and ranks. Ordinary rank is therefore paid
only by its genuine prime-field vector quotient. Rank-two upper groups
are the same radical with trivial actual middle factor. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGUnitaryRadicalFrattiniOrdinaryGenerators
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryCoordinates

theorem parameter_kernel_le_frattini (q : CFSG.PrimePower) (s : ℕ) :
    (fixedRadicalParameterHom q s).ker ≤ frattini (fixedRadical q s) := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  have hcard : Nat.card (fixedRadical q s) = q.prime^(q.exponent*(2*s+3)) := by
    rw [fixedRadical_card]
    change (q.prime^q.exponent)^(2*s+3) = q.prime^(q.exponent*(2*s+3))
    rw [pow_mul]
  have hp : IsPGroup q.prime (fixedRadical q s) := IsPGroup.of_card hcard
  have hcomm : commutator (fixedRadical q s) ≤ frattini (fixedRadical q s) := by
    rw [←primeAbelianizationGroupMap_ker q.prime (fixedRadical q s) hp]
    exact Abelianization.commutator_subset_ker _
  intro z hz
  obtain ⟨c,hc⟩ := exists_centralRadical_of_parameter_one q s z hz
  obtain ⟨x,y,hxy⟩ := centralRadical_eq_commutator q s c
  rw [←hc,←hxy]
  exact hcomm (Subgroup.commutator_mem_commutator
    (Subgroup.mem_top _) (Subgroup.mem_top _))

theorem radical_genRank_le (q : CFSG.PrimePower) (s : ℕ) :
    MarkedC4.genRank (fixedRadical q s) ≤ 2*((s+1)*q.exponent) := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  have hh := FrattiniSurjectiveOrdinaryGenerators.genRank_le
    (fixedRadicalParameterHom q s) (fixedRadicalParameterHom_surjective q s)
    (parameter_kernel_le_frattini q s)
  have hv := PrimeFieldBasisOrdinaryGenerators.genRank_le_finrank q.prime
    (V := Fin (s+1) → q.Extension 2)
  rw [primeVector_finrank] at hv
  exact hh.trans hv

theorem rank_two_upper_genRank_le (q : CFSG.PrimePower) :
    MarkedC4.genRank (naturalUnipotent 2 q) ≤ 2*q.exponent := by
  letI : Subsingleton (naturalUnipotent 0 q) :=
    (Nat.card_eq_one_iff_unique.mp (naturalUnipotent_card_zero q)).1
  have hsurj : Function.Surjective (radicalUpperHom q 0) := by
    intro g
    obtain ⟨⟨r,m⟩,hr⟩ := upperProduct_surjective q 0 g
    change radicalUpperHom q 0 r*middleUnipotentHom q 0 m = g at hr
    have hm : m = 1 := Subsingleton.elim _ _
    rw [hm,map_one,mul_one] at hr
    exact ⟨r,hr⟩
  let e := MulEquiv.ofBijective (radicalUpperHom q 0)
    ⟨radicalUpperHom_injective q 0,hsurj⟩
  rw [←CoprimeNilpotentProductGenerators.genRank_mulEquiv e]
  simpa only [Nat.zero_add,Nat.one_mul] using radical_genRank_le q 0

end SymmetricSubgroupAsymptotics.CFSGUnitaryRadicalFrattiniOrdinaryGenerators
