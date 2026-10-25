import SymmetricSubgroupAsymptotics.PrimitiveSocleUnitaryOneFactorOrdinaryTail

/-! The actual upper/opposite generation and the selected actual original
Sylow give an ordinary head bound independently of any permutation-degree
tail. The derived group and central quotient remain literal. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGUnitaryActualSylowOrdinaryHead
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryCoordinates

theorem genRank_le (r : ℕ) (q : CFSG.PrimePower) (hr : 2 ≤ r)
    (hs : r = 2 → q.order ≠ 2) :
    MarkedC4.genRank (CFSG.Models.TwistedA r q) ≤ q.exponent*(r*(r+1)/2)+1 := by
  by_cases htwo : r = 2
  · subst r
    have hq2 := CFSGTwistedAQuadraticTrace.order_two_le q
    have hq : 3 ≤ q.order := by have hh := hs rfl; omega
    letI : Finite (fixedNaturalPullback 2 q) :=
      Finite.of_injective (pullbackMatrix 2 q) (CFSGTwistedA2UnipotentArrays.pullbackMatrix_two_injective q)
    letI : Finite (OriginalFixedA 2 q) :=
      Finite.of_surjective (pullbackSource 2 q) (pullbackSource_surjective 2 (by decide) q)
    let A := commutator (OriginalFixedA 2 q)
    let U := CFSGTwistedA2UnipotentArrays.originalUnipotent q
    have hUA : U ≤ A := CFSGTwistedA2UnipotentArrays.originalUnipotent_le_commutator q hq
    let P : Sylow q.prime A :=
      (CFSGTwistedA2UnipotentArrays.originalSylow q hq).subtype
        (CFSGTwistedA2UnipotentArrays.originalSylow_le_commutator q hq)
    have hcard : Nat.card P = q.order^3 := by
      have he : Nat.card P = Nat.card U := Nat.card_congr (U.subgroupOfEquivOfLe hUA).toEquiv
      exact he.trans (CFSGTwistedA2UnipotentArrays.originalUnipotent_card q hq)
    have hP : Nat.card P ∣ q.prime^(q.exponent*3) := by
      rw [hcard]
      change (q.prime^q.exponent)^3 ∣ q.prime^(q.exponent*3)
      rw [pow_mul]
    have hh := GoodSylowPrimeOrderOrdinaryGenerators.genRank_le_of_surjective_prime_power
      q.prime (q.exponent*3) (CFSGTwistedA2UnipotentArrays.originalDerived_goodSylowPrime q hq)
      P hP (QuotientGroup.mk' (Subgroup.center A)) (QuotientGroup.mk'_surjective _)
    exact hh
  · obtain ⟨s,rfl⟩ : ∃ s : ℕ, r = s+3 := ⟨r-3,by omega⟩
    letI : Finite (Fixed (s+3) q) := originalFixed_finite q (s+3) (by omega)
    let A := commutator (Fixed (s+3) q)
    let U := originalUnipotent (s+3) q
    have hUA : U ≤ A := originalUnipotent_le_derived q s
    let P : Sylow q.prime A :=
      (originalSylow q (s+3) (by omega)).subtype (originalSylow_le_derived q s)
    have hcard : Nat.card P = q.order^((s+3)*(s+4)/2) := by
      have he : Nat.card P = Nat.card U := Nat.card_congr (U.subgroupOfEquivOfLe hUA).toEquiv
      exact he.trans (original_unipotent_card q (s+3) (by omega))
    have hP : Nat.card P ∣ q.prime^(q.exponent*((s+3)*(s+4)/2)) := by
      rw [hcard]
      change (q.prime^q.exponent)^((s+3)*(s+4)/2) ∣ q.prime^(q.exponent*((s+3)*(s+4)/2))
      rw [pow_mul]
    exact GoodSylowPrimeOrderOrdinaryGenerators.genRank_le_of_surjective_prime_power
      q.prime (q.exponent*((s+3)*(s+4)/2)) (originalDerived_goodSylowPrime q s)
      P hP (QuotientGroup.mk' (Subgroup.center A)) (QuotientGroup.mk'_surjective _)

end SymmetricSubgroupAsymptotics.CFSGUnitaryActualSylowOrdinaryHead
