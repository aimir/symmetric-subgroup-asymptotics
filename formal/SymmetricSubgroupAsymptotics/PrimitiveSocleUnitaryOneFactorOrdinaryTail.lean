import SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorSylowOrderOrdinaryTail
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryDerivedGoodSylow
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryProjectiveOrderLower
import SymmetricSubgroupAsymptotics.CFSGTwistedA2DerivedGoodSylow
import SymmetricSubgroupAsymptotics.CFSGUnitaryCompleteOuterBudget
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! Every admissible ORIGINAL unitary model in the one-factor ordinary
large-degree tail. The original upper Sylow is restricted to the original
derived fixed source and then mapped through its actual central quotient.
Its proved q^(r(r+1)/2) cardinal replaces an unproved generating-pair claim. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleUnitaryOneFactorOrdinaryTail
open PrimitiveSocleRawStructure CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryCoordinates

private theorem triangle_le_square (r : ℕ) (hr : 1 ≤ r) : r*(r+1)/2 ≤ r^2 := by
  have hh : r*(r+1) ≤ 2*r^2 := by nlinarith
  have hd : r*(r+1)/2 ≤ (2*r^2)/2 := Nat.div_le_div_right hh
  omega

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem genRank_le_ceiling (hk : D.factorCount = 1)
    (r : ℕ) (q : CFSG.PrimePower) (hr : 2 ≤ r) (hs : r=2 → q.order ≠ 2)
    (e : D.Simple ≃* CFSG.Models.TwistedA r q) (hn : 1024 ≤ Nat.card X) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  letI : IsSimpleGroup (CFSG.Models.TwistedA r q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.TwistedA r q) := Finite.of_equiv D.Simple e.toEquiv
  have hnoncomm : ¬ IsMulCommutative (CFSG.Models.TwistedA r q) := by
    intro h
    apply D.noncommutative
    apply isMulCommutative_iff.mpr
    intro x y
    apply e.injective
    simpa only [map_mul] using (isMulCommutative_iff.mp h) (e x) (e y)
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  have hellM := CFSGReduction.leastProperIndex_of_mulEquiv e ell hell
  have hfield : q.order ^ r ≤ ell :=
    twistedA_admissible_order_power_le_leastProperIndex r hr q hs ell hellM
  have houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)) := by
    rw [CFSGReduction.outer_card_congr e]
    exact twistedA_admissible_sufficient_outer_budget r hr q hs hnoncomm ell hellM
  by_cases htwo : r=2
  · subst r
    have hq2 : 2 ≤ q.order := q.prime_isPrime.two_le.trans
      (Nat.le_self_pow q.exponent_pos.ne' q.prime)
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
    have hcard : Nat.card P = q.order ^ 3 := by
      have he : Nat.card P = Nat.card U :=
        Nat.card_congr (U.subgroupOfEquivOfLe hUA).toEquiv
      exact he.trans (CFSGTwistedA2UnipotentArrays.originalUnipotent_card q hq)
    have hP : Nat.card P ∣ q.prime ^ (q.exponent * 3) := by
      rw [hcard]
      change (q.prime ^ q.exponent) ^ 3 ∣ q.prime ^ (q.exponent * 3)
      rw [pow_mul]
    let f : A →* D.Simple := e.symm.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center A))
    have hf : Function.Surjective f := e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
    exact PrimitiveSocleOneFactorSylowOrderOrdinaryTail.genRank_le_ceiling
      D hk q 2 3 (by decide)
      (CFSGTwistedA2UnipotentArrays.originalDerived_goodSylowPrime q hq)
      P hP f hf ell hell hfield houter hn
  · obtain ⟨s,rfl⟩ : ∃ s : ℕ, r=s+3 := ⟨r-3,by omega⟩
    letI : Finite (Fixed (s+3) q) := originalFixed_finite q (s+3) (by omega)
    let A := commutator (Fixed (s+3) q)
    let U := originalUnipotent (s+3) q
    have hUA : U ≤ A := originalUnipotent_le_derived q s
    let P : Sylow q.prime A :=
      (originalSylow q (s+3) (by omega)).subtype (originalSylow_le_derived q s)
    have hcard : Nat.card P = q.order ^ ((s+3)*(s+4)/2) := by
      have he : Nat.card P = Nat.card U :=
        Nat.card_congr (U.subgroupOfEquivOfLe hUA).toEquiv
      exact he.trans (original_unipotent_card q (s+3) (by omega))
    have hP : Nat.card P ∣ q.prime ^ (q.exponent * ((s+3)*(s+4)/2)) := by
      rw [hcard]
      change (q.prime ^ q.exponent) ^ ((s+3)*(s+4)/2) ∣
        q.prime ^ (q.exponent * ((s+3)*(s+4)/2))
      rw [pow_mul]
    let f : A →* D.Simple := e.symm.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center A))
    have hf : Function.Surjective f := e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
    apply PrimitiveSocleOneFactorSylowOrderOrdinaryTail.genRank_le_ceiling
      D hk q (s+3) ((s+3)*(s+4)/2) ?_
      (originalDerived_goodSylowPrime q s) P hP f hf ell hell hfield houter hn
    exact triangle_le_square (s+3) (by omega)

theorem exists_generating_finset (hk : D.factorCount = 1)
    (r : ℕ) (q : CFSG.PrimePower) (hr : 2 ≤ r) (hs : r=2 → q.order ≠ 2)
    (e : D.Simple ≃* CFSG.Models.TwistedA r q) (hn : 1024 ≤ Nat.card X) :
    ∃ U : Finset G, Subgroup.closure (U : Set G) = ⊤ ∧
      U.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨U,hU,hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨U,hgen,hU.le.trans (genRank_le_ceiling D hk r q hr hs e hn)⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleUnitaryOneFactorOrdinaryTail
