import SymmetricSubgroupAsymptotics.CFSGSufficientSixPointConsumers
import SymmetricSubgroupAsymptotics.CFSGSufficientSmallQuotientCompression
import SymmetricSubgroupAsymptotics.CFSGSufficientPrimitiveTernaryWeights
import SymmetricSubgroupAsymptotics.PrimitiveTernaryStrictHeadAwayFromTenTwelve

/-! The unchanged original relative-head frontier away from10/12, using
only bounded sharp estimates below27 and the sufficient medium estimate.
The large tail starts at34 and uses the existing primitive generator bound.
No relative head or original normal subgroup is substituted. -/

/-! The small nonaffine strict-head consumer away from degrees10/12.
All heads remain those of the original normal subgroup. Prime degrees
use the actual Frattini quotient dividend, not a primitive model list. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

private theorem valuation_receipt :
    (∀ q : Fin 3,q.val.factorization 3=0) ∧
    (∀ q : Fin 9,q.val.factorization 3≤1) := by decide +kernel

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]

private theorem quotient_le_two_of_five_six
    (D : NonaffineData G X) (hindex : SufficientSimpleIndexBounds)
    (hdegree : Nat.card X=5 ∨ Nat.card X=6) : Nat.card (G⧸finiteGroupSocle G)≤2 := by
  rcases hdegree with h5|h6
  · let e : X≃Fin 5 := Finite.equivFinOfCardEq h5
    letI : MulAction G (Fin 5) := MulAction.compHom (Fin 5) (labelledActionHom e)
    letI : FaithfulSMul G (Fin 5) := {
      eq_of_smul_eq_smul := fun {a b} hab =>
        labelledActionHom_injective e (Equiv.Perm.ext hab) }
    let D' : NonaffineData G (Fin 5) := D.transportPoints e
      (fun g x => (labelledActionHom_apply e g x).symm)
    exact D'.degreeFive_quotient_card_le_two_of_sufficient hindex
  · let e : X≃Fin 6 := Finite.equivFinOfCardEq h6
    letI : MulAction G (Fin 6) := MulAction.compHom (Fin 6) (labelledActionHom e)
    letI : FaithfulSMul G (Fin 6) := {
      eq_of_smul_eq_smul := fun {a b} hab =>
        labelledActionHom_injective e (Equiv.Perm.ext hab) }
    let D' : NonaffineData G (Fin 6) := D.transportPoints e
      (fun g x => (labelledActionHom_apply e g x).symm)
    exact PrimitiveDegreeSixActualNormalConsumers.nonaffine_socle_quotient_card_le_two_of_sufficient D' hindex

private theorem prime_quotient_divisor_of_card
    (D : NonaffineData G X) {p : ℕ} (hp : p.Prime)
    (hsmall : p=7 ∨ p=11 ∨ p=13) (hX : Nat.card X=p) :
    Nat.card (G⧸finiteGroupSocle G)∣p-1 := by
  let e : X≃Fin p := Finite.equivFinOfCardEq hX
  letI : MulAction G (Fin p) := MulAction.compHom (Fin p) (labelledActionHom e)
  letI : FaithfulSMul G (Fin p) := {
    eq_of_smul_eq_smul := fun {a b} hab =>
      labelledActionHom_injective e (Equiv.Perm.ext hab) }
  let D' : NonaffineData G (Fin p) := D.transportPoints e
    (fun g x => (labelledActionHom_apply e g x).symm)
  letI : MulAction.IsPretransitive (finiteGroupSocle G) (Fin p) := D'.socle_transitive
  exact SmallPrimeTransitiveNormalQuotientDivisor.quotient_card_dvd
    hp hsmall (finiteGroupSocle G)

theorem NonaffineData.ternaryHead_strict_fiveToThirteen_except_ten_twelve_of_sufficient
    (D : NonaffineData G X) (hindex : SufficientSimpleIndexBounds)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (hf : 5≤Nat.card X) (h13 : Nat.card X≤13)
    (h10 : Nat.card X≠10) (h12 : Nat.card X≠12)
    (N : Subgroup G) [N.Normal] :
    20*Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)<3*Nat.card X := by
  let c := actualChiefSeries G
  have hh := (primeRelativeHead_le_actualChiefWeight N c).trans
    (actualChiefSeriesTernaryWeight_le_semisimpleQuotient_factorization
      (finiteGroupSocle G) D.chart c)
  by_cases h56 : Nat.card X=5 ∨ Nat.card X=6
  · have hq := quotient_le_two_of_five_six D hindex h56
    have hv := valuation_receipt.1 ⟨Nat.card (G⧸finiteGroupSocle G),by omega⟩
    change (Nat.card (G⧸finiteGroupSocle G)).factorization 3=0 at hv
    omega
  by_cases h8 : Nat.card X=8
  · have hq := D.degreeEight_quotient_card_le_seven_of_sufficient hindex published8 h8
    have hv := valuation_receipt.2 ⟨Nat.card (G⧸finiteGroupSocle G),by omega⟩
    change (Nat.card (G⧸finiteGroupSocle G)).factorization 3≤1 at hv
    omega
  by_cases h9 : Nat.card X=9
  · have hq := D.degreeNine_quotient_card_le_eight_of_card_of_sufficient h9 hindex
    have hv := valuation_receipt.2 ⟨Nat.card (G⧸finiteGroupSocle G),by omega⟩
    change (Nat.card (G⧸finiteGroupSocle G)).factorization 3≤1 at hv
    omega
  have hprime : Nat.card X=7 ∨ Nat.card X=11 ∨ Nat.card X=13 := by omega
  have hp : (Nat.card X).Prime := by
    rcases hprime with h|h|h <;> rw [h] <;> decide
  have hd := prime_quotient_divisor_of_card D hp hprime rfl
  have hv : (Nat.card X-1).factorization 3≤1 := by
    rcases hprime with h|h|h <;> rw [h] <;> decide +kernel
  have hval := (Nat.factorization_le_iff_dvd
    (Nat.card_pos (α := G⧸finiteGroupSocle G)).ne' (by omega : Nat.card X-1≠0)).mpr hd 3
  omega

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure


/-! The complete strict-head consumer away from the two remaining
small nonaffine degrees10/12. This is a proved range reduction, not a new
published assumption or a claim that either remaining case is closed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
open PrimitiveSocleRawStructure
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

theorem primitiveTernaryStrictHead_awayFromTenTwelve_of_sufficient
    (hgen : PrimitiveNormalGeneratorInput) (hindex : SufficientSimpleIndexBounds)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPreprimitive G X] [Nontrivial X]
    (h3 : Nat.card X≠3) (h4 : Nat.card X≠4)
    (h10 : Nat.card X≠10) (h12 : Nat.card X≠12)
    (N : Subgroup G) [N.Normal] :
    20*Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)<3*Nat.card X := by
  by_cases hlarge : 34≤Nat.card X
  · exact c1_primitive_relative_tail_faithful hgen hlarge N
  cases Classical.choice (publishedONanScottStructure G X) with
  | inr P =>
      exact P.small_ternaryRelativeHead_strict inferInstance (by omega) h3 h4 N
  | inl D =>
      by_cases h14 : 14≤Nat.card X
      · exact D.ternaryHead_strict_fourteenToThirtyThree_of_sufficient hindex h14 (by omega) N
      · exact D.ternaryHead_strict_fiveToThirteen_except_ten_twelve_of_sufficient hindex published8
          (D.degree_five_le_of_sufficient hindex) (by omega) h10 h12 N

end SymmetricSubgroupAsymptotics
