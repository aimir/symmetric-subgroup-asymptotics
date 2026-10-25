import SymmetricSubgroupAsymptotics.TwoBlockSimpleLocalOrdinaryGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeEightSubnormalOrdinaryGenerators
import SymmetricSubgroupAsymptotics.OriginalAffineBlockCharacteristicHead
import SymmetricSubgroupAsymptotics.ActualWreathPrimeTopChiefOrdinaryBudget
import SymmetricSubgroupAsymptotics.TinyPrimeTopSharpFloorNumerics

/-! The actual degree-sixteen source with primitive affine eight-point
component costs six ordinary generators. The SAME local translation
quotient is one of the three already proved complement models. Orders
seven/twenty-one use the actual prime-top chief bound; the simple GL3(F2)
case uses actual two-coordinate axis/graph compression. The original
translation head has dimension three at prime top two. No new catalogue,
CFSG callback, current-degree bound, or arbitrary normal-rank lift occurs. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.OriginalAffineEightTwoBlockSharpStep
open OriginalAffineBlockCharacteristicHead
open PrimitiveAffineDegreeEightThreeImages GeneralThreeTwoSurvivingSubnormal
open TraceySharpHalfDegreeNumerics

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]
local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by have h := block.degrees_ge_two.1; omega)
variable (P : PrimitiveAffineProfile block.Component block.Fibre)

omit [Fintype block.Points] in
theorem exists_quotient_model (height : Nat.card block.Fibre = 8) :
    ∃ i : Fin 3, Nonempty ((block.Component ⧸ P.V) ≃* models i) := by
  let x : block.Fibre := ⟨x₀,block.map_base⟩
  let e : (block.Component ⧸ P.V) ≃* P.complement x :=
    (QuotientGroup.quotientMulEquivOfEq (P.complementProjection_ker x).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (P.complementProjection x) (P.complementProjection_surjective x))
  obtain ⟨i,⟨q⟩⟩ := PrimitiveAffineDegreeEightThreeImages.complement_model
    P block.component_preprimitive x height
  exact ⟨i,⟨e.trans q⟩⟩

include P in
theorem quotient_genRank_le_three (height : Nat.card block.Fibre = 8)
    (ht : Nat.card block.Points = 2) :
    MarkedC4.genRank (quotientState J block P).A ≤ 3 := by
  let S := quotientState J block P
  have hprime : (Fintype.card block.Points).Prime := by
    rw [Fintype.card_eq_nat_card,ht]
    decide
  have htopcard : Nat.card block.Top ≤ 2 := by
    have hh := Nat.card_le_card_of_injective
      (MulAction.toPermHom block.Top block.Points) MulAction.toPerm_injective
    have he : Nat.card (Equiv.Perm block.Points) = 2 := by rw [Nat.card_perm,ht]; decide
    exact hh.trans_eq he
  have htop : MarkedC4.genRank block.Top ≤ 1 :=
    FiniteGroupBinaryOrderGenerators.genRank_le_of_card_le_two_pow block.Top 1
      (by simpa only [pow_one] using htopcard)
  obtain ⟨i,⟨e⟩⟩ := exists_quotient_model J block P height
  fin_cases i
  · have hc : Nat.card S.D = 7 :=
      (Nat.card_congr e.toEquiv).trans model_zero_card
    have hgen := ActualWreathPrimeTopChiefOrdinaryBudget.genRank_le_cardFactors_add_top S block.base hprime
    have hOmega : ArithmeticFunction.cardFactors (Nat.card S.D) = 1 := by rw [hc]; decide +kernel
    rw [hOmega] at hgen
    change MarkedC4.genRank (quotientState J block P).A ≤ _ at hgen
    omega
  · have hc : Nat.card S.D = 21 :=
      (Nat.card_congr (e.trans GeneralThreeTwoSmallAffineBindings.twentyOneEquiv).toEquiv).trans
        SmallAffineSoluble8Row2Order.card
    have hgen := ActualWreathPrimeTopChiefOrdinaryBudget.genRank_le_cardFactors_add_top S block.base hprime
    have hOmega : ArithmeticFunction.cardFactors (Nat.card S.D) = 2 := by rw [hc]; decide +kernel
    rw [hOmega] at hgen
    change MarkedC4.genRank (quotientState J block P).A ≤ _ at hgen
    omega
  · let e₂ : S.D ≃* models (2 : Fin 3) := e
    letI : IsSimpleGroup (models (2 : Fin 3)) := model_two_simple
    letI : IsSimpleGroup S.D := e₂.isSimpleGroup
    have hlocal : MarkedC4.genRank S.D ≤ 2 := by
      calc
        MarkedC4.genRank S.D = MarkedC4.genRank (models (2 : Fin 3)) :=
          CoprimeNilpotentProductGenerators.genRank_mulEquiv e₂
        _ ≤ 2 := GeneralThreeTwoSurvivingOrdinaryGenerators.models_genRank_le_two 2
    have hgen := TwoBlockSimpleLocalOrdinaryGenerators.state_genRank_le_local_add_top S ht
    change MarkedC4.genRank (quotientState J block P).A ≤ MarkedC4.genRank S.D +
      MarkedC4.genRank block.Top at hgen
    omega

include P in
theorem genRank_le_six (height : Nat.card block.Fibre = 8) (hn : n = 16) :
    MarkedC4.genRank J ≤ 6 := by
  have hproduct : 8*Nat.card block.Points = n := by
    simpa only [height,Nat.card_fin] using block.degree_product
  have ht : Nat.card block.Points = 2 := by omega
  have hprime : (Fintype.card block.Points).Prime := by
    rw [Fintype.card_eq_nat_card,ht]
    decide
  have hdpos : 0 < translationDimension J block P :=
    (P.elementaryChart block.component_preprimitive).d_pos
  have hpow : P.p^translationDimension J block P = 8 :=
    (fibre_card_eq_prime_pow_dimension J block P).symm.trans height
  have hpdiv : P.p ∣ 2^3 := by
    change P.p ∣ 8
    rw [←hpow]
    exact dvd_pow_self _ hdpos.ne'
  have hp : P.p = 2 := Nat.prime_eq_prime_of_dvd_pow P.p_prime Nat.prime_two hpdiv
  have hd : translationDimension J block P = 3 := Nat.pow_right_injective (by decide : 2 ≤ 2)
    (by simpa only [hp] using hpow)
  have hcapacity := ActualWreathPrimeTopChiefOrdinaryBudget.elementary_capacity_le_dimension
    (OriginalBlockOrdinaryCompressionState.initialState J block) (QuotientGroup.mk' P.V)
      (translationChart J block P) block.base hprime
  change (headCharge J block P block.base).capacity ≤ translationDimension J block P at hcapacity
  have hgen := ActualWreathElementaryOrdinaryStep.genRank_le_capacity_add_next
    (OriginalBlockOrdinaryCompressionState.initialState J block) (QuotientGroup.mk' P.V)
      (translationChart J block P) (QuotientGroup.mk'_surjective P.V) block.base
  change MarkedC4.genRank J ≤ (headCharge J block P block.base).capacity +
    MarkedC4.genRank (quotientState J block P).A at hgen
  have hquotient := quotient_genRank_le_three J block P height ht
  omega

include P in
theorem genRank_le_sharpFloor (height : Nat.card block.Fibre = 8) (hn : n = 16) :
    MarkedC4.genRank J ≤ sharpFloor n := by
  have hsix : 6 ≤ sharpFloor 16 := TinyPrimeTopSharpFloorNumerics.le_sharpFloor_of_square
    16 6 4 (by decide)
      (TinyPrimeTopSharpFloorNumerics.log_le_of_pow 16 4 (by decide) (by decide)) (by decide)
  exact (genRank_le_six J block P height hn).trans (by simpa only [hn] using hsix)

include P in
theorem exists_generating_finset (height : Nat.card block.Fibre = 8) (hn : n = 16) :
    ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧ S.card ≤ sharpFloor n := by
  obtain ⟨S,hcard,hgen⟩ := MarkedC4.genRank_spec (G := J)
  exact ⟨S,hgen,hcard.le.trans (genRank_le_sharpFloor J block P height hn)⟩

end SymmetricSubgroupAsymptotics.OriginalAffineEightTwoBlockSharpStep
