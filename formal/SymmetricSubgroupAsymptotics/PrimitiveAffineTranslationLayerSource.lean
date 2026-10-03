import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveCoefficient
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveSmallNumerics
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveSmallOrder

/-!
# Stop an imprimitive affine transfer after the translation layer

The full affine-component tower is sometimes numerically wasteful in small
block cells. This file stops after the literal intersection with the local
translation groups. The quotient still acts faithfully on the nonzero
translations in every actual block, so it is already a valid comparator.

The first application closes the degree-three, eight-block cell. Tracey's
prime-to-characteristic bound makes the retained translation capacity at
most one; no catalogue or ambient-order assumption is used.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)

variable [Nontrivial block.Fibre]

/-- The exact local translation kernel, in the coordinates required by the
actual-wreath capacity theorem. -/
def localTranslationChart :
    ElementaryMinimalNormalChart (localMap block P).ker := by
  letI : Fact P.p.Prime := (chart block P).primeFact
  exact
    { p := P.p
      p_prime := P.p_prime
      primeFact := (chart block P).primeFact
      V := (chart block P).V
      addCommGroup := inferInstance
      module := inferInstance
      finiteDimensional := inferInstance
      equiv := (localKernelEquiv block P).symm }

/-- A one-layer relative envelope ending at the faithful complement-by-top
action. The complete normal-axis sum and the joint Yoneda fibre are charged
together by H. -/
noncomputable def translationLayerEnvelope
    (H : ElementaryLayerJointCapacityBound
      (elementaryChart block P).p
      (QuotientGroup.mk' (E block P))
      (QuotientGroup.mk'_surjective (E block P))
      (elementaryChart block P).quotientRepresentation
      (elementaryChart block P).originalKernelChart) :
    RelativeCompleteSourceEnvelope (preE7NonPairAction w U) := by
  letI : Finite (chart block P).V := Finite.of_injective
    (fun v : (chart block P).V =>
      (chart block P).equiv.symm (Multiplicative.ofAdd v))
    (chart block P).equiv.symm.injective
  letI : Finite (TranslationSubmodule block P) :=
    Finite.of_injective (TranslationSubmodule block P).subtype
      (TranslationSubmodule block P).subtype_injective
  letI : Finite (elementaryChart block P).V := by
    change Finite (TranslationSubmodule block P)
    infer_instance
  letI : Finite (elementaryChart block P).quotientRepresentation :=
    inferInstanceAs (Finite (elementaryChart block P).V)
  exact RelativeCompleteSourceEnvelope.elementaryStep
    (p := (elementaryChart block P).p)
    (E block P) (elementaryChart block P) H
    (RelativeCompleteSourceEnvelope.identity
      (preE7NonPairAction w U ⧸ E block P)
      (quotientDegree block) (quotientAction block P)
      (quotientAction_injective block P))

/-- Construction-facing form of the translation stop. -/
noncomputable def translationLayerSource
    (H : ElementaryLayerJointCapacityBound
      (elementaryChart block P).p
      (QuotientGroup.mk' (E block P))
      (QuotientGroup.mk'_surjective (E block P))
      (elementaryChart block P).quotientRepresentation
      (elementaryChart block P).originalKernelChart)
    (hv : 2 ≤ quotientDegree block)
    (hm : preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - quotientDegree block) / 8 -
        Real.logb 2 (elementaryChart block P).p /
          (elementaryChart block P).p * H.capacity)
    (hD : ∀ b : ℕ, H.coefficient ≤
      (2 : ℝ) ^ (affineComponentWidthCost w +
        8 * (w : ℝ) * Real.logb 2 (b + 1))) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  let T := translationLayerEnvelope block P H
  apply RelativeCompleteSourceEnvelope.toRankTailSourceOrYonedaTopOfMargin
    .acert T
  refine
    { eta_nonneg := ?_
      seedDegree_two_le := ?_
      margin := ?_
      coefficient_bound := ?_ }
  · have hp1 : (1 : ℝ) ≤ (elementaryChart block P).p := by
      exact_mod_cast (elementaryChart block P).p_prime.one_le
    have hlog : 0 ≤ Real.logb 2 (elementaryChart block P).p :=
      Real.logb_nonneg (by norm_num) hp1
    have hp0 : (0 : ℝ) ≤ (elementaryChart block P).p := by positivity
    simpa only [T, translationLayerEnvelope,
      RelativeCompleteSourceEnvelope.elementaryStep,
      RelativeCompleteSourceEnvelope.identity, add_zero] using
      mul_nonneg (div_nonneg hlog hp0) H.capacity_nonneg
  · simpa only [T, translationLayerEnvelope,
      RelativeCompleteSourceEnvelope.elementaryStep,
      RelativeCompleteSourceEnvelope.identity] using hv
  · simpa only [T, translationLayerEnvelope,
      RelativeCompleteSourceEnvelope.elementaryStep,
      RelativeCompleteSourceEnvelope.identity, add_zero] using hm
  · intro b
    simpa only [T, translationLayerEnvelope,
      RelativeCompleteSourceEnvelope.elementaryStep,
      RelativeCompleteSourceEnvelope.identity, mul_one] using hD b

/-- The degree-three, eight-block affine translation intersection already
has enough capacity deficit when one stops at its faithful degree-sixteen
quotient action. -/
noncomputable def degreeThreeEightTranslationSource
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 8) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  let C₀ := P.elementaryChart block.component_preprimitive
  letI : Fact P.p.Prime := C₀.primeFact
  letI : AddCommGroup C₀.V := C₀.addCommGroup
  letI : Module (ZMod P.p) C₀.V := C₀.module
  letI : FiniteDimensional (ZMod P.p) C₀.V := C₀.finiteDimensional
  letI : Finite C₀.V := Finite.of_injective
    (fun v : C₀.V => C₀.equiv.symm (Multiplicative.ofAdd v))
    C₀.equiv.symm.injective
  have hdegree₀ : Nat.card block.Fibre = P.p ^ C₀.d := by
    simpa [PrimitiveAffineProfile.ElementaryChart.d] using
      P.degree_eq_prime_pow_finrank C₀.equiv (origin block)
  have hdegree : 3 = P.p ^ C₀.d := hr.symm.trans hdegree₀
  have hpd := prime_pow_positive_injective (d := C₀.d) (e := 1)
    P.p_prime (by norm_num : Nat.Prime 3) C₀.d_pos (by norm_num)
    (hdegree.symm.trans (by norm_num))
  have hp : P.p = 3 := hpd.1
  have hd : C₀.d = 1 := hpd.2
  have hw : w = 24 := by
    rw [width_eq block, hr, hs]
  have hvEq : quotientDegree block = 16 := by
    rw [quotientDegree_eq block, hr, hs]
  have hdim : Module.finrank (ZMod P.p) C₀.V = 1 := by
    simpa only [PrimitiveAffineProfile.ElementaryChart.d] using hd
  have hdim' : Module.finrank (ZMod P.p)
      (P.elementaryChart block.component_preprimitive).V = 1 := by
    simpa only [C₀] using hdim
  let S := initialState hTraceyPerm block
  let C := localTranslationChart block P
  let raw := (affineCapacityInput hTraceyHalf hTraceyLog hTraceyRefined block)
    S (LocalQuotient block P) (localMap block P)
      (localMap_surjective block P) C
  let H := Classical.choose raw
  have hH := Classical.choose_spec raw
  have hdimChart : Module.finrank (ZMod P.p) (chart block P).V = 1 := by
    simpa only [chart] using hdim'
  have href := hH.2.2.1
  change TraceyRefinedInducedCapacityBounds P.p
    (Module.finrank (ZMod P.p) (chart block P).V)
    (Fintype.card block.Points) H.capacity at href
  rw [hdimChart, show Fintype.card block.Points = 8 by
    simpa only [Fintype.card_eq_nat_card] using hs, hp] at href
  have hcap : H.capacity ≤ 1 := by
    have h := href.primeTo 2 3 Nat.prime_two (by norm_num)
      (by norm_num) (by norm_num)
    norm_num at h
    exact h
  have hchartp : (elementaryChart block P).p = 3 := by
    simpa only [elementaryChart] using hp
  have hlog2 : Real.logb 2 3 ≤ 2 := by
    have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≤ 4)
    simpa [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num,
      Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using h
  have heta : Real.logb 2 3 / 3 * H.capacity ≤ (2 / 3 : ℝ) := by
    have hlog0 : 0 ≤ Real.logb 2 3 :=
      Real.logb_nonneg (by norm_num) (by norm_num)
    have hrate0 : 0 ≤ Real.logb 2 3 / 3 := div_nonneg hlog0 (by norm_num)
    calc
      Real.logb 2 3 / 3 * H.capacity ≤
          (Real.logb 2 3 / 3) * 1 :=
        mul_le_mul_of_nonneg_left hcap hrate0
      _ ≤ (2 / 3 : ℝ) := by
        norm_num
        linarith
  have hm : preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - quotientDegree block) / 8 -
        Real.logb 2 (elementaryChart block P).p /
          (elementaryChart block P).p * H.capacity := by
    have hwR : (w : ℝ) = 24 := by exact_mod_cast hw
    have heven : evenWidth w = 24 := by rw [hw]; rfl
    calc
      preE7CharacterRho * w = preE7CharacterRho * 24 := by rw [hwR]
      _ ≤ ((24 : ℝ) - 16) / 8 - 2 / 3 := by
        norm_num [preE7CharacterRho]
      _ ≤ ((evenWidth w : ℝ) - quotientDegree block) / 8 -
          Real.logb 2 (elementaryChart block P).p /
            (elementaryChart block P).p * H.capacity := by
        rw [heven, hvEq, hchartp]
        linarith
  have hcoeff₀ := hH.2.2.2.2
  change H.coefficient ≤ (P.p : ℝ) ^
      traceyAffineCoefficientExponent
        (Module.finrank (ZMod P.p) (chart block P).V)
        (Fintype.card block.Points)
        (traceyInducedGeneratorCeiling
          (Module.finrank (ZMod P.p) (chart block P).V)
          (Fintype.card block.Points))
        (traceyPermutationGeneratorCeiling w) w P.p at hcoeff₀
  rw [hdimChart, show Fintype.card block.Points = 8 by
    simpa only [Fintype.card_eq_nat_card] using hs, hp] at hcoeff₀
  have hcoeff : H.coefficient ≤ (3 : ℝ) ^
      traceyAffineCoefficientExponent 1 8
        (traceyInducedGeneratorCeiling 1 8)
        (traceyPermutationGeneratorCeiling 24) 24 3 := by
    have hexponent :
        traceyAffineCoefficientExponent 1 8
            (traceyInducedGeneratorCeiling 1 8)
            (traceyPermutationGeneratorCeiling w) w 3 =
          traceyAffineCoefficientExponent 1 8
            (traceyInducedGeneratorCeiling 1 8)
            (traceyPermutationGeneratorCeiling 24) 24 3 := by
      rw [hw]
    simpa only [hexponent] using hcoeff₀
  have hD : ∀ b : ℕ, H.coefficient ≤
      (2 : ℝ) ^ (affineComponentWidthCost w +
        8 * (w : ℝ) * Real.logb 2 (b + 1)) := by
    intro b
    let X : ℝ := Real.logb 2 3
    let A : ℕ := traceyAffineCoefficientExponent 1 8
      (traceyInducedGeneratorCeiling 1 8)
      (traceyPermutationGeneratorCeiling 24) 24 3
    have hX0 : 0 ≤ X := by
      dsimp [X]
      exact Real.logb_nonneg (by norm_num) (by norm_num)
    have hX4 : X ≤ 4 := by
      dsimp [X]
      exact hlog2.trans (by norm_num)
    have hXsq : X ^ 2 ≤ (4 : ℝ) ^ 2 := by nlinarith
    have hexp₀ := traceyAffineCoefficientExponent_log_le
      1 8 (traceyPermutationGeneratorCeiling 24) 24 3
      (by norm_num) (by norm_num)
    let q : ℝ := Real.sqrt (Real.logb 2 (8 : ℝ))
    let B : ℝ := 4 * 8 * 24 / q +
      8 * (traceyPermutationGeneratorCeiling 24 + 2) + 24
    have hqpos : 0 < q := by
      dsimp [q]
      exact Real.sqrt_pos.2 (Real.logb_pos (by norm_num) (by norm_num))
    have hA0 : 0 ≤ 4 * (8 : ℝ) ^ 2 / q := by positivity
    have hB0 : 0 ≤ B := by
      dsimp [B]
      positivity
    have hcore : X * (A : ℝ) ≤
        4 * (8 : ℝ) ^ 2 / q * (4 : ℝ) ^ 2 + B * 4 := by
      calc
        X * (A : ℝ) ≤ 4 * (8 : ℝ) ^ 2 / q * X ^ 2 + B * X := by
          simpa only [X, A, q, B, one_mul, Nat.cast_ofNat,
            Nat.cast_add, Nat.cast_one] using hexp₀
        _ ≤ 4 * (8 : ℝ) ^ 2 / q * (4 : ℝ) ^ 2 + B * 4 :=
          add_le_add (mul_le_mul_of_nonneg_left hXsq hA0)
            (mul_le_mul_of_nonneg_left hX4 hB0)
    have hlogb : 0 ≤ Real.logb 2 (b + 1) :=
      Real.logb_nonneg (by norm_num)
        (by exact_mod_cast (show 1 ≤ b + 1 by omega))
    have hexp : X * (A : ℝ) ≤
        affineComponentCoefficientExponent 3 8 24 b := by
      calc
        _ ≤ 4 * (8 : ℝ) ^ 2 / q * (4 : ℝ) ^ 2 + B * 4 := hcore
        _ ≤ 4 * (8 : ℝ) ^ 2 / q * (4 : ℝ) ^ 2 + B * 4 +
            3 * 8 * 4 + 2 * 8 * 4 * Real.logb 2 (b + 1) := by
          have htail : 0 ≤
              3 * (8 : ℝ) * 4 +
                2 * 8 * 4 * Real.logb 2 (b + 1) := by positivity
          linarith
        _ = affineComponentCoefficientExponent 3 8 24 b := by
          norm_num [affineComponentCoefficientExponent, q, B]
    have hpowReal : (3 : ℝ) ^ (A : ℝ) =
        (2 : ℝ) ^ (X * (A : ℝ)) := by
      dsimp [X]
      rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_logb (by norm_num : (0 : ℝ) < 2)
          (by norm_num) (by norm_num)]
    have hpow : (3 : ℝ) ^ A = (2 : ℝ) ^ (X * (A : ℝ)) := by
      rw [← Real.rpow_natCast (3 : ℝ) A]
      exact hpowReal
    calc
      H.coefficient ≤ (3 : ℝ) ^ A := by simpa only [A] using hcoeff
      _ = (2 : ℝ) ^ (X * (A : ℝ)) := hpow
      _ ≤ (2 : ℝ) ^ affineComponentCoefficientExponent 3 8 24 b :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ ≤ (2 : ℝ) ^ (affineComponentWidthCost 24 +
          8 * (24 : ℝ) * Real.logb 2 (b + 1)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (affineComponentCoefficientExponent_le_widthCost
            3 8 24 b (by norm_num) (by norm_num) (by norm_num))
      _ = (2 : ℝ) ^ (affineComponentWidthCost w +
          8 * (w : ℝ) * Real.logb 2 (b + 1)) := by
        rw [show affineComponentWidthCost w =
            affineComponentWidthCost 24 by rw [hw],
          show (w : ℝ) = 24 by exact_mod_cast hw]
  exact translationLayerSource block P H (by omega) hm hD

/-- Degree five with four actual blocks is also closed by the translation
stop.  The binary square in the block count forces capacity at most one. -/
noncomputable def degreeFiveFourTranslationSource
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 5)
    (hs : Nat.card block.Points = 4) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  let C₀ := P.elementaryChart block.component_preprimitive
  letI : Fact P.p.Prime := C₀.primeFact
  letI : AddCommGroup C₀.V := C₀.addCommGroup
  letI : Module (ZMod P.p) C₀.V := C₀.module
  letI : FiniteDimensional (ZMod P.p) C₀.V := C₀.finiteDimensional
  letI : Finite C₀.V := Finite.of_injective
    (fun v : C₀.V => C₀.equiv.symm (Multiplicative.ofAdd v))
    C₀.equiv.symm.injective
  have hdegree₀ : Nat.card block.Fibre = P.p ^ C₀.d := by
    simpa [PrimitiveAffineProfile.ElementaryChart.d] using
      P.degree_eq_prime_pow_finrank C₀.equiv (origin block)
  have hdegree : 5 = P.p ^ C₀.d := hr.symm.trans hdegree₀
  have hpd := prime_pow_positive_injective (d := C₀.d) (e := 1)
    P.p_prime (by norm_num : Nat.Prime 5) C₀.d_pos (by norm_num)
    (hdegree.symm.trans (by norm_num))
  have hp : P.p = 5 := hpd.1
  have hd : C₀.d = 1 := hpd.2
  have hdim : Module.finrank (ZMod P.p) (chart block P).V = 1 := by
    simpa only [chart, C₀, PrimitiveAffineProfile.ElementaryChart.d] using hd
  have hw : w = 5 * Nat.card block.Points := by
    simpa only [hr] using width_eq block
  have hvEq : quotientDegree block = 4 * Nat.card block.Points := by
    rw [quotientDegree_eq block, hr]
  let S := initialState hTraceyPerm block
  let C := localTranslationChart block P
  let raw := (affineCapacityInput hTraceyHalf hTraceyLog hTraceyRefined block)
    S (LocalQuotient block P) (localMap block P)
      (localMap_surjective block P) C
  let H := Classical.choose raw
  have hH := Classical.choose_spec raw
  have href := hH.2.2.1
  change TraceyRefinedInducedCapacityBounds P.p
    (Module.finrank (ZMod P.p) (chart block P).V)
    (Fintype.card block.Points) H.capacity at href
  rw [hdim, Fintype.card_eq_nat_card, hp] at href
  have hcap : H.capacity ≤ 1 := by
    have h := href.primeTo 2 2 Nat.prime_two (by norm_num)
      (by norm_num) (by rw [hs]; norm_num)
    rw [hs] at h
    norm_num at h
    exact h
  have hchartp : (elementaryChart block P).p = 5 := by
    simpa only [elementaryChart] using hp
  have hlog0 : 0 ≤ Real.logb 2 5 :=
    Real.logb_nonneg (by norm_num) (by norm_num)
  have heta : Real.logb 2 5 / 5 * H.capacity ≤ (7 / 15 : ℝ) := by
    have hrate0 : 0 ≤ Real.logb 2 5 / 5 := div_nonneg hlog0 (by norm_num)
    calc
      Real.logb 2 5 / 5 * H.capacity ≤
          (Real.logb 2 5 / 5) * 1 :=
        mul_le_mul_of_nonneg_left hcap hrate0
      _ ≤ (7 / 15 : ℝ) := by
        simpa only [mul_one] using
          logb_two_five_div_five_lt_seven_fifteenths.le
  have hm : preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - quotientDegree block) / 8 -
        Real.logb 2 (elementaryChart block P).p /
          (elementaryChart block P).p * H.capacity := by
    have hw20 : w = 20 := by omega
    have hv16 : quotientDegree block = 16 := by omega
    have heven : evenWidth w = 20 := by
      rw [hw20]
      norm_num [evenWidth, halfDegree]
    have hwR : (w : ℝ) = 20 := by exact_mod_cast hw20
    calc
      preE7CharacterRho * w = preE7CharacterRho * 20 := by rw [hwR]
      _ ≤ ((20 : ℝ) - 16) / 8 - 7 / 15 := by
        norm_num [preE7CharacterRho]
      _ ≤ ((evenWidth w : ℝ) - quotientDegree block) / 8 -
          Real.logb 2 (elementaryChart block P).p /
            (elementaryChart block P).p * H.capacity := by
        rw [heven, hv16, hchartp]
        linarith
  have hcoeff₀ := hH.2.2.2.2
  change H.coefficient ≤ (P.p : ℝ) ^
      traceyAffineCoefficientExponent
        (Module.finrank (ZMod P.p) (chart block P).V)
        (Fintype.card block.Points)
        (traceyInducedGeneratorCeiling
          (Module.finrank (ZMod P.p) (chart block P).V)
          (Fintype.card block.Points))
        (traceyPermutationGeneratorCeiling w) w P.p at hcoeff₀
  rw [hdim, Fintype.card_eq_nat_card, hp] at hcoeff₀
  have hD : ∀ b : ℕ, H.coefficient ≤
      (2 : ℝ) ^ (affineComponentWidthCost w +
        8 * (w : ℝ) * Real.logb 2 (b + 1)) := by
    intro b
    let s := Nat.card block.Points
    let X : ℝ := Real.logb 2 5
    let A : ℕ := traceyAffineCoefficientExponent 1 s
      (traceyInducedGeneratorCeiling 1 s)
      (traceyPermutationGeneratorCeiling w) w 5
    have hs2 : 2 ≤ s := by
      dsimp [s]
      omega
    have hX0 : 0 ≤ X := by simpa only [X] using hlog0
    have hX9 : X ≤ 9 := by
      have hlog3 : Real.logb 2 5 < 3 := by
        have h := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
          (by norm_num : (0 : ℝ) < 5) (by norm_num : (5 : ℝ) < 8)
        simpa [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num,
          Real.logb_pow,
          Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using h
      dsimp [X]
      linarith
    have hXsq : X ^ 2 ≤ (9 : ℝ) ^ 2 := by nlinarith
    have hraw := traceyAffineCoefficientExponent_log_le
      1 s (traceyPermutationGeneratorCeiling w) w 5
      (by norm_num) hs2
    let q : ℝ := Real.sqrt (Real.logb 2 (s : ℝ))
    let B : ℝ := 4 * s * w / q +
      s * (traceyPermutationGeneratorCeiling w + 2) + w
    have hqpos : 0 < q := by
      dsimp [q]
      exact Real.sqrt_pos.2
        (Real.logb_pos (by norm_num) (by exact_mod_cast hs2))
    have hA0 : 0 ≤ 4 * (s : ℝ) ^ 2 / q := by positivity
    have hB0 : 0 ≤ B := by
      dsimp [B]
      positivity
    have hcore : X * (A : ℝ) ≤
        4 * (s : ℝ) ^ 2 / q * (9 : ℝ) ^ 2 + B * 9 := by
      calc
        X * (A : ℝ) ≤
            4 * (s : ℝ) ^ 2 / q * X ^ 2 + B * X := by
          simpa only [X, A, q, B, one_mul, Nat.cast_ofNat,
            Nat.cast_add, Nat.cast_one] using hraw
        _ ≤ 4 * (s : ℝ) ^ 2 / q * (9 : ℝ) ^ 2 + B * 9 :=
          add_le_add (mul_le_mul_of_nonneg_left hXsq hA0)
            (mul_le_mul_of_nonneg_left hX9 hB0)
    have hlogb : 0 ≤ Real.logb 2 (b + 1) :=
      Real.logb_nonneg (by norm_num)
        (by exact_mod_cast (show 1 ≤ b + 1 by omega))
    have hexp : X * (A : ℝ) ≤
        affineComponentCoefficientExponent 5 s w b := by
      calc
        _ ≤ 4 * (s : ℝ) ^ 2 / q * (9 : ℝ) ^ 2 + B * 9 := hcore
        _ ≤ 4 * (s : ℝ) ^ 2 / q * (9 : ℝ) ^ 2 + B * 9 +
            3 * s * 9 + 2 * s * 9 * Real.logb 2 (b + 1) := by
          have htail : 0 ≤ 3 * (s : ℝ) * 9 +
              2 * s * 9 * Real.logb 2 (b + 1) := by positivity
          linarith
        _ = affineComponentCoefficientExponent 5 s w b := by
          norm_num [affineComponentCoefficientExponent, q, B, Nat.log]
    have hpowReal : (5 : ℝ) ^ (A : ℝ) =
        (2 : ℝ) ^ (X * (A : ℝ)) := by
      dsimp [X]
      rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_logb (by norm_num : (0 : ℝ) < 2)
          (by norm_num) (by norm_num)]
    have hpow : (5 : ℝ) ^ A = (2 : ℝ) ^ (X * (A : ℝ)) := by
      rw [← Real.rpow_natCast (5 : ℝ) A]
      exact hpowReal
    calc
      H.coefficient ≤ (5 : ℝ) ^ A := by
        simpa only [A, s] using hcoeff₀
      _ = (2 : ℝ) ^ (X * (A : ℝ)) := hpow
      _ ≤ (2 : ℝ) ^ affineComponentCoefficientExponent 5 s w b :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ ≤ (2 : ℝ) ^ (affineComponentWidthCost w +
          8 * (w : ℝ) * Real.logb 2 (b + 1)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (affineComponentCoefficientExponent_le_widthCost
            5 s w b (by norm_num) hs2 (by simpa only [s] using hw))
  exact translationLayerSource block P H
    (by rw [hvEq]; omega) hm hD

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
