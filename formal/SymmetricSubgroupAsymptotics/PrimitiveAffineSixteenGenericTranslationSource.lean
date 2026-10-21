import SymmetricSubgroupAsymptotics.PrimitiveAffineTranslationComparatorSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenTranslationColdSource
import SymmetricSubgroupAsymptotics.RefinedBinaryFourDimensionStrictGap
import SymmetricSubgroupAsymptotics.BinaryFourTranslationCoefficientBound

/-! Every actual imprimitive affine16 component has a complete source by
stopping at its correlated translation kernel. The same quotient acts on8s
points. Refined capacity gives a strict ordinary margin except at s2/4,
which use the checked-or-prepared fixed actual cold-rank sources instead.
No soluble order bound, chief-length classifier or published16 is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre) [Nontrivial block.Fibre]

def sixteenGenericTranslationSource_awayFromTwoFour
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre=16)
    (hs2 : Nat.card block.Points ≠ 2) (hs4 : Nat.card block.Points ≠ 4) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  let Q := sixteenBinaryProfile block P hr
  let S := initialState hTraceyPerm block
  let C := localTranslationChart block Q
  letI : Finite C.V := Module.finite_of_finite (ZMod C.p)
  letI : Finite (ActualWreathAffineCapacity.E S (localMap block Q) C).V :=
    Finite.of_injective
      (PermutationalWreathProduct.Compression.ElementarySubmodule
        (p := C.p) S.rho (localMap block Q) C.equiv.symm).subtype
      (PermutationalWreathProduct.Compression.ElementarySubmodule
        (p := C.p) S.rho (localMap block Q) C.equiv.symm).subtype_injective
  letI : Finite (ActualWreathAffineCapacity.E S (localMap block Q) C).quotientRepresentation :=
    inferInstanceAs (Finite (ActualWreathAffineCapacity.E S (localMap block Q) C).V)
  let D := ActualWreathAffineCapacity.refinedCapacityData S (localMap block Q) C
    traceyRefinedInducedModuleInput_proved
    (by simpa only [Fintype.card_eq_nat_card] using block.degrees_ge_two.2) block.base
  let H := (ActualWreathAffineCapacity.jointCapacityInputRefined S
    (localMap block Q) C block.base D).toJointCapacity
      (hpi := QuotientGroup.mk'_surjective (ActualWreathAffineCapacity.K S (localMap block Q)))
  have hd : Module.finrank (ZMod C.p) C.V=4 := by
    simpa only [C,localTranslationChart,chart,PrimitiveAffineProfile.ElementaryChart.d]
      using (Q.degreeSixteen_prime_dimension block.component_preprimitive (origin block) hr).2
  have hcap : H.capacity ≤ (19/10 : ℝ)*Nat.card block.Points := by
    have hb := D.bounds
    change TraceyRefinedInducedCapacityBounds 2
      (Module.finrank (ZMod C.p) C.V) (Fintype.card block.Points) (D.H : ℝ) at hb
    rw [hd,Fintype.card_eq_nat_card] at hb
    exact refined_binary_four_capacity_strict_gap block.degrees_ge_two.2 hs2 hs4 hb
  have hcoeff := ActualWreathAffineCapacity.jointCapacityRefined_coefficient_le
    S (localMap block Q) C block.base D
  have hcoeff' : H.coefficient ≤ (2 : ℝ)^traceyAffineCoefficientExponent
      4 (Nat.card block.Points) (traceyInducedGeneratorCeiling 4 (Nat.card block.Points))
      (traceyPermutationGeneratorCeiling w) w 2 := by
    simpa only [H,hd,Fintype.card_eq_nat_card,S,initialState] using hcoeff
  have hw : w=16*Nat.card block.Points :=
    (width_eq block).trans (congrArg (fun r : ℕ => r*Nat.card block.Points) hr)
  have heven : evenWidth w=w := by
    rw [hw]
    unfold evenWidth halfDegree
    omega
  have hm : preE7CharacterRho*w ≤ ((evenWidth w : ℝ)-(8*Fintype.card block.Points : ℕ))/8-
        Real.logb 2 (elementaryChart block Q).p/(elementaryChart block Q).p*H.capacity := by
    have hprime : (elementaryChart block Q).p=2 := rfl
    rw [hprime]
    norm_num only [Nat.cast_ofNat]
    rw [Real.logb_self_eq_one (by norm_num : (1 : ℝ)<2),heven]
    have hwR : (w : ℝ)=16*(Nat.card block.Points : ℝ) := by exact_mod_cast hw
    simp only [Fintype.card_eq_nat_card,Nat.cast_mul,Nat.cast_ofNat]
    norm_num only [preE7CharacterRho]
    have hsR : (0 : ℝ) ≤ Nat.card block.Points := Nat.cast_nonneg _
    nlinarith
  have hD : ∀ b : ℕ,H.coefficient ≤ (2 : ℝ)^
      (affineComponentWidthCost w+8*(w : ℝ)*Real.logb 2 (b+1)) := by
    intro b
    apply hcoeff'.trans
    rw [←Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (binary_four_translation_coefficient_exponent_le_widthCost
        (Nat.card block.Points) w b block.degrees_ge_two.2 hw)
  exact translationLayerFaithfulComparatorSource block Q H
    (8*Fintype.card block.Points)
    (quotientSixteenEightAction block Q hr)
    (quotientSixteenEightAction_injective block Q hr)
    (by have := block.degrees_ge_two.2; rw [Fintype.card_eq_nat_card]; omega) hm hD

/-- All actual block counts, with the two fixed equality cells handled
without claiming an ordinary margin that they do not satisfy. -/
def sixteenGenericTranslationSource
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre=16) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  by_cases hs2 : Nat.card block.Points=2
  · exact sixteenTwoBlockColdSource block P hTraceyPerm hr hs2
  by_cases hs4 : Nat.card block.Points=4
  · exact sixteenFourBlockColdSource block P hTraceyPerm hr hs4
  exact sixteenGenericTranslationSource_awayFromTwoFour block P hTraceyPerm hr hs2 hs4

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
