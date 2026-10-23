import SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleRootDegrees
import SymmetricSubgroupAsymptotics.CFSGGradedQuadraticFirstLayer
import SymmetricSubgroupAsymptotics.CFSGE6GeckSignedSimpleParameters
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLeadingHom
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckAdjacentCartanSign

/-! The paired parameter in the actual middle A3 product is unique.
Conjugation by W3 puts it back in the two original simple coordinates;
the other factor has integer height three and has zero first layer.
Arbitrary first-factor parameters and arbitrary coefficient automorphisms
are retained, with no fixed-field or characteristic restriction. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleFactorInjective
open CFSGE6GeckMiddleRootDegrees CFSGE6GeckMiddleAThreeCollecting
open CFSGE6GeckSignedSimpleParameters CFSGTwistedE6GeckDiagramCovariance
open CFSGTwistedE6GeckPositiveTwist CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGNormTwoCoordinateLeadingHom
open CFSGNormTwoCoordinateLeadingFactor CFSGNormTwoCoordinateHeight
open CFSGNormTwoGeckHeightSupport CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoCoordinateWeylRootMembership
open CFSGGradedMatrixGroupFirstLayer CFSGGradedQuadraticFirstLayer
open CFSGNormTwoGeckAdjacentCartanSign CFSGSerreQuadraticMatrix
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local notation "W" => canonicalWeyl rawData

def reflectedHighest (K : Type) [Field K] (r : K) : Positive K :=
  ⟨W K 3 * highestMiddle K r * (W K 3)⁻¹, reflected_highestMiddle_mem_positive K r⟩

private theorem reflectedHighest_eq_word (K : Type) [Field K] (r : K) :
    (reflectedHighest K r).val = rootWord A hd hs hp ho K [3, 2, 4] 3 r := by
  change W K 3 * ((W K 2 * W K 4) * canonicalRoot rawData K false 3 r *
      (W K 2 * W K 4)⁻¹) * (W K 3)⁻¹ =
    (W K 3 * (W K 2 * (W K 4 * 1))) * canonicalRoot rawData K false 3 r *
      (W K 3 * (W K 2 * (W K 4 * 1)))⁻¹
  group

theorem reflectedHighest_firstLayer_zero (K : Type) [Field K] (r : K) :
    firstLayer (weight A hs hp E6Base coordinateHeight) (reflectedHighest K r).val = 0 := by
  have hg := word_conjugate_quadraticGrade A hs hp E6Base E6Index K [3, 2, 4] 3 r
  have ht : 1 < coordinateHeight
      (wordRoot A hs hp E6Base E6Index [3, 2, 4] (E6Index 3)).val := by
    rw [reflected_highest_root_degree]
    decide
  have hz := firstLayer_eq_zero_of_height_gt_one (latticeWeight A hs hp E6Base)
    coordinateHeight.toAddMonoidHom _ _ hg ht
  have hw : (coordinateHeight.toAddMonoidHom ∘ latticeWeight A hs hp E6Base) =
      weight A hs hp E6Base coordinateHeight := by
    funext i
    cases i <;> simp [latticeWeight, weight, Function.comp_apply]
  rw [hw] at hz
  change firstLayer (weight A hs hp E6Base coordinateHeight)
    (rootWord A hd hs hp ho K [3, 2, 4] 3 r) = 0 at hz
  rwa [← reflectedHighest_eq_word] at hz

def ambientLeading (K : Type) [Field K] : Positive K →* Multiplicative (Fin 6 → K) :=
  leadingHom A hd hs hp ho K

theorem reflectedHighest_leading_one (K : Type) [Field K] (r : K) :
    ambientLeading K (reflectedHighest K r) = 1 := by
  change leadingCoordinates A hd hs hp ho K (reflectedHighest K r).val = 0
  funext i
  rw [← firstLayer_entry A hd hs hp ho K (reflectedHighest K r).val i]
  change firstLayer (weight A hs hp E6Base coordinateHeight) (reflectedHighest K r).val
    (Sum.inl (E6Index i))
    (Sum.inr (CFSGNormTwoGeckColumns.negativeIndex A hs hp (E6Index i))) = 0
  rw [reflectedHighest_firstLayer_zero]
  rfl

def pairedPositive (K : Type) [Field K] (sigma : K ≃+* K) (s : K) : Positive K :=
  positiveRoot A hd hs hp ho K 2 s * positiveRoot A hd hs hp ho K 4 (sigma s)

theorem pairedPositive_val (K : Type) [Field K] (sigma : K ≃+* K) (s : K) :
    (pairedPositive K sigma s).val = rawPairedHom K sigma false 1 (Multiplicative.ofAdd s) := rfl

theorem pairedPositive_leading_two (K : Type) [Field K] (sigma : K ≃+* K) (s : K) :
    (ambientLeading K (pairedPositive K sigma s)).toAdd 2 = s := by
  change (leadingHom A hd hs hp ho K
    (positiveRoot A hd hs hp ho K 2 s * positiveRoot A hd hs hp ho K 4 (sigma s))).toAdd 2 = s
  rw [map_mul, leadingHom_positiveRoot, leadingHom_positiveRoot]
  change (((Pi.single 2 s : Fin 6 → K) + (Pi.single 4 (sigma s) : Fin 6 → K)) : Fin 6 → K) 2 = s
  simp [Pi.single_apply]

private theorem square_conjugates_simple (K : Type) [Field K] (j : Fin 6)
    (hj : CFSGGeckSerreRepresentation.cartan E6Base E6Index j 3 = -1) (s : K) :
    (W K 3) ^ 2 * canonicalRoot rawData K false j s * ((W K 3) ^ 2)⁻¹ =
      canonicalRoot rawData K false j (-s) := by
  have h : (W K 3) ^ 2 * canonicalRoot rawData K false j s =
      canonicalRoot rawData K false j (-s) * (W K 3) ^ 2 :=
    adjacent_cartan_square_sign A hs hp E6Base E6Index 3 j hj K false s
  rw [h, mul_assoc, mul_inv_cancel, mul_one]

theorem square_conjugates_pair (K : Type) [Field K] (sigma : K ≃+* K) (s : K) :
    (W K 3) ^ 2 * rawPairedHom K sigma false 1 (Multiplicative.ofAdd s) * ((W K 3) ^ 2)⁻¹ =
      rawPairedHom K sigma false 1 (Multiplicative.ofAdd (-s)) := by
  let e := MulAut.conj ((W K 3) ^ 2)
  change e (canonicalRoot rawData K false 2 s * canonicalRoot rawData K false 4 (sigma s)) =
    canonicalRoot rawData K false 2 (-s) * canonicalRoot rawData K false 4 (sigma (-s))
  rw [map_mul, map_neg]
  exact congrArg₂ (· * ·)
    (square_conjugates_simple K 2 (by rw [E6_cartan]; decide) s)
    (square_conjugates_simple K 4 (by rw [E6_cartan]; decide) (sigma s))

def middlePair (K : Type) [Field K] (sigma : K ≃+* K) (s : K) :
    (Matrix GeckIndex GeckIndex K)ˣ :=
  W K 3 * rawPairedHom K sigma false 1 (Multiplicative.ofAdd s) * (W K 3)⁻¹

private theorem reflected_middlePair (K : Type) [Field K] (sigma : K ≃+* K) (s : K) :
    (MulAut.conj (W K 3)) (middlePair K sigma s) = (pairedPositive K sigma (-s)).val := by
  rw [pairedPositive_val]
  calc
    _ = (W K 3) ^ 2 * rawPairedHom K sigma false 1 (Multiplicative.ofAdd s) *
        ((W K 3) ^ 2)⁻¹ := by dsimp only [middlePair, MulAut.conj_apply]; rw [pow_two]; group
    _ = _ := square_conjugates_pair K sigma s

theorem middleFactor_snd_eq (K : Type) [Field K] (sigma : K ≃+* K)
    (r r' s s' : K)
    (he : highestMiddle K r * middlePair K sigma s = highestMiddle K r' * middlePair K sigma s') :
    s = s' := by
  have hh := congrArg (MulAut.conj (W K 3)) he
  rw [map_mul, map_mul, reflected_middlePair, reflected_middlePair] at hh
  have hpositive : reflectedHighest K r * pairedPositive K sigma (-s) =
      reflectedHighest K r' * pairedPositive K sigma (-s') := Subtype.ext hh
  have hl := congrArg (ambientLeading K) hpositive
  rw [map_mul, map_mul, reflectedHighest_leading_one, reflectedHighest_leading_one,
    one_mul, one_mul] at hl
  have htwo := congrArg (fun x : Multiplicative (Fin 6 → K) => x.toAdd 2) hl
  dsimp only at htwo
  rw [pairedPositive_leading_two, pairedPositive_leading_two] at htwo
  exact neg_inj.mp htwo

theorem middlePair_mem_positive (K : Type) [Field K] (sigma : K ≃+* K) (s : K) :
    middlePair K sigma s ∈ Positive K := by
  have h2 := positive_word_mem A hd hs hp ho K [3] 2 s (by
    change ∀ i, 0 ≤ (wordRoot A hs hp E6Base E6Index [3] (E6Index 2)).val i
    rw [paired_first_degree]
    intro i
    fin_cases i <;> decide)
  have h4 := positive_word_mem A hd hs hp ho K [3] 4 (sigma s) (by
    change ∀ i, 0 ≤ (wordRoot A hs hp E6Base E6Index [3] (E6Index 4)).val i
    rw [paired_second_degree]
    intro i
    fin_cases i <;> decide)
  have hm := (Positive K).mul_mem h2 h4
  have he : rootWord A hd hs hp ho K [3] 2 s * rootWord A hd hs hp ho K [3] 4 (sigma s) =
      middlePair K sigma s := by
    change ((W K 3 * 1) * canonicalRoot rawData K false 2 s * (W K 3 * 1)⁻¹) *
      ((W K 3 * 1) * canonicalRoot rawData K false 4 (sigma s) * (W K 3 * 1)⁻¹) =
      W K 3 * (canonicalRoot rawData K false 2 s * canonicalRoot rawData K false 4 (sigma s)) *
        (W K 3)⁻¹
    group
  exact he ▸ hm

end SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleFactorInjective
