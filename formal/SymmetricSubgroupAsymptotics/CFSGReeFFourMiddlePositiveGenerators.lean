import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddlePositiveSubgroup

/-! Each of the four literal middle factor families belongs to the
ordinary middle positive subgroup, with the other coordinates zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddlePositiveGenerators
open CFSGReeFFourMiddlePositiveSubgroup CFSGReeFFourMiddleWordInjective
open CFSGReeFFourFieldParameters CFSGE6GeckMiddleFactorInjective
open CFSGE6GeckMiddleHigherLeading CFSGE6GeckMiddleAThreeCollecting
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6GeckDiagramCovariance
open CFSGExceptionalCartanPositiveDefinite CFSGNormTwoCoordinateLeadingHom
open CFSGSerreQuadraticMatrix CFSGNormTwoRootPairing
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local instance : DecidableEq (Roots A) := Classical.decEq _

private abbrev simpleMiddle (K : Type) [Field K] (t : K) : Positive K :=
  positiveRoot A hd hs hp ho K 3 t

private theorem pair_zero (m : ℕ) : pairedPositive (Field m) (RingEquiv.refl (Field m)) 0=1 := by
  apply Subtype.ext
  change canonicalRoot rawData (Field m) false 2 0 *
    canonicalRoot rawData (Field m) false 4 0 = 1
  rw [canonicalRoot_zero,canonicalRoot_zero,mul_one]

private theorem simple_zero (m : ℕ) : positiveRoot A hd hs hp ho (Field m) 3 0=1 :=
  Subtype.ext (canonicalRoot_zero rawData (Field m) false 3)

private theorem high_zero (m : ℕ) : higherPositive (Field m) 0=1 := by
  apply Subtype.ext
  change highestMiddle (Field m) 0=1
  simp only [highestMiddle,canonicalRoot_zero,mul_one,mul_inv_cancel]

private theorem paired_high_zero (m : ℕ) : pairedHigherPositive (Field m) 0=1 := by
  apply Subtype.ext
  change middlePair (Field m) (RingEquiv.refl (Field m)) 0=1
  change canonicalWeyl rawData (Field m) 3 *
    (canonicalRoot rawData (Field m) false 2 0 * canonicalRoot rawData (Field m) false 4 0) *
    (canonicalWeyl rawData (Field m) 3)⁻¹=1
  rw [canonicalRoot_zero,canonicalRoot_zero,mul_one,mul_one,mul_inv_cancel]

private theorem four_factors_mem {G T : Type*} [Group G] [Zero T] (S : Subgroup G)
    (a b c d : T → G) (hza : a 0=1) (hzb : b 0=1) (hzc : c 0=1) (hzd : d 0=1)
    (hw : ∀ r s t u, a r * b s * c t * d u ∈ S) :
    (∀ r,a r∈S) ∧ (∀ s,b s∈S) ∧ (∀ t,c t∈S) ∧ (∀ u,d u∈S) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro r
    simpa only [hzb,hzc,hzd,mul_one] using hw r 0 0 0
  · intro s
    simpa only [hza,hzc,hzd,one_mul,mul_one] using hw 0 s 0 0
  · intro t
    simpa only [hza,hzb,hzd,one_mul,mul_one] using hw 0 0 t 0
  · intro u
    simpa only [hza,hzb,hzc,one_mul] using hw 0 0 0 u

private def firstFactor (m : ℕ) (a : Field m) : Positive (Field m) :=
  pairedPositive (Field m) (RingEquiv.refl (Field m)) a
private def secondFactor (m : ℕ) (b : Field m) : Positive (Field m) := simpleMiddle (Field m) b
private def thirdFactor (m : ℕ) (d : Field m) : Positive (Field m) := higherPositive (Field m) d
private def fourthFactor (m : ℕ) (c : Field m) : Positive (Field m) := pairedHigherPositive (Field m) c

private theorem factors_word (m : ℕ) (a b d c : Field m) :
    firstFactor m a * secondFactor m b * thirdFactor m d * fourthFactor m c =
      matrixMiddleWord (Field m) a b c d := rfl

private theorem all_factors_mem (m : ℕ) :
    (∀ a,firstFactor m a∈middlePositiveSubgroup m) ∧
    (∀ b,secondFactor m b∈middlePositiveSubgroup m) ∧
    (∀ d,thirdFactor m d∈middlePositiveSubgroup m) ∧
    (∀ c,fourthFactor m c∈middlePositiveSubgroup m) := by
  apply four_factors_mem (middlePositiveSubgroup m)
    (firstFactor m) (secondFactor m) (thirdFactor m) (fourthFactor m)
    (pair_zero m) (simple_zero m) (high_zero m) (paired_high_zero m)
  intro a b d c
  rw [factors_word]
  exact matrixMiddleWord_mem m a b c d

theorem pairedPositive_mem (m : ℕ) (a : Field m) :
    pairedPositive (Field m) (RingEquiv.refl (Field m)) a ∈ middlePositiveSubgroup m :=
  (all_factors_mem m).1 a

theorem simplePositive_mem (m : ℕ) (b : Field m) :
    positiveRoot A hd hs hp ho (Field m) 3 b ∈ middlePositiveSubgroup m :=
  (all_factors_mem m).2.1 b

theorem higherPositive_mem (m : ℕ) (d : Field m) :
    higherPositive (Field m) d ∈ middlePositiveSubgroup m :=
  (all_factors_mem m).2.2.1 d

theorem pairedHigherPositive_mem (m : ℕ) (c : Field m) :
    pairedHigherPositive (Field m) c ∈ middlePositiveSubgroup m :=
  (all_factors_mem m).2.2.2 c

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddlePositiveGenerators
