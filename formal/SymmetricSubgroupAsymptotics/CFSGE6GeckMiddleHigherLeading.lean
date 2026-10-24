import SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleFactorInjective
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveWordLeadingZero

/-! Both literal higher middle factors have trivial actual simple leading
coordinates. The heights are the original integers three and two, before
any reduction to a field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleHigherLeading
open CFSGE6GeckMiddleAThreeCollecting CFSGE6GeckMiddleFactorInjective
open CFSGE6GeckMiddleRootDegrees CFSGTwistedE6GeckDiagramCovariance
open CFSGTwistedE6GeckPositiveTwist CFSGNormTwoRootPairing
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoCoordinatePositiveWordLeadingZero CFSGNormTwoCoordinateLeadingHom
open CFSGNormTwoCoordinateHeight CFSGNormTwoGeckWeylWordDegree CFSGSerreQuadraticMatrix
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local instance : DecidableEq (Roots A) := Classical.decEq _

private theorem high_nonnegative :
    ∀i,0≤(wordRoot A hs hp E6Base E6Index [2,4] (E6Index 3)).val i := by
  rw [highest_root_degree]
  intro i
  fin_cases i <;> decide

private theorem first_nonnegative :
    ∀i,0≤(wordRoot A hs hp E6Base E6Index [3] (E6Index 2)).val i := by
  rw [paired_first_degree]
  intro i
  fin_cases i <;> decide

private theorem second_nonnegative :
    ∀i,0≤(wordRoot A hs hp E6Base E6Index [3] (E6Index 4)).val i := by
  rw [paired_second_degree]
  intro i
  fin_cases i <;> decide

def higherPositive (K : Type) [Field K] (r : K) : Positive K :=
  ⟨highestMiddle K r,highestMiddle_mem_positive K r⟩

def pairedHigherPositive (K : Type) [Field K] (s : K) : Positive K :=
  ⟨middlePair K (RingEquiv.refl K) s,middlePair_mem_positive K (RingEquiv.refl K) s⟩

theorem higherPositive_val (K : Type) [Field K] (r : K) :
    (higherPositive K r).val=highestMiddle K r := rfl

theorem pairedHigherPositive_val (K : Type) [Field K] (s : K) :
    (pairedHigherPositive K s).val=middlePair K (RingEquiv.refl K) s := rfl

theorem higherPositive_leading_one (K : Type) [Field K] (r : K) :
    ambientLeading K (higherPositive K r)=1 := by
  have he : higherPositive K r=positiveWord A hd hs hp ho K [2,4] 3 r high_nonnegative := by
    apply Subtype.ext
    change highestMiddle K r=(canonicalWeyl rawData K 2*(canonicalWeyl rawData K 4*1))*
      canonicalRoot rawData K false 3 r*(canonicalWeyl rawData K 2*(canonicalWeyl rawData K 4*1))⁻¹
    simp only [mul_one,highestMiddle]
  change CFSGNormTwoCoordinateLeadingHom.leadingHom A hd hs hp ho K (higherPositive K r)=1
  rw [he]
  apply leadingHom_positiveWord
  change 1<coordinateHeight (wordRoot A hs hp E6Base E6Index [2,4] (E6Index 3)).val
  rw [highest_root_degree]
  decide

theorem pairedHigherPositive_leading_one (K : Type) [Field K] (s : K) :
    ambientLeading K (pairedHigherPositive K s)=1 := by
  have he : pairedHigherPositive K s=
      positiveWord A hd hs hp ho K [3] 2 s first_nonnegative*
      positiveWord A hd hs hp ho K [3] 4 s second_nonnegative := by
    apply Subtype.ext
    change canonicalWeyl rawData K 3*
      (canonicalRoot rawData K false 2 s*canonicalRoot rawData K false 4 s)*
      (canonicalWeyl rawData K 3)⁻¹=
      ((canonicalWeyl rawData K 3*1)*canonicalRoot rawData K false 2 s*
        (canonicalWeyl rawData K 3*1)⁻¹)*
      ((canonicalWeyl rawData K 3*1)*canonicalRoot rawData K false 4 s*
        (canonicalWeyl rawData K 3*1)⁻¹)
    group
  change CFSGNormTwoCoordinateLeadingHom.leadingHom A hd hs hp ho K (pairedHigherPositive K s)=1
  rw [he,map_mul]
  have h2 := leadingHom_positiveWord A hd hs hp ho K [3] 2 s first_nonnegative (by
    change 1<coordinateHeight (wordRoot A hs hp E6Base E6Index [3] (E6Index 2)).val
    rw [paired_first_degree]
    decide)
  have h4 := leadingHom_positiveWord A hd hs hp ho K [3] 4 s second_nonnegative (by
    change 1<coordinateHeight (wordRoot A hs hp E6Base E6Index [3] (E6Index 4)).val
    rw [paired_second_degree]
    decide)
  rw [h2,h4,mul_one]

end SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleHigherLeading
