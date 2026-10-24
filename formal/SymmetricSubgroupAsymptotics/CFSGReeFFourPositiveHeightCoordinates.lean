import SymmetricSubgroupAsymptotics.CFSGE6GeckHeightCoordinateHom
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedPositiveFamilies
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedPositiveSourceImage

/-! The full actual ReeF4 positive subgroup inherits the genuine ambient
E6 height filtration and exact coordinate homomorphisms. This uses its
literal injective raw homomorphism, with no recognition by four simple
coordinates and no fixed-coordinate section lifting. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourPositiveHeightCoordinates
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedPositiveFamilies CFSGFFourOriginalMiddleWords
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6GeckHeightQuotientTwist
open CFSGNormTwoCoordinateExactHeightLayer CFSGNormTwoCoordinateRootHeightBound
local notation "A" => CartanMatrix.E₆
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _

def positiveRawHom (m : ℕ) : fixedPositive m→*Positive (Field m) :=
  ((fixedRawHom m).comp (fixedPositive m).subtype).codRestrict (Positive (Field m))
    (fun g=>g.property)

theorem positiveRawHom_injective (m : ℕ) : Function.Injective (positiveRawHom m) := by
  intro x y he
  apply Subtype.ext
  apply Subtype.ext
  apply rawHom_injective (Field m)
  exact congrArg (fun z : Positive (Field m)=>z.val) he

def tail (m : ℕ) (h : ℤ) : Subgroup (fixedPositive m) :=
  (TailInPositive (Field m) h).comap (positiveRawHom m)

def toAmbientTail (m : ℕ) (h : ℤ) : tail m h→*TailInPositive (Field m) h :=
  ((positiveRawHom m).comp (tail m h).subtype).codRestrict
    (TailInPositive (Field m) h) (fun u=>u.property)

def coordinateHom (m : ℕ) (h : ℤ) (hh : 0<h) :
    tail m h→*Multiplicative (ExactHeightRoot A h→Field m) :=
  (CFSGE6GeckHeightCoordinateHom.coordinateHom (Field m) h hh).comp (toAmbientTail m h)

theorem coordinateHom_kernel_le (m : ℕ) (h : ℤ) (hh : 0<h) :
    (coordinateHom m h hh).ker≤(tail m (h+1)).comap (tail m h).subtype := by
  intro u hu
  have ha : CFSGE6GeckHeightCoordinateHom.coordinateHom (Field m) h hh (toAmbientTail m h u)=1 := hu
  exact (CFSGE6GeckHeightCoordinateHom.coordinateHom_eq_one_iff (Field m) h hh _).mp ha

theorem first_tail_eq_top (m : ℕ) : tail m 1=⊤ := by
  rw [tail,CFSGTwistedE6GeckFixedPositiveSourceImage.first_tail_eq_top]
  exact Subgroup.comap_top (positiveRawHom m)

theorem terminal_tail_eq_bot (m : ℕ) :
    tail m ((rootHeightBound A : ℤ)+1)=⊥ := by
  rw [tail,CFSGTwistedE6GeckFixedPositiveSourceImage.terminal_tail_eq_bot]
  exact (positiveRawHom m).ker_eq_bot_iff.mpr (positiveRawHom_injective m)

end SymmetricSubgroupAsymptotics.CFSGReeFFourPositiveHeightCoordinates
