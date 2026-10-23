import SymmetricSubgroupAsymptotics.CFSGFFourE6PositiveOrbitFactors
import SymmetricSubgroupAsymptotics.CFSGFFourOrbitCoordinateChart
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedHeightOrbitLifting

/-! The actual singleton/paired positive root factors have exactly the
intrinsic orbit-coordinate classes in their OWN height quotient. This
is the literal bridge needed for coset separation; no full ordered root
normal-form or fixed-quotient lifting hypothesis is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6OrbitFactorHeightClass
open CFSGFFourE6PositiveOrbitFactors CFSGFFourOrbitCoordinateChart
open CFSGTwistedE6GeckHeightRootPermutation CFSGTwistedE6GeckIntrinsicHeightAction
open CFSGTwistedE6GeckHeightQuotientTwist CFSGTwistedE6GeckFixedHeightOrbitLifting
open CFSGTwistedE6GeckSectionRootParameters CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6WeylChamber

local instance heightIndexDecEq (h : ℤ) : DecidableEq (HeightIndex h) := inferInstance

local instance tailNormal (K : Type) [Field K] (h : ℤ) : (TailInPositive K h).Normal :=
  CFSGNormTwoCoordinateRootHeightFiltration.heightTail_normal_in_positive
    CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      CFSGExceptionalCartanPositiveDefinite.E6_positive_definite
        CartanMatrix.E₆_off_diag_nonpos K h

theorem heightRootPermutation_fixed_iff (h : ℤ) (k : HeightIndex h) :
    heightRootPermutation h k=k ↔ diagramRoot k.val.val=k.val.val := by
  constructor
  · intro he
    exact congrArg (fun j : HeightIndex h=>j.val.val) he
  · intro he
    apply Subtype.ext
    apply Subtype.ext
    exact he

def heightOrbitCoordinate (K : Type) [Field K] (h : ℤ) (k : HeightIndex h)
    (x : RootLine K k.val.val) : RootCoordinates K h :=
  orbitCoordinate (fun j : HeightIndex h=>RootLine K j.val.val) (heightRootPermutation h)
    (fun j=>(rootLineTwist K (RingEquiv.refl K) h j).toMonoidHom) (fun j=>j) k x

def coordinateClassHom (K : Type) [Field K] (h : ℤ) (hh : 0<h) :
    RootCoordinates K h→*Quotient K h :=
  (HeightImage K h).subtype.comp (intrinsicCoordinates K h hh).toMonoidHom

def singleCoordinate (K : Type) [Field K] (h : ℤ) (k : HeightIndex h)
    (x : RootLine K k.val.val) : RootCoordinates K h := Pi.mulSingle k x

private theorem map_pair {G C Q : Type*} [Group G] [Group C] [Group Q]
    (f : G→*Q) (e : C→*Q) (a b : G) (x y : C)
    (ha : f a=e x) (hb : f b=e y) : f (a*b)=e (x*y) := by
  rw [map_mul,map_mul,ha,hb]

theorem rootOrbitFactor_mem_tail (K : Type) [Field K] (h : ℤ) (k : HeightIndex h)
    (x : RootLine K k.val.val) : rootOrbitFactor K k.val x∈TailInPositive K h := by
  have h1 : positiveInclusion K k.val x∈TailInPositive K h :=
    rootLinePositive_mem_tail K h k x
  have ht : positiveTwist K (RingEquiv.refl K) (positiveInclusion K k.val x)=
      positiveInclusion K (heightRootPermutation h k).val
        (rootLineTwist K (RingEquiv.refl K) h k x) :=
    rootLinePositive_twist K (RingEquiv.refl K) h k x
  unfold rootOrbitFactor
  split_ifs
  · exact h1
  · apply (TailInPositive K h).mul_mem h1
    rw [ht]
    exact rootLinePositive_mem_tail K h (heightRootPermutation h k)
      (rootLineTwist K (RingEquiv.refl K) h k x)

theorem rootOrbitFactor_heightClass (K : Type) [Field K] (h : ℤ) (hh : 0<h)
    (k : HeightIndex h) (x : RootLine K k.val.val) :
    heightClass K h (rootOrbitFactor K k.val x)=
      (intrinsicCoordinates K h hh (heightOrbitCoordinate K h k x)).val := by
  have h1 : heightClass K h (positiveInclusion K k.val x)=
      (intrinsicCoordinates K h hh (Pi.mulSingle k x)).val := heightClass_single K h hh k x
  have ht : positiveTwist K (RingEquiv.refl K) (positiveInclusion K k.val x)=
      positiveInclusion K (heightRootPermutation h k).val
        (rootLineTwist K (RingEquiv.refl K) h k x) :=
    rootLinePositive_twist K (RingEquiv.refl K) h k x
  have h2 : heightClass K h (positiveInclusion K (heightRootPermutation h k).val
      (rootLineTwist K (RingEquiv.refl K) h k x))=
      (intrinsicCoordinates K h hh (Pi.mulSingle (heightRootPermutation h k)
        (rootLineTwist K (RingEquiv.refl K) h k x))).val :=
    heightClass_single K h hh (heightRootPermutation h k)
      (rootLineTwist K (RingEquiv.refl K) h k x)
  by_cases hk : diagramRoot k.val.val=k.val.val
  · have hp := (heightRootPermutation_fixed_iff h k).mpr hk
    simpa only [rootOrbitFactor,if_pos hk,heightOrbitCoordinate,orbitCoordinate,if_pos hp]
      using h1
  · have hp : heightRootPermutation h k≠k := fun he=>hk
      ((heightRootPermutation_fixed_iff h k).mp he)
    simp only [rootOrbitFactor,if_neg hk,heightOrbitCoordinate,orbitCoordinate,if_neg hp]
    change heightClass K h
        (positiveInclusion K k.val x*positiveTwist K (RingEquiv.refl K) (positiveInclusion K k.val x))=
      coordinateClassHom K h hh (singleCoordinate K h k x * singleCoordinate K h (heightRootPermutation h k)
        (rootLineTwist K (RingEquiv.refl K) h k x))
    have h1' : heightClass K h (positiveInclusion K k.val x)=
        coordinateClassHom K h hh (singleCoordinate K h k x) := h1
    have h2' : heightClass K h (positiveInclusion K (heightRootPermutation h k).val
        (rootLineTwist K (RingEquiv.refl K) h k x))=
        coordinateClassHom K h hh (singleCoordinate K h (heightRootPermutation h k)
          (rootLineTwist K (RingEquiv.refl K) h k x)) := h2
    exact map_pair (heightClass K h) (coordinateClassHom K h hh)
      (positiveInclusion K k.val x)
      (positiveTwist K (RingEquiv.refl K) (positiveInclusion K k.val x))
      (singleCoordinate K h k x) (singleCoordinate K h (heightRootPermutation h k)
        (rootLineTwist K (RingEquiv.refl K) h k x))
      h1' ((congrArg (heightClass K h) ht).trans h2')

end SymmetricSubgroupAsymptotics.CFSGFFourE6OrbitFactorHeightClass
