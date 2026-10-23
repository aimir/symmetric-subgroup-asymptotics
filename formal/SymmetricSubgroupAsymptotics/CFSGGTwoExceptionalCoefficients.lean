import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalMatrixCoordinates
import SymmetricSubgroupAsymptotics.CFSGGTwoIntegralRealization

/-! Constant matrix coefficients for the exceptional G2 quotient route.
The column map is integral and sourceOperator is the actual quadratic
realization of the ORIGINAL divided-power operator. targetOperator records
the long/short exchange, with the short third power becoming a long first
power. No covariance table or exceptional automorphism is assumed here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGGTwoExceptionalCoefficients
open CFSGGTwoSerreMatrices CFSGIntegralQuadraticRootOperators
variable (R : Type*) [CommRing R]

def column (M : Mat R) : Index → R :=
  Sum.elim (fun i => match i.val with
    | 0 => -M (pos 0) (neg 1)
    | 1 => -M (pos 0) (neg 2)
    | 2 => M (pos 1) (pos 2)
    | _ => -(M (pos 1) (pos 1)+M (pos 0) (pos 0)))
    (fun i => match i.val with
    | 0 => M (neg 0) (pos 1)
    | 1 => M (neg 0) (pos 2)
    | 2 => M (pos 2) (pos 1)
    | _ => -(M (pos 1) (pos 1)+M (pos 0) (pos 0)))

def sourceOperator (neg : Bool) (i : Fin 2) (k : Fin 4) (M : Mat R) : Mat R :=
  operator R (rootMatrix R neg i) (rootSecond R neg i) k.val M

def targetOperator (neg : Bool) (i : Fin 2) (k : Fin 4) (v : Index → R) : Index → R :=
  if i=0 then match k.val with
    | 0 => v
    | 3 => rootMatrix R neg 1 *ᵥ v
    | _ => 0
  else match k.val with
    | 0 => v
    | 1 => rootMatrix R neg 0 *ᵥ v
    | 2 => rootSecond R neg 0 *ᵥ v
    | _ => 0

theorem column_map {S : Type*} [CommRing S] (f : R →+* S) (M : Mat R) :
    column S (f.mapMatrix M)=fun i => f (column R M i) := by
  funext i
  rcases i with j|j <;> fin_cases j
  · change -f (M (pos 0) (neg 1))=f (-M (pos 0) (neg 1))
    exact (map_neg f _).symm
  · change -f (M (pos 0) (neg 2))=f (-M (pos 0) (neg 2))
    exact (map_neg f _).symm
  · rfl
  · change -(f (M (pos 1) (pos 1))+f (M (pos 0) (pos 0)))=
      f (-(M (pos 1) (pos 1)+M (pos 0) (pos 0)))
    rw [map_neg,map_add]
  · rfl
  · rfl
  · rfl
  · change -(f (M (pos 1) (pos 1))+f (M (pos 0) (pos 0)))=
      f (-(M (pos 1) (pos 1)+M (pos 0) (pos 0)))
    rw [map_neg,map_add]

theorem map_rootMatrix {S : Type*} [CommRing S] (f : R →+* S) (neg : Bool) (i : Fin 2) :
    f.mapMatrix (rootMatrix R neg i)=rootMatrix S neg i := by
  cases neg
  · exact map_positive R f i
  · exact map_negative R f i

theorem map_rootSecond {S : Type*} [CommRing S] (f : R →+* S) (neg : Bool) (i : Fin 2) :
    f.mapMatrix (rootSecond R neg i)=rootSecond S neg i := by
  cases neg
  · exact map_positiveSecond R f i
  · exact map_negativeSecond R f i

theorem sourceOperator_map {S : Type*} [CommRing S] (f : R →+* S)
    (neg : Bool) (i : Fin 2) (k : Fin 4) (M : Mat R) :
    f.mapMatrix (sourceOperator R neg i k M)=sourceOperator S neg i k (f.mapMatrix M) := by
  fin_cases k <;>
    simp only [sourceOperator,operator_zero,operator_one,operator_two,operator_three,
      map_add,map_sub,map_mul,map_rootMatrix,map_rootSecond]

theorem targetOperator_map {S : Type*} [CommRing S] (f : R →+* S)
    (neg : Bool) (i : Fin 2) (k : Fin 4) (v : Index → R) :
    targetOperator S neg i k (fun j => f (v j))=fun j => f (targetOperator R neg i k v j) := by
  fin_cases i <;> fin_cases k
  · rfl
  · funext j; exact (map_zero f).symm
  · funext j; exact (map_zero f).symm
  · change rootMatrix S neg 1 *ᵥ (fun j => f (v j))=
      fun j => f ((rootMatrix R neg 1 *ᵥ v) j)
    rw [←map_rootMatrix R f neg 1]
    funext j
    exact (RingHom.map_mulVec f (rootMatrix R neg 1) v j).symm
  · rfl
  · change rootMatrix S neg 0 *ᵥ (fun j => f (v j))=
      fun j => f ((rootMatrix R neg 0 *ᵥ v) j)
    rw [←map_rootMatrix R f neg 0]
    funext j
    exact (RingHom.map_mulVec f (rootMatrix R neg 0) v j).symm
  · change rootSecond S neg 0 *ᵥ (fun j => f (v j))=
      fun j => f ((rootSecond R neg 0 *ᵥ v) j)
    rw [←map_rootSecond R f neg 0]
    funext j
    exact (RingHom.map_mulVec f (rootSecond R neg 0) v j).symm
  · funext j; exact (map_zero f).symm

end SymmetricSubgroupAsymptotics.CFSGGTwoExceptionalCoefficients
