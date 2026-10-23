import SymmetricSubgroupAsymptotics.CFSGGTwoPositiveRootMatrices
import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalExceptionalRootCovariance

/-! Exact signs for the six exceptional positive directions. Reflected
Weyl words use the other inverses; the 2/4 exchange consequently has a
minus sign. Separate integral constant certificates prove these signs
before ring-hom transport. No fixed-U assertion is supplied as data. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoExceptionalPositiveDirections
open CFSGGTwoSerreMatrices CFSGGTwoShortWeylMatrices CFSGGTwoPositiveDirections
open CFSGGTwoPositiveWordCoordinates CFSGGTwoPositiveRootMatrices
open CFSGGTwoOriginalExceptionalRootCovariance
variable (R : Type*) [CommRing R]

def exchangedDirection (j : Fin 6) : Fin 6 :=
  match j.val with
  | 0 => 1
  | 1 => 0
  | 2 => 4
  | 3 => 5
  | 4 => 2
  | _ => 3

def signedParameter (j : Fin 6) (t : R) : R := if j.val=2 ∨ j.val=4 then -t else t

def reflectedUnit (j : Fin 6) : (Mat R)ˣ :=
  match j.val with
  | 0 => 1
  | 1 => 1
  | 2 => (shortWeyl R)⁻¹
  | 3 => (longWeyl R)⁻¹ * (shortWeyl R)⁻¹
  | 4 => (longWeyl R)⁻¹
  | _ => (shortWeyl R)⁻¹ * (longWeyl R)⁻¹

def reflectedLinear (j : Fin 6) : Mat R :=
  (reflectedUnit R j : Mat R)*positive R (exchangedNode (rootNode j))*
    (↑((reflectedUnit R j)⁻¹):Mat R)

def reflectedQuadratic (j : Fin 6) : Mat R :=
  (reflectedUnit R j : Mat R)*positiveSecond R (exchangedNode (rootNode j))*
    (↑((reflectedUnit R j)⁻¹):Mat R)

def signedLinear (j : Fin 6) : Mat R :=
  if j.val=2 ∨ j.val=4 then -positiveLinear R (exchangedDirection j)
  else positiveLinear R (exchangedDirection j)

def reflectedRoot (j : Fin 6) (t : R) : (Mat R)ˣ :=
  reflectedUnit R j * rootTransvection R false (exchangedNode (rootNode j)) t *
    (reflectedUnit R j)⁻¹

theorem map_reflectedUnit {S : Type*} [CommRing S] (f : R →+* S) (j : Fin 6) :
    Units.map f.mapMatrix.toMonoidHom (reflectedUnit R j)=reflectedUnit S j := by
  fin_cases j <;>
    simp only [reflectedUnit,map_one,map_mul,map_inv,map_shortWeyl,map_longWeyl]

theorem map_reflectedLinear {S : Type*} [CommRing S] (f : R →+* S) (j : Fin 6) :
    f.mapMatrix (reflectedLinear R j)=reflectedLinear S j := by
  have hg := congrArg (fun u : (Mat S)ˣ => (u:Mat S)) (map_reflectedUnit R f j)
  change f.mapMatrix (reflectedUnit R j : Mat R)=(reflectedUnit S j : Mat S) at hg
  have hi := congrArg (fun u : (Mat S)ˣ => (↑(u⁻¹):Mat S)) (map_reflectedUnit R f j)
  change f.mapMatrix (↑((reflectedUnit R j)⁻¹):Mat R)=
    (↑((reflectedUnit S j)⁻¹):Mat S) at hi
  change f.mapMatrix ((reflectedUnit R j : Mat R)*positive R (exchangedNode (rootNode j))*
      (↑((reflectedUnit R j)⁻¹):Mat R))=_
  rw [map_mul,map_mul,hg,hi,map_positive]
  rfl

theorem map_reflectedQuadratic {S : Type*} [CommRing S] (f : R →+* S) (j : Fin 6) :
    f.mapMatrix (reflectedQuadratic R j)=reflectedQuadratic S j := by
  have hg := congrArg (fun u : (Mat S)ˣ => (u:Mat S)) (map_reflectedUnit R f j)
  change f.mapMatrix (reflectedUnit R j : Mat R)=(reflectedUnit S j : Mat S) at hg
  have hi := congrArg (fun u : (Mat S)ˣ => (↑(u⁻¹):Mat S)) (map_reflectedUnit R f j)
  change f.mapMatrix (↑((reflectedUnit R j)⁻¹):Mat R)=
    (↑((reflectedUnit S j)⁻¹):Mat S) at hi
  change f.mapMatrix ((reflectedUnit R j : Mat R)*positiveSecond R (exchangedNode (rootNode j))*
      (↑((reflectedUnit R j)⁻¹):Mat R))=_
  rw [map_mul,map_mul,hg,hi,map_positiveSecond]
  rfl

theorem map_signedLinear {S : Type*} [CommRing S] (f : R →+* S) (j : Fin 6) :
    f.mapMatrix (signedLinear R j)=signedLinear S j := by
  by_cases h : j.val=2 ∨ j.val=4
  · simp only [signedLinear,if_pos h,map_neg,map_positiveLinear]
  · simp only [signedLinear,if_neg h,map_positiveLinear]

private theorem integer_linear_0 : reflectedLinear ℤ 0=signedLinear ℤ 0 := by
  decide +kernel

private theorem integer_quadratic_0 :
    reflectedQuadratic ℤ 0=positiveQuadratic ℤ (exchangedDirection 0) := by
  decide +kernel

private theorem integer_linear_1 : reflectedLinear ℤ 1=signedLinear ℤ 1 := by
  decide +kernel

private theorem integer_quadratic_1 :
    reflectedQuadratic ℤ 1=positiveQuadratic ℤ (exchangedDirection 1) := by
  decide +kernel

private theorem integer_linear_2 : reflectedLinear ℤ 2=signedLinear ℤ 2 := by
  decide +kernel

private theorem integer_quadratic_2 :
    reflectedQuadratic ℤ 2=positiveQuadratic ℤ (exchangedDirection 2) := by
  decide +kernel

private theorem integer_linear_3 : reflectedLinear ℤ 3=signedLinear ℤ 3 := by
  decide +kernel

private theorem integer_quadratic_3 :
    reflectedQuadratic ℤ 3=positiveQuadratic ℤ (exchangedDirection 3) := by
  decide +kernel

private theorem integer_linear_4 : reflectedLinear ℤ 4=signedLinear ℤ 4 := by
  decide +kernel

private theorem integer_quadratic_4 :
    reflectedQuadratic ℤ 4=positiveQuadratic ℤ (exchangedDirection 4) := by
  decide +kernel

private theorem integer_linear_5 : reflectedLinear ℤ 5=signedLinear ℤ 5 := by
  decide +kernel

private theorem integer_quadratic_5 :
    reflectedQuadratic ℤ 5=positiveQuadratic ℤ (exchangedDirection 5) := by
  decide +kernel

private theorem integer_linear (j : Fin 6) : reflectedLinear ℤ j=signedLinear ℤ j := by
  fin_cases j
  · exact integer_linear_0
  · exact integer_linear_1
  · exact integer_linear_2
  · exact integer_linear_3
  · exact integer_linear_4
  · exact integer_linear_5

private theorem integer_quadratic (j : Fin 6) :
    reflectedQuadratic ℤ j=positiveQuadratic ℤ (exchangedDirection j) := by
  fin_cases j
  · exact integer_quadratic_0
  · exact integer_quadratic_1
  · exact integer_quadratic_2
  · exact integer_quadratic_3
  · exact integer_quadratic_4
  · exact integer_quadratic_5

theorem reflectedLinear_eq (j : Fin 6) : reflectedLinear R j=signedLinear R j := by
  let f : ℤ →+* R := Int.castRingHom R
  calc
    _=f.mapMatrix (reflectedLinear ℤ j) := (map_reflectedLinear ℤ f j).symm
    _=f.mapMatrix (signedLinear ℤ j) := congrArg f.mapMatrix (integer_linear j)
    _=signedLinear R j := map_signedLinear ℤ f j

theorem reflectedQuadratic_eq (j : Fin 6) :
    reflectedQuadratic R j=positiveQuadratic R (exchangedDirection j) := by
  let f : ℤ →+* R := Int.castRingHom R
  calc
    _=f.mapMatrix (reflectedQuadratic ℤ j) := (map_reflectedQuadratic ℤ f j).symm
    _=f.mapMatrix (positiveQuadratic ℤ (exchangedDirection j)) :=
      congrArg f.mapMatrix (integer_quadratic j)
    _=positiveQuadratic R (exchangedDirection j) := map_positiveQuadratic ℤ f _

theorem reflectedRoot_val (j : Fin 6) (t : R) :
    (reflectedRoot R j t : Mat R)=
      polynomialRoot R (exchangedDirection j) (signedParameter R j t) := by
  change (reflectedUnit R j : Mat R)*
      (1+t • positive R (exchangedNode (rootNode j))+
        t^2 • positiveSecond R (exchangedNode (rootNode j)))*
      (↑((reflectedUnit R j)⁻¹):Mat R)=_
  rw [conjugation_quadratic]
  change 1+t • reflectedLinear R j+t^2 • reflectedQuadratic R j=_
  rw [reflectedLinear_eq,reflectedQuadratic_eq]
  by_cases h : j.val=2 ∨ j.val=4
  · simp only [signedLinear,signedParameter,polynomialRoot,if_pos h,neg_smul,smul_neg,neg_sq]
  · simp only [signedLinear,signedParameter,polynomialRoot,if_neg h]

end SymmetricSubgroupAsymptotics.CFSGGTwoExceptionalPositiveDirections
