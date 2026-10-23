import SymmetricSubgroupAsymptotics.CFSGGTwoPositiveWordCoordinates

/-! All six literal positive Weyl words have explicit integral quadratic
coefficients, with their actual signs. The original normalization is
positive0, positive1, first, -second, third, -highest. Separate constant
integer certificates and ring-hom transport prove the formulas in every
field before any characteristic-three collecting argument. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoPositiveRootMatrices
open CFSGGTwoSerreMatrices CFSGGTwoPositiveDirections
open CFSGGTwoOriginalMatrixCoordinates CFSGGTwoPositiveWordCoordinates
variable (R : Type*) [CommRing R]

def positiveLinear (j : Fin 6) : Mat R :=
  if j.val=3 ∨ j.val=5 then -matrixVectors R (Sum.inl (false,j))
  else matrixVectors R (Sum.inl (false,j))

def positiveQuadratic (j : Fin 6) : Mat R :=
  match j.val with
  | 0 => Matrix.single (pos 2) (neg 2) (-1)
  | 2 => Matrix.single (pos 1) (neg 1) (-1)
  | 3 => Matrix.single (pos 0) (neg 0) (-1)
  | _ => 0

def polynomialRoot (j : Fin 6) (t : R) : Mat R :=
  1+t • positiveLinear R j+t^2 • positiveQuadratic R j

theorem map_positiveLinear {S : Type*} [CommRing S] (f : R →+* S) (j : Fin 6) :
    f.mapMatrix (positiveLinear R j)=positiveLinear S j := by
  by_cases h : j.val=3 ∨ j.val=5
  · simp only [positiveLinear,if_pos h,map_neg,map_matrixVectors]
  · simp only [positiveLinear,if_neg h,map_matrixVectors]

private theorem map_single_negative_one {S : Type*} [CommRing S]
    (f : R →+* S) (i j : Index) :
    f.mapMatrix (Matrix.single i j (-1:R))=Matrix.single i j (-1:S) := by
  change (Matrix.single i j (-1:R)).map f=Matrix.single i j (-1:S)
  simp only [Matrix.map_single,map_neg,map_one]

theorem map_positiveQuadratic {S : Type*} [CommRing S] (f : R →+* S) (j : Fin 6) :
    f.mapMatrix (positiveQuadratic R j)=positiveQuadratic S j := by
  fin_cases j
  · exact map_single_negative_one R f _ _
  · exact map_zero f.mapMatrix
  · exact map_single_negative_one R f _ _
  · exact map_single_negative_one R f _ _
  · exact map_zero f.mapMatrix
  · exact map_zero f.mapMatrix

theorem map_polynomialRoot {S : Type*} [CommRing S] (f : R →+* S) (j : Fin 6) (t : R) :
    f.mapMatrix (polynomialRoot R j t)=polynomialRoot S j (f t) := by
  change f.mapMatrix (1+t • positiveLinear R j+t^2 • positiveQuadratic R j)=
    1+f t • positiveLinear S j+(f t)^2 • positiveQuadratic S j
  rw [map_add,map_add,map_one,map_scalar,map_scalar,map_positiveLinear,map_positiveQuadratic,map_pow]

private theorem integer_linear_0 :
    linearDirection ℤ 0=positiveLinear ℤ 0 := by
  decide +kernel

private theorem integer_quadratic_0 :
    secondDirection ℤ 0=positiveQuadratic ℤ 0 := by
  decide +kernel

private theorem integer_linear_1 :
    linearDirection ℤ 1=positiveLinear ℤ 1 := by
  decide +kernel

private theorem integer_quadratic_1 :
    secondDirection ℤ 1=positiveQuadratic ℤ 1 := by
  decide +kernel

private theorem integer_linear_2 :
    linearDirection ℤ 2=positiveLinear ℤ 2 := by
  decide +kernel

private theorem integer_quadratic_2 :
    secondDirection ℤ 2=positiveQuadratic ℤ 2 := by
  decide +kernel

private theorem integer_linear_3 :
    linearDirection ℤ 3=positiveLinear ℤ 3 := by
  decide +kernel

private theorem integer_quadratic_3 :
    secondDirection ℤ 3=positiveQuadratic ℤ 3 := by
  decide +kernel

private theorem integer_linear_4 :
    linearDirection ℤ 4=positiveLinear ℤ 4 := by
  decide +kernel

private theorem integer_quadratic_4 :
    secondDirection ℤ 4=positiveQuadratic ℤ 4 := by
  decide +kernel

private theorem integer_linear_5 :
    linearDirection ℤ 5=positiveLinear ℤ 5 := by
  decide +kernel

private theorem integer_quadratic_5 :
    secondDirection ℤ 5=positiveQuadratic ℤ 5 := by
  decide +kernel

private theorem integer_linear (j : Fin 6) :
    linearDirection ℤ j=positiveLinear ℤ j := by
  fin_cases j
  · exact integer_linear_0
  · exact integer_linear_1
  · exact integer_linear_2
  · exact integer_linear_3
  · exact integer_linear_4
  · exact integer_linear_5

private theorem integer_quadratic (j : Fin 6) :
    secondDirection ℤ j=positiveQuadratic ℤ j := by
  fin_cases j
  · exact integer_quadratic_0
  · exact integer_quadratic_1
  · exact integer_quadratic_2
  · exact integer_quadratic_3
  · exact integer_quadratic_4
  · exact integer_quadratic_5

theorem linearDirection_eq (j : Fin 6) : linearDirection R j=positiveLinear R j := by
  let f : ℤ →+* R := Int.castRingHom R
  calc
    _=f.mapMatrix (linearDirection ℤ j) := (map_linearDirection ℤ f j).symm
    _=f.mapMatrix (positiveLinear ℤ j) := congrArg f.mapMatrix (integer_linear j)
    _=positiveLinear R j := map_positiveLinear ℤ f j

theorem secondDirection_eq (j : Fin 6) : secondDirection R j=positiveQuadratic R j := by
  let f : ℤ →+* R := Int.castRingHom R
  calc
    _=f.mapMatrix (secondDirection ℤ j) := (map_secondDirection ℤ f j).symm
    _=f.mapMatrix (positiveQuadratic ℤ j) := congrArg f.mapMatrix (integer_quadratic j)
    _=positiveQuadratic R j := map_positiveQuadratic ℤ f j

theorem conjugation_quadratic (g : (Mat R)ˣ) (E D : Mat R) (t : R) :
    (g:Mat R)*(1+t • E+t^2 • D)*(↑(g⁻¹):Mat R)=
      1+t • ((g:Mat R)*E*(↑(g⁻¹):Mat R))+
        t^2 • ((g:Mat R)*D*(↑(g⁻¹):Mat R)) := by
  have hg : (g:Mat R)*(↑(g⁻¹):Mat R)=1 :=
    congrArg (fun u : (Mat R)ˣ => (u:Mat R)) (mul_inv_cancel g)
  simp only [mul_add,add_mul,mul_one,mul_smul_comm,smul_mul_assoc,hg]

theorem positiveRoot_val (K : Type) [Field K] (j : Fin 6) (t : K) :
    (positiveRoot K j t : Mat K)=polynomialRoot K j t := by
  change (directionWord K j : Mat K)*
      (1+t • positive K (rootNode j)+t^2 • positiveSecond K (rootNode j))*
      (↑((directionWord K j)⁻¹):Mat K)=_
  rw [←directionUnit_eq,conjugation_quadratic]
  change 1+t • linearDirection K j+t^2 • secondDirection K j=
    1+t • positiveLinear K j+t^2 • positiveQuadratic K j
  rw [linearDirection_eq,secondDirection_eq]

end SymmetricSubgroupAsymptotics.CFSGGTwoPositiveRootMatrices
