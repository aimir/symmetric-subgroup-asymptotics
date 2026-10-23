import SymmetricSubgroupAsymptotics.CFSGGTwoPositiveRootMatrices

/-! The two orthogonal simple-Weyl/higher-root pairs in the actual
six-root normalization. Three small integer coefficient identities are
transported to arbitrary fields. No group or field elements are enumerated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOrthogonalWeylAxes
open CFSGGTwoSerreMatrices CFSGGTwoShortWeylMatrices CFSGGTwoPositiveDirections
open CFSGGTwoPositiveRootMatrices CFSGGTwoPositiveWordCoordinates

private theorem integer_short_linear :
    (shortWeyl ℤ : Mat ℤ)*positiveLinear ℤ 5=
      positiveLinear ℤ 5*(shortWeyl ℤ : Mat ℤ) := by
  decide +kernel

private theorem integer_long_linear :
    (longWeyl ℤ : Mat ℤ)*positiveLinear ℤ 3=
      positiveLinear ℤ 3*(longWeyl ℤ : Mat ℤ) := by
  decide +kernel

private theorem integer_long_quadratic :
    (longWeyl ℤ : Mat ℤ)*positiveQuadratic ℤ 3=
      positiveQuadratic ℤ 3*(longWeyl ℤ : Mat ℤ) := by
  decide +kernel

private theorem map_weyl_values {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    f.mapMatrix (shortWeyl R : Mat R)=(shortWeyl S : Mat S) ∧
      f.mapMatrix (longWeyl R : Mat R)=(longWeyl S : Mat S) :=
  ⟨congrArg (fun u : (Mat S)ˣ => (u:Mat S)) (map_shortWeyl R f),
    congrArg (fun u : (Mat S)ˣ => (u:Mat S)) (map_longWeyl R f)⟩

private theorem commute_polynomial {R : Type*} [CommRing R]
    (W E D : Mat R) (hE : W*E=E*W) (hD : W*D=D*W) (t : R) :
    W*(1+t • E+t^2 • D)=(1+t • E+t^2 • D)*W := by
  simp only [mul_add,add_mul,mul_one,one_mul,mul_smul_comm,smul_mul_assoc,hE,hD]

variable (K : Type) [Field K]

theorem short_highest_linear : Commute (shortWeyl K : Mat K) (positiveLinear K 5) := by
  let f : ℤ →+* K := Int.castRingHom K
  have h := congrArg f.mapMatrix integer_short_linear
  simpa only [map_mul,map_positiveLinear,(map_weyl_values f).1] using h

theorem long_middle_linear : Commute (longWeyl K : Mat K) (positiveLinear K 3) := by
  let f : ℤ →+* K := Int.castRingHom K
  have h := congrArg f.mapMatrix integer_long_linear
  simpa only [map_mul,map_positiveLinear,(map_weyl_values f).2] using h

theorem long_middle_quadratic : Commute (longWeyl K : Mat K) (positiveQuadratic K 3) := by
  let f : ℤ →+* K := Int.castRingHom K
  have h := congrArg f.mapMatrix integer_long_quadratic
  simpa only [map_mul,map_positiveQuadratic,(map_weyl_values f).2] using h

theorem short_highest_commute (t : K) : Commute (shortWeyl K) (positiveRoot K 5 t) := by
  change _ * _ = _ * _
  apply Units.ext
  simp only [Units.val_mul,positiveRoot_val]
  apply commute_polynomial _ _ _ (short_highest_linear K).eq _ t
  change (shortWeyl K : Mat K)*0=0*(shortWeyl K : Mat K)
  rw [mul_zero,zero_mul]

theorem long_middle_commute (t : K) : Commute (longWeyl K) (positiveRoot K 3 t) := by
  change _ * _ = _ * _
  apply Units.ext
  simp only [Units.val_mul,positiveRoot_val]
  exact commute_polynomial _ _ _ (long_middle_linear K).eq (long_middle_quadratic K).eq t

end SymmetricSubgroupAsymptotics.CFSGGTwoOrthogonalWeylAxes
