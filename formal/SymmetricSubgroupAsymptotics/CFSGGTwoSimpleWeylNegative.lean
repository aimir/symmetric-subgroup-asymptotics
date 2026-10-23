import SymmetricSubgroupAsymptotics.CFSGGTwoPositiveRootMatrices
import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalPositiveRootWords

/-! Literal same-axis Weyl transport, including the minus parameter.
Three separate integer coefficient certificates are transported to fields;
there is no field-size restriction or ordinary G2 simplicity premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoSimpleWeylNegative
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration CFSGGTwoSerreMatrices CFSGGTwoShortWeylMatrices
open CFSGGTwoPositiveDirections CFSGGTwoPositiveRootMatrices
open CFSGGTwoPositiveWordCoordinates CFSGGTwoExceptionalCoefficients
open CFSGGTwoOriginalPositiveRootWords CFSGGTwoOriginalNaturalEquivalence

private theorem integer_short_linear :
    (shortWeyl ℤ : Mat ℤ)*positiveLinear ℤ 0=
      (-rootMatrix ℤ true 0)*(shortWeyl ℤ : Mat ℤ) := by decide +kernel
private theorem integer_short_quadratic :
    (shortWeyl ℤ : Mat ℤ)*positiveQuadratic ℤ 0=
      rootSecond ℤ true 0*(shortWeyl ℤ : Mat ℤ) := by decide +kernel
private theorem integer_long_linear :
    (longWeyl ℤ : Mat ℤ)*positiveLinear ℤ 1=
      (-rootMatrix ℤ true 1)*(longWeyl ℤ : Mat ℤ) := by decide +kernel

private theorem map_weyl_values {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    f.mapMatrix (shortWeyl R : Mat R)=(shortWeyl S : Mat S) ∧
      f.mapMatrix (longWeyl R : Mat R)=(longWeyl S : Mat S) :=
  ⟨congrArg (fun u : (Mat S)ˣ => (u:Mat S)) (map_shortWeyl R f),
    congrArg (fun u : (Mat S)ˣ => (u:Mat S)) (map_longWeyl R f)⟩

private theorem polynomial_intertwines {R : Type*} [CommRing R]
    (W E D F Q : Mat R) (hE : W*E=(-F)*W) (hD : W*D=Q*W) (t : R) :
    W*(1+t • E+t^2 • D)=(1+(-t) • F+(-t)^2 • Q)*W := by
  simp only [mul_add,add_mul,mul_one,one_mul,mul_smul_comm,smul_mul_assoc,hE,hD,
    neg_mul,smul_neg,neg_smul,neg_sq]

variable (K : Type) [Field K]

theorem short_native (t : K) :
    shortWeyl K*positiveRoot K 0 t*(shortWeyl K)⁻¹=rootTransvection K true 0 (-t) := by
  let f : ℤ →+* K := Int.castRingHom K
  have hE := congrArg f.mapMatrix integer_short_linear
  have hD := congrArg f.mapMatrix integer_short_quadratic
  simp only [map_mul,map_neg,map_rootMatrix,map_rootSecond,map_positiveLinear,map_positiveQuadratic,
    (map_weyl_values f).1] at hE hD
  apply mul_inv_eq_iff_eq_mul.mpr
  apply Units.ext
  simp only [Units.val_mul,positiveRoot_val,rootTransvection_val]
  exact polynomial_intertwines _ _ _ _ _ hE hD t

theorem long_native (t : K) :
    longWeyl K*positiveRoot K 1 t*(longWeyl K)⁻¹=rootTransvection K true 1 (-t) := by
  let f : ℤ →+* K := Int.castRingHom K
  have hE := congrArg f.mapMatrix integer_long_linear
  simp only [map_mul,map_neg,map_rootMatrix,map_positiveLinear,(map_weyl_values f).2] at hE
  have hD : (longWeyl K:Mat K)*positiveQuadratic K 1=
      rootSecond K true 1*(longWeyl K:Mat K) := by
    simp [positiveQuadratic,rootSecond,negativeSecond,positiveSecond]
  apply mul_inv_eq_iff_eq_mul.mpr
  apply Units.ext
  simp only [Units.val_mul,positiveRoot_val,rootTransvection_val]
  exact polynomial_intertwines _ _ _ _ _ hE hD t

theorem short_original (t : K) :
    shortWord K*positiveModel K 0 t*(shortWord K)⁻¹=
      modelRoot CartanMatrix.G₂ K true 0 (-t) := by
  apply (modelEquivNatural K).injective
  apply Subtype.ext
  simpa only [map_mul,map_inv,shortWord_native,positiveModel_native,modelEquivNatural_root,
    Subgroup.coe_mul,Subgroup.coe_inv] using short_native K t

theorem long_original (t : K) :
    longWord K*positiveModel K 1 t*(longWord K)⁻¹=
      modelRoot CartanMatrix.G₂ K true 1 (-t) := by
  apply (modelEquivNatural K).injective
  apply Subtype.ext
  simpa only [map_mul,map_inv,longWord_native,positiveModel_native,modelEquivNatural_root,
    Subgroup.coe_mul,Subgroup.coe_inv] using long_native K t

end SymmetricSubgroupAsymptotics.CFSGGTwoSimpleWeylNegative
