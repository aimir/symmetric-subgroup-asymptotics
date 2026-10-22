import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCanonicalWeyl
import SymmetricSubgroupAsymptotics.CFSGQuadraticRootAdditive

/-! A proved rational Weyl-square sign identity descends through the actual
integer matrix polynomials to every coefficient ring and root parameter. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I] (D : Data A I)

private theorem commute_second {R : Type*} [Ring R] [Algebra ℚ R]
    (w e d : R) (hs : e*e=d+d) (he : w*e= -(e*w)) : w*d=d*w := by
  have ht : (2:ℚ) • (w*d)=(2:ℚ) • (d*w) := by
    calc
      (2:ℚ) • (w*d)=w*(d+d) := by simp only [two_smul,mul_add]
      _=w*(e*e) := by rw [hs]
      _=(e*e)*w := by
        rw [←mul_assoc,he,neg_mul,mul_assoc,he,mul_neg,neg_neg]
        simp only [mul_assoc]
      _=(d+d)*w := by rw [hs]
      _=(2:ℚ) • (d*w) := by simp only [two_smul,add_mul]
  have hz : (2:ℚ) • (w*d-d*w)=0 := by rw [smul_sub,ht,sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (by norm_num))

variable (i j : Fin n) (neg : Bool)
    (he : (canonicalWeyl D ℚ i : Matrix I I ℚ)^2*fieldRoot D ℚ neg j=
      -(fieldRoot D ℚ neg j*(canonicalWeyl D ℚ i : Matrix I I ℚ)^2))
include he

private theorem integer_sign :
    (canonicalWeyl D ℤ i : Matrix I I ℤ)^2*integerRoot D neg j=
      -(integerRoot D neg j*(canonicalWeyl D ℤ i : Matrix I I ℤ)^2) := by
  apply CFSGSerreSquareZeroMatrix.integerCast_injective I
  change (Int.castRingHom ℚ).mapMatrix (_^2*_)=(Int.castRingHom ℚ).mapMatrix (-(_*_^2))
  simp only [map_mul,map_neg,map_pow,map_canonicalWeyl_val]
  exact he

private theorem integer_second :
    (canonicalWeyl D ℤ i : Matrix I I ℤ)^2*D.integerSecond neg j=
      D.integerSecond neg j*(canonicalWeyl D ℤ i : Matrix I I ℤ)^2 := by
  apply CFSGSerreSquareZeroMatrix.integerCast_injective I
  change (Int.castRingHom ℚ).mapMatrix (_^2*_)=(Int.castRingHom ℚ).mapMatrix (_*_^2)
  simp only [map_mul,map_pow,map_canonicalWeyl_val]
  exact commute_second _ _ _ (fieldRoot_square D ℚ neg j) he

theorem field_weyl_square_sign (K : Type*) [CommRing K] :
    (canonicalWeyl D K i : Matrix I I K)^2*fieldRoot D K neg j=
      -(fieldRoot D K neg j*(canonicalWeyl D K i : Matrix I I K)^2) := by
  have hh := congrArg (Int.castRingHom K).mapMatrix (integer_sign D i j neg he)
  simpa only [map_mul,map_neg,map_pow,map_canonicalWeyl_val,fieldRoot] using hh

theorem field_weyl_square_second (K : Type*) [CommRing K] :
    (canonicalWeyl D K i : Matrix I I K)^2*fieldSecond D K neg j=
      fieldSecond D K neg j*(canonicalWeyl D K i : Matrix I I K)^2 := by
  have hh := congrArg (Int.castRingHom K).mapMatrix (integer_second D i j neg he)
  simpa only [map_mul,map_pow,map_canonicalWeyl_val,fieldSecond] using hh

theorem canonical_weyl_square_root (K : Type*) [CommRing K] (t : K) :
    (canonicalWeyl D K i)^2*canonicalRoot D K neg j t=
      canonicalRoot D K neg j (-t)*(canonicalWeyl D K i)^2 := by
  apply Units.ext
  simp only [Units.val_mul,Units.val_pow_eq_pow_val,canonicalRoot_val,mul_add,mul_one,
    mul_smul_comm,field_weyl_square_sign D i j neg he K,
    field_weyl_square_second D i j neg he K,smul_neg,neg_smul,neg_sq,
    add_mul,one_mul,neg_mul,smul_mul_assoc]

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
