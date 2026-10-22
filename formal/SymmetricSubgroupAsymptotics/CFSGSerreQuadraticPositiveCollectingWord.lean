import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticRationalRootValues
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCanonicalRootAdditive
import SymmetricSubgroupAsymptotics.CFSGUnitConjugationPolynomial
import SymmetricSubgroupAsymptotics.CFSGUnitConjugationNilpotence
import SymmetricSubgroupAsymptotics.CFSGPairSubalgebraQuadraticExponentials

/-! Rational positive-root collecting as an ACTUAL canonical group word.
All nilpotence inputs are recovered from the original simple root by
the two displayed genuine unit conjugations. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticPositiveCollectingWord
open CFSGSerreQuadraticMatrix CFSGUnitConjugationPolynomial CFSGUnitConjugationNilpotence
variable {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I] (D : Data A I)

theorem positive_commutator_word (i j : Fin r) (Y : Matrix I I ℚ)
    (hc : Commute (fieldRoot D ℚ false j) Y)
    (hplus : (canonicalRoot D ℚ false i 1 : Matrix I I ℚ)*fieldRoot D ℚ false j*
      (((canonicalRoot D ℚ false i 1)⁻¹ : (Matrix I I ℚ)ˣ) : Matrix I I ℚ)=
        fieldRoot D ℚ false j+Y)
    (hweyl : (canonicalWeyl D ℚ i : Matrix I I ℚ)*fieldRoot D ℚ false j*
      (((canonicalWeyl D ℚ i)⁻¹ : (Matrix I I ℚ)ˣ) : Matrix I I ℚ)=Y) (a : ℚ) :
    canonicalRoot D ℚ false i 1*canonicalRoot D ℚ false j a*
      (canonicalRoot D ℚ false i 1)⁻¹*(canonicalRoot D ℚ false j a)⁻¹=
      canonicalWeyl D ℚ i*canonicalRoot D ℚ false j a*(canonicalWeyl D ℚ i)⁻¹ := by
  let x := fieldRoot D ℚ false j
  let u := canonicalRoot D ℚ false i 1
  let w := canonicalWeyl D ℚ i
  have hx : x^3=0 := fieldRoot_cube D ℚ false j
  have hY : Y^3=0 := pow_eq_zero_of_conjugate w x Y hweyl 3 hx
  have hsum : (x+Y)^3=0 := pow_eq_zero_of_conjugate u x (x+Y) hplus 3 hx
  have hpolyU := conjugate_quadratic u x (x+Y) hplus a
  have hpolyW := conjugate_quadratic w x Y hweyl a
  have hcollect := CFSGPairSubalgebraQuadraticExponentials.product_difference_of_commute
    x Y hc hx hY hsum a
  have ha : (canonicalRoot D ℚ false j a : Matrix I I ℚ)=1+a • x+(a^2/2) • x^2 :=
    canonicalRoot_val_rational D false j a
  have hna : (((canonicalRoot D ℚ false j a)⁻¹ : (Matrix I I ℚ)ˣ) : Matrix I I ℚ)=
      1+a • (-x)+(a^2/2) • (-x)^2 := by
    rw [canonicalRoot_inverse,canonicalRoot_val_rational]
    simp only [neg_smul,smul_neg,neg_sq]
    dsimp only [x]
  apply Units.ext
  change (u:Matrix I I ℚ)*(canonicalRoot D ℚ false j a : Matrix I I ℚ)*
    ((u⁻¹:(Matrix I I ℚ)ˣ):Matrix I I ℚ)*
      (((canonicalRoot D ℚ false j a)⁻¹ : (Matrix I I ℚ)ˣ):Matrix I I ℚ)=
    (w:Matrix I I ℚ)*(canonicalRoot D ℚ false j a : Matrix I I ℚ)*
      ((w⁻¹:(Matrix I I ℚ)ˣ):Matrix I I ℚ)
  simp only [ha,hna]
  rw [hpolyU,hpolyW]
  exact hcollect

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticPositiveCollectingWord
