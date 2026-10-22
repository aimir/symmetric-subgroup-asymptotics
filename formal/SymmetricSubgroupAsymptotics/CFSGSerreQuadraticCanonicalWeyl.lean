import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCanonicalRoots
import SymmetricSubgroupAsymptotics.CFSGQuadraticWeylStrings
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-! The canonical integral Weyl word and its rational operator. A rational
fourth-power identity transfers through the integer polynomial to every
coefficient ring, including characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I] (D : Data A I)

theorem canonicalRoot_operator (neg : Bool) (i : Fin n) (t : ℚ) :
    Matrix.toLinAlgEquiv' (canonicalRoot D ℚ neg i t : Matrix I I ℚ)=
      CFSGQuadraticWeylStrings.exponential (Matrix.toLinAlgEquiv' (fieldRoot D ℚ neg i)) t := by
  have hd : fieldSecond D ℚ neg i=(1/2:ℚ) • (fieldRoot D ℚ neg i*fieldRoot D ℚ neg i) := by
    calc
      _=(1/2:ℚ) • (fieldSecond D ℚ neg i+fieldSecond D ℚ neg i) := by module
      _=_ := by rw [fieldRoot_square]
  have hdo : Matrix.toLinAlgEquiv' (fieldSecond D ℚ neg i)=
      (1/2:ℚ) • (Matrix.toLinAlgEquiv' (fieldRoot D ℚ neg i)*
        Matrix.toLinAlgEquiv' (fieldRoot D ℚ neg i)) := by rw [hd,map_smul,map_mul]
  rw [canonicalRoot_val,map_add,map_add,map_one,map_smul,map_smul,hdo]
  simp only [CFSGQuadraticWeylStrings.exponential,smul_smul]
  rw [show t^2*(1/2:ℚ)=t^2/2 by ring]

def canonicalWeyl (K : Type*) [CommRing K] (i : Fin n) : (Matrix I I K)ˣ :=
  canonicalRoot D K false i 1*canonicalRoot D K true i (-1)*canonicalRoot D K false i 1

theorem canonicalWeyl_operator (i : Fin n) :
    Matrix.toLinAlgEquiv' (canonicalWeyl D ℚ i : Matrix I I ℚ)=
      CFSGQuadraticWeylStrings.word (Matrix.toLinAlgEquiv' (fieldRoot D ℚ false i))
        (Matrix.toLinAlgEquiv' (fieldRoot D ℚ true i)) := by
  simp only [canonicalWeyl,Units.val_mul,map_mul,canonicalRoot_operator,
    CFSGQuadraticWeylStrings.word]

theorem map_canonicalRoot_val {K L : Type*} [CommRing K] [CommRing L]
    (f : K→+*L) (neg : Bool) (i : Fin n) (t : K) :
    f.mapMatrix (canonicalRoot D K neg i t : Matrix I I K)=
      (canonicalRoot D L neg i (f t) : Matrix I I L) := by
  ext a b
  simp [canonicalRoot_val,fieldRoot,fieldSecond,Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply]

theorem map_canonicalWeyl_val {K L : Type*} [CommRing K] [CommRing L]
    (f : K→+*L) (i : Fin n) :
    f.mapMatrix (canonicalWeyl D K i : Matrix I I K)=
      (canonicalWeyl D L i : Matrix I I L) := by
  simp only [canonicalWeyl,Units.val_mul,map_mul,map_canonicalRoot_val,map_one,map_neg]

theorem canonicalWeyl_four_integral (i : Fin n) (h : (canonicalWeyl D ℚ i)^4=1) :
    (canonicalWeyl D ℤ i)^4=1 := by
  apply Units.ext
  apply CFSGSerreSquareZeroMatrix.integerCast_injective I
  change (Int.castRingHom ℚ).mapMatrix (↑((canonicalWeyl D ℤ i)^4):Matrix I I ℤ)=
    (Int.castRingHom ℚ).mapMatrix (1:Matrix I I ℤ)
  rw [Units.val_pow_eq_pow_val,map_pow,map_canonicalWeyl_val,map_one]
  simpa only [Units.val_pow_eq_pow_val,Units.val_one] using
    congrArg (fun u : (Matrix I I ℚ)ˣ=>(u:Matrix I I ℚ)) h

theorem canonicalWeyl_four_of_rational (K : Type*) [CommRing K] (i : Fin n)
    (h : (canonicalWeyl D ℚ i)^4=1) : (canonicalWeyl D K i)^4=1 := by
  apply Units.ext
  have hi := congrArg (fun u : (Matrix I I ℤ)ˣ=>(u:Matrix I I ℤ))
    (canonicalWeyl_four_integral D i h)
  have hh := congrArg (Int.castRingHom K).mapMatrix hi
  simpa only [Units.val_pow_eq_pow_val,Units.val_one,map_pow,map_one,map_canonicalWeyl_val] using hh

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
