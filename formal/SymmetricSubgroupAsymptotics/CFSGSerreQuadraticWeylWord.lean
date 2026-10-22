import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticWeylConjugationTransport

/-! Literal canonical Weyl words over every coefficient ring, including
integers. Exact cast transport keeps both unit inverses integral. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticWeylWord
open CFSGSerreQuadraticMatrix
variable {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I] (D : Data A I)

def canonicalWord (K : Type*) [CommRing K] : List (Fin r)→(Matrix I I K)ˣ
  | []=>1
  | i::w=>canonicalWeyl D K i*canonicalWord K w

theorem map_word_val {K L : Type*} [CommRing K] [CommRing L]
    (f : K→+*L) (w : List (Fin r)) :
    f.mapMatrix (canonicalWord D K w : Matrix I I K)=
      (canonicalWord D L w : Matrix I I L) := by
  induction w with
  | nil=>simp only [canonicalWord,Units.val_one,map_one]
  | cons i w ih=>simp only [canonicalWord,Units.val_mul,map_mul,map_canonicalWeyl_val,ih]

theorem map_word_inv_val {K L : Type*} [CommRing K] [CommRing L]
    (f : K→+*L) (w : List (Fin r)) :
    f.mapMatrix (((canonicalWord D K w)⁻¹ : (Matrix I I K)ˣ) : Matrix I I K)=
      (((canonicalWord D L w)⁻¹ : (Matrix I I L)ˣ) : Matrix I I L) := by
  induction w with
  | nil=>simp only [canonicalWord,inv_one,Units.val_one,map_one]
  | cons i w ih=>
    simp only [canonicalWord,mul_inv_rev,Units.val_mul,map_mul,map_canonicalWeyl_inv_val,ih]

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticWeylWord
