import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCanonicalWeyl
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCanonicalRootAdditive

/-! Exact integer-cast transport of a rational Weyl/root commutator
coefficient. This retains the canonical unit inverse and works in every
coefficient ring, including bad characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
variable {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I] (D : Data A I)

theorem map_fieldRoot {K L : Type*} [CommRing K] [CommRing L]
    (f : K→+*L) (neg : Bool) (i : Fin r) :
    f.mapMatrix (fieldRoot D K neg i)=fieldRoot D L neg i := by
  ext a b
  simp [fieldRoot]

theorem map_canonicalWeyl_inv_val {K L : Type*} [CommRing K] [CommRing L]
    (f : K→+*L) (i : Fin r) :
    f.mapMatrix (((canonicalWeyl D K i)⁻¹ : (Matrix I I K)ˣ) : Matrix I I K)=
      (((canonicalWeyl D L i)⁻¹ : (Matrix I I L)ˣ) : Matrix I I L) := by
  simp only [canonicalWeyl,mul_inv_rev,Units.val_mul,canonicalRoot_inverse,
    map_mul,map_canonicalRoot_val,map_neg,map_one]

theorem weyl_root_bracket_of_rational (K : Type*) [CommRing K] (i j : Fin r)
    (h : (canonicalWeyl D ℚ i : Matrix I I ℚ)*fieldRoot D ℚ false j*
      (((canonicalWeyl D ℚ i)⁻¹ : (Matrix I I ℚ)ˣ) : Matrix I I ℚ)=
      ⁅fieldRoot D ℚ false i,fieldRoot D ℚ false j⁆) :
    (canonicalWeyl D K i : Matrix I I K)*fieldRoot D K false j*
      (((canonicalWeyl D K i)⁻¹ : (Matrix I I K)ˣ) : Matrix I I K)=
      ⁅fieldRoot D K false i,fieldRoot D K false j⁆ := by
  have hi : (canonicalWeyl D ℤ i : Matrix I I ℤ)*fieldRoot D ℤ false j*
      (((canonicalWeyl D ℤ i)⁻¹ : (Matrix I I ℤ)ˣ) : Matrix I I ℤ)=
      ⁅fieldRoot D ℤ false i,fieldRoot D ℤ false j⁆ := by
    apply CFSGSerreSquareZeroMatrix.integerCast_injective I
    change (Int.castRingHom ℚ).mapMatrix
      ((canonicalWeyl D ℤ i : Matrix I I ℤ)*fieldRoot D ℤ false j*
        (((canonicalWeyl D ℤ i)⁻¹ : (Matrix I I ℤ)ˣ) : Matrix I I ℤ))=
      (Int.castRingHom ℚ).mapMatrix ⁅fieldRoot D ℤ false i,fieldRoot D ℤ false j⁆
    simpa only [map_mul,Ring.lie_def,map_sub,map_canonicalWeyl_val,
      map_canonicalWeyl_inv_val,map_fieldRoot] using h
  have hk := congrArg (Int.castRingHom K).mapMatrix hi
  simpa only [map_mul,Ring.lie_def,map_sub,map_canonicalWeyl_val,
    map_canonicalWeyl_inv_val,map_fieldRoot] using hk

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
