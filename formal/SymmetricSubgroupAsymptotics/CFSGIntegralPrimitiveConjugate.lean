import SymmetricSubgroupAsymptotics.CFSGUnitConjugationPolynomial
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum

/-! An integral unimodular conjugation between primitive integral
matrix lines has rational scalar +1 or -1. One unit coefficient in each
matrix suffices; no large word-column calculation is required. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGIntegralPrimitiveConjugate
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem scalar_eq_sign (u : (Matrix I I ℤ)ˣ) (A B : Matrix I I ℤ)
    (ia ja ib jb : I) (hA : A ia ja=1) (hB : B ib jb=1) (c : ℚ)
    (hc : (Int.castRingHom ℚ).mapMatrix
      ((u : Matrix I I ℤ)*A*((u⁻¹ : (Matrix I I ℤ)ˣ) : Matrix I I ℤ))=
      c • (Int.castRingHom ℚ).mapMatrix B) : c=1 ∨ c= -1 := by
  let C : Matrix I I ℤ := (u : Matrix I I ℤ)*A*((u⁻¹ : (Matrix I I ℤ)ˣ) : Matrix I I ℤ)
  let D : Matrix I I ℤ := ((u⁻¹ : (Matrix I I ℤ)ˣ) : Matrix I I ℤ)*B*(u : Matrix I I ℤ)
  have hca : c=(C ib jb:ℚ) := by
    have hh := congrArg (fun M : Matrix I I ℚ=>M ib jb) hc
    change (C ib jb:ℚ)=c*(B ib jb:ℚ) at hh
    rw [hB,Int.cast_one,mul_one] at hh
    exact hh.symm
  have hback : (Int.castRingHom ℚ).mapMatrix A=c • (Int.castRingHom ℚ).mapMatrix D := by
    have hh := congrArg (fun M : Matrix I I ℚ=>
      (Int.castRingHom ℚ).mapMatrix (((u⁻¹ : (Matrix I I ℤ)ˣ) : Matrix I I ℤ))*M*
        (Int.castRingHom ℚ).mapMatrix (u : Matrix I I ℤ)) hc
    have hv : (Int.castRingHom ℚ).mapMatrix (((u⁻¹ : (Matrix I I ℤ)ˣ) : Matrix I I ℤ))*
        (Int.castRingHom ℚ).mapMatrix (u : Matrix I I ℤ)=1 := by
      rw [←map_mul,Units.inv_mul,map_one]
    have hl : (Int.castRingHom ℚ).mapMatrix (((u⁻¹ : (Matrix I I ℤ)ˣ) : Matrix I I ℤ))*
        (Int.castRingHom ℚ).mapMatrix
          ((u : Matrix I I ℤ)*A*((u⁻¹ : (Matrix I I ℤ)ˣ) : Matrix I I ℤ))*
        (Int.castRingHom ℚ).mapMatrix (u : Matrix I I ℤ)=
        (Int.castRingHom ℚ).mapMatrix A := by
      simp only [map_mul]
      calc
        _=((Int.castRingHom ℚ).mapMatrix (((u⁻¹ : (Matrix I I ℤ)ˣ) : Matrix I I ℤ))*
            (Int.castRingHom ℚ).mapMatrix (u : Matrix I I ℤ))*
          (Int.castRingHom ℚ).mapMatrix A*
          ((Int.castRingHom ℚ).mapMatrix (((u⁻¹ : (Matrix I I ℤ)ˣ) : Matrix I I ℤ))*
            (Int.castRingHom ℚ).mapMatrix (u : Matrix I I ℤ)) := by noncomm_ring
        _=_ := by rw [hv,one_mul,mul_one]
    dsimp only at hh
    rw [hl] at hh
    simpa only [D,map_mul,smul_mul_assoc,mul_smul_comm] using hh
  have hab : C ib jb*D ia ja=1 := by
    have hh := congrArg (fun M : Matrix I I ℚ=>M ia ja) hback
    change (A ia ja:ℚ)=c*(D ia ja:ℚ) at hh
    rw [hA,Int.cast_one,hca] at hh
    exact_mod_cast hh.symm
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hab with h|h
  · left
    simpa only [h,Int.cast_one] using hca
  · right
    simpa only [h,Int.cast_neg,Int.cast_one] using hca

end SymmetricSubgroupAsymptotics.CFSGIntegralPrimitiveConjugate
