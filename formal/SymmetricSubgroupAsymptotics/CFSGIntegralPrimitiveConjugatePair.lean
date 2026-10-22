import SymmetricSubgroupAsymptotics.CFSGIntegralPrimitiveConjugate

/-! Two integral unimodular conjugates of primitive matrix generators
can span the same rational line only with scalar +1 or -1. The argument
conjugates back to the original primitive generators, so it does not
require a selected unit entry in either large conjugated matrix. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGIntegralPrimitiveConjugatePair
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem scalar_eq_sign (u v : (Matrix I I ℤ)ˣ) (A B : Matrix I I ℤ)
    (ia ja ib jb : I) (hA : A ia ja=1) (hB : B ib jb=1) (c : ℚ)
    (hc : (Int.castRingHom ℚ).mapMatrix
      ((u : Matrix I I ℤ)*A*((u⁻¹ : (Matrix I I ℤ)ˣ) : Matrix I I ℤ))=
      c • (Int.castRingHom ℚ).mapMatrix
        ((v : Matrix I I ℤ)*B*((v⁻¹ : (Matrix I I ℤ)ˣ) : Matrix I I ℤ))) :
    c=1 ∨ c= -1 := by
  apply CFSGIntegralPrimitiveConjugate.scalar_eq_sign (v⁻¹*u) A B ia ja ib jb hA hB c
  let f : Matrix I I ℤ→+*Matrix I I ℚ := (Int.castRingHom ℚ).mapMatrix
  have hcancel : f (((v⁻¹ : (Matrix I I ℤ)ˣ) : Matrix I I ℤ))*
      f (v : Matrix I I ℤ)=1 := by
    rw [←map_mul,Units.inv_mul,map_one]
  have hh := congrArg (fun M : Matrix I I ℚ=>
    f (((v⁻¹ : (Matrix I I ℤ)ˣ) : Matrix I I ℤ))*M*f (v : Matrix I I ℤ)) hc
  dsimp only at hh
  have hleft : f (((v⁻¹ : (Matrix I I ℤ)ˣ) : Matrix I I ℤ))*
      f ((u : Matrix I I ℤ)*A*((u⁻¹ : (Matrix I I ℤ)ˣ) : Matrix I I ℤ))*
        f (v : Matrix I I ℤ)=
      f (((v⁻¹*u : (Matrix I I ℤ)ˣ) : Matrix I I ℤ)*A*
        ((((v⁻¹*u)⁻¹ : (Matrix I I ℤ)ˣ) : Matrix I I ℤ))) := by
    simp only [map_mul,Units.val_mul,mul_inv_rev,inv_inv,mul_assoc]
  have hright : f (((v⁻¹ : (Matrix I I ℤ)ˣ) : Matrix I I ℤ))*
      (c • f ((v : Matrix I I ℤ)*B*((v⁻¹ : (Matrix I I ℤ)ˣ) : Matrix I I ℤ)))*
        f (v : Matrix I I ℤ)=c • f B := by
    simp only [map_mul,mul_smul_comm,smul_mul_assoc]
    have hprod : f (((v⁻¹ : (Matrix I I ℤ)ˣ) : Matrix I I ℤ))*
        (f (v : Matrix I I ℤ)*f B*f (((v⁻¹ : (Matrix I I ℤ)ˣ) : Matrix I I ℤ)))*
          f (v : Matrix I I ℤ)=f B := by
      calc
        _=(f (((v⁻¹ : (Matrix I I ℤ)ˣ) : Matrix I I ℤ))*f (v : Matrix I I ℤ))*
          f B*(f (((v⁻¹ : (Matrix I I ℤ)ˣ) : Matrix I I ℤ))*f (v : Matrix I I ℤ)) := by
            noncomm_ring
        _=_ := by rw [hcancel,one_mul,mul_one]
    rw [hprod]
  rw [hleft,hright] at hh
  exact hh

end SymmetricSubgroupAsymptotics.CFSGIntegralPrimitiveConjugatePair
