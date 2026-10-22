import SymmetricSubgroupAsymptotics.CFSGIntegralPrimitiveConjugatePair

/-! A scalar coefficient of an integral matrix on a unimodular conjugate
of a primitive integral matrix line is an integer. Unlike the two-sided
sign theorem, the arbitrary matrix need not itself be primitive. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGIntegralPrimitiveLineScalar
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem scalar_is_integer (u : (Matrix I I ℤ)ˣ) (B M : Matrix I I ℤ)
    (i j : I) (hB : B i j=1) (c : ℚ)
    (hc : (Int.castRingHom ℚ).mapMatrix M=
      c • (Int.castRingHom ℚ).mapMatrix
        ((u : Matrix I I ℤ)*B*((u⁻¹ : (Matrix I I ℤ)ˣ) : Matrix I I ℤ))) :
    ∃n : ℤ,c=(n:ℚ) := by
  let f : Matrix I I ℤ→+*Matrix I I ℚ := (Int.castRingHom ℚ).mapMatrix
  let N : Matrix I I ℤ := ((u⁻¹ : (Matrix I I ℤ)ˣ) : Matrix I I ℤ)*M*(u : Matrix I I ℤ)
  have hcancel : f (((u⁻¹ : (Matrix I I ℤ)ˣ) : Matrix I I ℤ))*f (u : Matrix I I ℤ)=1 := by
    rw [←map_mul,Units.inv_mul,map_one]
  have hh := congrArg (fun X : Matrix I I ℚ=>
    f (((u⁻¹ : (Matrix I I ℤ)ˣ) : Matrix I I ℤ))*X*f (u : Matrix I I ℤ)) hc
  dsimp only at hh
  have hprod : f (((u⁻¹ : (Matrix I I ℤ)ˣ) : Matrix I I ℤ))*
      (f (u : Matrix I I ℤ)*f B*f (((u⁻¹ : (Matrix I I ℤ)ˣ) : Matrix I I ℤ)))*
        f (u : Matrix I I ℤ)=f B := by
    calc
      _=(f (((u⁻¹ : (Matrix I I ℤ)ˣ) : Matrix I I ℤ))*f (u : Matrix I I ℤ))*f B*
        (f (((u⁻¹ : (Matrix I I ℤ)ˣ) : Matrix I I ℤ))*f (u : Matrix I I ℤ)) := by noncomm_ring
      _=_ := by rw [hcancel,one_mul,mul_one]
  have hback : f N=c • f B := by
    change f (((u⁻¹ : (Matrix I I ℤ)ˣ) : Matrix I I ℤ))*f M*f (u : Matrix I I ℤ)=
      f (((u⁻¹ : (Matrix I I ℤ)ˣ) : Matrix I I ℤ))*
        (c • f ((u : Matrix I I ℤ)*B*((u⁻¹ : (Matrix I I ℤ)ˣ) : Matrix I I ℤ)))*
          f (u : Matrix I I ℤ) at hh
    simp only [map_mul,mul_smul_comm,smul_mul_assoc] at hh
    rw [hprod] at hh
    simpa only [N,map_mul] using hh
  have he := congrArg (fun X : Matrix I I ℚ=>X i j) hback
  change (N i j:ℚ)=c*(B i j:ℚ) at he
  rw [hB,Int.cast_one,mul_one] at he
  exact ⟨N i j,he.symm⟩

theorem integer_inverse_coefficients_are_signs (c d : ℚ)
    (hc : ∃n : ℤ,c=(n:ℚ)) (hd : ∃n : ℤ,d=(n:ℚ)) (hprod : c*d=1) :
    c=1 ∨ c= -1 := by
  obtain ⟨n,rfl⟩ := hc
  obtain ⟨m,rfl⟩ := hd
  have hnm : n*m=1 := by exact_mod_cast hprod
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hnm with h|h
  · left;simpa only [h,Int.cast_one]
  · right;simpa only [h,Int.cast_neg,Int.cast_one]

end SymmetricSubgroupAsymptotics.CFSGIntegralPrimitiveLineScalar
