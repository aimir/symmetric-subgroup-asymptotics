import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! The literal eight A2-adjoint Singer columns in characteristic two.
This selected coefficient calculation is independent of any claim that
an arbitrary root space has the required block decomposition. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGCharacteristicTwoA2SingerAdjointBlock
variable {K M : Type*} [CommRing K] [CharP K 2] [AddCommGroup M] [Module K M]

/-- Column order: Halpha,Hbeta,Ealpha,Ebeta,E(alpha+beta),
Falpha,Fbeta,F(alpha+beta). -/
theorem singer_seven (f : Module.End K M) (v : Fin 8→M)
    (h0 : f (v 0)=v 1+v 2)
    (h1 : f (v 1)=v 0+v 1+v 2)
    (h2 : f (v 2)=v 3+v 4)
    (h3 : f (v 3)=v 6+v 7)
    (h4 : f (v 4)=v 0+v 2+v 5)
    (h5 : f (v 5)=v 6)
    (h6 : f (v 6)=v 4)
    (h7 : f (v 7)=v 2) (j : Fin 8) : (f^7) (v j)=v j := by
  have p0 : (f^7) (v 0)=v 0 := by
    simp only [pow_succ,pow_zero,Module.End.mul_apply,Module.End.one_apply,
      h0,h1,h2,h3,h4,h5,h6,h7,map_add]
    try abel_nf
    simp only [←Int.cast_smul_eq_zsmul K,←Nat.cast_smul_eq_nsmul K,
      Int.cast_ofNat,CharTwo.ofNat_eq_mod,Nat.reduceMod,Nat.cast_zero,Nat.cast_one,
      zero_smul,one_smul,zero_add,add_zero]
  have p1 : (f^7) (v 1)=v 1 := by
    simp only [pow_succ,pow_zero,Module.End.mul_apply,Module.End.one_apply,
      h0,h1,h2,h3,h4,h5,h6,h7,map_add]
    try abel_nf
    simp only [←Int.cast_smul_eq_zsmul K,←Nat.cast_smul_eq_nsmul K,
      Int.cast_ofNat,CharTwo.ofNat_eq_mod,Nat.reduceMod,Nat.cast_zero,Nat.cast_one,
      zero_smul,one_smul,zero_add,add_zero]
  have p2 : (f^7) (v 2)=v 2 := by
    simp only [pow_succ,pow_zero,Module.End.mul_apply,Module.End.one_apply,
      h0,h1,h2,h3,h4,h5,h6,h7,map_add]
    try abel_nf
    simp only [←Int.cast_smul_eq_zsmul K,←Nat.cast_smul_eq_nsmul K,
      Int.cast_ofNat,CharTwo.ofNat_eq_mod,Nat.reduceMod,Nat.cast_zero,Nat.cast_one,
      zero_smul,one_smul,zero_add,add_zero]
  have p3 : (f^7) (v 3)=v 3 := by
    simp only [pow_succ,pow_zero,Module.End.mul_apply,Module.End.one_apply,
      h0,h1,h2,h3,h4,h5,h6,h7,map_add]
    try abel_nf
    simp only [←Int.cast_smul_eq_zsmul K,←Nat.cast_smul_eq_nsmul K,
      Int.cast_ofNat,CharTwo.ofNat_eq_mod,Nat.reduceMod,Nat.cast_zero,Nat.cast_one,
      zero_smul,one_smul,zero_add,add_zero]
  have p4 : (f^7) (v 4)=v 4 := by
    simp only [pow_succ,pow_zero,Module.End.mul_apply,Module.End.one_apply,
      h0,h1,h2,h3,h4,h5,h6,h7,map_add]
    try abel_nf
    simp only [←Int.cast_smul_eq_zsmul K,←Nat.cast_smul_eq_nsmul K,
      Int.cast_ofNat,CharTwo.ofNat_eq_mod,Nat.reduceMod,Nat.cast_zero,Nat.cast_one,
      zero_smul,one_smul,zero_add,add_zero]
  have p5 : (f^7) (v 5)=v 5 := by
    simp only [pow_succ,pow_zero,Module.End.mul_apply,Module.End.one_apply,
      h0,h1,h2,h3,h4,h5,h6,h7,map_add]
    try abel_nf
    simp only [←Int.cast_smul_eq_zsmul K,←Nat.cast_smul_eq_nsmul K,
      Int.cast_ofNat,CharTwo.ofNat_eq_mod,Nat.reduceMod,Nat.cast_zero,Nat.cast_one,
      zero_smul,one_smul,zero_add,add_zero]
  have p6 : (f^7) (v 6)=v 6 := by
    simp only [pow_succ,pow_zero,Module.End.mul_apply,Module.End.one_apply,
      h0,h1,h2,h3,h4,h5,h6,h7,map_add]
    try abel_nf
    simp only [←Int.cast_smul_eq_zsmul K,←Nat.cast_smul_eq_nsmul K,
      Int.cast_ofNat,CharTwo.ofNat_eq_mod,Nat.reduceMod,Nat.cast_zero,Nat.cast_one,
      zero_smul,one_smul,zero_add,add_zero]
  have p7 : (f^7) (v 7)=v 7 := by
    simp only [pow_succ,pow_zero,Module.End.mul_apply,Module.End.one_apply,
      h0,h1,h2,h3,h4,h5,h6,h7,map_add]
    try abel_nf
    simp only [←Int.cast_smul_eq_zsmul K,←Nat.cast_smul_eq_nsmul K,
      Int.cast_ofNat,CharTwo.ofNat_eq_mod,Nat.reduceMod,Nat.cast_zero,Nat.cast_one,
      zero_smul,one_smul,zero_add,add_zero]
  fin_cases j <;> first | exact p0 | exact p1 | exact p2 | exact p3 | exact p4 | exact p5 | exact p6 | exact p7

end SymmetricSubgroupAsymptotics.CFSGCharacteristicTwoA2SingerAdjointBlock
