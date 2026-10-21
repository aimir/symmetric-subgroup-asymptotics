import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryCoxeterMatrix

/-! Literal binary Coxeter transport of the sparse long and short root
arrays, retaining both the original matrix unit and paired coordinate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryConjugation
open Matrix CFSGSymplecticSerreMatrices CFSGSymplecticBinaryRotationArrays
open CFSGSymplecticBinaryCoxeterMatrix CFSGTypeAMonomialMatrices CFSGTypeAMonomialRootAction
variable {K : Type} [Field K] [CharP K 2]

theorem conjugation_single (s : ℕ) (a b : Index (s+1)) :
    ((coxeterWeyl K s).val : Mat K (s+1))*Matrix.single a b 1*
      (↑((coxeterWeyl K s).val⁻¹) : Mat K (s+1))=
      Matrix.single (cyclePerm s a) (cyclePerm s b) 1 := by
  have hm := monomial_mul_transvection (F:=K) (cyclePerm s).symm (fun _=>1) a b 1 one_ne_zero
  rw [←coxeter_binary_monomial (K:=K) s] at hm
  simp only [Equiv.symm_symm,one_mul,div_one,Matrix.transvection] at hm
  have hc := congrArg (fun A : Mat K (s+1) => A*(↑((coxeterWeyl K s).val⁻¹) : Mat K (s+1))) hm
  have hh : (1 : Mat K (s+1))+
      ((coxeterWeyl K s).val : Mat K (s+1))*Matrix.single a b 1*
        (↑((coxeterWeyl K s).val⁻¹) : Mat K (s+1))=
      1+Matrix.single (cyclePerm s a) (cyclePerm s b) 1 := by
    simpa only [mul_add,add_mul,mul_one,one_mul,mul_assoc,Units.mul_inv] using hc
  exact add_left_cancel hh

theorem conjugation_long (s : ℕ) (a : Index (s+1)) :
    ((coxeterWeyl K s).val : Mat K (s+1))*longArray a*
      (↑((coxeterWeyl K s).val⁻¹) : Mat K (s+1))=longArray (cyclePerm s a) := by
  simp only [longArray,mul_add,add_mul,mul_one,Units.mul_inv,conjugation_single,cyclePerm_paired]

theorem conjugation_short (s : ℕ) (a b : Index (s+1)) :
    ((coxeterWeyl K s).val : Mat K (s+1))*shortArray a b*
      (↑((coxeterWeyl K s).val⁻¹) : Mat K (s+1))=
      shortArray (cyclePerm s a) (cyclePerm s b) := by
  simp only [shortArray,mul_add,add_mul,mul_one,Units.mul_inv,conjugation_single,cyclePerm_paired]

theorem inverse_conjugation_short (s : ℕ) (a b : Index (s+1)) :
    (↑((coxeterWeyl K s).val⁻¹) : Mat K (s+1))*shortArray a b*
      ((coxeterWeyl K s).val : Mat K (s+1))=
      shortArray ((cyclePerm s).symm a) ((cyclePerm s).symm b) := by
  have hh := conjugation_short (K:=K) s ((cyclePerm s).symm a) ((cyclePerm s).symm b)
  simp only [Equiv.apply_symm_apply] at hh
  have hc := congrArg (fun A : Mat K (s+1) =>
    (↑((coxeterWeyl K s).val⁻¹) : Mat K (s+1))*A*((coxeterWeyl K s).val : Mat K (s+1))) hh
  simpa only [mul_assoc,Units.inv_mul_cancel_left,Units.inv_mul,Units.mul_inv,one_mul,mul_one] using hc.symm

end SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryConjugation
