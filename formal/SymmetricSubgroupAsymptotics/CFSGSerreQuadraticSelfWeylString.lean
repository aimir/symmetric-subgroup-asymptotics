import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticAdjointTriple
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticAdjointWeylString

/-! An actual self-root Weyl flip from its three sl₂ brackets.
All conjugations are the original canonical quadratic units. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticSelfWeylString
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticAdjointWeylString
variable {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I] (D : Data A I)

theorem weyl_conjugates_self (i : Fin r) (H : Matrix I I ℚ)
    (hEF : ⁅fieldRoot D ℚ false i,fieldRoot D ℚ true i⁆=H)
    (hHE : ⁅H,fieldRoot D ℚ false i⁆=(2:ℚ) • fieldRoot D ℚ false i)
    (hHF : ⁅H,fieldRoot D ℚ true i⁆= -(2:ℚ) • fieldRoot D ℚ true i) :
    (canonicalWeyl D ℚ i : Matrix I I ℚ)*fieldRoot D ℚ false i*
      (((canonicalWeyl D ℚ i)⁻¹ : (Matrix I I ℚ)ˣ) : Matrix I I ℚ)=
      -fieldRoot D ℚ true i := by
  let E := fieldRoot D ℚ false i
  let F := fieldRoot D ℚ true i
  have hEH : ⁅E,H⁆= -(2:ℚ) • E := by
    calc
      ⁅E,H⁆= -⁅H,E⁆ := (lie_skew _ _).symm
      _= -(2:ℚ) • E := by rw [hHE]; simp only [neg_smul,E]
  have hFH : ⁅F,H⁆=(2:ℚ) • F := by
    calc
      ⁅F,H⁆= -⁅H,F⁆ := (lie_skew _ _).symm
      _=(2:ℚ) • F := by rw [hHF]; simp only [neg_smul,neg_neg,F]
  have hFE : ⁅F,E⁆= -H := by
    calc
      ⁅F,E⁆= -⁅E,F⁆ := (lie_skew _ _).symm
      _= -H := by rw [hEF]
  have hUu (a : ℚ) : operator D false i a H=H+(2*a) • (-E) := by
    rw [operator_apply]
    have hh := canonicalRoot_conjugation_of_double_lie D false i H
      (by rw [hEH,lie_smul,lie_self,smul_zero]) a
    rw [hEH] at hh
    calc
      _=H+a • (-(2:ℚ) • E) := hh
      _=_ := by module
  have hUp (a : ℚ) : operator D false i a (-E)= -E := by
    rw [map_neg,operator_apply]
    have hh := canonicalRoot_conjugation_of_double_lie D false i E
      (by rw [lie_self,lie_zero]) a
    simpa only [E,lie_self,smul_zero,add_zero] using congrArg Neg.neg hh
  have hUm (a : ℚ) : operator D false i a F=F+a • H+a^2 • (-E) := by
    rw [operator_apply]
    have hh := canonicalRoot_conjugation_of_triple_lie D false i F
      (by rw [hEF,hEH,lie_smul,lie_self,smul_zero]) a
    rw [hEF,hEH] at hh
    calc
      _=F+a • H+(a^2/2) • (-(2:ℚ) • E) := hh
      _=_ := by module
  have hVu (a : ℚ) : operator D true i a H=H+(2*a) • F := by
    rw [operator_apply]
    have hh := canonicalRoot_conjugation_of_double_lie D true i H
      (by rw [hFH,lie_smul,lie_self,smul_zero]) a
    rw [hFH] at hh
    calc
      _=H+a • ((2:ℚ) • F) := hh
      _=_ := by module
  have hVp (a : ℚ) : operator D true i a (-E)= -E+a • H+a^2 • F := by
    rw [map_neg,operator_apply]
    have hh := canonicalRoot_conjugation_of_triple_lie D true i E
      (by rw [hFE,lie_neg,hFH,lie_neg,lie_smul,lie_self,smul_zero,neg_zero]) a
    rw [hFE,lie_neg,hFH] at hh
    have hn := congrArg Neg.neg hh
    calc
      _= -(E+a • (-H)+(a^2/2) • (-((2:ℚ) • F))) := hn
      _=_ := by module
  have hVm (a : ℚ) : operator D true i a F=F := by
    rw [operator_apply]
    have hh := canonicalRoot_conjugation_of_double_lie D true i F
      (by rw [lie_self,lie_zero]) a
    simpa only [F,lie_self,smul_zero,add_zero] using hh
  have hh := (CFSGQuadraticWeylParameterStrings.word_triple
    (operator D false i) (operator D true i) (1:ℚˣ) H (-E) F
    hUu hUp hUm hVu hVp hVm).2.1
  simp only [map_neg,Units.val_one,inv_one,one_pow,one_smul] at hh
  have hn := congrArg Neg.neg hh
  simp only [neg_neg] at hn
  change CFSGAlgebraConjugationAction.action ℚ (Matrix I I ℚ) (canonicalWeyl D ℚ i) E= -F
  rw [canonicalWeyl,map_mul,map_mul]
  change operator D false i 1 (operator D true i (-1) (operator D false i 1 E))= -F
  simpa only [CFSGQuadraticWeylParameterStrings.word,Module.End.mul_apply,
    Units.val_one,inv_one] using hn

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticSelfWeylString
