import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterStarMiddleWord
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleSquareOriginalWords

/-! The selected four-root conjugation identity is bound to the actual
original fixed middle words for every parameter, including zero.
The selected parameter itself need not be Ree-fixed; no such membership
is used or claimed. The full outer root and higher layers are separate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOuterStarOriginalMiddle
open CFSGReeFFourOuterStarConjugation CFSGReeFFourOuterStarMiddleWord
open CFSGReeFFourMiddleSquareOriginalWords CFSGReeFFourMiddleSquareRootWordValues
open CFSGReeFFourMiddleDerivedFiveWord CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourRelativeWeylRawWords CFSGReeFFourMiddleWeylConstantWord
open CFSGReeFFourFieldParameters CFSGFFourE6PositiveRootUnits
open CFSGReeFFourRelativePositiveSubgroups
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord

theorem raw_fourCycle_eq (m : ℕ) :
    fixedRawHom m (fourCycle m)=rawY (Field m) := by
  rw [raw_fourCycle]
  simp only [yWord,rawY,canonicalWord,mul_one] <;> rfl

theorem raw_middleWeyl_eq (m : ℕ) :
    fixedRawHom m (middleFixedWeyl m)=rawW (Field m) := by
  rw [fixedRawHom_apply]
  have h := rawHom_middleRelativeWeyl m
  calc
    _ = canonicalWord e6Data (Field m) [2,4,3,2,4,3] := h
    _ = rawW (Field m) := by
      simp only [canonicalWord,rawW,mul_one,mul_assoc] <;> rfl

theorem raw_fiveWord_eq (m : ℕ) :
    fixedRawHom m (fiveWord m)=rawR (Field m) := by
  rw [fiveWord,map_mul,map_pow,raw_middleWeyl_eq,raw_fourCycle_eq]
  rfl

theorem selected_original_parameter_relation (m : ℕ) (a : Field m) :
    fixedRawHom m (fourCycle m)*starHom (Field m) (Multiplicative.ofAdd (Pi.single 0 a))*
        (fixedRawHom m (fourCycle m))⁻¹=
      fixedRawHom m (fiveWord m)*starHom (Field m) (Multiplicative.ofAdd (Pi.single 0 a))*
        (fixedRawHom m (fiveWord m))⁻¹ := by
  rw [raw_fourCycle_eq,raw_fiveWord_eq]
  exact selected_parameter_conjugate (Field m) a

end SymmetricSubgroupAsymptotics.CFSGReeFFourOuterStarOriginalMiddle
