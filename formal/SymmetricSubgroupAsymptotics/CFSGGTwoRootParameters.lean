import SymmetricSubgroupAsymptotics.CFSGGTwoImageRealization
import SymmetricSubgroupAsymptotics.CFSGQuadraticRootAdditive
import Mathlib.LinearAlgebra.Matrix.Notation

/-! Actual additive and injective simple-root parameters in the folded G2
matrix group. The coefficient-one entry works in characteristics two and
three, including the quadratic short-root direction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGGTwoRootParameters
open CFSGGTwoSerreMatrices

def baseRow : Fin 2 → Index := ![pos 0, pos 1]
def baseColumn : Fin 2 → Index := ![pos 1, pos 2]

theorem baseRow_ne_column (i : Fin 2) : baseRow i ≠ baseColumn i := by
  fin_cases i <;> decide

theorem positive_parameter_entry (K : Type) [Field K] (i : Fin 2) :
    positive K i (baseRow i) (baseColumn i) = 1 := by
  fin_cases i
  · change positive K 0 (pos 0) (pos 1) = 1
    rw [positive_zero_explicit]
    norm_num [pos, neg, Matrix.single_apply, Sum.inr_ne_inl, Fin.ext_iff]
  · change positive K 1 (pos 1) (pos 2) = 1
    rw [positive_one_explicit]
    norm_num [pos, neg, Matrix.single_apply, Sum.inr_ne_inl, Fin.ext_iff]

theorem positiveSecond_parameter_entry (K : Type) [Field K] (i : Fin 2) :
    positiveSecond K i (baseRow i) (baseColumn i) = 0 := by
  fin_cases i <;> simp [positiveSecond, baseRow, baseColumn, pos, neg]

def parameterRow (negRoot : Bool) (i : Fin 2) : Index :=
  if negRoot then baseColumn i else baseRow i
def parameterColumn (negRoot : Bool) (i : Fin 2) : Index :=
  if negRoot then baseRow i else baseColumn i

theorem rootTransvection_parameter_entry (K : Type) [Field K]
    (negRoot : Bool) (i : Fin 2) (t : K) :
    (rootTransvection K negRoot i t : Mat K)
      (parameterRow negRoot i) (parameterColumn negRoot i) = t := by
  have hne := baseRow_ne_column i
  cases negRoot <;>
    simp only [parameterRow, parameterColumn, Bool.false_eq_true, if_false, if_true,
      rootTransvection_val, rootMatrix, rootSecond, negative, negativeSecond,
      Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply, if_neg hne, if_neg (Ne.symm hne), positive_parameter_entry,
      positiveSecond_parameter_entry, smul_eq_mul, mul_one, mul_zero, zero_add, add_zero]

theorem rootTransvection_injective (K : Type) [Field K] (negRoot : Bool) (i : Fin 2) :
    Function.Injective (rootTransvection K negRoot i) := by
  intro t u h
  have he := congrArg (fun g : (Mat K)ˣ =>
    (g : Mat K) (parameterRow negRoot i) (parameterColumn negRoot i)) h
  simpa only [rootTransvection_parameter_entry] using he

theorem rootTransvection_zero (K : Type) [Field K] (negRoot : Bool) (i : Fin 2) :
    rootTransvection K negRoot i 0 = 1 := by
  apply Units.ext
  simp only [rootTransvection_val, zero_smul, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero,
    Units.val_one]

theorem rootTransvection_add (K : Type) [Field K] (negRoot : Bool) (i : Fin 2) (t u : K) :
    rootTransvection K negRoot i t * rootTransvection K negRoot i u =
      rootTransvection K negRoot i (t + u) :=
  CFSGQuadraticRootExponential.rootUnit_add (rootMatrix K negRoot i) (rootSecond K negRoot i)
    (rootMatrix_square K negRoot i) (rootMatrix_mul_second K negRoot i)
    (rootSecond_mul_matrix K negRoot i) (rootSecond_square K negRoot i) t u

def rootHom (K : Type) [Field K] (negRoot : Bool) (i : Fin 2) :
    Multiplicative K →* naturalGroup K where
  toFun t := naturalRoot K negRoot i t.toAdd
  map_one' := by
    apply Subtype.ext
    change rootTransvection K negRoot i 0 = 1
    exact rootTransvection_zero K negRoot i
  map_mul' t u := by
    apply Subtype.ext
    exact (rootTransvection_add K negRoot i t.toAdd u.toAdd).symm

theorem rootHom_injective (K : Type) [Field K] (negRoot : Bool) (i : Fin 2) :
    Function.Injective (rootHom K negRoot i) := by
  intro t u h
  have he : t.toAdd = u.toAdd :=
    rootTransvection_injective K negRoot i (congrArg Subtype.val h)
  exact congrArg Multiplicative.ofAdd he

end SymmetricSubgroupAsymptotics.CFSGGTwoRootParameters
