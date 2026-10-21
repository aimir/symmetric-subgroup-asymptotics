import SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotentArray
import SymmetricSubgroupAsymptotics.CFSGSuzukiFieldParameters

/-! Exact multiplication and powers of the original pinned Suzuki matrices
and their canonical invertible lifts. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotent
open CFSG.Models.SuzukiConstruction
open CFSGSuzukiFieldParameters

abbrev Ambient (m : ℕ) := Matrix.GeneralLinearGroup (Fin 4) (CFSG.Models.SuzukiConstruction.Field m)

theorem unipotent_eq_twistedArray (m : ℕ) (a b : CFSG.Models.SuzukiConstruction.Field m) :
    unipotent m a b = twistedArray (theta m) a b := rfl

@[simp] theorem unipotent_zero (m : ℕ) : unipotent m 0 0 = 1 :=
  twistedArray_zero (theta m)

theorem unipotent_mul (m : ℕ) (a b c d : CFSG.Models.SuzukiConstruction.Field m) :
    unipotent m a b * unipotent m c d =
      unipotent m (a + c) (b + d + theta m a * c) :=
  twistedArray_mul (theta m) (theta_twice m) a b c d

theorem unipotent_square (m : ℕ) (a b : CFSG.Models.SuzukiConstruction.Field m) :
    unipotent m a b * unipotent m a b = unipotent m 0 (theta m a * a) :=
  twistedArray_square (theta m) (theta_twice m) a b

theorem unipotent_four (m : ℕ) (a b : CFSG.Models.SuzukiConstruction.Field m) :
    unipotent m a b ^ 4 = 1 :=
  twistedArray_four (theta m) (theta_twice m) a b

def unipotentElement (m : ℕ) (a b : CFSG.Models.SuzukiConstruction.Field m) : Ambient m :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (unipotent m a b)
    (by rw [unipotent_det]; exact one_ne_zero)

@[simp] theorem unipotentElement_coe (m : ℕ) (a b : CFSG.Models.SuzukiConstruction.Field m) :
    (unipotentElement m a b : Mat m) = unipotent m a b := rfl

@[simp] theorem unipotentElement_zero (m : ℕ) : unipotentElement m 0 0 = 1 := by
  apply Units.ext
  exact unipotent_zero m

theorem unipotentElement_mul (m : ℕ) (a b c d : CFSG.Models.SuzukiConstruction.Field m) :
    unipotentElement m a b * unipotentElement m c d =
      unipotentElement m (a + c) (b + d + theta m a * c) := by
  apply Units.ext
  exact unipotent_mul m a b c d

@[simp] theorem unipotentElement_inv (m : ℕ) (a b : CFSG.Models.SuzukiConstruction.Field m) :
    (unipotentElement m a b)⁻¹ = unipotentElement m a (b + theta m a * a) := by
  apply inv_eq_of_mul_eq_one_right
  apply Units.ext
  exact twistedArray_mul_inverse (theta m) (theta_twice m) a b

theorem unipotentElement_four (m : ℕ) (a b : CFSG.Models.SuzukiConstruction.Field m) :
    unipotentElement m a b ^ 4 = 1 := by
  apply Units.ext
  change unipotent m a b ^ 4 = 1
  exact unipotent_four m a b

theorem unipotentElement_injective (m : ℕ) :
    Function.Injective (fun ab : CFSG.Models.SuzukiConstruction.Field m ×
      CFSG.Models.SuzukiConstruction.Field m => unipotentElement m ab.1 ab.2) := by
  intro ab cd h
  have ha := congrArg (fun g : Ambient m => (g : Mat m) 1 0) h
  have hb := congrArg (fun g : Ambient m => (g : Mat m) 2 0) h
  exact Prod.ext ha hb

theorem unipotentElement_mem_model (m : ℕ) (a b : CFSG.Models.SuzukiConstruction.Field m) :
    unipotentElement m a b ∈ subgroup m :=
  Subgroup.subset_closure (Or.inl ⟨a, b, rfl⟩)

end SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotent
