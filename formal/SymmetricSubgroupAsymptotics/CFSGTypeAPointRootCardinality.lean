import SymmetricSubgroupAsymptotics.CFSGTypeAProjectivePointRoots
import Mathlib.FieldTheory.Finiteness
import Lean.Elab.Tactic.Omega

/-! The exact original point-root size q^(n-1), obtained from the dual
hyperplane of forms vanishing on the original nonzero centre vector. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeAProjectivePointRoots
open Module LinearMap Matrix
variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n]

def pointEvaluation (v : n→F) : Dual F (Dual F (n→F)) where
  toFun f := f v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype n] [DecidableEq n] in
theorem pointEvaluation_ker (v : n→F) :
    LinearMap.ker (pointEvaluation v)=pointForms v := rfl

omit [Fintype n] [DecidableEq n] in
theorem pointEvaluation_ne_zero {v : n→F} (hv : v≠0) : pointEvaluation v≠0 := by
  intro he
  apply hv
  funext i
  have hh := congrArg (fun f : Dual F (Dual F (n→F)) => f (LinearMap.proj i)) he
  exact hh

theorem pointForms_finrank_add_one {v : n→F} (hv : v≠0) :
    Module.finrank F (pointForms v)+1=Fintype.card n := by
  have hh := Module.Dual.finrank_ker_add_one_of_ne_zero (pointEvaluation_ne_zero hv)
  simpa only [pointEvaluation_ker,Subspace.dual_finrank_eq,
    Module.finrank_fintype_fun_eq_card] using hh

theorem pointForms_finrank {v : n→F} (hv : v≠0) :
    Module.finrank F (pointForms v)=Fintype.card n-1 := by
  have hh := pointForms_finrank_add_one hv
  omega

theorem pointRoot_card {v : n→F} (hv : v≠0) :
    Nat.card (pointRoot v)=Nat.card F^(Fintype.card n-1) := by
  let e : Multiplicative (pointForms v)≃pointForms v :=
    ⟨Multiplicative.toAdd,Multiplicative.ofAdd,fun _ => rfl,fun _ => rfl⟩
  calc
    Nat.card (pointRoot v)=Nat.card (Multiplicative (pointForms v)) :=
      Nat.card_congr (pointRootEquiv hv).toEquiv.symm
    _=Nat.card (pointForms v) := Nat.card_congr e
    _=Nat.card F^Module.finrank F (pointForms v) :=
      Module.natCard_eq_pow_finrank (K:=F) (V:=pointForms v)
    _=Nat.card F^(Fintype.card n-1) := by rw [pointForms_finrank hv]

end SymmetricSubgroupAsymptotics.CFSGTypeAProjectivePointRoots
