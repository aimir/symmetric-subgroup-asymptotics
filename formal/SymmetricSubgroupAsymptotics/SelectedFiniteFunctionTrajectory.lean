import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Fold

/-! A displayed finite trajectory proves the value of the corresponding
ordered function applications. No injectivity or linearity is needed. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.SelectedFiniteFunctionTrajectory

theorem foldl_eq_last {V : Type*} (n : ℕ) (f : Fin n → V → V)
    (v : Fin (n+1) → V)
    (hstep : ∀ i : Fin n, f i (v i.castSucc) = v i.succ) :
    (List.ofFn f).foldl (fun x g => g x) (v 0) = v (Fin.last n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ, List.foldl_cons]
    rw [show f 0 (v 0) = v ((0 : Fin (n+1)).succ) from hstep 0]
    exact ih (fun i => f i.succ) (fun i => v i.succ) (fun i => hstep i.succ)

end SymmetricSubgroupAsymptotics.SelectedFiniteFunctionTrajectory
