import SymmetricSubgroupAsymptotics.CFSGSerreDividedPowerPathComposition
import SymmetricSubgroupAsymptotics.CFSGSerreCrossNodeCommutation

/-! Commuting actual original divided-power operators through a specified
finite path. The fold argument is proved for abstract functions first,
so its kernel proof never expands the Serre lattice construction. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreDividedPowerPathCommutation

/-- Execute instructions from left to right, with no algebraic hypotheses. -/
def execute {S M : Type*} (D : S → M → M) : List S → M → M
  | [], x => x
  | s :: ss, x => execute D ss (D s x)

theorem execute_commute {S M : Type*} (D : S → M → M) (F : M → M)
    (ss : List S) (hcomm : ∀ s ∈ ss, Function.Commute F (D s)) (x : M) :
    F (execute D ss x) = execute D ss (F x) := by
  induction ss generalizing x with
  | nil => rfl
  | cons s ss ih =>
    have hs : Function.Commute F (D s) := hcomm s List.mem_cons_self
    have ht : ∀ t ∈ ss, Function.Commute F (D t) :=
      fun t ht => hcomm t (List.mem_cons_of_mem _ ht)
    change F (execute D ss (D s x)) = execute D ss (D s (F x))
    rw [ih ht, hs x]

open CFSG.Models.Chevalley CFSGSerreDividedPowerPaths
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)

private theorem applySteps_eq_execute (f : Bool) (ss : List (Fin r × ℕ))
    (x : integralLattice A) :
    applySteps A f ss x = execute (fun s => integralOperator A f s.1 s.2) ss x := by
  induction ss generalizing x with
  | nil => rfl
  | cons s ss ih => exact ih _

theorem applySteps_commute_of_lie_zero (e f : Bool) (i : Fin r) (k : ℕ)
    (ss : List (Fin r × ℕ))
    (hzero : ∀ s ∈ ss, ⁅rootVector A e i, rootVector A f s.1⁆ = 0)
    (x : integralLattice A) :
    integralOperator A e i k (applySteps A f ss x) =
      applySteps A f ss (integralOperator A e i k x) := by
  rw [applySteps_eq_execute, applySteps_eq_execute]
  apply execute_commute
  intro s hs y
  have hc := CFSGSerreCrossNodeCommutation.integralOperators_commute_of_lie_zero
    A e f i s.1 (hzero s hs) k s.2
  exact congrArg (fun D : Module.End ℤ (integralLattice A) => D y) hc.eq

theorem path_commute_of_lie_zero (e f : Bool) (i : Fin r) (k : ℕ)
    (start : Fin r) (ss : List (Fin r × ℕ))
    (hzero : ∀ s ∈ ss, ⁅rootVector A e i, rootVector A f s.1⁆ = 0) :
    integralOperator A e i k (pathVector A f start ss) =
      applySteps A f ss (integralOperator A e i k
        (CFSGSerreDiagram.latticeGenerator A (if f then .F start else .E start))) :=
  applySteps_commute_of_lie_zero A e f i k ss hzero _

end SymmetricSubgroupAsymptotics.CFSGSerreDividedPowerPathCommutation
