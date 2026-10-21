import SymmetricSubgroupAsymptotics.CFSGSerreDividedPowers
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.Solvable

/-! Every literal simple-root direction in the pinned construction is
commutative. This uses the actual operators and their common divided
powers, without asserting exponential additivity or invertibility. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGSerreDividedPowers
open CFSG.Models.Chevalley
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (K : Type) [Field K]

theorem baseChangedIntegralOperator_commute (negative : Bool) (i : Fin n) (k l : ℕ) :
    Commute ((integralOperator A negative i k).baseChange K)
      ((integralOperator A negative i l).baseChange K) := by
  have h := congrArg (fun f : Module.End ℤ (integralLattice A) =>
      (Module.End.baseChangeHom ℤ K (integralLattice A)) f)
    (integralOperator_commute A negative i k l).eq
  simpa only [map_mul] using h

theorem rootOperator_commute (negative : Bool) (i : Fin n) (a b : K) :
    Commute (rootOperator A K negative i a) (rootOperator A K negative i b) := by
  unfold rootOperator
  apply Commute.sum_left
  intro k hk
  apply Commute.sum_right
  intro l hl
  show (a ^ k • (integralOperator A negative i k).baseChange K) *
      (b ^ l • (integralOperator A negative i l).baseChange K) =
    (b ^ l • (integralOperator A negative i l).baseChange K) *
      (a ^ k • (integralOperator A negative i k).baseChange K)
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [(baseChangedIntegralOperator_commute A K negative i k l).eq, mul_comm (a ^ k) (b ^ l)]

theorem rootElements_commute (negative : Bool) (i : Fin n) (a b : K)
    (g h : Ambient A K) (hg : IsRootElement A K negative i a g)
    (hh : IsRootElement A K negative i b h) : Commute g h := by
  apply LinearEquiv.toLinearMap_injective
  change g.toLinearMap * h.toLinearMap = h.toLinearMap * g.toLinearMap
  rw [hg, hh]
  exact (rootOperator_commute A K negative i a b).eq

def rootDirection (negative : Bool) (i : Fin n) : Subgroup (Ambient A K) :=
  Subgroup.closure {g | ∃ a : K, IsRootElement A K negative i a g}

theorem rootDirection_commutative (negative : Bool) (i : Fin n) :
    IsMulCommutative (rootDirection A K negative i) := by
  apply Subgroup.isMulCommutative_closure
  rintro g ⟨a, ha⟩ h ⟨b, hb⟩
  exact (rootElements_commute A K negative i a b g h ha hb).eq

theorem rootDirection_soluble (negative : Bool) (i : Fin n) :
    IsSolvable (rootDirection A K negative i) := by
  letI serreRootDirection_commutative : IsMulCommutative (rootDirection A K negative i) :=
    rootDirection_commutative A K negative i
  exact isSolvable_of_comm (fun a b => mul_comm' a b)

theorem rootDirection_le_model (negative : Bool) (i : Fin n) :
    rootDirection A K negative i ≤ subgroup A K := by
  apply Subgroup.closure_mono
  rintro g ⟨a, ha⟩
  exact ⟨negative, i, a, ha⟩

theorem zero_isRootElement (negative : Bool) (i : Fin n) :
    IsRootElement A K negative i 0 (1 : Ambient A K) := by
  change (1 : Module.End K (Space A K)) = rootOperator A K negative i 0
  exact (rootOperator_zero A K negative i).symm

end SymmetricSubgroupAsymptotics.CFSGSerreDividedPowers
