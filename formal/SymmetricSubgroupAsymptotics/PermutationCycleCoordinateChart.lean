import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Logic.Equiv.Fin.Rotate

/-! Actual cyclic coordinates on each orbit of a finite permutation,
including its fixed points. The length is the actual minimal period,
and rotation intertwines the chart with the given permutation. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PermutationCycleCoordinateChart

theorem iterate_rotate {I : Type*} (f : I → I) (x : I) (m : ℕ)
    (hm : f^[m] x=x) (i : Fin m) :
    f^[((finRotate m i).val)] x=f (f^[i.val] x) := by
  cases m with
  | zero => exact Fin.elim0 i
  | succ n =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [finRotate_last]
      simpa only [Fin.val_zero,Fin.val_last,Function.iterate_zero_apply,
        Function.iterate_succ_apply'] using hm.symm
    · have hr : finRotate (n+1) j.castSucc=j.succ := finRotate_of_lt j.isLt
      rw [hr]
      exact Function.iterate_succ_apply' f j.val x

variable {I : Type*} [Finite I] (σ : Equiv.Perm I) (x : I)

theorem cycleLength_pos : 0<Function.minimalPeriod (σ : I → I) x :=
  Function.minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts x)

def orbitChart : Fin (Function.minimalPeriod (σ : I → I) x) ≃
    {y : I // σ.SameCycle x y} :=
  Equiv.ofBijective (fun i => ⟨(σ : I → I)^[i.val] x,by
      refine ⟨(i.val : ℤ),?_⟩
      simp only [zpow_natCast,Equiv.Perm.coe_pow]⟩) (by
    constructor
    · intro i j he
      apply Fin.ext
      exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
        i.isLt j.isLt).mp (congrArg Subtype.val he)
    · intro y
      obtain ⟨m,hm⟩ := y.property.exists_nat_pow_eq
      refine ⟨⟨m % Function.minimalPeriod (σ : I → I) x,
        Nat.mod_lt _ (cycleLength_pos σ x)⟩,?_⟩
      apply Subtype.ext
      change (σ : I → I)^[m % Function.minimalPeriod (σ : I → I) x] x=y.val
      rw [Function.iterate_mod_minimalPeriod_eq]
      simpa only [Equiv.Perm.coe_pow] using hm)

theorem orbitChart_apply (i : Fin (Function.minimalPeriod (σ : I → I) x)) :
    (orbitChart σ x i).val=(σ : I → I)^[i.val] x := rfl

theorem orbitChart_rotate (i : Fin (Function.minimalPeriod (σ : I → I) x)) :
    (orbitChart σ x (finRotate _ i)).val=σ (orbitChart σ x i).val := by
  simp only [orbitChart_apply]
  exact iterate_rotate (σ : I → I) x _ (Function.iterate_minimalPeriod) i

end SymmetricSubgroupAsymptotics.PermutationCycleCoordinateChart
