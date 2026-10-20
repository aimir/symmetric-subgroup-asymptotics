import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.GroupAction.Basic

/-! Exact symmetric and alternating point stabilizers on the displayed
finite point set. The maps extend permutations of the successor points and
fix zero; their signs and inverse restrictions are proved symbolically. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.FinZeroPermutationStabilizer

open Equiv

variable (n : ℕ)

def lift : Perm (Fin n) →* Perm (Fin (n + 1)) where
  toFun g := Perm.decomposeFin.symm (0, g)
  map_one' := by
    ext x
    refine Fin.cases ?_ (fun i => ?_) x <;> simp
  map_mul' g h := by
    ext x
    refine Fin.cases ?_ (fun i => ?_) x <;> simp

@[simp] theorem lift_zero (g : Perm (Fin n)) : lift n g 0 = 0 := by
  exact Perm.decomposeFin_symm_apply_zero 0 g

@[simp] theorem lift_succ (g : Perm (Fin n)) (i : Fin n) :
    lift n g i.succ = (g i).succ := by
  simpa only [Equiv.swap_self, Equiv.refl_apply] using
    Perm.decomposeFin_symm_apply_succ g 0 i

theorem lift_injective : Function.Injective (lift n) := by
  intro g h he
  apply Equiv.ext
  intro i
  apply Fin.succ_injective
  simpa only [lift_succ] using DFunLike.congr_fun he i.succ

@[simp] theorem sign_lift (g : Perm (Fin n)) : Perm.sign (lift n g) = Perm.sign g := by
  simpa only [ite_true, one_mul] using Perm.decomposeFin.symm_sign (0 : Fin (n + 1)) g

theorem lift_decompose_of_fixes {g : Perm (Fin (n + 1))} (hg : g 0 = 0) :
    lift n (Perm.decomposeFin g).2 = g := by
  have hzero : (Perm.decomposeFin g).1 = 0 := by
    calc
      (Perm.decomposeFin g).1 = Perm.decomposeFin.symm (Perm.decomposeFin g) 0 :=
        (Perm.decomposeFin_symm_apply_zero _ _).symm
      _ = g 0 := congrArg (fun q : Perm (Fin (n + 1)) => q 0)
        (Perm.decomposeFin.symm_apply_apply g)
      _ = 0 := hg
  change Perm.decomposeFin.symm (0, (Perm.decomposeFin g).2) = g
  rw [← hzero]
  exact Perm.decomposeFin.symm_apply_apply g

def toSymmetricStabilizer :
    Perm (Fin n) →* MulAction.stabilizer (Perm (Fin (n + 1))) (0 : Fin (n + 1)) where
  toFun g := ⟨lift n g, lift_zero n g⟩
  map_one' := by apply Subtype.ext; exact (lift n).map_one
  map_mul' g h := by apply Subtype.ext; exact (lift n).map_mul g h

def symmetricEquiv :
    Perm (Fin n) ≃* MulAction.stabilizer (Perm (Fin (n + 1))) (0 : Fin (n + 1)) :=
  MulEquiv.ofBijective (toSymmetricStabilizer n) ⟨
    fun _ _ h => lift_injective n (congrArg Subtype.val h),
    fun g => ⟨(Perm.decomposeFin g.1).2, Subtype.ext (lift_decompose_of_fixes n g.2)⟩⟩

def toAlternatingStabilizer : alternatingGroup (Fin n) →*
    MulAction.stabilizer (alternatingGroup (Fin (n + 1))) (0 : Fin (n + 1)) where
  toFun g := ⟨⟨lift n g.1, by
    change Perm.sign (lift n g.1) = 1
    rw [sign_lift]
    exact g.2⟩, lift_zero n g.1⟩
  map_one' := by apply Subtype.ext; apply Subtype.ext; exact (lift n).map_one
  map_mul' g h := by apply Subtype.ext; apply Subtype.ext; exact (lift n).map_mul g.1 h.1

def alternatingEquiv : alternatingGroup (Fin n) ≃*
    MulAction.stabilizer (alternatingGroup (Fin (n + 1))) (0 : Fin (n + 1)) :=
  MulEquiv.ofBijective (toAlternatingStabilizer n) (by
    constructor
    · intro g h he
      apply Subtype.ext
      apply lift_injective n
      exact congrArg
        (fun q : MulAction.stabilizer (alternatingGroup (Fin (n + 1)))
          (0 : Fin (n + 1)) => (q.1 : Perm (Fin (n + 1)))) he
    · intro g
      let q : Perm (Fin n) := (Perm.decomposeFin g.1.1).2
      have hq : lift n q = g.1.1 := lift_decompose_of_fixes n g.2
      have hsign : q ∈ alternatingGroup (Fin n) := by
        change Perm.sign q = 1
        rw [← sign_lift n q, hq]
        exact g.1.2
      refine ⟨⟨q, hsign⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hq)

end SymmetricSubgroupAsymptotics.FinZeroPermutationStabilizer

end
