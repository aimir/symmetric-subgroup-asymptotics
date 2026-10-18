import SymmetricSubgroupAsymptotics.NormalPMonolithicCommutator

/-! The regular Klein action on four binary coordinates has exactly the
constant fixed line, also on any invariant subspace containing that line.
The two coordinate identities are actual intertwining identities, not
assumptions about normal-subgroup bounds. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace BinaryFourRegularFixedLine

variable {B V : Type} [Group B] [AddCommGroup V] [Module (ZMod 2) V]
variable (rho : Representation (ZMod 2) B V) (P : Subgroup B) [P.Normal]

/-- Applies equally to the full four-coordinate module and its augmentation
submodule: only the injection into the literal coordinates differs. -/
theorem fixed_isAtom
    (j : V →ₗ[ZMod 2] (Fin 4 → ZMod 2)) (hj : Function.Injective j)
    (u v : P)
    (hu : ∀ x i, j (rho u x) i = j x (![1, 0, 3, 2] i))
    (hv : ∀ x i, j (rho v x) i = j x (![2, 3, 0, 1] i))
    (c : V) (hc : c ∈ NormalPMonolithicCommutator.fixed rho P)
    (hjc : ∀ i, j c i = 1) :
    IsAtom (NormalPMonolithicCommutator.fixed rho P) := by
  have hcne : c ≠ 0 := by
    intro h
    have hh := hjc 0
    rw [h, map_zero] at hh
    exact zero_ne_one hh
  have hclass : ∀ x ∈ NormalPMonolithicCommutator.fixed rho P,
      x = 0 ∨ x = c := by
    intro x hx
    have hxu : rho (u : B) x = x := hx u
    have hxv : rho (v : B) x = x := hx v
    have h01 : j x 0 = j x 1 := by
      simpa only [hxu, Matrix.cons_val_zero] using hu x 0
    have h02 : j x 0 = j x 2 := by
      simpa only [hxv, Matrix.cons_val_zero] using hv x 0
    have h23 : j x 2 = j x 3 := by
      simpa only [hxu, Matrix.cons_val_succ, Matrix.cons_val_zero] using hu x 2
    have hconstant : ∀ i, j x i = j x 0 := by
      intro i
      fin_cases i
      · rfl
      · exact h01.symm
      · exact h02.symm
      · exact h23.symm.trans h02.symm
    have hbinary : j x 0 = 0 ∨ j x 0 = 1 := by
      have hall : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel
      exact hall _
    rcases hbinary with hz | ho
    · left
      apply hj
      ext i
      simpa only [map_zero, Pi.zero_apply, hz] using hconstant i
    · right
      apply hj
      ext i
      rw [hconstant, ho, hjc]
  apply isAtom_iff_le_of_ge.mpr
  constructor
  · intro hbot
    have := hc
    rw [hbot] at this
    exact hcne this
  · intro W hW hWT
    have hWsub : W.toSubmodule ≠ ⊥ := by
      intro h
      exact hW (Subrepresentation.toSubmodule_injective h)
    obtain ⟨w, hw, hwne⟩ := W.toSubmodule.ne_bot_iff.mp hWsub
    have hwc : w = c := (hclass w (hWT hw)).resolve_left hwne
    intro x hx
    rcases hclass x hx with hzero | heq
    · rw [hzero]
      exact W.toSubmodule.zero_mem
    · rw [heq, ← hwc]
      exact hw

end BinaryFourRegularFixedLine
end SymmetricSubgroupAsymptotics

end
