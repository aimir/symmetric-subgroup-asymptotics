import SymmetricSubgroupAsymptotics.CFSGNormTwoRootPairing
import Mathlib.Tactic.NormNum

/-! Separation of ORIGINAL integer root degrees. Equalities are tested
in the norm-two lattice before reducing any coefficient characteristic. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoRootDegreeSeparation
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
variable {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℤ)

theorem root_val_ne_zero (k : Roots A) : k.val≠0 := by
  intro hk
  have hn := k.property
  rw [hk] at hn
  simp at hn

theorem root_val_ne_double (k l : Roots A) : k.val≠l.val+l.val := by
  intro hkl
  have hn := k.property
  rw [hkl] at hn
  simp only [map_add,LinearMap.add_apply,l.property] at hn
  norm_num at hn

theorem root_val_ne_of_ne (k l : Roots A) (hkl : k≠l) : k.val≠l.val := by
  intro h
  exact hkl (Subtype.ext h)

end SymmetricSubgroupAsymptotics.CFSGNormTwoRootDegreeSeparation
