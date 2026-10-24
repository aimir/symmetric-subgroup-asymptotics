import Mathlib.Algebra.Lie.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

/-! Sparse double-derivation identities for rational source Lie
algebras. In particular, two length-one strings through a common
raising direction have commuting raised vectors when their starting
vectors commute. The division by two takes place over the original
rational source, before any integral lattice reduction. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGRationalLieDoubleDerivation
variable {L:Type*} [LieRing L] [LieAlgebra ℚ L]

theorem lie_twice_bracket (x y z:L) :
    ⁅x,⁅x,⁅y,z⁆⁆⁆=
      ⁅⁅x,⁅x,y⁆⁆,z⁆+(2:ℚ) • ⁅⁅x,y⁆,⁅x,z⁆⁆+⁅y,⁅x,⁅x,z⁆⁆⁆ := by
  rw [leibniz_lie x y z,lie_add,leibniz_lie x ⁅x,y⁆ z,
    leibniz_lie x y ⁅x,z⁆]
  module

theorem raised_commute_of_two_strings (x y z:L) (hyz:⁅y,z⁆=0)
    (hxy:⁅x,⁅x,y⁆⁆=0) (hxz:⁅x,⁅x,z⁆⁆=0) :
    ⁅⁅x,y⁆,⁅x,z⁆⁆=0 := by
  have h:=lie_twice_bracket x y z
  rw [hyz,lie_zero,lie_zero,hxy,hxz,zero_lie,lie_zero,add_zero,zero_add] at h
  exact (smul_eq_zero.mp h.symm).resolve_left (by norm_num : (2:ℚ)≠0)

end SymmetricSubgroupAsymptotics.CFSGRationalLieDoubleDerivation
