import Mathlib.Algebra.Field.Equiv
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.GroupWithZero.Units.Basic

/-! One shear reflection forces a common field automorphism on two
scalar axes. This elementary argument is independent of any group model.
An application must prove the actual compatibility with its Weyl word;
this file does not assume or supply that geometric compatibility. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.SemilinearScalarPairRigidity
variable {K : Type*} [Field K]

def diagonalAction (tau nu : K ≃+* K) (p : Kˣ × Kˣ) : Kˣ × Kˣ :=
  (Units.map tau.toMonoidHom p.1, Units.map nu.toMonoidHom p.2)

def shearReflection (p : Kˣ × Kˣ) : Kˣ × Kˣ :=
  (p.1⁻¹, p.1*p.2)

theorem ringEquiv_eq_of_units (tau nu : K ≃+* K)
    (h : ∀ u : Kˣ, Units.map tau.toMonoidHom u = Units.map nu.toMonoidHom u) :
    tau = nu := by
  apply RingEquiv.ext
  intro x
  by_cases hx : x = 0
  · subst x
    exact (map_zero tau).trans (map_zero nu).symm
  · have he := congrArg (fun u : Kˣ => u.val) (h (Units.mk0 x hx))
    exact he

theorem ringEquiv_eq_of_commute (tau nu : K ≃+* K)
    (h : ∀ p : Kˣ × Kˣ,
      diagonalAction tau nu (shearReflection p) =
        shearReflection (diagonalAction tau nu p)) : tau = nu := by
  apply ringEquiv_eq_of_units
  intro u
  have he := congrArg (fun p : Kˣ × Kˣ => p.2) (h (u,1))
  change Units.map nu.toMonoidHom (u*1) =
    Units.map tau.toMonoidHom u * Units.map nu.toMonoidHom 1 at he
  simpa only [mul_one, map_one] using he.symm

end SymmetricSubgroupAsymptotics.SemilinearScalarPairRigidity
