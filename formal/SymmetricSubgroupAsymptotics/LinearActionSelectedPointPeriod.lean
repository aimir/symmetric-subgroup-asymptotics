import SymmetricSubgroupAsymptotics.PointPeriodTwicePrimeOrder
import Mathlib.Algebra.Module.Equiv.Basic

/-! Transport of a selected period through an ABSTRACT original linear
action. The action, group element, endomorphism and vector are parameters;
no concrete matrix entries or expanded unit powers enter this proof.
Concrete consumers supply one genuine endomorphism equality. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.LinearActionSelectedPointPeriod

variable {G R V : Type*} [Group G] [Semiring R] [AddCommMonoid V] [Module R V]

theorem fourteen_dvd_orderOf (rho : G →* (V ≃ₗ[R] V)) (g : G)
    (A : Module.End R V)
    (hA : (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp rho) g = A)
    (v : V) (hreturn : (A^14) v = v)
    (htwo : (A^2) v ≠ v) (hseven : (A^7) v ≠ v) : 14 ∣ orderOf g := by
  letI : MulAction G V := MulAction.compHom V rho
  have hpow (n : ℕ) : g^n • v = (A^n) v := by
    change ((LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp rho) (g^n)) v = (A^n) v
    rw [map_pow,hA]
  apply PointPeriodTwicePrimeOrder.fourteen_dvd_orderOf g v
  · exact (hpow 14).trans hreturn
  · exact fun h => htwo ((hpow 2).symm.trans h)
  · exact fun h => hseven ((hpow 7).symm.trans h)

end SymmetricSubgroupAsymptotics.LinearActionSelectedPointPeriod
