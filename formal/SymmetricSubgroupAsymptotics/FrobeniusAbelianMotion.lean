import Mathlib.Algebra.Group.End
import Mathlib.Data.Finite.Card
import Mathlib.Algebra.Group.Hom.Defs

/-! For an automorphism of a finite abelian group with no nonidentity
fixed point, its actual multiplicative difference is an automorphism.
This is the commuting-fibre solver for abelian Frobenius kernels. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FrobeniusAbelianMotion

variable {N : Type*} [CommGroup N]

def motion (a : MulAut N) : N →* N where
  toFun n := a n*n⁻¹
  map_one' := by simp
  map_mul' n m := by
    simp only [map_mul, mul_inv_rev]
    simp only [mul_assoc, mul_comm, mul_left_comm]

theorem motion_injective (a : MulAut N)
    (hfree : ∀ n : N, a n=n → n=1) : Function.Injective (motion a) := by
  intro n m he
  have hker : motion a (n*m⁻¹)=1 := by
    rw [map_mul, map_inv, he, mul_inv_cancel]
  have hfix : a (n*m⁻¹)=n*m⁻¹ := mul_inv_eq_one.mp hker
  exact mul_inv_eq_one.mp (hfree _ hfix)

def motionEquiv [Finite N] (a : MulAut N)
    (hfree : ∀ n : N, a n=n → n=1) : N ≃* N :=
  MulEquiv.ofBijective (motion a)
    ⟨motion_injective a hfree, Finite.surjective_of_injective (motion_injective a hfree)⟩

theorem motionEquiv_apply [Finite N] (a : MulAut N)
    (hfree : ∀ n : N, a n=n → n=1) (n : N) :
    motionEquiv a hfree n=a n*n⁻¹ := rfl

end SymmetricSubgroupAsymptotics.FrobeniusAbelianMotion
