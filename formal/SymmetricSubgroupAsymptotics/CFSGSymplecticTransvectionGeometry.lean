import SymmetricSubgroupAsymptotics.CFSGSymplecticTransvectionForm
import Mathlib.Algebra.Module.Equiv.Basic

/-! Genuine natural symplectic transvections on the original paired
vector space. Their commutation relation is exactly orthogonality,
in every characteristic. No intrinsic recognition of these elements
by abstract group automorphisms is asserted here. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticTransvectionGeometry
open CFSGSymplecticSerreMatrices
variable {K : Type} [Field K]

def transvection (r : ℕ) (v : Index r → K) (a : K) : (Index r → K) ≃ₗ[K] (Index r → K) where
  toFun x := x + (a * pairing r v x) • v
  invFun x := x + ((-a) * pairing r v x) • v
  left_inv x := by
    funext i
    simp only [pairing_add_right, pairing_smul_right, pairing_self, mul_zero, add_zero,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  right_inv x := by
    funext i
    simp only [pairing_add_right, pairing_smul_right, pairing_self, mul_zero, add_zero,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  map_add' x y := by
    funext i
    simp only [pairing_add_right, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  map_smul' c x := by
    funext i
    simp only [pairing_smul_right, Pi.add_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem transvection_apply (r : ℕ) (v x : Index r → K) (a : K) :
    transvection r v a x = x + (a * pairing r v x) • v := rfl

@[simp] theorem transvection_self (r : ℕ) (v : Index r → K) (a : K) :
    transvection r v a v = v := by
  simp only [transvection_apply, pairing_self, mul_zero, zero_smul, add_zero]

@[simp] theorem transvection_zero (r : ℕ) (v : Index r → K) : transvection r v 0 = 1 := by
  apply LinearEquiv.ext
  intro x
  change x + (0 * pairing r v x) • v = x
  simp only [zero_mul, zero_smul, add_zero]

theorem transvection_add (r : ℕ) (v : Index r → K) (a b : K) :
    transvection r v (a + b) = transvection r v a * transvection r v b := by
  apply LinearEquiv.ext
  intro x
  funext i
  simp only [LinearEquiv.mul_apply, transvection_apply, pairing_add_right,
    pairing_smul_right, pairing_self, mul_zero, add_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem transvection_preserves_pairing (r : ℕ) (v x y : Index r → K) (a : K) :
    pairing r (transvection r v a x) (transvection r v a y) = pairing r x y := by
  simp only [transvection_apply, pairing_add_left, pairing_add_right,
    pairing_smul_left, pairing_smul_right, pairing_self, mul_zero, add_zero]
  rw [pairing_swap r x v]
  ring

theorem transvection_parameter_injective (r : ℕ) (v : Index r → K) (hv : v ≠ 0) :
    Function.Injective (transvection r v) := by
  intro a b hab
  obtain ⟨x, hx⟩ := exists_pairing_ne_zero r v hv
  have he := congrArg (fun f : (Index r → K) ≃ₗ[K] (Index r → K) => f x) hab
  simp only [transvection_apply] at he
  have hc : (a * pairing r v x) • v = (b * pairing r v x) • v := add_left_cancel he
  have hscalar : a * pairing r v x = b * pairing r v x := (smul_left_injective K hv) hc
  exact mul_right_cancel₀ hx hscalar

theorem transvection_commute_iff (r : ℕ) (v w : Index r → K) (a b : K)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    Commute (transvection r v a) (transvection r w b) ↔ pairing r v w = 0 := by
  constructor
  · intro hc
    by_contra hvw
    have hwv : pairing r w v ≠ 0 := by rw [pairing_swap]; exact neg_ne_zero.mpr hvw
    have he := congrArg (fun f : (Index r → K) ≃ₗ[K] (Index r → K) => f v) hc.eq
    have hx : (v + (b * pairing r w v) • w) +
        (a * ((b * pairing r w v) * pairing r v w)) • v =
        v + (b * pairing r w v) • w := by
      simpa only [LinearEquiv.mul_apply, transvection_apply, pairing_add_right,
        pairing_smul_right, pairing_self, mul_zero, zero_smul, add_zero, zero_add] using he
    have hz : (a * ((b * pairing r w v) * pairing r v w)) • v = 0 :=
      add_left_cancel (hx.trans (add_zero _).symm)
    have hcoef : a * ((b * pairing r w v) * pairing r v w) ≠ 0 :=
      mul_ne_zero ha (mul_ne_zero (mul_ne_zero hb hwv) hvw)
    have hv0 : v = 0 := (smul_eq_zero.mp hz).resolve_left hcoef
    exact hvw (by rw [hv0, pairing_zero_left])
  · intro hvw
    have hwv : pairing r w v = 0 := by rw [pairing_swap, hvw, neg_zero]
    change transvection r v a * transvection r w b = transvection r w b * transvection r v a
    apply LinearEquiv.ext
    intro x
    funext i
    simp only [LinearEquiv.mul_apply, transvection_apply, pairing_add_right,
      pairing_smul_right, hvw, hwv, mul_zero, add_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

end SymmetricSubgroupAsymptotics.CFSGSymplecticTransvectionGeometry
