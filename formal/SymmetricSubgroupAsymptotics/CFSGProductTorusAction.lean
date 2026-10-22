import SymmetricSubgroupAsymptotics.CFSGIntegerMatrixPowerHom
import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.Algebra.BigOperators.Pi

/-! A commuting family of actual rank-one tori realizes the literal
Cartan power map on the same root parameters. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGProductTorusAction
open CFSGIntegerMatrixPowerHom
variable {I K G : Type*} [Fintype I] [DecidableEq I] [Field K] [Group G]

@[simp] theorem powerHom_mulSingle (A : Matrix I I ℤ) (j : I) (t : Kˣ) (i : I) :
    powerHom (G := Kˣ) A (Pi.mulSingle j t) i = t ^ A i j := by
  classical
  simp [powerHom, Pi.mulSingle_apply]

variable (torus : I → Kˣ →* G)
    (hc : Pairwise fun i j => ∀ x y, Commute (torus i x) (torus j y))

def productTorusHom : (I → Kˣ) →* G := MonoidHom.noncommPiCoprod torus hc

/-- The rank-one identities imply the exact full Cartan scaling vector,
with no unproved compatibility or torus-size premise. -/
theorem product_action (A : Matrix I I ℤ) (root : I → Multiplicative K →* G)
    (hact : ∀ j t i a, torus j t * root i (Multiplicative.ofAdd a) * (torus j t)⁻¹ =
      root i (Multiplicative.ofAdd (a * (t : K) ^ A i j))) (x : I → Kˣ) (i : I) (a : K) :
    productTorusHom torus hc x * root i (Multiplicative.ofAdd a) *
        (productTorusHom torus hc x)⁻¹ =
      root i (Multiplicative.ofAdd (a * (powerHom (G := Kˣ) A x i : K))) := by
  let T := productTorusHom torus hc
  suffices ∀ a, T x * root i (Multiplicative.ofAdd a) * (T x)⁻¹ =
      root i (Multiplicative.ofAdd (a * (powerHom (G := Kˣ) A x i : K))) from this a
  apply Pi.mulSingle_induction (fun y : I → Kˣ => ∀ a,
    T y * root i (Multiplicative.ofAdd a) * (T y)⁻¹ =
      root i (Multiplicative.ofAdd (a * (powerHom (G := Kˣ) A y i : K)))) x
  · intro a
    simp
  · intro y z hy hz a
    calc
      T (y * z) * root i (Multiplicative.ofAdd a) * (T (y * z))⁻¹ =
          T y * (T z * root i (Multiplicative.ofAdd a) * (T z)⁻¹) * (T y)⁻¹ := by
        simp only [map_mul, mul_inv_rev]
        group
      _ = root i (Multiplicative.ofAdd ((a * (powerHom (G := Kˣ) A z i : K)) * (powerHom (G := Kˣ) A y i : K))) :=
        by rw [hz, hy]
      _ = root i (Multiplicative.ofAdd (a * (powerHom (G := Kˣ) A (y * z) i : K))) := by
        simp only [map_mul, Pi.mul_apply, Units.val_mul]
        congr 2
        ring
  · intro j t a
    change MonoidHom.noncommPiCoprod torus hc (Pi.mulSingle j t) * _ *
      (MonoidHom.noncommPiCoprod torus hc (Pi.mulSingle j t))⁻¹ = _
    rw [MonoidHom.noncommPiCoprod_mulSingle, powerHom_mulSingle]
    simpa only [Units.val_zpow_eq_zpow_val] using hact j t i a

end SymmetricSubgroupAsymptotics.CFSGProductTorusAction
