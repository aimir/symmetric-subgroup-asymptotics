import SymmetricSubgroupAsymptotics.LinearJointMotionFixedDual
import SymmetricSubgroupAsymptotics.AbelianActionCommutingFibreBound
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Tactic.Abel

/-! Exact commuting-fibre duality for the original abelian semidirect
product. The linear realization is required to agree with each literal
automorphism on every original kernel element. The original two factors
are swapped only in the explicit coordinate equivalence; both projected
operators and both fixed-functional conditions remain correlated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AbelianSemidirectLinearFibreDuality
open LinearJointMotionFixedDual AbelianActionCommutingFibreBound

variable {K N G : Type*} [Field K] [CommGroup N] [Group G]
    [Module K (Additive N)]

theorem commute_iff_joint_motion_zero
    (φ : G →* MulAut N) (ρ : G →* (Additive N ≃ₗ[K] Additive N))
    (hcompat : ∀ (g : G) (n : N), ρ g (Additive.ofMul n) = Additive.ofMul (φ g n))
    (g h : G) (hgh : Commute g h) (a b : N) :
    Commute (⟨a, g⟩ : N ⋊[φ] G) (⟨b, h⟩ : N ⋊[φ] G) ↔
      jointMotion (ρ g).toLinearMap (ρ h).toLinearMap
        (Additive.ofMul b, Additive.ofMul a) = 0 := by
  constructor
  · intro hc
    have he : a * φ g b = b * φ h a := congrArg SemidirectProduct.left hc
    have ha : Additive.ofMul a + ρ g (Additive.ofMul b) =
        Additive.ofMul b + ρ h (Additive.ofMul a) := by
      rw [hcompat, hcompat]
      exact congrArg Additive.ofMul he
    change (ρ g (Additive.ofMul b) - Additive.ofMul b) +
      -(ρ h (Additive.ofMul a) - Additive.ofMul a) = 0
    calc
      _ = (Additive.ofMul a + ρ g (Additive.ofMul b)) -
          (Additive.ofMul b + ρ h (Additive.ofMul a)) := by abel
      _ = 0 := sub_eq_zero.mpr ha
  · intro hc
    have ha : Additive.ofMul a + ρ g (Additive.ofMul b) =
        Additive.ofMul b + ρ h (Additive.ofMul a) := by
      apply sub_eq_zero.mp
      calc
        _ = jointMotion (ρ g).toLinearMap (ρ h).toLinearMap
            (Additive.ofMul b, Additive.ofMul a) := by
          change _ = (ρ g (Additive.ofMul b) - Additive.ofMul b) +
            -(ρ h (Additive.ofMul a) - Additive.ofMul a)
          abel
        _ = 0 := hc
    rw [hcompat, hcompat] at ha
    apply SemidirectProduct.ext
    · exact congrArg Additive.toMul ha
    · exact hgh

def commutingFibreEquivKernel
    (φ : G →* MulAut N) (ρ : G →* (Additive N ≃ₗ[K] Additive N))
    (hcompat : ∀ (g : G) (n : N), ρ g (Additive.ofMul n) = Additive.ofMul (φ g n))
    (g h : G) (hgh : Commute g h) :
    Fibre φ g h ≃ (jointMotion (ρ g).toLinearMap (ρ h).toLinearMap).ker where
  toFun p := ⟨(Additive.ofMul p.val.2, Additive.ofMul p.val.1),
    (commute_iff_joint_motion_zero φ ρ hcompat g h hgh p.val.1 p.val.2).mp p.property⟩
  invFun p := ⟨(p.val.2.toMul, p.val.1.toMul),
    (commute_iff_joint_motion_zero φ ρ hcompat g h hgh p.val.2.toMul p.val.1.toMul).mpr
      p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_commuting_fibre [FiniteDimensional K (Additive N)]
    (φ : G →* MulAut N) (ρ : G →* (Additive N ≃ₗ[K] Additive N))
    (hcompat : ∀ (g : G) (n : N), ρ g (Additive.ofMul n) = Additive.ofMul (φ g n))
    (g h : G) (hgh : Commute g h) :
    Nat.card (Fibre φ g h) = Nat.card N *
      Nat.card {ℓ : Module.Dual K (Additive N) //
        (∀ v : Additive N, ℓ (ρ g v) = ℓ v) ∧
        (∀ v : Additive N, ℓ (ρ h v) = ℓ v)} := by
  exact (Nat.card_congr (commutingFibreEquivKernel φ ρ hcompat g h hgh)).trans
    (card_joint_motion_kernel (ρ g).toLinearMap (ρ h).toLinearMap)

end SymmetricSubgroupAsymptotics.AbelianSemidirectLinearFibreDuality
