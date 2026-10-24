import SymmetricSubgroupAsymptotics.LinearMotionDualKernelCardinality
import SymmetricSubgroupAsymptotics.AbelianActionClassBound
import SymmetricSubgroupAsymptotics.InvariantAnnihilatorOrbitIndex
import SymmetricSubgroupAsymptotics.AffineInertiaOrbitDomination
import Mathlib.Tactic.Abel

/-! Exact commuting fibres of an actual linear semidirect product.
The SAME commuting complement pair determines the motion map and the
joint fixed functionals. No form, character classification, or orbit
bound is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.LinearSemidirectCommutingFibres
open LinearMotionDualKernelCardinality AbelianActionCommutingFibreBound
open InvariantAnnihilatorOrbitIndex AffineInertiaOrbitDomination

variable {G K V : Type*} [Group G] [Field K] [AddCommGroup V] [Module K V]

def linearActionHom (ρ : G →* (V ≃ₗ[K] V)) : G →* MulAut (Multiplicative V) where
  toFun g := {
    toFun a := Multiplicative.ofAdd (ρ g a.toAdd)
    invFun a := Multiplicative.ofAdd ((ρ g).symm a.toAdd)
    left_inv a := (ρ g).symm_apply_apply a.toAdd
    right_inv a := (ρ g).apply_symm_apply a.toAdd
    map_mul' a b := (ρ g).map_add a.toAdd b.toAdd }
  map_one' := by
    apply MulEquiv.ext
    intro a
    apply Multiplicative.toAdd.injective
    change ρ 1 a.toAdd = a.toAdd
    rw [map_one]
    rfl
  map_mul' g h := by
    apply MulEquiv.ext
    intro a
    apply Multiplicative.toAdd.injective
    change ρ (g*h) a.toAdd = ρ g (ρ h a.toAdd)
    rw [map_mul]
    rfl

abbrev AffineGroup (ρ : G →* (V ≃ₗ[K] V)) :=
  Multiplicative V ⋊[linearActionHom ρ] G

def commutingFibreEquivKernel (ρ : G →* (V ≃ₗ[K] V)) (g h : G) (hgh : Commute g h) :
    Fibre (linearActionHom ρ) g h ≃
      LinearMap.ker (motionMap (ρ g).toLinearMap (ρ h).toLinearMap) where
  toFun p := ⟨(p.val.1.toAdd, p.val.2.toAdd), by
    have he := congrArg (fun z : AffineGroup ρ => z.left.toAdd) p.property
    change p.val.1.toAdd + ρ g p.val.2.toAdd =
      p.val.2.toAdd + ρ h p.val.1.toAdd at he
    change (p.val.1.toAdd - ρ h p.val.1.toAdd) -
      (p.val.2.toAdd - ρ g p.val.2.toAdd) = 0
    calc
      _ = (p.val.1.toAdd + ρ g p.val.2.toAdd) -
          (p.val.2.toAdd + ρ h p.val.1.toAdd) := by abel
      _ = 0 := sub_eq_zero.mpr he⟩
  invFun p := ⟨(Multiplicative.ofAdd p.val.1, Multiplicative.ofAdd p.val.2), by
    change (⟨Multiplicative.ofAdd p.val.1, g⟩ : AffineGroup ρ) *
        ⟨Multiplicative.ofAdd p.val.2, h⟩ =
      ⟨Multiplicative.ofAdd p.val.2, h⟩ * ⟨Multiplicative.ofAdd p.val.1, g⟩
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      change p.val.1 + ρ g p.val.2 = p.val.2 + ρ h p.val.1
      apply sub_eq_zero.mp
      have he : (p.val.1 - ρ h p.val.1) - (p.val.2 - ρ g p.val.2) = 0 := p.property
      calc
        _ = (p.val.1 - ρ h p.val.1) - (p.val.2 - ρ g p.val.2) := by abel
        _ = 0 := he
    · exact hgh⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> rfl

theorem dual_fixed_iff (ρ : G →* (V ≃ₗ[K] V)) (g : G) (φ : Module.Dual K V) :
    letI := dualAction ρ
    g • φ = φ ↔ (ρ g).toLinearMap.dualMap φ = φ := by
  letI := dualAction ρ
  constructor
  · intro hφ
    apply LinearMap.ext
    intro v
    change φ (ρ g v) = φ v
    have he := LinearMap.congr_fun hφ (ρ g v)
    change φ (ρ g⁻¹ (ρ g v)) = φ (ρ g v) at he
    rw [map_inv] at he
    change φ ((ρ g).symm (ρ g v)) = φ (ρ g v) at he
    rw [LinearEquiv.symm_apply_apply] at he
    exact he.symm
  · intro hφ
    apply LinearMap.ext
    intro v
    change φ (ρ g⁻¹ v) = φ v
    have he := LinearMap.congr_fun hφ (ρ g⁻¹ v)
    change φ (ρ g (ρ g⁻¹ v)) = φ (ρ g⁻¹ v) at he
    rw [map_inv] at he
    change φ (ρ g ((ρ g).symm v)) = φ ((ρ g).symm v) at he
    rw [LinearEquiv.apply_symm_apply] at he
    rw [map_inv]
    change φ ((ρ g).symm v) = φ v
    exact he.symm

def jointDualFixedEquiv (ρ : G →* (V ≃ₗ[K] V)) (g h : G) :
    letI := dualAction ρ
    jointInvariantDual (ρ g).toLinearMap (ρ h).toLinearMap ≃
      jointFixed (Module.Dual K V) g h := by
  letI := dualAction ρ
  exact {
    toFun φ := ⟨φ.val,
      (dual_fixed_iff ρ g φ.val).mpr (sub_eq_zero.mp φ.property.1),
      (dual_fixed_iff ρ h φ.val).mpr (sub_eq_zero.mp φ.property.2)⟩
    invFun φ := ⟨φ.val, by
      change (ρ g).toLinearMap.dualMap φ.val - φ.val = 0 ∧
        (ρ h).toLinearMap.dualMap φ.val - φ.val = 0
      exact ⟨sub_eq_zero.mpr ((dual_fixed_iff ρ g φ.val).mp φ.property.1),
        sub_eq_zero.mpr ((dual_fixed_iff ρ h φ.val).mp φ.property.2)⟩⟩
    left_inv φ := Subtype.ext rfl
    right_inv φ := Subtype.ext rfl }

theorem commuting_fibre_card [Finite K] [Module.Finite K V]
    (ρ : G →* (V ≃ₗ[K] V)) (g h : G) (hgh : Commute g h) :
    letI := dualAction ρ
    Nat.card (Fibre (linearActionHom ρ) g h) =
      Nat.card V * Nat.card (jointFixed (Module.Dual K V) g h) := by
  letI := dualAction ρ
  calc
    _ = Nat.card (LinearMap.ker (motionMap (ρ g).toLinearMap (ρ h).toLinearMap)) :=
      Nat.card_congr (commutingFibreEquivKernel ρ g h hgh)
    _ = Nat.card V * Nat.card (jointInvariantDual (ρ g).toLinearMap (ρ h).toLinearMap) :=
      motion_kernel_card _ _
    _ = _ := congrArg (fun n : ℕ => Nat.card V * n)
      (Nat.card_congr (jointDualFixedEquiv ρ g h))

end SymmetricSubgroupAsymptotics.LinearSemidirectCommutingFibres
