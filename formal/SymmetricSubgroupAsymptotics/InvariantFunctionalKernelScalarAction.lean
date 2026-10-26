import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Group.Subgroup.Ker

/-! Preserving an actual functional kernel retains a genuine scalar
quotient. The scalar is derived from the SAME representation, and its
kernel fixes the actual functional. It is not replaced by a trivial
quotient action or by an assumed splitting. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.InvariantFunctionalKernelScalarAction

variable {K V G : Type*} [Field K] [AddCommGroup V] [Module K V] [Group G]
    (ρ : G →* (V ≃ₗ[K] V)) (ℓ : Module.Dual K V) (a : V)
    (ha : ℓ a=1) (hstable : ∀ (g : G) (v : V), ℓ (ρ g v)=0 ↔ ℓ v=0)
include ha hstable

theorem scalar_formula (g : G) (v : V) :
    ℓ (ρ g v)=ℓ (ρ g a)*ℓ v := by
  have hv : ℓ (v-ℓ v • a)=0 := by
    rw [map_sub,map_smul,ha,smul_eq_mul,mul_one,sub_self]
  have hz := (hstable g (v-ℓ v • a)).mpr hv
  have he : ℓ (ρ g v)-ℓ v*ℓ (ρ g a)=0 := by
    simpa only [map_sub,map_smul,smul_eq_mul] using hz
  exact (sub_eq_zero.mp he).trans (mul_comm _ _)

theorem scalar_ne_zero (g : G) : ℓ (ρ g a)≠0 := by
  intro h
  have hh := (hstable g a).mp h
  rw [ha] at hh
  exact one_ne_zero hh

def scalarHom : G →* Kˣ where
  toFun g := Units.mk0 (ℓ (ρ g a)) (scalar_ne_zero ρ ℓ a ha hstable g)
  map_one' := by
    apply Units.ext
    change ℓ (ρ 1 a)=1
    rw [ρ.map_one]
    exact ha
  map_mul' g h := by
    apply Units.ext
    change ℓ (ρ (g*h) a)=ℓ (ρ g a)*ℓ (ρ h a)
    rw [ρ.map_mul]
    exact scalar_formula ρ ℓ a ha hstable g (ρ h a)

theorem kernel_fixes_functional (g : (scalarHom ρ ℓ a ha hstable).ker) (v : V) :
    ℓ (ρ g.val v)=ℓ v := by
  have he : ℓ (ρ g.val a)=1 := congrArg Units.val g.property
  rw [scalar_formula ρ ℓ a ha hstable,he,one_mul]

end SymmetricSubgroupAsymptotics.InvariantFunctionalKernelScalarAction
