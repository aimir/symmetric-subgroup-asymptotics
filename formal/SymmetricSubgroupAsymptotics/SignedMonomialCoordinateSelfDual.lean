import SymmetricSubgroupAsymptotics.SignedMonomialFixedCoordinateCode
import SymmetricSubgroupAsymptotics.LinearContragredientSmallSpaceAction
import Mathlib.LinearAlgebra.Dual.Basis

/-! The coordinate pairing intertwines a genuine monomial action and
its contragredient when its actual inverse-transported scalars agree.
The latter identity will be proved from literal binary signs, not assumed
as a class-capacity or dual-transitivity premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SignedMonomialCoordinateSelfDual

theorem delta_image {G I K : Type*} [Group G] [Field K]
    (ρ : G →* ((I → K) ≃ₗ[K] (I → K)))
    (t : G →* Equiv.Perm I) (a : G → I → Kˣ)
    (hformula : ∀ (g : G) (w : I → K) (i : I),
      ρ g w i=(a g i : K)*w ((t g).symm i)) (g : G) (i : I) :
    ρ g (Pi.single i (1 : K) : I → K)=
      (a g (t g i) : K) • (Pi.single (t g i) (1 : K) : I → K) := by
  funext j
  rw [hformula]
  by_cases hj : j=t g i
  · subst j
    have hp : (t g).symm (t g i)=i := (t g).symm_apply_apply i
    rw [hp]
    simp only [Pi.single_eq_same,Pi.smul_apply,smul_eq_mul]
  · have hpre : (t g).symm j≠i := by
      intro he
      have hji : j=t g i := ((t g).apply_symm_apply j).symm.trans (congrArg (t g) he)
      exact hj hji
    simp only [Pi.single_eq_of_ne hpre,Pi.smul_apply,Pi.single_eq_of_ne hj,
      smul_eq_mul,mul_zero]

def coordinateDualEquiv {I K : Type*} [Field K] [Finite I] :
    (I → K) ≃ₗ[K] Module.Dual K (I → K) :=
  (Pi.basisFun K I).toDualEquiv

theorem coordinateDualEquiv_intertwines
    {G I K : Type*} [Group G] [Field K] [Finite I]
    (ρ : G →* ((I → K) ≃ₗ[K] (I → K)))
    (t : G →* Equiv.Perm I) (a : G → I → Kˣ)
    (hformula : ∀ (g : G) (w : I → K) (i : I),
      ρ g w i=(a g i : K)*w ((t g).symm i))
    (hinverse : ∀ (g : G) (i : I),a g⁻¹ ((t g).symm i)=a g i)
    (g : G) (v : I → K) :
    coordinateDualEquiv (ρ g v)=
      LinearContragredientSmallSpaceAction.contragredient ρ g (coordinateDualEquiv v) := by
  apply (Pi.basisFun K I).ext
  intro i
  let j := (t g).symm i
  have hj : t g⁻¹ i=j := by rw [map_inv]; rfl
  have hsingle : (ρ g).symm ((Pi.basisFun K I) i)=
      (a g i : K) • (Pi.basisFun K I) j := by
    have hρ : (ρ g).symm=ρ g⁻¹ := by rw [ρ.map_inv]; rfl
    rw [hρ,Pi.basisFun_apply]
    have h := delta_image ρ t a hformula g⁻¹ i
    have hiunit : a g⁻¹ j=a g i := hinverse g i
    simpa only [hj,Pi.basisFun_apply,hiunit] using h
  change (Pi.basisFun K I).toDual (ρ g v) ((Pi.basisFun K I) i)=
    (Pi.basisFun K I).toDual v ((ρ g).symm ((Pi.basisFun K I) i))
  rw [hsingle,map_smul,(Pi.basisFun K I).toDual_apply_left,
    (Pi.basisFun K I).toDual_apply_left,Pi.basisFun_repr,Pi.basisFun_repr]
  change ρ g v i=(a g i : K)*v j
  exact hformula g v i

end SymmetricSubgroupAsymptotics.SignedMonomialCoordinateSelfDual
