import SymmetricSubgroupAsymptotics.CFSGSesquilinearSimilitudeRigidity
import SymmetricSubgroupAsymptotics.CFSGHermitianPairTransport
import Mathlib.LinearAlgebra.Dual.Basis

/-! The common-multiplier theorem on the literal finite-field matrix
pairing sigma(v) dot H*w. Any invertible matrix H is allowed; in particular
the original signed reversal is retained without skew normalization.
Neither an abstract duality nor field-involution coherence is an input. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFiniteHermitianSimilitudeRigidity
open CFSGTwistedAUnitaryParameters
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
local instance (s : K ≃+* K) : RingHomInvPair s.toRingHom s.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv s
local instance (s : K ≃+* K) : RingHomInvPair s.symm.toRingHom s.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm s

def hermitianDual (sigma : K ≃+* K) (H : (Matrix I I K)ˣ) :
    (I → K) →+ Module.Dual K (I → K) where
  toFun v := {
    toFun := hermitianPair sigma H v
    map_add' := hermitianPair_add_right sigma H v
    map_smul' := by
      intro a w
      change hermitianPair sigma H v (a • w) = a * hermitianPair sigma H v w
      simpa only [one_smul, map_one, one_mul] using hermitianPair_smul sigma H 1 a v w }
  map_zero' := by
    apply LinearMap.ext
    intro w
    change hermitianPair sigma H 0 w = 0
    simp [hermitianPair, Function.comp_def]
  map_add' v z := by
    apply LinearMap.ext
    intro w
    exact hermitianPair_add_left sigma H v z w

theorem hermitianDual_injective (sigma : K ≃+* K) (H : (Matrix I I K)ˣ) :
    Function.Injective (hermitianDual sigma H) := by
  intro v w hvw
  by_contra hne
  have hne' : v - w ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨z, hz⟩ := hermitianPair_surjective sigma H (v - w) hne' 1
  have he : hermitianDual sigma H (v - w) = 0 := by rw [map_sub, hvw, sub_self]
  have he' : hermitianPair sigma H (v - w) z = 0 := congrArg
    (fun f : Module.Dual K (I → K) => f z) he
  exact one_ne_zero (hz.symm.trans he')

theorem hermitianDual_surjective [Finite K] (sigma : K ≃+* K)
    (H : (Matrix I I K)ˣ) : Function.Surjective (hermitianDual sigma H) := by
  let E := (Pi.basisFun K I).toDualEquiv
  have hs : Function.Surjective (fun v => E.symm (hermitianDual sigma H v)) :=
    Finite.surjective_of_injective (E.symm.injective.comp (hermitianDual_injective sigma H))
  intro f
  obtain ⟨v, hv⟩ := hs (E.symm f)
  exact ⟨v, E.symm.injective hv⟩

def hermitianDuality [Finite K] (sigma : K ≃+* K) (H : (Matrix I I K)ˣ) :
    (I → K) ≃+ Module.Dual K (I → K) :=
  AddEquiv.ofBijective (hermitianDual sigma H)
    ⟨hermitianDual_injective sigma H, hermitianDual_surjective sigma H⟩

theorem hermitianDuality_smul [Finite K] (sigma : K ≃+* K)
    (H : (Matrix I I K)ˣ) (a : K) (v : I → K) :
    hermitianDuality sigma H (a • v) = sigma a • hermitianDuality sigma H v := by
  apply LinearMap.ext
  intro w
  change hermitianPair sigma H (a • v) w = sigma a * hermitianPair sigma H v w
  simpa only [one_smul, mul_one] using hermitianPair_smul sigma H a 1 v w

theorem exists_multiplier_and_field_commute [Finite K] (sigma tau : K ≃+* K)
    (H : (Matrix I I K)ˣ) (e : (I → K) ≃ₛₗ[tau.toRingHom] (I → K))
    (he : ∀ v w, hermitianPair sigma H (e v) (e w) = 0 ↔ hermitianPair sigma H v w = 0)
    (i₀ i₁ : I) (hne : i₀ ≠ i₁) :
    ∃ c : K, c ≠ 0 ∧
      (∀ v w, hermitianPair sigma H (e v) (e w) = c * tau (hermitianPair sigma H v w)) ∧
      Function.Commute sigma tau :=
  CFSGSesquilinearSimilitudeRigidity.exists_multiplier_and_field_commute sigma tau
    (hermitianDuality sigma H) (hermitianDuality_smul sigma H) e he i₀ i₁ hne

end SymmetricSubgroupAsymptotics.CFSGFiniteHermitianSimilitudeRigidity
