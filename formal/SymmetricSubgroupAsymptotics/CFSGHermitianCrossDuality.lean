import SymmetricSubgroupAsymptotics.CFSGHermitianCrossEmbeddingFieldCoherence
import Mathlib.LinearAlgebra.Dual.Basis

/-! A genuine nondegenerate pairing between two equal-dimensional
coordinate spaces gives an additive Hermitian cross-duality. Only
original nondegeneracy is used; finite-field cardinality supplies its
surjectivity, with no orthogonal-group order or target recognition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGHermitianCrossDuality
open CFSGTwistedAUnitaryParameters CFSGHermitianOrthogonalSpan
variable {K I J : Type*} [Field K] [Fintype I] [DecidableEq I] [Fintype J]

def crossDual (sigma : K ≃+* K) (H : Matrix J J K)
    (a b : (I → K) →ₗ[K] (J → K)) : (I → K) →+ Module.Dual K (I → K) :=
  CFSGHermitianCrossEmbeddingFieldCoherence.pulledPair sigma
    (RingEquiv.refl K) (RingEquiv.refl K) H a b

theorem crossDual_injective (sigma : K ≃+* K) (H : Matrix J J K)
    (a b : (I → K) →ₗ[K] (J → K))
    (hND : ∀ v : I → K, (∀ w : I → K, hermitianPair sigma H (a v) (b w) = 0) → v = 0) :
    Function.Injective (crossDual sigma H a b) := by
  intro v w he
  apply sub_eq_zero.mp
  apply hND
  intro z
  have hz : crossDual sigma H a b (v - w) = 0 := by rw [map_sub, he, sub_self]
  exact congrArg (fun L : Module.Dual K (I → K) => L z) hz

theorem crossDual_surjective [Finite K] (sigma : K ≃+* K) (H : Matrix J J K)
    (a b : (I → K) →ₗ[K] (J → K))
    (hND : ∀ v : I → K, (∀ w : I → K, hermitianPair sigma H (a v) (b w) = 0) → v = 0) :
    Function.Surjective (crossDual sigma H a b) := by
  let E := (Pi.basisFun K I).toDualEquiv
  have hs : Function.Surjective (fun v => E.symm (crossDual sigma H a b v)) :=
    Finite.surjective_of_injective (E.symm.injective.comp (crossDual_injective sigma H a b hND))
  intro L
  obtain ⟨v, hv⟩ := hs (E.symm L)
  exact ⟨v, E.symm.injective hv⟩

def crossDuality [Finite K] (sigma : K ≃+* K) (H : Matrix J J K)
    (a b : (I → K) →ₗ[K] (J → K))
    (hND : ∀ v : I → K, (∀ w : I → K, hermitianPair sigma H (a v) (b w) = 0) → v = 0) :
    (I → K) ≃+ Module.Dual K (I → K) :=
  AddEquiv.ofBijective (crossDual sigma H a b)
    ⟨crossDual_injective sigma H a b hND, crossDual_surjective sigma H a b hND⟩

theorem crossDuality_apply [Finite K] (sigma : K ≃+* K) (H : Matrix J J K)
    (a b : (I → K) →ₗ[K] (J → K))
    (hND : ∀ v : I → K, (∀ w : I → K, hermitianPair sigma H (a v) (b w) = 0) → v = 0)
    (v w : I → K) :
    crossDuality sigma H a b hND v w = hermitianPair sigma H (a v) (b w) := rfl

theorem crossDuality_smul [Finite K] (sigma : K ≃+* K) (H : Matrix J J K)
    (a b : (I → K) →ₗ[K] (J → K))
    (hND : ∀ v : I → K, (∀ w : I → K, hermitianPair sigma H (a v) (b w) = 0) → v = 0)
    (c : K) (v : I → K) :
    crossDuality sigma H a b hND (c • v) = sigma c • crossDuality sigma H a b hND v := by
  apply LinearMap.ext
  intro w
  change hermitianPair sigma H (a (c • v)) (b w) = sigma c * hermitianPair sigma H (a v) (b w)
  rw [map_smul]
  have hh := hermitianPair_smul sigma H c 1 (a v) (b w)
  simpa only [one_smul, mul_one] using hh

end SymmetricSubgroupAsymptotics.CFSGHermitianCrossDuality
