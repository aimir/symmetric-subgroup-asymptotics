import SymmetricSubgroupAsymptotics.CFSGHermitianMaximalCrossPairing
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Actual nondegenerate cross-pairing of two planes realizes arbitrary
two prescribed values. The map is linear in its second variable; no
unitary group order, duality recognition, or scalar-field premise is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
open CFSGTwistedAUnitaryParameters
variable {K I : Type*} [Field K] [Fintype I]
variable (sigma : K ≃+* K) (H : Matrix I I K)

def planePairingValues (P : Submodule K (I → K)) (y : Fin 2 → I → K) :
    P →ₗ[K] (Fin 2 → K) :=
  LinearMap.pi (fun j => (pairRightLinear sigma H (y j)).comp P.subtype)

theorem planePairingValues_injective
    (P Z : Submodule K (I → K)) (y : Fin 2 → I → K)
    (hspan : Submodule.span K (Set.range y) = Z)
    (hND : ∀ x ∈ P, (∀ z ∈ Z, hermitianPair sigma H z x = 0) → x = 0) :
    Function.Injective (planePairingValues sigma H P y) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  apply Subtype.ext
  apply hND x.val x.property
  have hY (j : Fin 2) : y j ∈ leftPerp sigma H (K ∙ x.val) := by
    intro z hz
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
    have hh := congrFun hx j
    change hermitianPair sigma H (y j) x.val = 0 at hh
    have hs := hermitianPair_smul sigma H 1 a (y j) x.val
    simpa only [one_smul, map_one, one_mul, hh, mul_zero] using hs
  have hle : Z ≤ leftPerp sigma H (K ∙ x.val) := by
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro z ⟨j, rfl⟩
    exact hY j
  intro z hz
  exact hle hz x.val (Submodule.mem_span_singleton_self _)

theorem planePairingValues_surjective
    (P Z : Submodule K (I → K)) (hdP : Module.finrank K P = 2)
    (y : Fin 2 → I → K) (hspan : Submodule.span K (Set.range y) = Z)
    (hND : ∀ x ∈ P, (∀ z ∈ Z, hermitianPair sigma H z x = 0) → x = 0) :
    Function.Surjective (planePairingValues sigma H P y) := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simpa using hdP)).mp
  exact planePairingValues_injective sigma H P Z y hspan hND

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
