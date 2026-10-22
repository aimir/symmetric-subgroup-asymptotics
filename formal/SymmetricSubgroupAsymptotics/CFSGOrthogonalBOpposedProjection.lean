import SymmetricSubgroupAsymptotics.CFSGOrthogonalBPositiveMiddleWords
import SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularVectorCount
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! A singular n-space disjoint from the SAME original positive n-space
has an actual negative-coordinate chart. Its kernel is proved zero from
the literal Gram norm; no Witt decomposition or polar-label hypothesis
is supplied as an input. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBOpposedProjection
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBPositiveSubspace
open CFSGOrthogonalBVectorCoordinates CFSGOrthogonalBSingularVectorCount
open CFSGPolarSubspacePoints
variable (K : Type) [Field K]

def negativeLinear (n : ℕ) : (Index n → K) →ₗ[K] (Fin n → K) where
  toFun v i := v (neg n i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def negativeOn (n : ℕ) (Q : Submodule K (Index n → K)) : Q →ₗ[K] (Fin n → K) :=
  (negativeLinear K n).comp Q.subtype

theorem negativeOn_injective (n : ℕ) (Q : Subspaces (gram K n).toBilin')
    (hdis : Disjoint Q.val (positiveSubspace K n)) :
    Function.Injective (negativeOn K n Q.val) := by
  have hkernel (z : Q.val) (hz : negativeOn K n Q.val z = 0) : z = 0 := by
    have hn (i : Fin n) : z.val (neg n i) = 0 := congrFun hz i
    have hnorm := Q.property z.val z.property z.val z.property
    rw [gram_norm_dot] at hnorm
    have hneg : negativePart K n z.val = 0 := funext hn
    have hm : z.val (middle n) = 0 := by
      have hp : z.val (middle n) ^ 2 = 0 := by
        simpa [hneg, CFSGParabolicQuadricCount.dotDual] using hnorm
      exact sq_eq_zero_iff.mp hp
    have hp : z.val ∈ positiveSubspace K n := (mem_positiveSubspace K n z.val).mpr ⟨hn, hm⟩
    have hi : z.val ∈ (Q.val ⊓ positiveSubspace K n : Submodule K (Index n → K)) :=
      ⟨z.property, hp⟩
    rw [hdis.eq_bot] at hi
    have hzero : z.val = 0 := hi
    exact Subtype.ext hzero
  intro x y he
  have hz : negativeOn K n Q.val (x - y) = 0 := by rw [map_sub, he, sub_self]
  exact sub_eq_zero.mp (hkernel (x - y) hz)

def negativeEquiv (n : ℕ) (Q : Subspaces (gram K n).toBilin')
    (hdis : Disjoint Q.val (positiveSubspace K n)) (hdim : Module.finrank K Q.val = n) :
    Q.val ≃ₗ[K] (Fin n → K) :=
  LinearMap.linearEquivOfInjective (negativeOn K n Q.val) (negativeOn_injective K n Q hdis)
    (by simpa using hdim)

def graphLift (n : ℕ) (Q : Subspaces (gram K n).toBilin')
    (hdis : Disjoint Q.val (positiveSubspace K n)) (hdim : Module.finrank K Q.val = n) :
    (Fin n → K) →ₗ[K] (Index n → K) :=
  Q.val.subtype.comp (negativeEquiv K n Q hdis hdim).symm.toLinearMap

theorem graphLift_negative (n : ℕ) (Q : Subspaces (gram K n).toBilin')
    (hdis : Disjoint Q.val (positiveSubspace K n)) (hdim : Module.finrank K Q.val = n)
    (y : Fin n → K) : negativePart K n (graphLift K n Q hdis hdim y) = y := by
  exact (negativeEquiv K n Q hdis hdim).apply_symm_apply y

theorem graphLift_range (n : ℕ) (Q : Subspaces (gram K n).toBilin')
    (hdis : Disjoint Q.val (positiveSubspace K n)) (hdim : Module.finrank K Q.val = n) :
    (graphLift K n Q hdis hdim).range = Q.val := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    exact ((negativeEquiv K n Q hdis hdim).symm y).property
  · intro x hx
    refine ⟨negativeEquiv K n Q hdis hdim ⟨x, hx⟩, ?_⟩
    exact congrArg Subtype.val ((negativeEquiv K n Q hdis hdim).symm_apply_apply ⟨x, hx⟩)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBOpposedProjection
