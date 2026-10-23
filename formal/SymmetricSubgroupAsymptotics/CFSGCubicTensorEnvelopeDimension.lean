import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! A scalar-aware envelope for cubic Frobenius tensor coordinates.
Slots 0 and 7 belong to a one-dimensional base-field subspace. The
triples (1,2,4) and (3,6,5) are determined by their first coordinates.
The envelope has base dimension at most eight, not twenty-four. No
identification with a group radical or actual diagram action is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGCubicTensorEnvelopeDimension
variable {F K : Type*} [Field F] [Field K] [Algebra F K]

def tensorEmbedding (W : Submodule F K) (sigma : K →ₗ[F] K) :
    (W × K × K × W) →ₗ[F] (Fin 8 → K) where
  toFun p i := match i.val with
    | 0 => p.1.val
    | 1 => p.2.1
    | 2 => sigma p.2.1
    | 3 => p.2.2.1
    | 4 => sigma (sigma p.2.1)
    | 5 => sigma (sigma p.2.2.1)
    | 6 => sigma p.2.2.1
    | _ => p.2.2.2.val
  map_add' p q := by
    funext i
    fin_cases i <;> simp
  map_smul' a p := by
    funext i
    fin_cases i <;> simp

def tensorEnvelope (W : Submodule F K) (sigma : K →ₗ[F] K) :
    Submodule F (Fin 8 → K) := (tensorEmbedding W sigma).range

theorem mem_tensorEnvelope (W : Submodule F K) (sigma : K →ₗ[F] K)
    (v : Fin 8 → K) (h0 : v 0 ∈ W) (h7 : v 7 ∈ W)
    (h2 : v 2 = sigma (v 1)) (h4 : v 4 = sigma (v 2))
    (h6 : v 6 = sigma (v 3)) (h5 : v 5 = sigma (v 6)) :
    v ∈ tensorEnvelope W sigma := by
  refine ⟨(⟨v 0, h0⟩, v 1, v 3, ⟨v 7, h7⟩), ?_⟩
  funext i
  fin_cases i <;> simp [tensorEmbedding, h2, h4, h6, h5]

theorem tensorEnvelope_finrank_le [FiniteDimensional F K]
    (W : Submodule F K) (sigma : K →ₗ[F] K) :
    Module.finrank F (tensorEnvelope W sigma) ≤
      2 * Module.finrank F W + 2 * Module.finrank F K := by
  have h := LinearMap.finrank_range_le (tensorEmbedding W sigma)
  simp only [Module.finrank_prod] at h
  change Module.finrank F (tensorEmbedding W sigma).range ≤ _
  omega

theorem tensorEnvelope_finrank_le_eight [FiniteDimensional F K]
    (W : Submodule F K) (sigma : K →ₗ[F] K)
    (hW : Module.finrank F W ≤ 1) (hK : Module.finrank F K ≤ 3) :
    Module.finrank F (tensorEnvelope W sigma) ≤ 8 := by
  have h := tensorEnvelope_finrank_le W sigma
  omega

end SymmetricSubgroupAsymptotics.CFSGCubicTensorEnvelopeDimension
