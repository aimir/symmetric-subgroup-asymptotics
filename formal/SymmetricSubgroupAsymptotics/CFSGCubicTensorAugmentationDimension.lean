import SymmetricSubgroupAsymptotics.CFSGCubicTensorEnvelopeDimension

/-! The seven raised cubic tensor coordinates have base dimension
at most seven. They are determined by two extension-field entries and
one entry in a one-dimensional base-field subspace. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGCubicTensorAugmentationDimension
variable {F K : Type*} [Field F] [Field K] [Algebra F K]

def augmentationEmbedding (W : Submodule F K) (sigma : K →ₗ[F] K) :
    (K × K × W) →ₗ[F] (Fin 7 → K) where
  toFun p i := match i.val with
    | 0 => p.1
    | 1 => sigma p.1
    | 2 => p.2.1
    | 3 => sigma (sigma p.1)
    | 4 => sigma (sigma p.2.1)
    | 5 => sigma p.2.1
    | _ => p.2.2.val
  map_add' p q := by
    funext i
    fin_cases i <;> simp
  map_smul' a p := by
    funext i
    fin_cases i <;> simp

def augmentationEnvelope (W : Submodule F K) (sigma : K →ₗ[F] K) :
    Submodule F (Fin 7 → K) := (augmentationEmbedding W sigma).range

theorem mem_augmentationEnvelope (W : Submodule F K) (sigma : K →ₗ[F] K)
    (v : Fin 7 → K) (h6 : v 6 ∈ W)
    (h1 : v 1 = sigma (v 0)) (h3 : v 3 = sigma (v 1))
    (h5 : v 5 = sigma (v 2)) (h4 : v 4 = sigma (v 5)) :
    v ∈ augmentationEnvelope W sigma := by
  refine ⟨(v 0, v 2, ⟨v 6, h6⟩), ?_⟩
  funext i
  fin_cases i <;> simp [augmentationEmbedding, h1, h3, h5, h4]

theorem augmentationEnvelope_finrank_le [FiniteDimensional F K]
    (W : Submodule F K) (sigma : K →ₗ[F] K) :
    Module.finrank F (augmentationEnvelope W sigma) ≤
      2 * Module.finrank F K + Module.finrank F W := by
  have h := LinearMap.finrank_range_le (augmentationEmbedding W sigma)
  simp only [Module.finrank_prod] at h
  change Module.finrank F (augmentationEmbedding W sigma).range ≤ _
  omega

theorem augmentationEnvelope_finrank_le_seven [FiniteDimensional F K]
    (W : Submodule F K) (sigma : K →ₗ[F] K)
    (hW : Module.finrank F W ≤ 1) (hK : Module.finrank F K ≤ 3) :
    Module.finrank F (augmentationEnvelope W sigma) ≤ 7 := by
  have h := augmentationEnvelope_finrank_le W sigma
  omega

end SymmetricSubgroupAsymptotics.CFSGCubicTensorAugmentationDimension
