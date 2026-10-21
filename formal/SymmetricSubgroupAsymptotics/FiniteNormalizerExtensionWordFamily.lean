import SymmetricSubgroupAsymptotics.FiniteNormalizerPElementExtension
import SymmetricSubgroupAsymptotics.FiniteGeneratorEquivWordCertificate

/-! Uniform families of actual normalizing prime-power extension witnesses.
Every entry retains ordinary inclusion words, normalizer words, its literal
power equation and seed nonmembership. No order flag replaces a group witness. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

structure FiniteNormalizerExtensionWordFamily
    {G I ι κ : Type*} [Group G]
    (seed : ι → G) (source : I → κ → G) (p exponent : ℕ) where
  elements : I → G
  normalizer : ∀ i, FiniteGeneratorEquivWordCertificate (MulAut.conj (elements i)) seed seed
  power_eq_one : ∀ i, elements i ^ (p ^ exponent) = 1
  outside_seed : ∀ i, elements i ∉ Subgroup.closure (Set.range seed)
  inclusionWords : I → FiniteGeneratorWord κ
  inclusion_eq : ∀ i, (inclusionWords i).eval (source i) = elements i

namespace FiniteNormalizerExtensionWordFamily

variable {G I ι κ : Type*} [Group G]
variable {seed : ι → G} {source : I → κ → G} {p exponent : ℕ}
variable (C : FiniteNormalizerExtensionWordFamily seed source p exponent)

abbrev extension (i : I) : Subgroup G :=
  Subgroup.closure (Set.range seed) ⊔ Subgroup.zpowers (C.elements i)

theorem normalizes_seed (i : I) :
    C.elements i ∈ Subgroup.normalizer (Subgroup.closure (Set.range seed)) := by
  apply Subgroup.mem_normalizer_iff_conj_image_eq.mpr
  exact congrArg (fun K : Subgroup G => (K : Set G)) (C.normalizer i).map_closure_eq

theorem element_mem_source (i : I) :
    C.elements i ∈ Subgroup.closure (Set.range (source i)) := by
  rw [← C.inclusion_eq i]
  exact (C.inclusionWords i).eval_mem_closure (source i)

theorem extension_isPGroup (hseed : IsPGroup p (Subgroup.closure (Set.range seed)))
    (i : I) : IsPGroup p (C.extension i) :=
  FiniteNormalizerPElementExtension.extension_isPGroup _ hseed
    (C.elements i) exponent (C.power_eq_one i) (C.normalizes_seed i)

theorem card_lt_extension [Finite G] (i : I) :
    Nat.card (Subgroup.closure (Set.range seed)) < Nat.card (C.extension i) :=
  FiniteNormalizerPElementExtension.card_lt_extension _ (C.elements i) (C.outside_seed i)

theorem extension_le_source (i : I)
    (hsource : Subgroup.closure (Set.range seed) ≤ Subgroup.closure (Set.range (source i))) :
    C.extension i ≤ Subgroup.closure (Set.range (source i)) :=
  FiniteNormalizerPElementExtension.extension_le _ _ hsource
    (C.elements i) (C.element_mem_source i)

end FiniteNormalizerExtensionWordFamily
end SymmetricSubgroupAsymptotics
end
