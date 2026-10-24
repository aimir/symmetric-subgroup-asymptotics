import SymmetricSubgroupAsymptotics.LinearMapPositivePrimaryDecomposition
import SymmetricSubgroupAsymptotics.LinearMapCyclicCodeCharacteristicPolynomial
import SymmetricSubgroupAsymptotics.WeightedMultisetPartitionExpansion
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-! The actual positive primary chart gives positive weighted labels.
Their expansion is exactly the normalized factor multiset of the actual
characteristic polynomial. Equal weighted labels construct an actual
polynomial-module intertwiner through the existing cyclic-code theorem;
no uniqueness of a chosen primary chart is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.LinearMapPrimaryWeightedCode
open Polynomial UniqueFactorizationMonoid
open WeightedMultisetPartitionExpansion FiniteMultisetLabelMatching
variable {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    [AddCommGroup W] [Module K W] [Module.Finite K W]

def labels {A : Module.End K V} (C : LinearMapPositivePrimaryDecomposition.Chart A) :
    Multiset (K[X] × ℕ) := labelMultiset (fun i => (C.prime i, C.exponent i))

omit [Module.Finite K V] in
theorem labels_positive {A : Module.End K V}
    (C : LinearMapPositivePrimaryDecomposition.Chart A) :
    ∀ b ∈ labels C, 0 < b.2 := by
  intro b hb
  obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hb
  exact C.positive i

theorem expand_labels {A : Module.End K V}
    (C : LinearMapPositivePrimaryDecomposition.Chart A) :
    WeightedMultisetPartitionExpansion.expand (labels C) = normalizedFactors A.charpoly := by
  have hzero : (0 : K[X]) ∉ LinearMapCyclicCodeEquivalence.code C.cyclic := by
    intro hz
    obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hz
    exact (C.cyclic.monic i).ne_zero hi
  symm
  rw [← LinearMapCyclicCodeCharacteristicPolynomial.code_prod C.cyclic,
    normalizedFactors_multiset_prod _ hzero]
  simp only [LinearMapCyclicCodeEquivalence.code, labelMultiset, labels,
    WeightedMultisetPartitionExpansion.expand,
    Multiset.bind, Multiset.join, Multiset.map_map, Function.comp_def]
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro i _
  rw [C.power_eq i, (C.irreducible i).normalizedFactors_pow,
    (C.monic i).normalize_eq_self]

theorem normalizedFactors_card {A : Module.End K V}
    (C : LinearMapPositivePrimaryDecomposition.Chart A) :
    (normalizedFactors A.charpoly).card = ∑ i : C.cyclic.ι, C.exponent i := by
  rw [← expand_labels C]
  simp only [labels, labelMultiset, WeightedMultisetPartitionExpansion.expand,
    Multiset.card_bind, Multiset.map_map,
    Function.comp_def, Multiset.card_replicate]
  rfl

omit [Module.Finite K V] in
theorem map_power_labels {A : Module.End K V}
    (C : LinearMapPositivePrimaryDecomposition.Chart A) :
    (labels C).map (fun b => b.1 ^ b.2) =
      LinearMapCyclicCodeEquivalence.code C.cyclic := by
  simp only [labels, labelMultiset, LinearMapCyclicCodeEquivalence.code,
    Multiset.map_map, Function.comp_def]
  exact Multiset.map_congr rfl (fun i _ => (C.power_eq i).symm)

theorem exists_intertwining_equiv_of_labels_eq {A : Module.End K V} {B : Module.End K W}
    (C : LinearMapPositivePrimaryDecomposition.Chart A)
    (D : LinearMapPositivePrimaryDecomposition.Chart B) (h : labels C = labels D) :
    ∃ F : V ≃ₗ[K] W, ∀ v, F (A v) = B (F v) := by
  have he := congrArg (Multiset.map (fun b : K[X] × ℕ => b.1 ^ b.2)) h
  rw [map_power_labels C, map_power_labels D] at he
  exact LinearMapCyclicCodeEquivalence.exists_intertwining_equiv C.cyclic D.cyclic he

end SymmetricSubgroupAsymptotics.LinearMapPrimaryWeightedCode
