import SymmetricSubgroupAsymptotics.FiniteExtensionQuotientImageCount
import SymmetricSubgroupAsymptotics.OriginalKernelWholeLayerCount

/-! All-subgroup count for an actual elementary extension, summing over
EVERY literal quotient image. Each image retains its actual quotient-action
module chart, invariant-kernel generators and complete lift fibres.
This is a structural counting theorem, not a global transitive census. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.FiniteElementaryExtensionSubgroupCount

local instance subgroupFinite {G : Type} [Group G] [Finite G] : Finite (Subgroup G) :=
  Finite.of_injective (fun K : Subgroup G => (K : Set G)) SetLike.coe_injective
local instance subgroupFintype {G : Type} [Group G] [Finite G] : Fintype (Subgroup G) :=
  Fintype.ofFinite _

variable {p : ℕ} [Fact p.Prime] {E Q : Type} [Group E] [Finite E] [Group Q] [Finite Q]

/-- The actual representation may depend on the chosen literal quotient image.
There is no unproved hypothesis bounding the number of subgroup lifts. -/
theorem card_subgroup_le_sum_module_capacities
    (π : E →* Q) (hπ : Function.Surjective π)
    (A : (H : Subgroup Q) → Rep (ZMod p) H)
    (chart : ∀ H, OriginalKernelModuleChart (π.subgroupComap H) (A H))
    (cap d : Subgroup Q → ℕ)
    (hgen : ∀ H, UniformSubrepresentationGeneratorBound (A H).ρ (cap H))
    (f : (H : Subgroup Q) → Fin (d H) → H)
    (hf : ∀ H, Subgroup.closure (Set.range (f H)) = ⊤) :
    Nat.card (Subgroup E) ≤ ∑ H : Subgroup Q, (Nat.card (A H))^(cap H+d H) := by
  apply FiniteExtensionQuotientImageCount.card_subgroup_le_of_image_bounds π
  intro H
  exact OriginalKernelWholeLayerCount.card_fullImage_le_of_uniform
    (π.subgroupComap H) (π.subgroupComap_surjective_of_surjective H hπ)
    (A H) (chart H) (hgen H) (f H) (hf H)

/-- A genuine uniform local exponent can be used after the exact image sum;
the full number of quotient images remains charged. -/
theorem card_subgroup_le_uniform_module_budget
    (π : E →* Q) (hπ : Function.Surjective π)
    (A : (H : Subgroup Q) → Rep (ZMod p) H)
    (chart : ∀ H, OriginalKernelModuleChart (π.subgroupComap H) (A H))
    (cap d : Subgroup Q → ℕ)
    (hgen : ∀ H, UniformSubrepresentationGeneratorBound (A H).ρ (cap H))
    (f : (H : Subgroup Q) → Fin (d H) → H)
    (hf : ∀ H, Subgroup.closure (Set.range (f H)) = ⊤)
    (N k : ℕ) (hcard : ∀ H, Nat.card (A H) ≤ N)
    (hN : 1 ≤ N) (hbudget : ∀ H, cap H+d H ≤ k) :
    Nat.card (Subgroup E) ≤ Nat.card (Subgroup Q)*N^k := by
  have hh := card_subgroup_le_sum_module_capacities π hπ A chart cap d hgen f hf
  calc
    Nat.card (Subgroup E) ≤ ∑ H : Subgroup Q, (Nat.card (A H))^(cap H+d H) := hh
    _ ≤ ∑ _H : Subgroup Q, N^k := by
      apply Finset.sum_le_sum
      intro H _
      exact (Nat.pow_le_pow_left (hcard H) (cap H+d H)).trans
        (Nat.pow_le_pow_right hN (hbudget H))
    _ = Nat.card (Subgroup Q)*N^k := by
      simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.card_eq_fintype_card]

end SymmetricSubgroupAsymptotics.FiniteElementaryExtensionSubgroupCount
