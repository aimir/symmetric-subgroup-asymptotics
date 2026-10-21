import SymmetricSubgroupAsymptotics.AlgebraLeadingGeneratorAntichain
import SymmetricSubgroupAsymptotics.BooleanFourAntichainFive
import SymmetricSubgroupAsymptotics.BinaryElementaryPairMonomialWidth

/-! Five necessary generators force actual leading generators into the
quadratic layer. This retains their lower polynomial terms; it does not
replace a kernel vector by its leading monomial. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

open BinaryElementaryPairMonomialWidth

private theorem boolean_four_support_injective : Function.Injective support := by
  have h : ∀ a b : Fin 16, support a = support b → a = b := by decide
  exact fun a b => h a b

variable {k A M : Type} [Field k] [Ring A] [Algebra k A]
    [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    {d : ℕ}

theorem boolean_four_generating_finset_with_quadratic_leading_terms
    (hd : ModuleGeneratedBy A M d) (C : M →ₗ[k] (Fin 16 → k))
    (hC : Function.Injective C)
    (hraise : ∀ v a b, FiniteRowLeadingWeight.HasLeading (C v) a →
      support b ⊆ support a →
      ∃ r : A, FiniteRowLeadingWeight.HasLeading (C (r • v)) b)
    (hlow : ∀ S : Finset M, Submodule.span A (S : Set M) = ⊤ → 5 ≤ S.card) :
    ∃ (S : Finset M) (label : M → Fin 16),
      Submodule.span A (S : Set M) = ⊤ ∧
      (∀ v ∈ S, FiniteRowLeadingWeight.HasLeading (C v) (label v) ∧
        (support (label v)).card = 2) ∧
      Set.InjOn label (S : Set M) := by
  obtain ⟨S, label, hspan, hlead, hinj, hanti⟩ :=
    algebra_generating_finset_with_leading_antichain hd C hC 0
      (fun a b => support b ⊆ support a)
      (fun a => show support a ⊆ support a from fun _ h => h) hraise
  let T : Finset (Finset (Fin 4)) := (S.image label).image support
  have hT : IsAntichain (· ⊆ ·) (T : Set (Finset (Fin 4))) := by
    intro a ha b hb hne hab
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
    exact hanti hj hi (fun he => hne (congrArg support he).symm) hab
  have hcard : 5 ≤ T.card := by
    have hc₁ : (S.image label).card = S.card := Finset.card_image_of_injOn hinj
    have hc₂ : T.card = (S.image label).card :=
      Finset.card_image_of_injective _ boolean_four_support_injective
    rw [hc₂, hc₁]
    exact hlow S hspan
  refine ⟨S, label, hspan, ?_, hinj⟩
  intro v hv
  refine ⟨(hlead v hv).2, ?_⟩
  apply boolean_four_antichain_five_member_card T hT hcard
  exact Finset.mem_image.mpr ⟨label v, Finset.mem_image.mpr ⟨v, hv, rfl⟩, rfl⟩

end SymmetricSubgroupAsymptotics
