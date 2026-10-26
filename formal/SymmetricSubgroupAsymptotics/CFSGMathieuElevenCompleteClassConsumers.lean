import SymmetricSubgroupAsymptotics.CFSGMathieuElevenClassConsumersOfOuterOne
import SymmetricSubgroupAsymptotics.CFSGMathieuElevenOuterBound

/-! Closed actual M11 class consumers. The raw outer-cardinality premise
of the earlier conditional module is supplied by the actual model
theorem, with its finite/simple instances transported from the SAME
internal factor. No new profile, callback, or outer hypothesis occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuElevenCompleteClassConsumers
open PrimitiveSocleRawStructure CFSG.Models.Presentations.M11

private theorem outer_one_of_factor
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) (e : D.Simple ≃* Model) : Nat.card (Outer Model) ≤ 1 := by
  letI : Finite Model := Finite.of_equiv D.Simple e.toEquiv
  letI : IsSimpleGroup Model := e.symm.isSimpleGroup
  exact CFSGMathieuElevenOuterBound.outer_card_le_one

theorem primitive_subnormal_class_cube
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) (e : D.Simple ≃* Model)
    (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card X - 1) :=
  CFSGMathieuElevenClassConsumersOfOuterOne.primitive_subnormal_class_cube
    D e (outer_one_of_factor D e) H hH

theorem proper_subnormal_class_cube_gap
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) (e : D.Simple ≃* Model)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card X - 2) :=
  CFSGMathieuElevenClassConsumersOfOuterOne.proper_subnormal_class_cube_gap
    D e (outer_one_of_factor D e) H hH hne

theorem original_small_fibre_subnormal_gap
    {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω) = g • π ω)
    (c : ℕ) (hc : c = 2 ∨ c = 3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x) = c)
    (E : NonaffineData (OriginalBlockClassBound.Top (A := A) (X := X)) X)
    (e : E.Simple ≃* Model) (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card Ω - 2) :=
  CFSGMathieuElevenClassConsumersOfOuterOne.original_small_fibre_subnormal_gap
    π hπ c hc hsize E e (outer_one_of_factor E e) H hH

theorem original_component_class_cube
    {A Ω : Type} [Group A] [MulAction A Ω] [MulAction.IsPretransitive A Ω]
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)
    (E : NonaffineData D.Component D.Fibre) (e : E.Simple ≃* Model)
    (hdegree : 4 ≤ Nat.card D.Fibre)
    (hSmaller : ∀ n : ℕ, n < Nat.card Ω → 4 ≤ n →
      ∀ L : Subgroup (Equiv.Perm (Fin n)),
        Nat.card (ConjClasses L) ^ 3 ≤ 5 ^ (n - 1)) :
    Nat.card (ConjClasses A) ^ 3 ≤ 5 ^ (Nat.card Ω - 1) :=
  CFSGMathieuElevenClassConsumersOfOuterOne.original_component_class_cube
    D E e (outer_one_of_factor E e) hdegree hSmaller

end SymmetricSubgroupAsymptotics.CFSGMathieuElevenCompleteClassConsumers
