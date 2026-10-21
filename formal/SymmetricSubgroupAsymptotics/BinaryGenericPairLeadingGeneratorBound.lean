import SymmetricSubgroupAsymptotics.BinaryBooleanFourLeadingDerivativeWords
import SymmetricSubgroupAsymptotics.BinaryMonomialRaisingWords
import SymmetricSubgroupAsymptotics.AlgebraOperatorLeadingGeneratorBound

/-! A common two-layer generation engine for arbitrary actual leading
derivatives and prescribed pointwise kernel shears. Exact translation
formulas are not required. The proof composes operators in the original
acting algebra. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryGenericPairLeadingGeneratorBound
open BinaryElementaryPairMonomialWidth BinaryBooleanFourPolynomialCoordinates
open BinaryMonomialRaisingWords (index differenceIndex)
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

def Raises (Allowed : Finset (Fin 4) → Prop) (a b : Monomial) : Prop :=
  if a.1 then (if b.1 then support b.2 ⊆ support a.2 else Allowed (support b.2 \ support a.2))
  else b.1 = false ∧ support b.2 ⊆ support a.2

private theorem difference_support : ∀ a b : Fin 16,
    support (differenceIndex b a) = support b \ support a := by decide
private theorem difference_disjoint : ∀ a b : Fin 16,
    Disjoint (support (differenceIndex b a)) (support a) := by decide
private theorem union_difference_contains : ∀ a b : Fin 16,
    support b ⊆ support (unionIndex (differenceIndex b a) a) := by decide

variable {A M : Type} [Ring A] [AddCommGroup M] [Module A M] [Module (ZMod 2) M]
    (C : M →ₗ[ZMod 2] (Fin 32 → ZMod 2))

theorem exists_operator_of_leading_derivatives
    (hderivative : ∀ (l : Bool) (i : Fin 4) (v : M) (a : Fin 16),
      FiniteRowLeadingWeight.HasLeading (C v) (index (l, a)) → i ∈ support a →
      ∃ r : A, FiniteRowLeadingWeight.HasLeading (C (r • v)) (index (l, removeIndex i a)))
    (l : Bool) (v : M) (a b : Fin 16)
    (hv : FiniteRowLeadingWeight.HasLeading (C v) (index (l, a)))
    (hba : support b ⊆ support a) :
    ∃ r : A, FiniteRowLeadingWeight.HasLeading (C (r • v)) (index (l, b)) := by
  apply ModuleLeadingOperatorWords.exists_operator_of_run derivativeStep
    (fun z c => FiniteRowLeadingWeight.HasLeading (C z) (index (l, c))) _
    (derivativePath a b) a b (derivativePath_valid a b hba) v hv
  intro i a b hab z hz
  change (if i ∈ support a then some (removeIndex i a) else none) = some b at hab
  split_ifs at hab with hi
  have he : removeIndex i a = b := Option.some.inj hab
  subst b
  exact hderivative l i z a hz hi

theorem exists_operator_of_raises (Allowed : Finset (Fin 4) → Prop)
    (hderivative : ∀ (l : Bool) (i : Fin 4) (v : M) (a : Fin 16),
      FiniteRowLeadingWeight.HasLeading (C v) (index (l, a)) → i ∈ support a →
      ∃ r : A, FiniteRowLeadingWeight.HasLeading (C (r • v)) (index (l, removeIndex i a)))
    (hshear : ∀ (v : M) (a b : Fin 16),
      FiniteRowLeadingWeight.HasLeading (C v) (index (true, a)) →
      Allowed (support b) → Disjoint (support b) (support a) →
      ∃ r : A, FiniteRowLeadingWeight.HasLeading (C (r • v)) (index (false, unionIndex b a)))
    (v : M) (a b : Monomial) (hv : FiniteRowLeadingWeight.HasLeading (C v) (index a))
    (hab : Raises Allowed a b) :
    ∃ r : A, FiniteRowLeadingWeight.HasLeading (C (r • v)) (index b) := by
  rcases a with ⟨l, a⟩
  rcases b with ⟨s, b⟩
  cases l <;> cases s
  · exact exists_operator_of_leading_derivatives C hderivative false v a b hv hab.2
  · cases hab.1
  · change Allowed (support b \ support a) at hab
    have hAllowed : Allowed (support (differenceIndex b a)) := by
      rwa [difference_support]
    obtain ⟨r, hr⟩ := hshear v a (differenceIndex b a) hv hAllowed (difference_disjoint a b)
    obtain ⟨q, hq⟩ := exists_operator_of_leading_derivatives C hderivative false (r • v)
      (unionIndex (differenceIndex b a) a) b hr (union_difference_contains a b)
    exact ⟨q * r, by simpa only [mul_smul] using hq⟩
  · change support b ⊆ support a at hab
    exact exists_operator_of_leading_derivatives C hderivative true v a b hv hab

theorem generating_finset_le_of_width
    [Algebra (ZMod 2) A] [IsScalarTower (ZMod 2) A M]
    {d w : ℕ} (hd : ModuleGeneratedBy A M d) (hC : Function.Injective C)
    (Allowed : Finset (Fin 4) → Prop)
    (hderivative : ∀ (l : Bool) (i : Fin 4) (v : M) (a : Fin 16),
      FiniteRowLeadingWeight.HasLeading (C v) (index (l, a)) → i ∈ support a →
      ∃ r : A, FiniteRowLeadingWeight.HasLeading (C (r • v)) (index (l, removeIndex i a)))
    (hshear : ∀ (v : M) (a b : Fin 16),
      FiniteRowLeadingWeight.HasLeading (C v) (index (true, a)) →
      Allowed (support b) → Disjoint (support b) (support a) →
      ∃ r : A, FiniteRowLeadingWeight.HasLeading (C (r • v)) (index (false, unionIndex b a)))
    (hwidth : ∀ s : Finset Monomial, IsAntichain (Raises Allowed) (s : Set Monomial) → s.card ≤ w) :
    ∃ S : Finset M, Submodule.span A (S : Set M) = ⊤ ∧ S.card ≤ w := by
  let rel : Fin 32 → Fin 32 → Prop := fun a b => Raises Allowed (index.symm a) (index.symm b)
  refine algebra_generating_finset_le_of_operator_leading_width hd C hC 0 rel ?_ ?_ w ?_
  · intro a
    change Raises Allowed (index.symm a) (index.symm a)
    rcases index.symm a with ⟨l, b⟩
    cases l <;> simp [Raises]
  · intro v a b hv hab
    have hv' : FiniteRowLeadingWeight.HasLeading (C v) (index (index.symm a)) := by
      simpa only [Equiv.apply_symm_apply] using hv
    obtain ⟨r, hr⟩ := exists_operator_of_raises C Allowed hderivative hshear v
      (index.symm a) (index.symm b) hv' hab
    exact ⟨r, by simpa only [Equiv.apply_symm_apply] using hr⟩
  · intro s hs
    let t := s.image index.symm
    have ht : IsAntichain (Raises Allowed) (t : Set Monomial) := by
      intro a ha b hb hne hab
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
      exact hs hx hy (fun he => hne (congrArg index.symm he)) hab
    have hb := hwidth t ht
    rwa [Finset.card_image_of_injective _ index.symm.injective] at hb

end SymmetricSubgroupAsymptotics.BinaryGenericPairLeadingGeneratorBound
