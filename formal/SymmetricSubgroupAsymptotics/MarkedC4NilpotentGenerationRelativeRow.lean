import SymmetricSubgroupAsymptotics.MarkedC4RelativeGenerationLiteralEncoding
import Mathlib.Data.Fintype.EquivFin
import Mathlib.GroupTheory.Nilpotent

/-! Ordinary nilpotent-core generation with a bounded finite set constructs
an actual fixed-container relative row. No marked bound is an input. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.NilpotentGenerationRelative

/-- Padding by the identity retains precisely the same generated subgroup. -/
theorem exists_padded_generating_tuple {G : Type} [Group G]
    (K : Subgroup G) (S : Finset G) {l : ℕ} (hcard : S.card≤l)
    (hgen : Subgroup.closure ((S : Set G) ∪ K)=⊤) :
    ∃ t : Fin l → G, Subgroup.closure (Set.range t ∪ K)=⊤ := by
  let t : Fin l → G := fun i =>
    if hi : i.val<S.card then ((S.equivFin).symm ⟨i.val,hi⟩ : G) else 1
  refine ⟨t,top_unique ?_⟩
  rw [← hgen]
  apply Subgroup.closure_mono
  intro x hx
  rcases hx with hs | hk
  · left
    let j := S.equivFin ⟨x,hs⟩
    refine ⟨⟨j.val,lt_of_lt_of_le j.isLt hcard⟩,?_⟩
    change (if hi : j.val<S.card then ((S.equivFin).symm ⟨j.val,hi⟩ : G) else 1)=x
    simp only [dif_pos j.isLt]
    exact congrArg Subtype.val ((S.equivFin).symm_apply_apply ⟨x,hs⟩)
  · exact Or.inr hk

variable {b l : ℕ} {A : Type} [Fintype A]
  (D : Subgroup (PermutationGroup b))
  (source : A → Subgroup (PermutationGroup b))
  (hsource : Function.Injective source) (hD : ∀ a, source a≤D)

/-- The target remembers the SAME ambient nilpotent subgroup in D. -/
def TargetPredicate (J : Subgroup (PermutationGroup b)) : Prop :=
  Group.IsNilpotent J ∧ J≤D

/-- The ordinary published nilpotent-generation conclusion, specialized to
these actual sources, supplies an encoding row. The hypothesis contains
neither a moment estimate nor target Hom counts nor recovery data. -/
def row_of_nilpotent_generation
    (hordinary : ∀ a, ∃ (K : Subgroup (source a)) (S : Finset (source a)),
      Group.IsNilpotent K ∧ S.card≤l ∧
        Subgroup.closure ((S : Set (source a)) ∪ K)=⊤)
    (q : ℕ → ℝ) (hcost : (Fintype.card D : ℝ)^l≤(2 : ℝ)^(q b)) :
    RelativeGeneratorEncodingRow
      (fun _ r => ∑ a : A, (Nat.card (source a →* Multiplicative (ZMod 4)) : ℝ)^r)
      (fun _ r => ∑ z : {J : Subgroup (PermutationGroup b) // TargetPredicate D J},
        (Nat.card (z.1 →* Multiplicative (ZMod 4)) : ℝ)^r)
      q l b := by
  choose K S hnil hcard hgen using hordinary
  have ht : ∀ a, ∃ t : Fin l → source a,
      Subgroup.closure (Set.range t ∪ K a)=⊤ :=
    fun a => exists_padded_generating_tuple (K a) (S a) (hcard a) (hgen a)
  choose tuple htuple using ht
  have htarget (a : A) : TargetPredicate D ((K a).map (source a).subtype) := by
    constructor
    · letI := hnil a
      exact Group.nilpotent_of_mulEquiv
        ((K a).equivMapOfInjective (source a).subtype Subtype.coe_injective)
    · intro x hx
      obtain ⟨k,_,rfl⟩ := hx
      exact hD a k.property
  exact RelativeGenerationLiteral.row D source hsource hD K tuple htuple
    (TargetPredicate D) htarget q hcost

end SymmetricSubgroupAsymptotics.MarkedC4.NilpotentGenerationRelative
