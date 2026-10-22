import Mathlib.GroupTheory.Index
import Mathlib.SetTheory.Cardinal.Finite

/-! Separate group cosets by arbitrary chosen data. The data need not
descend to cosets: applying it to inverse representatives gives an
injection whenever equality of the data forces a left subgroup factor.
No normality of either subgroup is required. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGCosetDataIndex
variable {A D S : Type*} [Group A] [Group D] [Finite D] [Finite S]

theorem index_le_of_coset_data (T : Subgroup A) (C : Subgroup D)
    (c : A → D) (s : A → S)
    (hsep : ∀ a b, (c a : D ⧸ C) = c b → s a = s b → a * b⁻¹ ∈ T) :
    T.index ≤ C.index * Nat.card S := by
  classical
  let enc : A ⧸ T → (D ⧸ C) × S := fun q =>
    ((c (q.out⁻¹) : D ⧸ C), s (q.out⁻¹))
  have hinj : Function.Injective enc := by
    intro x y h
    have hT := hsep (x.out⁻¹) (y.out⁻¹) (congrArg Prod.fst h) (congrArg Prod.snd h)
    have he : (x.out : A ⧸ T) = y.out :=
      QuotientGroup.eq.mpr (by simpa only [inv_inv] using hT)
    exact x.out_eq'.symm.trans (he.trans y.out_eq')
  calc
    T.index = Nat.card (A ⧸ T) := T.index_eq_card
    _ ≤ Nat.card ((D ⧸ C) × S) := Nat.card_le_card_of_injective enc hinj
    _ = C.index * Nat.card S := by rw [Nat.card_prod, C.index_eq_card]

end SymmetricSubgroupAsymptotics.CFSGCosetDataIndex
