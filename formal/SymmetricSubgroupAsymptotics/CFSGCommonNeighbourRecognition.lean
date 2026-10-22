import Mathlib.Data.Finite.Card

/-! Recognizing a relation by distance two and a common-neighbour count.
The two geometric alternatives and their numerical bounds are explicit
theorem inputs; applications must prove them on their original geometry. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGCommonNeighbourRecognition
variable {L : Type*} (rel : L → L → Prop)

def CommonNeighbours (x y : L) := {z : L // rel x z ∧ rel y z}

def TwoStep (x y : L) : Prop :=
  x≠y ∧ ¬rel x y ∧ ∃z,rel x z ∧ rel y z

def commonNeighbourEquiv (f : L ≃ L) (hf : ∀ x y,rel (f x) (f y) ↔ rel x y)
    (x y : L) : CommonNeighbours rel x y ≃ CommonNeighbours rel (f x) (f y) where
  toFun z := ⟨f z.val,(hf x z.val).mpr z.property.1,(hf y z.val).mpr z.property.2⟩
  invFun z := ⟨f.symm z.val,
    (hf x (f.symm z.val)).mp (by simpa only [f.apply_symm_apply] using z.property.1),
    (hf y (f.symm z.val)).mp (by simpa only [f.apply_symm_apply] using z.property.2)⟩
  left_inv z := Subtype.ext (f.symm_apply_apply z.val)
  right_inv z := Subtype.ext (f.apply_symm_apply z.val)

theorem commonNeighbour_card (f : L ≃ L) (hf : ∀ x y,rel (f x) (f y) ↔ rel x y)
    (x y : L) :
    Nat.card (CommonNeighbours rel (f x) (f y)) = Nat.card (CommonNeighbours rel x y) :=
  (Nat.card_congr (commonNeighbourEquiv rel f hf x y)).symm

theorem twoStep_iff (f : L ≃ L) (hf : ∀ x y,rel (f x) (f y) ↔ rel x y)
    (x y : L) : TwoStep rel (f x) (f y) ↔ TwoStep rel x y := by
  constructor
  · rintro ⟨hne,hn,⟨z,hxz,hyz⟩⟩
    refine ⟨fun h=>hne (congrArg f h),fun h=>hn ((hf x y).mpr h),f.symm z,?_,?_⟩
    · apply (hf x (f.symm z)).mp
      simpa only [f.apply_symm_apply] using hxz
    · apply (hf y (f.symm z)).mp
      simpa only [f.apply_symm_apply] using hyz
  · rintro ⟨hne,hn,⟨z,hxz,hyz⟩⟩
    exact ⟨fun h=>hne (f.injective h),fun h=>hn ((hf x y).mp h),f z,
      (hf x z).mpr hxz,(hf y z).mpr hyz⟩

variable {rel} (special other : L → L → Prop) (bound : ℕ)
    (partition : ∀x y,TwoStep rel x y ↔ special x y ∨ other x y)
    (special_large : ∀x y,special x y → bound < Nat.card (CommonNeighbours rel x y))
    (other_small : ∀x y,other x y → Nat.card (CommonNeighbours rel x y) ≤ bound)

include partition special_large other_small

theorem special_iff (x y : L) : special x y ↔
    TwoStep rel x y ∧ bound < Nat.card (CommonNeighbours rel x y) := by
  constructor
  · intro h
    exact ⟨(partition x y).mpr (Or.inl h),special_large x y h⟩
  · rintro ⟨hstep,hcard⟩
    rcases (partition x y).mp hstep with h|h
    · exact h
    · exact False.elim ((Nat.not_lt_of_ge (other_small x y h)) hcard)

theorem preserves_special (f : L ≃ L)
    (hf : ∀x y,rel (f x) (f y) ↔ rel x y) (x y : L) :
    special (f x) (f y) ↔ special x y := by
  rw [special_iff special other bound partition special_large other_small,
    special_iff special other bound partition special_large other_small,
    twoStep_iff rel f hf,commonNeighbour_card rel f hf]

end SymmetricSubgroupAsymptotics.CFSGCommonNeighbourRecognition
