import SymmetricSubgroupAsymptotics.WreathHomProjectionRange
import SymmetricSubgroupAsymptotics.SubgroupProductClassBound
import SymmetricSubgroupAsymptotics.BlockKernelClassBound

/-! A coordinate-capacity bound for arbitrary correlated wreath subgroups.
The kernel retains its actual coordinate images; no full base or splitting
assumption is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.WreathSubgroupClassCapacity
open WreathHomProjectionRange

variable {A C Q I : Type} [Group A] [Group C] [Group Q] [MulAction Q I]

def kernelCoordinate (f : A →* PermutationalWreathProduct C Q I) (i : I) :
    (topProjection f).ker →* C where
  toFun a := (f a.val).left i
  map_one' := by simp
  map_mul' a b := by
    have ha : (f a.val).right = 1 := a.property
    simp [PermutationalWreathProduct.mul_left,ha]

theorem kernelCoordinates_injective
    (f : A →* PermutationalWreathProduct C Q I) (hf : Function.Injective f) :
    Function.Injective (fun a i => kernelCoordinate f i a) := by
  intro a b he
  apply Subtype.ext
  apply hf
  apply PermutationalWreathProduct.ext
  · exact he
  · exact a.property.trans b.property.symm

theorem class_card_le_capacity_mul_top [Finite A] [Finite C] [Finite I]
    (f : A →* PermutationalWreathProduct C Q I) (hf : Function.Injective f)
    (c : ℕ) (hc : ∀ L : Subgroup C, Nat.card (ConjClasses L) ≤ c) :
    Nat.card (ConjClasses A) ≤ c^Nat.card I *
      Nat.card (ConjClasses (topProjection f).range) := by
  letI : Fintype I := Fintype.ofFinite _
  have hk : Nat.card (ConjClasses (topProjection f).ker) ≤ c^Nat.card I := by
    have h := conjugacyClass_card_le_finite_coordinate_bounds
      (fun _ : I => C) (fun _ => c) (fun _ => hc)
      (topProjection f).ker (kernelCoordinate f) (kernelCoordinates_injective f hf)
    simpa only [Finset.prod_const,Finset.card_univ,Nat.card_eq_fintype_card] using h
  exact (conjugacyClass_card_le_kernel_mul_range (topProjection f)).trans
    (Nat.mul_le_mul_right _ hk)

theorem subgroup_class_card_le_three [Finite C] (horder : Nat.card C ≤ 6)
    (hclass : Nat.card (ConjClasses C) ≤ 3) (L : Subgroup C) :
    Nat.card (ConjClasses L) ≤ 3 := by
  by_cases hL : L=⊤
  · subst L
    let e : C ≃* (⊤ : Subgroup C) := Subgroup.topEquiv.symm
    exact (Nat.card_le_card_of_surjective
      (ConjClasses.map e.toMonoidHom)
      (ConjClasses.map_surjective e.surjective)).trans hclass
  · have hi : 2 ≤ L.index := L.one_lt_index_of_ne_top hL
    have hm : Nat.card L * L.index ≤ 6 := L.card_mul_index.le.trans horder
    have hc : Nat.card L ≤ 3 := by
      nlinarith [Nat.mul_le_mul_left (Nat.card L) hi]
    exact (Nat.card_le_card_of_surjective (@ConjClasses.mk L _)
      ConjClasses.mk_surjective).trans hc

end SymmetricSubgroupAsymptotics.WreathSubgroupClassCapacity
