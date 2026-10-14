import SymmetricSubgroupAsymptotics.Non2PreE7C2Wreath
import SymmetricSubgroupAsymptotics.TwoBlockProjectionIrreducibility

/-! Product-coordinate affine actions for any subgroup of a two-block
linear wreath. The actual complement subgroup is retained throughout. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace WreathAffineCoordinates

open SemidirectProduct

variable {V A : Type} [CommGroup V] [Group A] (φ : A →* MulAut V)

def action : C2Wreath.W A →* MulAut (V × V) where
  toFun g := (φ g.left.1).prodCongr (φ g.left.2) * C2Wreath.swapAut V g.right
  map_one' := by
    apply MulEquiv.ext
    intro v
    apply Prod.ext <;> simp <;> rfl
  map_mul' g h := by
    rcases g with ⟨⟨a, b⟩, c⟩
    rcases h with ⟨⟨d, e⟩, f⟩
    rcases C2Wreath.cases c with rfl | rfl <;>
      rcases C2Wreath.cases f with rfl | rfl
    all_goals
      apply MulEquiv.ext
      intro v
    · change (φ (a * d) v.1, φ (b * e) v.2) =
        (φ a (φ d v.1), φ b (φ e v.2))
      rw [map_mul, map_mul]
      rfl
    · change (φ (a * d) v.2, φ (b * e) v.1) =
        (φ a (φ d v.2), φ b (φ e v.1))
      rw [map_mul, map_mul]
      rfl
    · change (φ (a * e) v.2, φ (b * d) v.1) =
        (φ a (φ e v.2), φ b (φ d v.1))
      rw [map_mul, map_mul]
      rfl
    · change (φ (a * e) v.1, φ (b * d) v.2) =
        (φ a (φ e v.1), φ b (φ d v.2))
      rw [map_mul, map_mul]
      rfl

theorem action_inl (a : A × A) (v : V × V) :
    action φ (inl a) v = (φ a.1 v.1, φ a.2 v.2) := by
  change ((φ a.1).prodCongr (φ a.2) * C2Wreath.swapAut V 1) v = _
  rw [map_one]
  rfl

theorem action_swap (a : A × A) (v : V × V) :
    action φ (⟨a, C2Wreath.gen⟩ : C2Wreath.W A) v = (φ a.1 v.2, φ a.2 v.1) := by
  change (φ a.1 (C2Wreath.swapAut V C2Wreath.gen v).1,
    φ a.2 (C2Wreath.swapAut V C2Wreath.gen v).2) = _
  rw [C2Wreath.swapAut_gen]

theorem action_injective [Nontrivial V] (hφ : Function.Injective φ) :
    Function.Injective (action φ) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨⟨a, b⟩, c⟩ h
  rcases C2Wreath.cases c with rfl | rfl
  · have ha : φ a = 1 := by
      apply MulEquiv.ext
      intro v
      have he := congrArg (fun f : MulAut (V × V) ↦ (f (v, 1)).1) h
      simpa only [action_inl, MulAut.one_apply] using he
    have hb : φ b = 1 := by
      apply MulEquiv.ext
      intro v
      have he := congrArg (fun f : MulAut (V × V) ↦ (f (1, v)).2) h
      simpa only [action_inl, MulAut.one_apply] using he
    exact SemidirectProduct.ext
      (Prod.ext (hφ (ha.trans φ.map_one.symm)) (hφ (hb.trans φ.map_one.symm))) rfl
  · obtain ⟨v, hv⟩ := exists_ne (1 : V)
    have he := congrArg (fun f : MulAut (V × V) ↦ (f (v, 1)).1) h
    have hv1 : 1 = v := by simpa only [action_swap, map_one, MulAut.one_apply] using he
    exact (hv hv1.symm).elim

variable (C : Subgroup (C2Wreath.W A))

def restrictedAction : C →* MulAut (V × V) := (action φ).comp C.subtype
abbrev Model := (V × V) ⋊[restrictedAction φ C] C
abbrev Local := V ⋊[φ] A

def intoWreath : Model φ C →* C2Wreath.W (Local φ) where
  toFun g := ⟨(⟨g.left.1, g.right.val.left.1⟩,
    ⟨g.left.2, g.right.val.left.2⟩), g.right.val.right⟩
  map_one' := by
    apply SemidirectProduct.ext
    · apply Prod.ext <;> apply SemidirectProduct.ext <;> rfl
    · rfl
  map_mul' g h := by
    rcases g with ⟨⟨u, v⟩, ⟨⟨p, c⟩, hp⟩⟩
    rcases h with ⟨⟨w, z⟩, ⟨⟨q, d⟩, hq⟩⟩
    rcases C2Wreath.cases c with rfl | rfl
    all_goals
      apply SemidirectProduct.ext
      · apply Prod.ext <;> apply SemidirectProduct.ext <;>
          simp only [mul_left, mul_right, restrictedAction, MonoidHom.comp_apply,
            action_inl, action_swap, C2Wreath.swapAut_one, C2Wreath.swapAut_gen] <;> rfl
      · rfl

theorem intoWreath_injective : Function.Injective (intoWreath φ C) := by
  intro g h he
  apply SemidirectProduct.ext
  · exact Prod.ext
      (congrArg (fun z : C2Wreath.W (Local φ) ↦ z.left.1.left) he)
      (congrArg (fun z : C2Wreath.W (Local φ) ↦ z.left.2.left) he)
  · apply Subtype.ext
    apply SemidirectProduct.ext
    · exact Prod.ext
        (congrArg (fun z : C2Wreath.W (Local φ) ↦ z.left.1.right) he)
        (congrArg (fun z : C2Wreath.W (Local φ) ↦ z.left.2.right) he)
    · exact congrArg (fun z : C2Wreath.W (Local φ) ↦ z.right) he

def permutationAction {X : Type} (ρ : Local φ →* Equiv.Perm X) :
    Model φ C →* Equiv.Perm (X ⊕ X) :=
  (C2Wreath.action ρ).comp (intoWreath φ C)

theorem permutationAction_injective {X : Type} [Nonempty X]
    (ρ : Local φ →* Equiv.Perm X) (hρ : Function.Injective ρ) :
    Function.Injective (permutationAction φ C ρ) :=
  (C2Wreath.action_injective ρ hρ).comp (intoWreath_injective φ C)

end WreathAffineCoordinates
end SymmetricSubgroupAsymptotics

end
