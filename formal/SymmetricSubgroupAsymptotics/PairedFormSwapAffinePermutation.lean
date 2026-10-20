import SymmetricSubgroupAsymptotics.PairedFormSwapAffineAction

/-! Faithful permutation action of the graph-and-swap affine model,
with the actual two local affine coordinates retained. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PairedFormSwapAffine

open SemidirectProduct

variable {V R Y : Type} [CommGroup V] [Group R]
variable (φ : R →* MulAut V) (B : V → V → Y)
variable (hsymm : ∀ x y, B x y = B y x)

abbrev Local := V ⋊[φ] R

def intoWreath : Model φ B hsymm →* C2Wreath.W (Local φ) where
  toFun g := ⟨(⟨g.left.1, g.right.left.val.1⟩,
    ⟨g.left.2, g.right.left.val.2⟩), g.right.right⟩
  map_one' := by
    apply SemidirectProduct.ext
    · apply Prod.ext <;> apply SemidirectProduct.ext <;> rfl
    · rfl
  map_mul' g h := by
    rcases g with ⟨⟨u, v⟩, ⟨p, c⟩⟩
    rcases h with ⟨⟨w, z⟩, ⟨q, d⟩⟩
    rcases C2Wreath.cases c with rfl | rfl
    all_goals
      apply SemidirectProduct.ext
      · apply Prod.ext <;> apply SemidirectProduct.ext <;>
          simp only [mul_left, mul_right, action_one, action_swap,
            C2Wreath.swapAut_one, C2Wreath.swapAut_gen] <;> rfl
      · rfl

theorem intoWreath_injective : Function.Injective (intoWreath φ B hsymm) := by
  intro g h he
  apply SemidirectProduct.ext
  · exact Prod.ext
      (congrArg (fun z : C2Wreath.W (Local φ) ↦ z.left.1.left) he)
      (congrArg (fun z : C2Wreath.W (Local φ) ↦ z.left.2.left) he)
  · apply SemidirectProduct.ext
    · apply Subtype.ext
      exact Prod.ext
        (congrArg (fun z : C2Wreath.W (Local φ) ↦ z.left.1.right) he)
        (congrArg (fun z : C2Wreath.W (Local φ) ↦ z.left.2.right) he)
    · exact congrArg (fun z : C2Wreath.W (Local φ) ↦ z.right) he

variable {X : Type} (ρ : Local φ →* Equiv.Perm X)

def permutationAction : Model φ B hsymm →* Equiv.Perm (X ⊕ X) :=
  (C2Wreath.action ρ).comp (intoWreath φ B hsymm)

theorem permutationAction_injective [Nonempty X] (hρ : Function.Injective ρ) :
    Function.Injective (permutationAction φ B hsymm ρ) :=
  (C2Wreath.action_injective ρ hρ).comp (intoWreath_injective φ B hsymm)

def pairInr : Graph φ B →* Model φ B hsymm :=
  (inr : Complement φ B hsymm →* Model φ B hsymm).comp
    (inl : Graph φ B →* Complement φ B hsymm)

def firstTranslation : V →* Model φ B hsymm :=
  (inl : V × V →* Model φ B hsymm).comp (MonoidHom.inl V V)

theorem permutationAction_pair (g : Graph φ B) :
    permutationAction φ B hsymm ρ (pairInr φ B hsymm g) =
      Equiv.Perm.sumCongr (ρ (inr g.val.1)) (ρ (inr g.val.2)) :=
  C2Wreath.action_inl ρ _

theorem permutationAction_swap :
    permutationAction φ B hsymm ρ (inr (inr C2Wreath.gen)) = Equiv.sumComm X X :=
  C2Wreath.action_inr_gen ρ

theorem conj_inl (g : Model φ B hsymm) (v : V × V) :
    g * inl v * g⁻¹ = inl (action φ B hsymm g.right v) := by
  conv_lhs => rw [← inl_left_mul_inr_right g]
  have h : (inr g.right : Model φ B hsymm) * inl v * (inr g.right)⁻¹ =
      inl (action φ B hsymm g.right v) := by
    rw [← map_inv]
    exact (inl_aut (φ := action φ B hsymm) g.right v).symm
  calc
    (inl g.left * inr g.right : Model φ B hsymm) * inl v *
        (inl g.left * inr g.right)⁻¹ =
      inl g.left * ((inr g.right : Model φ B hsymm) * inl v * (inr g.right)⁻¹) *
        (inl g.left)⁻¹ := by group
    _ = inl (g.left * action φ B hsymm g.right v * g.left⁻¹) := by
      rw [h, ← map_inv, ← map_mul, ← map_mul]
    _ = _ := by rw [mul_comm g.left, mul_inv_cancel_right]

end PairedFormSwapAffine
end SymmetricSubgroupAsymptotics

end
