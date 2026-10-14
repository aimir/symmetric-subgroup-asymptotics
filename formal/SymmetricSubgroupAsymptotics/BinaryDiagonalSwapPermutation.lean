import SymmetricSubgroupAsymptotics.BinaryDiagonalSwapCoordinates

/-! The faithful imprimitive action of the diagonal/swap affine model.
The embedding into the ordinary two-block wreath product retains both
translation coordinates and the common local linear coordinate. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace BinaryDiagonalSwap

open SemidirectProduct

variable {V R : Type} [CommGroup V] [Group R]
variable (φ : R →* MulAut V)

def intoWreath : Model φ →* C2Wreath.W (Local φ) where
  toFun g := ⟨(⟨g.left.1, g.right.1⟩, ⟨g.left.2, g.right.1⟩), g.right.2⟩
  map_one' := by
    apply SemidirectProduct.ext
    · apply Prod.ext <;> apply SemidirectProduct.ext <;> rfl
    · rfl
  map_mul' g h := by
    rcases g with ⟨⟨u, v⟩, ⟨r, c⟩⟩
    rcases h with ⟨⟨w, z⟩, ⟨s, d⟩⟩
    rcases C2Wreath.cases c with rfl | rfl
    all_goals
      apply SemidirectProduct.ext
      · apply Prod.ext <;> apply SemidirectProduct.ext <;>
          simp only [mul_left, mul_right, action_one, action_swap,
            C2Wreath.swapAut_one, C2Wreath.swapAut_gen] <;> rfl
      · rfl

theorem intoWreath_injective : Function.Injective (intoWreath φ) := by
  intro g h he
  apply SemidirectProduct.ext
  · exact Prod.ext
      (congrArg (fun z : C2Wreath.W (Local φ) ↦ z.left.1.left) he)
      (congrArg (fun z : C2Wreath.W (Local φ) ↦ z.left.2.left) he)
  · exact Prod.ext
      (congrArg (fun z : C2Wreath.W (Local φ) ↦ z.left.1.right) he)
      (congrArg (fun z : C2Wreath.W (Local φ) ↦ z.right) he)

variable {X : Type} (ρ : Local φ →* Equiv.Perm X)

def permutationAction : Model φ →* Equiv.Perm (X ⊕ X) :=
  (C2Wreath.action ρ).comp (intoWreath φ)

theorem permutationAction_injective [Nonempty X]
    (hρ : Function.Injective ρ) : Function.Injective (permutationAction φ ρ) :=
  (C2Wreath.action_injective ρ hρ).comp (intoWreath_injective φ)

theorem permutationAction_inl (v : V × V) :
    permutationAction φ ρ (inl v) =
      Equiv.Perm.sumCongr (ρ (inl v.1)) (ρ (inl v.2)) :=
  C2Wreath.action_inl ρ _

theorem permutationAction_diagonal (r : R) :
    permutationAction φ ρ (inr (r, 1)) =
      Equiv.Perm.sumCongr (ρ (inr r)) (ρ (inr r)) :=
  C2Wreath.action_inl ρ _

theorem permutationAction_swap :
    permutationAction φ ρ (inr (1, C2Wreath.gen)) = Equiv.sumComm X X :=
  C2Wreath.action_inr_gen ρ

end BinaryDiagonalSwap
end SymmetricSubgroupAsymptotics

end
