import SymmetricSubgroupAsymptotics.SmallFibreTwentyFourClassPacketGap
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! Same-model transport of raw finite class/outer/index budgets into the
original binary/ternary small-fibre consumer. This is a generic theorem,
not a new profile constructor or an installed finite-model hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteSimpleModelSmallFibreClassConsumer
open PrimitiveSocleRawStructure OriginalBlockClassBound CFSGReduction

theorem subnormal_class_cube_gap_of_model_bounds
    {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω) = g • π ω)
    (c : ℕ) (hc : c = 2 ∨ c = 3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x) = c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (S : Type) [Group S] [Finite S] (e : E.Simple ≃* S)
    (b k o : ℕ)
    (hindex : ∀ K : Subgroup S, K ≠ ⊤ → b ≤ K.index)
    (hclass : Nat.card (ConjClasses S) ≤ k) (houter : Nat.card (Outer S) ≤ o)
    (hscaled : 24 * (k * o) ^ 3 ≤ 3 ^ b)
    (hsquare : ∀ ell : ℕ, LeastProperIndex S ell → ell ^ 2 < Nat.card S)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card Ω - 2) := by
  have hκ : Nat.card (ConjClasses E.Simple) ≤ k :=
    (Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
      (ConjClasses.map_surjective e.symm.surjective)).trans hclass
  have ho : Nat.card (Outer E.Simple) ≤ o := by
    rw [outer_card_congr e]
    exact houter
  apply SmallFibreTwentyFourClassPacketGap.subnormal_class_cube_gap_of_scaled_class_packet
    π hπ c hc hsize E ?_ ?_ H hH
  · intro K hK
    have hmap : K.map e.toMonoidHom ≠ ⊤ := by
      intro ht
      apply hK
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
    have hi := hindex (K.map e.toMonoidHom) hmap
    have hiEq : (K.map e.toMonoidHom).index = K.index := K.index_map_equiv e
    rw [hiEq] at hi
    exact (Nat.mul_le_mul_left 24 (Nat.pow_le_pow_left (Nat.mul_le_mul hκ ho) 3)).trans
      (hscaled.trans (Nat.pow_le_pow_right (by decide : 0 < 3) hi))
  · intro ell hell
    have hh := hsquare ell (leastProperIndex_of_mulEquiv e ell hell)
    rwa [Nat.card_congr e.toEquiv]

end SymmetricSubgroupAsymptotics.FiniteSimpleModelSmallFibreClassConsumer
