import SymmetricSubgroupAsymptotics.TwistedMonomialCocycleFilteredFrame
import SymmetricSubgroupAsymptotics.TwistedSimpleRootCocycleCount

/-! Whole twisted cocycles with genuine full root-local image. The
filtered frame code and exact simple outer fibre are composed without
dropping the onto-local predicate or replacing the actual coordinate twist. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwistedFullLocalCocycleCount
open TwistedMonomialCocycleFrame TwistedCocycleAssociatedHom

variable {Q X A U : Type*} [Group Q] [Finite Q] [Group A] [Finite A]
    [IsSimpleGroup A] [MulAction Q X] [Finite X]
    [MulAction.IsPretransitive Q X] [Group U] [Finite U]
variable (rho : Q →* MulAut (X → A)) (theta : Q → X → MulAut A)
    (hcoord : ∀ q : Q,∀ f : X → A,∀ x : X,
      (rho q f) (q • x)=theta q x (f x)) (x0 : X)
variable (β : MulAction.stabilizer Q x0 →* U) (ι : A →* U)
    (hcompat : ∀ h a,ι (rootAction rho theta hcoord x0 h a)=β h*ι a*(β h)⁻¹)

abbrev Family := {c : Cocycle rho //
  Function.Surjective (associatedHom (rootAction rho theta hcoord x0) β ι hcompat
    (rootRestriction rho theta hcoord x0 c))}

variable (E : Subgroup U) [E.Normal] (hιE : ∀ a,ι a∈E)
    (hθ : Function.Surjective (TwistedSimpleRootCocycleCount.outerMap β E))

include hιE hθ in
theorem card_family_le (C : SemisimpleNormalChart E)
    (e : quotientImage E (TwistedSimpleRootCocycleCount.zeroAxis (U := U)) ≃* A)
    (hZ : IsCenterless A) (hι : Function.Injective ι) :
    (Nat.card (Family rho theta hcoord x0 β ι hcompat) : ℝ) ≤
      (Nat.card A : ℝ)^(Nat.card X)*
        (Nat.card (A ≃* A)*
          (Real.logb 2 (Nat.card (TwistedSimpleRootCocycleCount.outerMap β E).ker)/
            Real.logb 2 (Nat.card A))) := by
  let α := rootAction rho theta hcoord x0
  let P : Cocycle α → Prop := fun r => Function.Surjective (associatedHom α β ι hcompat r)
  have hf := TwistedMonomialCocycleFilteredFrame.card_le_transitive_filtered
    rho theta hcoord x0 P
  have hf' : (Nat.card (Family rho theta hcoord x0 β ι hcompat) : ℝ) ≤
      (Nat.card A : ℝ)^(Nat.card X)*
        (Nat.card (TwistedSimpleRootCocycleCount.FullRoot α β ι hcompat) : ℝ) := by
    exact_mod_cast hf
  have hr := TwistedSimpleRootCocycleCount.card_fullRoot_le α β ι hcompat E hιE hθ C e hZ hι
  exact hf'.trans (mul_le_mul_of_nonneg_left hr (by positivity))

end SymmetricSubgroupAsymptotics.TwistedFullLocalCocycleCount
