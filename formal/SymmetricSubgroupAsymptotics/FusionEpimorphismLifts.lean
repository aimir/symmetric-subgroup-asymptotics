import SymmetricSubgroupAsymptotics.FusionGoursatCount
import SymmetricSubgroupAsymptotics.Non2SchurBound

/-!
# Actual quotient epimorphisms and surviving extension fibres

This is the bridge from physical Goursat counting to the Schur estimate.
The source remains one whole original subgroup J; every original quotient
map and extension fibre is retained, including empty nonsplit fibres.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {J Q B : Type*} [Group J] [Group Q] [Group B]

instance fusionEpimorphism_finite [Finite J] [Finite Q] : Finite (GroupEpimorphism J Q) :=
  Finite.of_injective (fun f : GroupEpimorphism J Q => (f.1 : J → Q))
    (fun _ _ h => Subtype.ext (DFunLike.coe_injective h))

instance fusionEpimorphism_fintype [Finite J] [Finite Q] : Fintype (GroupEpimorphism J Q) :=
  Fintype.ofFinite _

/-- An onto original quotient map is exactly an onto map to the base and
an onto lift in that literal fibre. No independent source is introduced. -/
def fusionEpimorphismLiftEquiv (π : Q →* B) (hπ : Function.Surjective π) :
    GroupEpimorphism J Q ≃
      Σ β : GroupEpimorphism J B,
        {f : HomomorphicLift π β.1 // Function.Surjective f.1} where
  toFun f := ⟨⟨π.comp f.1,hπ.comp f.2⟩,⟨f.1,rfl⟩,f.2⟩
  invFun d := ⟨d.2.1.1,d.2.2⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨β,hβ⟩,⟨⟨f,hf⟩,hs⟩⟩
    cases hf
    rfl

/-- Survival is checked on the original onto lift, not on its unmarked
base quotient or a numerical surrogate. -/
def FusionEpimorphismLiftSurvival (π : Q →* B)
    (S : GroupEpimorphism J Q → Prop) (β : GroupEpimorphism J B)
    (f : HomomorphicLift π β.1) : Prop :=
  ∃ hf : Function.Surjective f.1, S ⟨f.1,hf⟩

def fusionEpimorphismSurvivalEquiv (π : Q →* B) (hπ : Function.Surjective π)
    (S : GroupEpimorphism J Q → Prop) :
    {f : GroupEpimorphism J Q // S f} ≃
      Σ β : GroupEpimorphism J B,
        {f : HomomorphicLift π β.1 // FusionEpimorphismLiftSurvival π S β f} where
  toFun f := ⟨⟨π.comp f.1.1,hπ.comp f.1.2⟩,⟨f.1.1,rfl⟩,f.1.2,f.2⟩
  invFun d := ⟨⟨d.2.1.1,d.2.2.choose⟩,d.2.2.choose_spec⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨β,hβ⟩,⟨⟨f,hf⟩,hs⟩⟩
    cases hf
    rfl

/-- Exact retained-fibre sum for the original extension. -/
theorem fusionEpimorphism_survival_card [Finite J] [Finite Q] [Finite B]
    (π : Q →* B) (hπ : Function.Surjective π) (S : GroupEpimorphism J Q → Prop) :
    Nat.card {f : GroupEpimorphism J Q // S f} =
      ∑ β : GroupEpimorphism J B,
        Nat.card {f : HomomorphicLift π β.1 // FusionEpimorphismLiftSurvival π S β f} := by
  rw [Nat.card_congr (fusionEpimorphismSurvivalEquiv π hπ S)]
  exact Nat.card_sigma

section Numerical

variable {J₀ Q₀ B₀ : Type} [Group J₀] [Group Q₀] [Group B₀]
variable [Finite J₀] [Finite Q₀] [Finite B₀]

/-- Sum the actual Schur costs only after retaining the original base maps.
Each rank is that of the actual Sylow kernel for that same map β. -/
theorem fusionEpimorphism_survival_card_le_schur (p : ℕ) [Fact p.Prime]
    (π : Q₀ →* B₀) (hπ : Function.Surjective π)
    (M : Rep (ZMod p) B₀) [Finite M] (E : OriginalKernelModuleChart π M)
    (P : ∀ β : GroupEpimorphism J₀ B₀, Sylow p β.1.ker)
    (S : GroupEpimorphism J₀ Q₀ → Prop) :
    (Nat.card {f : GroupEpimorphism J₀ Q₀ // S f} : ℝ) ≤
      ∑ β : GroupEpimorphism J₀ B₀,
        Nat.card M * Nat.card (groupCohomology.H1 M) *
          (p : ℝ) ^ (representationSchurCapacity M.ρ *
            Module.finrank (ZMod p) (PrimeAbelianization p (P β : Subgroup β.1.ker))) := by
  rw [fusionEpimorphism_survival_card π hπ S,Nat.cast_sum]
  apply Finset.sum_le_sum
  intro β _
  exact homomorphicLift_survival_card_le_schur p π β.1 β.2 M E (P β)
    (FusionEpimorphismLiftSurvival π S β)

/-- The quotient-map factor, original extension constants, and original
Schur capacity are separated. The sole numerical rank premise concerns
actual Frattini quotients, suitable for the published permutation bound. -/
theorem fusionEpimorphism_survival_card_le_schur_of_rank_bound (p : ℕ) [Fact p.Prime]
    (π : Q₀ →* B₀) (hπ : Function.Surjective π)
    (M : Rep (ZMod p) B₀) [Finite M] (E : OriginalKernelModuleChart π M)
    (P : ∀ β : GroupEpimorphism J₀ B₀, Sylow p β.1.ker)
    (S : GroupEpimorphism J₀ Q₀ → Prop) (b : ℝ)
    (hrank : ∀ β : GroupEpimorphism J₀ B₀,
      (Module.finrank (ZMod p) (PrimeAbelianization p (P β : Subgroup β.1.ker)) : ℝ) ≤ b/p) :
    (Nat.card {f : GroupEpimorphism J₀ Q₀ // S f} : ℝ) ≤
      Nat.card (GroupEpimorphism J₀ B₀) *
        (Nat.card M * Nat.card (groupCohomology.H1 M) *
          (p : ℝ) ^ (representationSchurCapacity M.ρ * (b/p))) := by
  rw [fusionEpimorphism_survival_card π hπ S,Nat.cast_sum]
  calc
    _ ≤ ∑ β : GroupEpimorphism J₀ B₀,
        Nat.card M * Nat.card (groupCohomology.H1 M) *
          (p : ℝ) ^ (representationSchurCapacity M.ρ * (b/p)) := by
      apply Finset.sum_le_sum
      intro β _
      exact homomorphicLift_survival_card_le_schur_of_rank_bound p π β.1 β.2 M E
        (P β) (FusionEpimorphismLiftSurvival π S β) b (hrank β)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_eq_nat_card]

end Numerical

end SymmetricSubgroupAsymptotics
