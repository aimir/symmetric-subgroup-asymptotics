import SymmetricSubgroupAsymptotics.FusionEpimorphismLifts
import Mathlib.GroupTheory.Subgroup.Center

/-!
# Central-cut fibres on the original complete source

The actual central extension need not split. If one lift exists, differences
of its actual lifts are exactly homomorphisms into its central kernel.
Every original survival condition is retained before taking cardinal bounds.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {J Q B : Type*} [Group J] [Group Q] [Group B]

/-- The original extension kernel is central in the original group. -/
def FusionCentralKernel (π : Q →* B) : Prop :=
  ∀ a : π.ker, ∀ q : Q, Commute (a : Q) q

/-- Centrality turns the actual crossed equation into the usual hom equation. -/
theorem fusionCentral_cocycle_mul (π : Q →* B) (hC : FusionCentralKernel π)
    (f₀ : J →* Q) (z : KernelCocycle π f₀) (x y : J) : z.1 (x*y)=z.1 x*z.1 y := by
  apply Subtype.ext
  rw [z.2]
  change (z.1 x : Q)*f₀ x*(z.1 y : Q)*(f₀ x)⁻¹=(z.1 x : Q)*(z.1 y : Q)
  calc
    _ = (z.1 x : Q)*(f₀ x*(z.1 y : Q)*(f₀ x)⁻¹) := by group
    _ = _ := congrArg (fun t : Q => (z.1 x : Q)*t) ((hC (z.1 y) (f₀ x)).symm.mul_inv_cancel)

def fusionCentralCocycleEquivHom (π : Q →* B) (hC : FusionCentralKernel π)
    (f₀ : J →* Q) : KernelCocycle π f₀ ≃ (J →* π.ker) where
  toFun z := MonoidHom.mk' z.1 (fusionCentral_cocycle_mul π hC f₀ z)
  invFun f := ⟨f,by
    intro x y
    rw [f.map_mul]
    change (f x : Q)*(f y : Q)=(f x : Q)*f₀ x*(f y : Q)*(f₀ x)⁻¹
    have he := congrArg (fun t : Q => (f x : Q)*t) ((hC (f y) (f₀ x)).symm.mul_inv_cancel)
    calc
      _ = (f x : Q)*(f₀ x*(f y : Q)*(f₀ x)⁻¹) := he.symm
      _ = _ := by group⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A chosen origin inside the actual fibre gives a reversible torsor chart;
it does not give a section of the group extension. -/
def fusionCentralLiftEquivHom (π : Q →* B) (hC : FusionCentralKernel π)
    (β : J →* B) (f₀ : HomomorphicLift π β) : HomomorphicLift π β ≃ (J →* π.ker) :=
  (homomorphicLiftEquivCocycle π β f₀).trans (fusionCentralCocycleEquivHom π hC f₀.1)

/-- Any surviving original fibre costs at most the same-source central Hom
count, including empty nonsplit fibres and onto-only restrictions. -/
theorem fusionCentralLift_survival_card_le [Finite J] [Finite Q]
    (π : Q →* B) (hC : FusionCentralKernel π) (β : J →* B)
    (S : HomomorphicLift π β → Prop) :
    Nat.card {f : HomomorphicLift π β // S f} ≤ Nat.card (J →* π.ker) := by
  by_cases hf : Nonempty (HomomorphicLift π β)
  · obtain ⟨f₀⟩ := hf
    calc
      _ ≤ Nat.card (HomomorphicLift π β) :=
        Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
      _ = _ := Nat.card_congr (fusionCentralLiftEquivHom π hC β f₀)
  · letI : IsEmpty (HomomorphicLift π β) := not_nonempty_iff.mp hf
    simp

/-- Sum only after retaining every actual base quotient map. -/
theorem fusionCentralEpimorphism_survival_card_le [Finite J] [Finite Q] [Finite B]
    (π : Q →* B) (hπ : Function.Surjective π) (hC : FusionCentralKernel π)
    (S : GroupEpimorphism J Q → Prop) :
    Nat.card {f : GroupEpimorphism J Q // S f} ≤
      Nat.card (GroupEpimorphism J B)*Nat.card (J →* π.ker) := by
  rw [fusionEpimorphism_survival_card π hπ S]
  calc
    _ ≤ ∑ _β : GroupEpimorphism J B, Nat.card (J →* π.ker) := by
      apply Finset.sum_le_sum
      intro β _
      exact fusionCentralLift_survival_card_le π hC β.1 (FusionEpimorphismLiftSurvival π S β)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,Fintype.card_eq_nat_card]

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- An actual binary kernel chart identifies its exact Hom cardinality. -/
theorem fusionBinaryKernelHom_card [Finite J] [Finite V]
    (π : Q →* B) (E : π.ker ≃* Multiplicative V) :
    Nat.card (J →* π.ker)=2^(Module.finrank (ZMod 2) V*binaryCharacterRank J) := by
  rw [Nat.card_congr (E.monoidHomCongrRightEquiv (M := J)),binaryAbelianizationGroupHom_card]
  rw [Nat.mul_comm]

/-- The exact binary-marker factor for every fixed actual quotient fibre. -/
theorem fusionCentralBinaryLift_survival_card_le [Finite J] [Finite Q] [Finite V]
    (π : Q →* B) (hC : FusionCentralKernel π) (E : π.ker ≃* Multiplicative V)
    (β : J →* B) (S : HomomorphicLift π β → Prop) :
    Nat.card {f : HomomorphicLift π β // S f} ≤
      2^(Module.finrank (ZMod 2) V*binaryCharacterRank J) := by
  simpa only [fusionBinaryKernelHom_card π E] using fusionCentralLift_survival_card_le π hC β S

/-- The binary factor remains attached to the same original base map and
source, so it can be retained jointly inside the later graph moment. -/
theorem fusionCentralBinaryEpimorphism_survival_card_le
    [Finite J] [Finite Q] [Finite B] [Finite V]
    (π : Q →* B) (hπ : Function.Surjective π) (hC : FusionCentralKernel π)
    (E : π.ker ≃* Multiplicative V) (S : GroupEpimorphism J Q → Prop) :
    Nat.card {f : GroupEpimorphism J Q // S f} ≤
      Nat.card (GroupEpimorphism J B)*2^(Module.finrank (ZMod 2) V*binaryCharacterRank J) := by
  simpa only [fusionBinaryKernelHom_card π E] using
    fusionCentralEpimorphism_survival_card_le π hπ hC S

/-- A literal central subgroup supplies the actual quotient centrality. -/
theorem fusionCentralKernel_quotient (C : Subgroup Q) [C.Normal] (hC : C≤Subgroup.center Q) :
    FusionCentralKernel (QuotientGroup.mk' C) := by
  intro a q
  have ha : (a : Q)∈C := by
    have := a.2
    simpa only [QuotientGroup.ker_mk'] using this
  exact (Subgroup.mem_center_iff.mp (hC ha) q).symm

/-- The original central subgroup itself may supply the binary chart. -/
theorem fusionCentralBinaryQuotient_survival_card_le [Finite J] [Finite Q] [Finite V]
    (C : Subgroup Q) [C.Normal] (hC : C≤Subgroup.center Q)
    (E : C ≃* Multiplicative V) (S : GroupEpimorphism J Q → Prop) :
    Nat.card {f : GroupEpimorphism J Q // S f} ≤
      Nat.card (GroupEpimorphism J (Q ⧸ C))*
        2^(Module.finrank (ZMod 2) V*binaryCharacterRank J) :=
  fusionCentralBinaryEpimorphism_survival_card_le (QuotientGroup.mk' C)
    (QuotientGroup.mk'_surjective C) (fusionCentralKernel_quotient C hC)
    ((MulEquiv.subgroupCongr (QuotientGroup.ker_mk' C)).trans E) S

end SymmetricSubgroupAsymptotics
