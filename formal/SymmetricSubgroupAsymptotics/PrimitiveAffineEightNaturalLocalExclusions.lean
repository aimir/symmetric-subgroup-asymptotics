import SymmetricSubgroupAsymptotics.FinZeroPermutationStabilizer
import SymmetricSubgroupAsymptotics.SmallTernaryQuotientObstructions
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightNaturalTops
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
The other two excluded primitive eight-point actions are the actual natural
alternating and symmetric groups. Restriction to the seven remaining
points identifies their point stabilizers exactly; simplicity of A7 and
its index two in S7 exclude all onto maps of order three or six.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineEightNaturalLocalExclusions

open Equiv
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

private theorem six_lt_card_alternating_seven :
    6 < Nat.card (alternatingGroup (Fin 7)) := by
  rw [nat_card_alternatingGroup]
  norm_num

theorem alternating_no_eligible_pointStabilizer_quotient
    {Q : Type} [Group Q] [Finite Q]
    (f : MulAction.stabilizer (alternatingGroup (Fin 8)) (0 : Fin 8) →* Q)
    (hQ : Nat.card Q = 3 ∨ Nat.card Q = 6) :
    ¬ Function.Surjective f := by
  letI : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  intro hf
  exact not_surjective_three_or_six_of_simple six_lt_card_alternating_seven
    (f.comp (FinZeroPermutationStabilizer.alternatingEquiv 7).toMonoidHom) hQ
    (hf.comp (FinZeroPermutationStabilizer.alternatingEquiv 7).surjective)

theorem symmetric_no_eligible_pointStabilizer_quotient
    {Q : Type} [Group Q] [Finite Q]
    (f : MulAction.stabilizer (Perm (Fin 8)) (0 : Fin 8) →* Q)
    (hQ : Nat.card Q = 3 ∨ Nat.card Q = 6) :
    ¬ Function.Surjective f := by
  letI : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  intro hf
  exact not_surjective_three_or_six_of_simple_subgroup
    (alternatingGroup (Fin 7)) (by simp)
    six_lt_card_alternating_seven
    (f.comp (FinZeroPermutationStabilizer.symmetricEquiv 7).toMonoidHom) hQ
    (hf.comp (FinZeroPermutationStabilizer.symmetricEquiv 7).surjective)

/-- Remove only the redundant top-subgroup wrapper, preserving the point. -/
def topPointStabilizerEquiv {X : Type} (x : X) :
    MulAction.stabilizer (⊤ : Subgroup (Perm X)) x ≃*
      MulAction.stabilizer (Perm X) x where
  toFun g := ⟨g.1.1, g.2⟩
  invFun g := ⟨⟨g.1, Subgroup.mem_top _⟩, g.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The retained two literal A8 generators give the same actual stabilizer. -/
theorem row23_no_eligible_pointStabilizer_quotient :
    ∀ (Q : Type) [Group Q] [Finite Q]
      (f : MulAction.stabilizer DegreeTwoPairedEightSharedTops.Top23 (0 : Fin 8) →* Q),
      (Nat.card Q = 3 ∨ Nat.card Q = 6) → ¬ Function.Surjective f := by
  rw [DegreeTwoPairedEightSharedTops.top23_eq_alternating]
  exact fun _ _ _ f hQ => alternating_no_eligible_pointStabilizer_quotient f hQ

/-- Likewise for the retained literal S8 generators. -/
theorem row24_no_eligible_pointStabilizer_quotient :
    ∀ (Q : Type) [Group Q] [Finite Q]
      (f : MulAction.stabilizer DegreeTwoPairedEightSharedTops.Top24 (0 : Fin 8) →* Q),
      (Nat.card Q = 3 ∨ Nat.card Q = 6) → ¬ Function.Surjective f := by
  rw [DegreeTwoPairedEightSharedTops.top24_eq_top]
  intro Q _ _ f hQ hf
  exact symmetric_no_eligible_pointStabilizer_quotient
    (f.comp (topPointStabilizerEquiv (0 : Fin 8)).symm.toMonoidHom) hQ
    (hf.comp (topPointStabilizerEquiv (0 : Fin 8)).symm.surjective)

end PrimitiveAffineEightNaturalLocalExclusions
end SymmetricSubgroupAsymptotics

end
