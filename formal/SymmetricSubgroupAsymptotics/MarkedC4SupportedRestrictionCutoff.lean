import SymmetricSubgroupAsymptotics.MarkedC4SupportedPermutationRestriction
import SymmetricSubgroupAsymptotics.MarkedC4EmbeddedPermutationOrbit

/-! Canonical slot restriction preserves the original orbit cutoff. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.SupportedRestrictionCutoff
open SupportedPermutationRestriction

variable {b C : ℕ} (a : Fin (b+1))
  (P : Subgroup (Equiv.Perm (Fin (b+1))))
  (hP : NilpotentPhysicalProductEncoding.supported a.val P)

include hP in
theorem action_range :
    (EmbeddedPermutationOrbit.action (G := restrict a P) (slots a)).range=P := by
  calc
    _ = (restrict a P).map (extension a) := by
      ext p
      constructor
      · rintro ⟨g,rfl⟩
        exact ⟨g.1,g.2,rfl⟩
      · rintro ⟨g,hg,rfl⟩
        exact ⟨⟨g,hg⟩,rfl⟩
    _ = P := recover a P hP

include hP in
theorem cutoff (hcut : ∀ x : Fin (b+1),Nat.card (MulAction.orbit P x)<C) :
    ∀ x : Fin a.val,Nat.card (MulAction.orbit (restrict a P) x)<C := by
  intro x
  have he := EmbeddedPermutationOrbit.orbit_card_image (G := restrict a P) (slots a) x
  rw [action_range a P hP] at he
  exact he.symm.le.trans_lt (hcut (slots a x))
end SymmetricSubgroupAsymptotics.MarkedC4.SupportedRestrictionCutoff
