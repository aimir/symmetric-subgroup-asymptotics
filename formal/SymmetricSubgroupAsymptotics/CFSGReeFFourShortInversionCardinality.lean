import SymmetricSubgroupAsymptotics.CFSGReeFFourReducedPositiveIntersection
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedSubgroupPeeling
import Mathlib.Algebra.Group.Subgroup.Finite

/-! Exact inversion counts for all sixteen original short words. The
proved full positive intersection is conjugate to the actual first-peel
remainder. Its existing cardinality factorization and the actual peel
bijection cancel to determine the inversion count. No ambient group
order, complementary-word identity, or cell disjointness is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourShortInversionCardinality
open CFSGReeFFourReducedPositiveIntersection CFSGReeFFourShortPairedWeylMenu
open CFSGReeFFourFixedSubgroupPeeling CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourOppositionFixedPositiveNegative CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedAmbientHom CFSGOpposedSubgroupPeeling

private instance fixedFinite (m : ℕ) : Finite (originalModelFixed m) :=
  Finite.of_injective (fixedAmbientHom m) (fixedAmbientHom_injective m)

/-- Conjugation by the SAME actual short word exchanges its two
positive-intersection orientations. -/
theorem shortPositiveIntersection_map_conj (m : ℕ) (i : Fin 16) :
    (shortPositiveIntersection m i).map
        (MulAut.conj (shortModelWord m i)).toMonoidHom =
      remainderPart (fixedPositive m) (fixedPositive m) (shortModelWord m i) := by
  ext x
  constructor
  · rintro ⟨u,hu,rfl⟩
    change u∈fixedPositive m ∧
      shortModelWord m i*u*(shortModelWord m i)⁻¹∈fixedPositive m at hu
    refine ⟨hu.2,u,hu.1,rfl⟩
  · intro hx
    obtain ⟨u,hu,he⟩ := hx.2
    refine ⟨u,?_,he⟩
    change u∈fixedPositive m ∧
      shortModelWord m i*u*(shortModelWord m i)⁻¹∈fixedPositive m
    refine ⟨hu,?_⟩
    change shortModelWord m i*u*(shortModelWord m i)⁻¹=x at he
    rw [he]
    exact hx.1

theorem short_remainder_card (m : ℕ) (i : Fin 16) :
    Nat.card (remainderPart (fixedPositive m) (fixedPositive m) (shortModelWord m i)) =
      Nat.card (shortPositiveIntersection m i) := by
  rw [←shortPositiveIntersection_map_conj]
  exact Subgroup.card_map_of_injective (MulAut.conj (shortModelWord m i)).injective

/-- The existing local positive chart determines the actual inversion
block cardinality, without a whole-group order formula. -/
theorem short_inversion_card (m : ℕ) (i : Fin 16) :
    Nat.card (inversionPart (fixedPositive m) (fixedNegative m) (shortModelWord m i)) =
      (2^(2*m+1))^(inversionWeight i) := by
  have hpeel := fixedPositive_card_first_peel m (shortWord i)
  change Nat.card (fixedPositive m) =
    Nat.card (remainderPart (fixedPositive m) (fixedPositive m) (shortModelWord m i))*
      Nat.card (inversionPart (fixedPositive m) (fixedNegative m) (shortModelWord m i)) at hpeel
  rw [short_remainder_card] at hpeel
  have hchart := shortPositiveIntersection_card_factorization m i
  exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α:=shortPositiveIntersection m i))
    (hpeel.symm.trans hchart)

end SymmetricSubgroupAsymptotics.CFSGReeFFourShortInversionCardinality
