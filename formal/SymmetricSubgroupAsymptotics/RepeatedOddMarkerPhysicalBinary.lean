import SymmetricSubgroupAsymptotics.RepeatedOddMarkerPhysicalProfile
import SymmetricSubgroupAsymptotics.FiniteProductPGroup
import SymmetricSubgroupAsymptotics.PGroupTransitiveDegree

/-!
# Original binary exteriors in the physical repeated-marker count

Binaryity is installed from the original orbit actions. The exact full
profile count retains every exterior normalizer and multiplicity. An
arbitrary further predicate on the original physical subgroup receives
an upper bound by inclusion, so earlier ownership exclusions do not
require an unproved naturality or an equality for a restricted fibre.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.RepeatedOddMarkerPhysicalBinary

open RepeatedOddMarkerPhysicalProfile

variable {α : Type} [Fintype α] (Ω : α → Type)
    [∀ a, Fintype (Ω a)] [∀ a, Nonempty (Ω a)]
    (m : α → ℕ) (U : ∀ a, Subgroup (Equiv.Perm (Ω a))) (g : ℕ)

theorem exteriorDegree_ne_three (hU : ∀ a, IsPGroup 2 (U a))
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y) :
    ∀ a, Fintype.card (Ω a) ≠ 3 := by
  intro a
  let x : Ω a := Classical.choice inferInstance
  have h := binary_transitive_degree_ne_three (hU a) x (htrans a x)
  simpa only [Nat.card_eq_fintype_card] using h

/-- Exact count, with binaryity checked on each original exterior action. -/
theorem card_physical_rat {X : Type}
    (e : ModelPoints Ω m g ≃ X) (hU : ∀ a, IsPGroup 2 (U a))
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U) :
    (Nat.card (PhysicalFamily Ω m U g X) : ℚ) =
      ((3*g + ∑ a, m a * Fintype.card (Ω a)).factorial : ℚ) * modelWeight Ω m U g /
        ((6 : ℚ)^g * g.factorial * exteriorDenominator Ω m U) :=
  RepeatedOddMarkerPhysicalProfile.card_physical_rat Ω m U g e
    (orbitProfileProduct_isPGroup m U hU) htrans hsep
    (exteriorDegree_ne_three Ω U hU htrans)

/-- Keep any ownership test on the original subgroup. Only inclusion is
used; the predicate need not be invariant under relabelling. -/
theorem card_restricted_physical_le {X : Type}
    (e : ModelPoints Ω m g ≃ X) (hU : ∀ a, IsPGroup 2 (U a))
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U)
    (P : Subgroup (Equiv.Perm X) → Prop) :
    (Nat.card {H : PhysicalFamily Ω m U g X // P H.1} : ℚ) ≤
      ((3*g + ∑ a, m a * Fintype.card (Ω a)).factorial : ℚ) * modelWeight Ω m U g /
        ((6 : ℚ)^g * g.factorial * exteriorDenominator Ω m U) := by
  letI : Finite X := Finite.of_equiv (ModelPoints Ω m g) e
  letI : Finite (PhysicalFamily Ω m U g X) :=
    Finite.of_injective (fun H : PhysicalFamily Ω m U g X =>
      (H.1 : Set (Equiv.Perm X)))
      (fun _ _ h => Subtype.ext (SetLike.coe_injective h))
  rw [← card_physical_rat Ω m U g e hU htrans hsep]
  exact_mod_cast (Nat.card_le_card_of_injective
    (fun H : {H : PhysicalFamily Ω m U g X // P H.1} => H.1)
    Subtype.val_injective)

end SymmetricSubgroupAsymptotics.RepeatedOddMarkerPhysicalBinary

end
