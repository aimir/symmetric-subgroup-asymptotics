import SymmetricSubgroupAsymptotics.BinaryTransitiveActionClasses
import SymmetricSubgroupAsymptotics.BinaryWideMenuMass

/-!
# The actual complete binary pair-menu index

An entry retains one actual action class, one distinct original pairing,
one original normal and one literal central cut. Exactly one auxiliary
frame is chosen per pairing. The entry's cost and normalizer are the
original objects, and the complete sum agrees with the proved weighted
menu mass. Subfamilies may discard entries but cannot duplicate them.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

local instance originalNormal {G : Type*} [Group G]
    (N : {N : Subgroup G // N.Normal}) : N.1.Normal := N.2

instance realizedPairingFintype {X I : Type} [Finite X]
    (U : Subgroup (Equiv.Perm X)) : Fintype (RealizedPairing U I) := by
  letI : Finite (RealizedPairing U I) := RealizedPairing.finite
  exact Fintype.ofFinite _

instance originalNormalFintype {G : Type*} [Group G] [Finite G] :
    Fintype {N : Subgroup G // N.Normal} := Fintype.ofFinite _

instance centralCutFintype {X I : Type} [Finite I]
    {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U I)
    (N : Subgroup U) [N.Normal] : Fintype (F.CentralCut N) :=
  Fintype.ofFinite _

/-- The complete original finite index; proof and chart choices are not
additional entries. Normals and cuts remain dependent on their actual source. -/
abbrev BinaryOriginalMenuEntry (k : ℕ) (X : Type) :=
  Σ i : BinaryTransitiveActionClass X,
    Σ p : RealizedPairing i.representative (Fin (2^k)),
      Σ N : {N : Subgroup i.representative // N.Normal},
        p.chosenFrame.CentralCut N.1

namespace BinaryOriginalMenuEntry

variable {X : Type} {k : ℕ}

/-- The actual coefficient belonging to this original cut representation. -/
def cost (j : BinaryOriginalMenuEntry k X) : ℝ :=
  j.2.1.chosenFrame.centralCutCost j.2.2.1.1 j.2.2.2

/-- The normalizer is that of this chosen ORIGINAL permutation action. -/
def divisor (j : BinaryOriginalMenuEntry k X) : ℝ :=
  Nat.card (Subgroup.normalizer (j.1.representative : Set (Equiv.Perm X)))

theorem cost_nonneg (j : BinaryOriginalMenuEntry k X) : 0 ≤ j.cost :=
  Nat.cast_nonneg _

theorem divisor_pos [Finite X] (j : BinaryOriginalMenuEntry k X) : 0 < j.divisor := by
  dsimp only [divisor]
  exact_mod_cast (Nat.card_pos
    (α := Subgroup.normalizer (j.1.representative : Set (Equiv.Perm X))))

/-- The literal sigma sum is the already proved original weighted mass.
Coincident numeric costs or targets do not identify different entries. -/
theorem sum_cost_divisor_eq [Finite X] (k : ℕ) :
    (∑ j : BinaryOriginalMenuEntry k X, j.cost/j.divisor) =
      binaryOriginalWeightedMenuMass k
        (BinaryTransitiveActionClass.representative (X := X)) := by
  simp only [cost, divisor, Fintype.sum_sigma,
    binaryOriginalWeightedMenuMass, binaryActionPairMenuMass,
    BinaryPairFrame.frameMenuMass, BinaryPairFrame.normalCentralCutMass,
    Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr (by ext; simp only [Finset.mem_univ])
  intro i _
  apply Finset.sum_congr (by ext; simp only [Finset.mem_univ])
  intro p _
  apply Finset.sum_congr (by ext; simp only [Finset.mem_univ])
  intro N _
  apply Finset.sum_congr (by ext; simp only [Finset.mem_univ])
  intro C _
  rfl

/-- Any actual subfamily is dominated by the complete original sum.
This is literal subtype inclusion, not a bound on a selected label count. -/
theorem subfamily_mass_le [Finite X] (P : BinaryOriginalMenuEntry k X → Prop) :
    (∑ j : {j : BinaryOriginalMenuEntry k X // P j}, j.1.cost/j.1.divisor) ≤
      ∑ j : BinaryOriginalMenuEntry k X, j.cost/j.divisor := by
  calc
    _ = ∑ j ∈ Finset.univ.image
        (Subtype.val : {j : BinaryOriginalMenuEntry k X // P j} →
          BinaryOriginalMenuEntry k X), j.cost/j.divisor :=
      (Finset.sum_image Subtype.val_injective.injOn).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun j _ _ => div_nonneg j.cost_nonneg j.divisor_pos.le)

/-- A numerical constant bounds the complete ACTUAL original menu at all
power degrees. Representative completeness and separation are internal. -/
theorem uniform_mass_le :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ {X : Type} [Finite X] (k : ℕ)
      (hdegree : Nat.card X = 2^(k+1)),
      (∑ j : BinaryOriginalMenuEntry k X, j.cost/j.divisor) ≤
        (2 : ℝ)^(((2 : ℝ)^(k+1))^2/128+H) := by
  obtain ⟨H,hH,hbound⟩ := binaryOriginalWeightedMenuMass_uniform_le
  refine ⟨H,hH,?_⟩
  intro X _ k hdegree
  rw [sum_cost_divisor_eq]
  let P : Sylow 2 (Equiv.Perm X) := Classical.choice inferInstance
  exact hbound k P BinaryTransitiveActionClass.representative
    BinaryTransitiveActionClass.representative_pretransitive
    BinaryTransitiveActionClass.representative_isPGroup hdegree
    BinaryTransitiveActionClass.representative_separated

/-- The same fixed constant applies to every actual acceptance predicate
by inclusion. This statement does not assert that the predicate covers normals. -/
theorem uniform_subfamily_mass_le :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ {X : Type} [Finite X] (k : ℕ)
      (hdegree : Nat.card X = 2^(k+1)) (P : BinaryOriginalMenuEntry k X → Prop),
      (∑ j : {j : BinaryOriginalMenuEntry k X // P j}, j.1.cost/j.1.divisor) ≤
        (2 : ℝ)^(((2 : ℝ)^(k+1))^2/128+H) := by
  obtain ⟨H,hH,hbound⟩ := uniform_mass_le
  refine ⟨H,hH,?_⟩
  intro X _ k hdegree P
  exact (subfamily_mass_le P).trans (hbound k hdegree)

end BinaryOriginalMenuEntry
end SymmetricSubgroupAsymptotics

end
