import SymmetricSubgroupAsymptotics.C3EpimorphismCharacters
import SymmetricSubgroupAsymptotics.C1RetainedAnnihilator

/-!
# Exhaustive character partition of the trivial-axis regular C3 branch

Every full trivial-axis local subgroup is classified by its complete
complement and one nonzero oriented ternary character.  The classification
retains an arbitrary predicate on the original physical subgroup.  It then
partitions exactly into the existing split-character owner and the nonzero
part of the retained nonsplit annihilator.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

variable {J : Type*} [Group J]

/-- Change the target of a literal epimorphism from the regular permutation
copy of C3 to C3 itself, then remember the corresponding nonzero character. -/
def regularC3EpimorphismEquivNonzero :
    GroupEpimorphism J ternaryRegularAction ≃
      {χ : PrimeCharacters 3 J // χ ≠ 0} :=
  (fusionGroupEpimorphismCongr (MulEquiv.refl J)
    ternaryRegularEquiv.symm).trans ternaryEpimorphismEquivNonzero

@[simp] theorem regularC3EpimorphismEquivNonzero_symm_apply
    (χ : {χ : PrimeCharacters 3 J // χ ≠ 0}) :
    regularC3EpimorphismEquivNonzero.symm χ =
      c3EpimorphismOfCharacter χ := by
  rfl

def c3PhysicalCharacterGraph {Z : Type*}
    (K : Subgroup (Equiv.Perm Z)) (χ : PrimeCharacters 3 K) :
    Subgroup (ternaryRegularAction × Equiv.Perm Z) :=
  (ternaryActualGraph ⟨K,χ⟩).map
    (ternaryPhysicalCoordinateEquiv (Z := Z)).toMonoidHom

/-- Complete character parameters for the trivial-axis branch, with the
survival test evaluated on the original physical subgroup. -/
abbrev C3TrivialCharacterData (b : ℕ)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop) :=
  Σ K : Subgroup (Equiv.Perm (Fin b)),
    {χ : {χ : PrimeCharacters 3 K // χ ≠ 0} //
      P (c3PhysicalCharacterGraph K χ.1)}

/-- The literal trivial-axis local family is the survival-restricted pointed
Goursat family for the identity quotient map. -/
def c3TrivialAxisPointedEquiv (b : ℕ)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop) :
    C3TrivialAxisLocalFamily P ≃
      {H : FusionPointedSubgroups (MonoidHom.id ternaryRegularAction)
          (Equiv.Perm (Fin b)) // P H.1} where
  toFun H := ⟨⟨H.1.1,H.1.2.1,by simpa using H.2⟩,H.1.2.2⟩
  invFun H := ⟨⟨H.1.1,H.1.2.1,H.2⟩,by simpa using H.1.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Rewrite the exact Goursat epimorphism parameter as the corresponding
physical nonzero character graph. -/
def c3GoursatCharactersEquiv (b : ℕ)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop) :
    (Σ K : Subgroup (Equiv.Perm (Fin b)),
      {β : GroupEpimorphism K ternaryRegularAction //
        P (fusionGoursatEncode (MonoidHom.id ternaryRegularAction) ⟨K,β⟩).1}) ≃
      C3TrivialCharacterData b P where
  toFun d := by
    let χ := regularC3EpimorphismEquivNonzero d.2.1
    refine ⟨d.1,⟨χ,?_⟩⟩
    have hβ : c3EpimorphismOfCharacter χ = d.2.1 := by
      rw [← regularC3EpimorphismEquivNonzero_symm_apply]
      exact regularC3EpimorphismEquivNonzero.symm_apply_apply d.2.1
    rw [c3PhysicalCharacterGraph,c3Epimorphism_character_graph,hβ]
    exact d.2.2
  invFun d := by
    refine ⟨d.1,⟨regularC3EpimorphismEquivNonzero.symm d.2.1,?_⟩⟩
    rw [regularC3EpimorphismEquivNonzero_symm_apply]
    change P (fusionQuotientGraph (MonoidHom.id ternaryRegularAction) d.1
      (c3EpimorphismOfCharacter d.2.1).1)
    rw [← c3Epimorphism_character_graph]
    exact d.2.2
  left_inv d := by
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      exact regularC3EpimorphismEquivNonzero.symm_apply_apply d.2.1
  right_inv d := by
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      exact regularC3EpimorphismEquivNonzero.apply_symm_apply d.2.1

/-- Exact classification of every surviving trivial-axis state. -/
def c3TrivialAxisCharacterEquiv (b : ℕ)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop) :
    C3TrivialAxisLocalFamily P ≃ C3TrivialCharacterData b P :=
  (c3TrivialAxisPointedEquiv b P).trans
    ((fusionGoursatSurvivalEquiv (MonoidHom.id ternaryRegularAction)
      Function.surjective_id (fun H => P H.1)).trans
        (c3GoursatCharactersEquiv b P))

abbrev C3SplitCharacterBranch (b : ℕ)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop) :=
  {d : C3TrivialCharacterData b P // TernarySplit d.2.1.1}

abbrev C3NonsplitCharacterBranch (b : ℕ)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop) :=
  {d : C3TrivialCharacterData b P // ¬ TernarySplit d.2.1.1}

/-- Exhaustive local split/nonsplit dichotomy after the direct axis has been
removed. -/
def c3TrivialCharacterPartitionEquiv (b : ℕ)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop) :
    C3TrivialCharacterData b P ≃
      C3SplitCharacterBranch b P ⊕ C3NonsplitCharacterBranch b P :=
  (Equiv.sumCompl (fun d : C3TrivialCharacterData b P =>
    TernarySplit d.2.1.1)).symm

theorem c3TrivialAxis_card_partition (b : ℕ)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop) :
    Nat.card (C3TrivialAxisLocalFamily P) =
      Nat.card (C3SplitCharacterBranch b P) +
        Nat.card (C3NonsplitCharacterBranch b P) := by
  rw [Nat.card_congr (c3TrivialAxisCharacterEquiv b P),
    Nat.card_congr (c3TrivialCharacterPartitionEquiv b P),Nat.card_sum]

/-- Every split state enters the already installed physical oriented-character
owner, with the same original survival predicate. -/
theorem c3SplitCharacter_mem_existing_owner (b : ℕ)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop)
    (d : C3SplitCharacterBranch b P) :
    TernaryPhysicalPredicate
      (fun L => P (L.map
        (ternaryPhysicalCoordinateEquiv (Z := Fin b)).toMonoidHom))
      (c3PhysicalCharacterGraph d.1.1 d.1.2.1.1) := by
  refine ⟨⟨ternaryActualGraph ⟨d.1.1,d.1.2.1.1⟩,?_⟩,rfl⟩
  refine ⟨⟨⟨d.1.1,d.1.2.1.1⟩,d.2,d.1.2.2⟩,rfl⟩

/-- Every state outside the split owner retains a nonzero character in the
literal nonsplit annihilator of its complete source. -/
theorem c3NonsplitCharacter_mem_retained_annihilator (b : ℕ)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop)
    (d : C3NonsplitCharacterBranch b P) :
    d.1.2.1.1 ∈ ternaryNonsplitAnnihilator d.1.1 ∧ d.1.2.1.1 ≠ 0 := by
  exact ⟨(ternaryNonsplitAnnihilator_mem_iff d.1.2.1.1).mpr d.2,
    d.1.2.1.2⟩

end SymmetricSubgroupAsymptotics

end
