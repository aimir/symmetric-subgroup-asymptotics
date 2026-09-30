import SymmetricSubgroupAsymptotics.BinaryS16CanonicalCarrierProfile

/-!
# The unmarked S16 residual partition

The checked structural dichotomy partitions each actual retained-background
subgroup by a deterministic first branch.  The positive branch keeps the
same residual-sector element; the other branch keeps the same literal
permutation subgroup in the already existing complete even critical family.
No orbit, chart, route, or owner witness is added to the counted object.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryS16ResidualPartition

open SymmetricSubgroupAsymptotics
open BinaryS16CanonicalCarrierProfile

local instance subgroupFinite {G : Type*} [Group G] [Finite G] :
    Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G ↦ (H : Set G))
    SetLike.coe_injective

/-- Actual subgroups in the checked retained background. -/
abbrev ResidualFamily (N : ℕ) :=
  {H : Subgroup (Equiv.Perm (Fin (2 * N))) // ResidualSector H}

/-- The same actual residual subgroups whose canonical profile has positive
carrier support. -/
abbrev PositiveResidualFamily (N : ℕ) :=
  {H : ResidualFamily N //
    HasPositiveSupport H.1 smallRegistryMixtureEquations H.2}

/-- Forget the branch tag while keeping the literal permutation subgroup. -/
def partitionUnderlying (N : ℕ) :
    PositiveResidualFamily N ⊕ EvenCriticalSubgroups N →
      Subgroup (Equiv.Perm (Fin (2 * N)))
  | .inl H => H.1.1
  | .inr H => H.1

/-- Deterministic injection into the positive residual branch or the already
counted complete critical family.  In both branches the subgroup is unchanged. -/
def residualPartition (N : ℕ) :
    ResidualFamily N → PositiveResidualFamily N ⊕ EvenCriticalSubgroups N :=
  fun H =>
    if hpositive :
        HasPositiveSupport H.1 smallRegistryMixtureEquations H.2 then
      .inl ⟨H,hpositive⟩
    else
      .inr ⟨H.1,
        (checked_hasPositiveSupport_or_isEvenCritical H.1 H.2).resolve_left
          hpositive⟩

@[simp] theorem partitionUnderlying_residualPartition (N : ℕ)
    (H : ResidualFamily N) :
    partitionUnderlying N (residualPartition N H) = H.1 := by
  unfold residualPartition
  split <;> rfl

/-- The partition is injective because either output retains the original
literal subgroup. -/
theorem residualPartition_injective (N : ℕ) :
    Function.Injective (residualPartition N) := by
  intro H K h
  apply Subtype.ext
  calc
    H.1 = partitionUnderlying N (residualPartition N H) :=
      (partitionUnderlying_residualPartition N H).symm
    _ = partitionUnderlying N (residualPartition N K) :=
      congrArg (partitionUnderlying N) h
    _ = K.1 := partitionUnderlying_residualPartition N K

/-- Cardinal form of the checked S16 split.  The right summand is the
existing complete critical owner, and the positive summand remains an
unmarked subtype of the original residual sector. -/
theorem residualFamily_card_le_partition (N : ℕ) :
    Nat.card (ResidualFamily N) ≤
      Nat.card (PositiveResidualFamily N) +
        Nat.card (EvenCriticalSubgroups N) := by
  letI : Finite (EvenCriticalSubgroups N) := by
    rw [← criticalSubgroups_even N]
    infer_instance
  calc
    Nat.card (ResidualFamily N) ≤
        Nat.card (PositiveResidualFamily N ⊕ EvenCriticalSubgroups N) :=
      Nat.card_le_card_of_injective (residualPartition N)
        (residualPartition_injective N)
    _ = Nat.card (PositiveResidualFamily N) +
        Nat.card (EvenCriticalSubgroups N) := Nat.card_sum

end SymmetricSubgroupAsymptotics.BinaryS16ResidualPartition

end
