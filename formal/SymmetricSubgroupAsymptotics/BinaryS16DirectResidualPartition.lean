import SymmetricSubgroupAsymptotics.BinaryS16JointCertifiedWord
import SymmetricSubgroupAsymptotics.BinaryS16ResidualPartition

/-!
# Direct unmarked S16 residual partition

The partition is keyed by the old support of the same Type-valued joint
profile used by the certified word.  No comparison with the earlier checked
profile, and no orbit or route marking, is used.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryS16DirectResidualPartition

open SymmetricSubgroupAsymptotics
open BinaryS16CanonicalCarrierProfile
open BinaryS16ResidualPartition

local instance subgroupFinite {G : Type} [Group G] [Finite G] :
    Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G ↦ (H : Set G))
    SetLike.coe_injective

/-- The original residual subgroups whose direct joint-profile old support is
positive. -/
abbrev DirectPositiveResidualFamily (N : ℕ) :=
  {H : ResidualFamily N //
    0 < BinaryS16JointOrbitData.oldSupport H.1 H.2}

/-- The direct numerical support dichotomy. -/
theorem directPositive_or_isEvenCritical {N : ℕ}
    (H : Subgroup (Equiv.Perm (Fin (2 * N))))
    (hH : ResidualSector H) :
    0 < BinaryS16JointOrbitData.oldSupport H hH ∨
      IsEvenCriticalSubgroup N H := by
  rcases BinaryS16JointOrbitData.hasPositiveOrbit_or_isEvenCritical H hH with
    hp | hc
  · exact Or.inl
      ((BinaryS16JointOrbitData.hasPositiveOrbit_iff_oldSupport_pos H hH).mp hp)
  · exact Or.inr hc

/-- Forget the branch tag while retaining the literal permutation subgroup. -/
def partitionUnderlying (N : ℕ) :
    DirectPositiveResidualFamily N ⊕ EvenCriticalSubgroups N →
      Subgroup (Equiv.Perm (Fin (2 * N)))
  | .inl H => H.1.1
  | .inr H => H.1

/-- Deterministic direct-support partition into the physical positive branch
or the existing complete even-critical owner. -/
def residualPartition (N : ℕ) :
    ResidualFamily N → DirectPositiveResidualFamily N ⊕ EvenCriticalSubgroups N :=
  fun H =>
    if hpositive : 0 < BinaryS16JointOrbitData.oldSupport H.1 H.2 then
      .inl ⟨H,hpositive⟩
    else
      .inr ⟨H.1,(directPositive_or_isEvenCritical H.1 H.2).resolve_left
        hpositive⟩

@[simp] theorem partitionUnderlying_residualPartition (N : ℕ)
    (H : ResidualFamily N) :
    partitionUnderlying N (residualPartition N H) = H.1 := by
  unfold residualPartition
  split <;> rfl

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

/-- Cardinal form of the direct unmarked split. -/
theorem residualFamily_card_le_partition (N : ℕ) :
    Nat.card (ResidualFamily N) ≤
      Nat.card (DirectPositiveResidualFamily N) +
        Nat.card (EvenCriticalSubgroups N) := by
  letI : Finite (EvenCriticalSubgroups N) := by
    rw [← criticalSubgroups_even N]
    infer_instance
  calc
    Nat.card (ResidualFamily N) ≤
        Nat.card (DirectPositiveResidualFamily N ⊕ EvenCriticalSubgroups N) :=
      Nat.card_le_card_of_injective (residualPartition N)
        (residualPartition_injective N)
    _ = Nat.card (DirectPositiveResidualFamily N) +
        Nat.card (EvenCriticalSubgroups N) := Nat.card_sum

end SymmetricSubgroupAsymptotics.BinaryS16DirectResidualPartition

end
