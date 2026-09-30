import SymmetricSubgroupAsymptotics.BinaryS16DirectResidualPartition
import SymmetricSubgroupAsymptotics.BinaryDegreeEightSixteenPhysicalEncoding

/-!
# Fixed direct-support aggregation for the S16 residual sector

The positive direct family is disintegrated over the exact old support of the
same joint profile and certified word.  The resulting counting theorem has no
profile-choice multiplicity.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.BinaryS16DirectFixedSupportClosure

open SymmetricSubgroupAsymptotics
open BinaryCarrierActualDecoratedTransport
open BinaryCarrierParameterProfiles
open BinaryDegreeEightSixteenPhysicalDecoration
open BinaryDegreeEightSixteenPhysicalEncoding
open BinaryS16DirectResidualPartition
open BinaryS16ResidualPartition

local instance subgroupFinite {G : Type} [Group G] [Finite G] :
    Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G ↦ (H : Set G))
    SetLike.coe_injective

abbrev SupportIndex (N : ℕ) := {c : Fin (N + 1) // 0 < c.1}

/-- The direct support of a positive residual subgroup. -/
def directOldSupport {N : ℕ} (H : DirectPositiveResidualFamily N) : ℕ :=
  BinaryS16JointOrbitData.oldSupport H.1.1 H.1.2

theorem directOldSupport_pos {N : ℕ}
    (H : DirectPositiveResidualFamily N) : 0 < directOldSupport H := H.2

theorem directOldSupport_le {N : ℕ}
    (H : DirectPositiveResidualFamily N) : directOldSupport H ≤ N :=
  BinaryS16JointOrbitData.oldSupport_le_halfDegree H.1.1 H.1.2

def supportIndex {N : ℕ}
    (H : DirectPositiveResidualFamily N) : SupportIndex N :=
  ⟨⟨directOldSupport H,Nat.lt_succ_iff.mpr (directOldSupport_le H)⟩,
    directOldSupport_pos H⟩

abbrev FixedSupportFamily (N : ℕ) (C : SupportIndex N) :=
  {H : DirectPositiveResidualFamily N // supportIndex H = C}

def positiveResidualSigmaEquiv (N : ℕ) :
    DirectPositiveResidualFamily N ≃
      Σ C : SupportIndex N, FixedSupportFamily N C :=
  (Equiv.sigmaFiberEquiv (supportIndex (N := N))).symm

theorem positiveResidual_card_eq_sum (N : ℕ) :
    Nat.card (DirectPositiveResidualFamily N) =
      ∑ C : SupportIndex N, Nat.card (FixedSupportFamily N C) := by
  calc
    Nat.card (DirectPositiveResidualFamily N) =
        Nat.card (Σ C : SupportIndex N, FixedSupportFamily N C) :=
      Nat.card_congr (positiveResidualSigmaEquiv N)
    _ = ∑ C : SupportIndex N, Nat.card (FixedSupportFamily N C) :=
      Nat.card_sigma

/-- Packed `K = 10` estimate, conditional only on the fibrewise physical
reconstruction data in each genuine direct-support fibre. -/
theorem positiveResidual_card_le_packed_sum_of_keyFibre_subsingleton
    {N : ℕ} (hN : 4 ≤ N)
    (blocks : ∀ C : SupportIndex N,
      FixedSupportFamily N C → CanonicalMixedBlockTable N C.1.1)
    (target : ∀ C : SupportIndex N,
      FixedSupportFamily N C → Target N C.1.1)
    (hfibre : ∀ C d t,
      Subsingleton (KeyFibre (blocks C) (target C) d t)) :
    Nat.card (DirectPositiveResidualFamily N) ≤
      ∑ C : SupportIndex N,
        (2 * N + 2) ^ (10 * (2 * C.1.1)) *
          ∑ b : RetainedBin N C.1.1,
            Nat.card (PhysicalFamily
              (N - binSupport b.1) b.1.1.1 b.1.1.2 (Fin (2 * N))) := by
  rw [positiveResidual_card_eq_sum]
  exact Finset.sum_le_sum (fun C _ ↦
    PhysicalEncoding.card_le_bound_mul_sum_of_keyFibre_subsingleton
      (hN := hN) (blocks C) (target C) (hfibre C))

/-- Complete residual bound after adjoining the already counted critical
owner. -/
theorem residual_card_le_critical_add_packed_sum_of_keyFibre_subsingleton
    {N : ℕ} (hN : 4 ≤ N)
    (blocks : ∀ C : SupportIndex N,
      FixedSupportFamily N C → CanonicalMixedBlockTable N C.1.1)
    (target : ∀ C : SupportIndex N,
      FixedSupportFamily N C → Target N C.1.1)
    (hfibre : ∀ C d t,
      Subsingleton (KeyFibre (blocks C) (target C) d t)) :
    Nat.card (ResidualFamily N) ≤
      Nat.card (EvenCriticalSubgroups N) +
        ∑ C : SupportIndex N,
          (2 * N + 2) ^ (10 * (2 * C.1.1)) *
            ∑ b : RetainedBin N C.1.1,
              Nat.card (PhysicalFamily
                (N - binSupport b.1) b.1.1.1 b.1.1.2 (Fin (2 * N))) := by
  calc
    Nat.card (ResidualFamily N) ≤
        Nat.card (DirectPositiveResidualFamily N) +
          Nat.card (EvenCriticalSubgroups N) :=
      residualFamily_card_le_partition N
    _ ≤ (∑ C : SupportIndex N,
          (2 * N + 2) ^ (10 * (2 * C.1.1)) *
            ∑ b : RetainedBin N C.1.1,
              Nat.card (PhysicalFamily
                (N - binSupport b.1) b.1.1.1 b.1.1.2 (Fin (2 * N)))) +
          Nat.card (EvenCriticalSubgroups N) :=
      Nat.add_le_add_right
        (positiveResidual_card_le_packed_sum_of_keyFibre_subsingleton
          hN blocks target hfibre) _
    _ = Nat.card (EvenCriticalSubgroups N) +
        ∑ C : SupportIndex N,
          (2 * N + 2) ^ (10 * (2 * C.1.1)) *
            ∑ b : RetainedBin N C.1.1,
              Nat.card (PhysicalFamily
                (N - binSupport b.1) b.1.1.1 b.1.1.2 (Fin (2 * N))) :=
      Nat.add_comm _ _

end SymmetricSubgroupAsymptotics.BinaryS16DirectFixedSupportClosure

end
