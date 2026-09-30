import SymmetricSubgroupAsymptotics.BinaryS16SupportAccounting
import SymmetricSubgroupAsymptotics.BinaryDegreeEightSixteenPhysicalEncoding

/-!
# Fixed-support aggregation for the S16 residual sector

Every positive residual subgroup has one deterministic canonical old-support
value between one and the half-degree.  This file disintegrates the unmarked
family over precisely that finite numerical index.  A mixed table/physical
target reconstruction theorem may then be proved separately in each support
fibre without charging the number of orbit profiles, action types, or carrier
presentations.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.BinaryS16FixedSupportClosure

open SymmetricSubgroupAsymptotics
open BinaryCarrierActualDecoratedTransport
open BinaryCarrierParameterProfiles
open BinaryDegreeEightSixteenPhysicalDecoration
open BinaryDegreeEightSixteenPhysicalEncoding
open BinaryS16ResidualPartition
open BinaryS16SupportAccounting

local instance subgroupFinite {G : Type*} [Group G] [Finite G] :
    Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G ↦ (H : Set G))
    SetLike.coe_injective

/-- The finite set of possible positive canonical old-support values. -/
abbrev SupportIndex (N : ℕ) := {c : Fin (N + 1) // 0 < c.1}

/-- The unique support index of a positive residual subgroup. -/
def supportIndex {N : ℕ} (H : PositiveResidualFamily N) : SupportIndex N :=
  ⟨⟨positiveResidualOldSupport H,
      Nat.lt_succ_iff.mpr (positiveResidualOldSupport_le H)⟩,
    positiveResidualOldSupport_pos H⟩

/-- The unmarked positive residual family in one deterministic support
fibre. -/
abbrev FixedSupportFamily (N : ℕ) (C : SupportIndex N) :=
  {H : PositiveResidualFamily N // supportIndex H = C}

/-- Positive residuals are exactly the sigma of their fixed-support fibres. -/
def positiveResidualSigmaEquiv (N : ℕ) :
    PositiveResidualFamily N ≃
      Σ C : SupportIndex N, FixedSupportFamily N C :=
  (Equiv.sigmaFiberEquiv (supportIndex (N := N))).symm

/-- Exact cardinal disintegration over the genuine numerical support index.
There is no orbit-profile or action-type multiplicity. -/
theorem positiveResidual_card_eq_sum (N : ℕ) :
    Nat.card (PositiveResidualFamily N) =
      ∑ C : SupportIndex N, Nat.card (FixedSupportFamily N C) := by
  calc
    Nat.card (PositiveResidualFamily N) =
        Nat.card (Σ C : SupportIndex N, FixedSupportFamily N C) :=
      Nat.card_congr (positiveResidualSigmaEquiv N)
    _ = ∑ C : SupportIndex N, Nat.card (FixedSupportFamily N C) :=
      Nat.card_sigma

/-- Fixed-index equality is the same as the pre-existing numerical
old-support equality. -/
def fixedSupportEquivAtOldSupport {N : ℕ} (C : SupportIndex N) :
    FixedSupportFamily N C ≃ PositiveResidualAtOldSupport N C.1.1 where
  toFun H := ⟨H.1,congrArg (fun c : SupportIndex N ↦ c.1.1) H.2⟩
  invFun H := by
    refine ⟨H.1,?_⟩
    apply Subtype.ext
    apply Fin.ext
    exact H.2
  left_inv H := by
    apply Subtype.ext
    rfl
  right_inv H := by
    apply Subtype.ext
    rfl

/-- The optimal generic positive-residual estimate retains the exact
mixed-table cardinality in each support fibre. -/
theorem positiveResidual_card_le_table_sum_of_keyFibre_subsingleton
    {N : ℕ}
    (blocks : ∀ C : SupportIndex N,
      FixedSupportFamily N C → CanonicalMixedBlockTable N C.1.1)
    (target : ∀ C : SupportIndex N,
      FixedSupportFamily N C → Target N C.1.1)
    (hfibre : ∀ C d t,
      Subsingleton (KeyFibre (blocks C) (target C) d t)) :
    Nat.card (PositiveResidualFamily N) ≤
      ∑ C : SupportIndex N,
        Nat.card (CanonicalMixedBlockTable N C.1.1) *
          ∑ b : RetainedBin N C.1.1,
            Nat.card (PhysicalFamily
              (N - binSupport b.1) b.1.1.1 b.1.1.2 (Fin (2 * N))) := by
  rw [positiveResidual_card_eq_sum]
  exact Finset.sum_le_sum (fun C _ ↦
    card_le_table_mul_sum_of_keyFibre_subsingleton
      (blocks C) (target C) (hfibre C))

/-- Packed `K = 10` form of the fixed-support aggregation theorem. -/
theorem positiveResidual_card_le_packed_sum_of_keyFibre_subsingleton
    {N : ℕ} (hN : 4 ≤ N)
    (blocks : ∀ C : SupportIndex N,
      FixedSupportFamily N C → CanonicalMixedBlockTable N C.1.1)
    (target : ∀ C : SupportIndex N,
      FixedSupportFamily N C → Target N C.1.1)
    (hfibre : ∀ C d t,
      Subsingleton (KeyFibre (blocks C) (target C) d t)) :
    Nat.card (PositiveResidualFamily N) ≤
      ∑ C : SupportIndex N,
        (2 * N + 2) ^ (10 * (2 * C.1.1)) *
          ∑ b : RetainedBin N C.1.1,
            Nat.card (PhysicalFamily
              (N - binSupport b.1) b.1.1.1 b.1.1.2 (Fin (2 * N))) := by
  rw [positiveResidual_card_eq_sum]
  exact Finset.sum_le_sum (fun C _ ↦
    PhysicalEncoding.card_le_bound_mul_sum_of_keyFibre_subsingleton
      (hN := hN) (blocks C) (target C) (hfibre C))

/-- Full retained-background conclusion after adjoining the already counted
complete even critical owner. -/
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
        Nat.card (PositiveResidualFamily N) +
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

end SymmetricSubgroupAsymptotics.BinaryS16FixedSupportClosure

end
