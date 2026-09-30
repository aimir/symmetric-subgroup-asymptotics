import SymmetricSubgroupAsymptotics.BinaryCarrierParameterUnion

/-!
# Actual decorated transport for binary carrier profiles

This file isolates the finite-cardinality interface needed by the eventual
physical carrier producer.  A residual subgroup is sent jointly to

* a bounded decoration, containing the reconstruction data which cannot be
  recovered from the image alone; and
* one actual subgroup in one retained physical `(a,T)` bin.

The target is deliberately a sigma type over the literal retained bins.  The
cardinality lemmas therefore preserve the per-bin sum needed by the original
weight estimates, instead of enlarging every image to the full parameter
union.  No existence or construction of the physical transport is asserted
here.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierActualDecoratedTransport

open BinaryCarrierParameterProfiles BinaryCarrierParameterUnion

local instance subgroupFinite {G : Type*} [Group G] [Finite G] :
    Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G ↦ (H : Set G)) SetLike.coe_injective

attribute [local instance] Fintype.ofFinite

/-- The literal residual subgroups on the original `2N` point set. -/
abbrev Source (N : ℕ)
    (Residual : Subgroup (Equiv.Perm (Fin (2 * N))) → Prop) :=
  {H : Subgroup (Equiv.Perm (Fin (2 * N))) // Residual H}

/-- Half of the number of points occupied by the binary carrier bin `(a,T)`.
The cyclic-four multiplicity contributes `2a` and the other carrier actions
contribute `4T` in these units. -/
def binSupport {N : ℕ}
    (b : bins N (fun _ _ ↦ True)) : ℕ :=
  2 * b.1.1 + 4 * b.1.2

theorem binSupport_pos {N : ℕ} (b : bins N (fun _ _ ↦ True)) :
    0 < binSupport b :=
  (bin_properties N (fun _ _ ↦ True) b).1

theorem binSupport_le {N : ℕ} (b : bins N (fun _ _ ↦ True)) :
    binSupport b ≤ N :=
  (bin_properties N (fun _ _ ↦ True) b).2.1

/-- Bins obeying the reversible-cell retention window.  `Cold` is the source
carrier support in half-point units and `binSupport b` is the support retained
by the target.  Thus the target never grows the carrier support and retains at
least one quarter of it. -/
abbrev RetainedBin (N Cold : ℕ) :=
  {b : bins N (fun _ _ ↦ True) //
    binSupport b ≤ Cold ∧ Cold ≤ 4 * binSupport b}

theorem retained_support_le {N Cold : ℕ} (b : RetainedBin N Cold) :
    binSupport b.1 ≤ Cold :=
  b.2.1

theorem retained_quarter {N Cold : ℕ} (b : RetainedBin N Cold) :
    Cold ≤ 4 * binSupport b.1 :=
  b.2.2

/-- The actual physical target, still separated by its retained `(a,T)` bin.
The residual critical parameter is exactly `N - (2a+4T)`, and every subgroup
lives on the original labelled point set `Fin (2N)`. -/
abbrev Target (N Cold : ℕ) :=
  Σ b : RetainedBin N Cold,
    PhysicalFamily
      (N - binSupport b.1) b.1.1.1 b.1.1.2 (Fin (2 * N))

private instance physicalFamilyFinite (R a T N : ℕ) :
    Finite (PhysicalFamily R a T (Fin (2 * N))) := by
  unfold PhysicalFamily AssembledOrbitProfilesOn
  infer_instance

private instance targetFinite (N Cold : ℕ) : Finite (Target N Cold) := by
  unfold Target
  infer_instance

/-- Abstract joint-injection certificate.  The producer must construct the
decoration and actual physical target simultaneously: neither component is
required to be injective by itself. -/
structure Transport (N Cold K : ℕ)
    (Residual : Subgroup (Equiv.Perm (Fin (2 * N))) → Prop) where
  Decoration : Type
  decorationFinite : Finite Decoration
  decoration : Source N Residual → Decoration
  target : Source N Residual → Target N Cold
  joint_injective :
    Function.Injective (fun H ↦ (decoration H, target H))
  decoration_card_le :
    Nat.card Decoration ≤ (2 * N + 2) ^ (K * (2 * Cold))

namespace Transport

variable {N Cold K : ℕ}
  {Residual : Subgroup (Equiv.Perm (Fin (2 * N))) → Prop}
  (T : Transport N Cold K Residual)

/-- On a fixed actual target subgroup, the decoration alone is injective. -/
def fiberDecoration (y : Target N Cold) :
    {H : Source N Residual // T.target H = y} → T.Decoration :=
  fun H ↦ T.decoration H.1

theorem fiberDecoration_injective (y : Target N Cold) :
    Function.Injective (T.fiberDecoration y) := by
  intro H H' hdecoration
  apply Subtype.ext
  apply T.joint_injective
  apply Prod.ext
  · exact hdecoration
  · exact H.2.trans H'.2.symm

/-- Every fibre over one literal target subgroup is bounded by the complete
decoration budget. -/
theorem target_fiber_card_le (y : Target N Cold) :
    Nat.card {H : Source N Residual // T.target H = y} ≤
      (2 * N + 2) ^ (K * (2 * Cold)) := by
  letI : Finite T.Decoration := T.decorationFinite
  exact (Nat.card_le_card_of_injective (T.fiberDecoration y)
    (T.fiberDecoration_injective y)).trans T.decoration_card_le

/-- Exact disintegration of the source into fibres over actual target
subgroups.  This form is useful when a later argument improves the uniform
decoration estimate on selected target bins. -/
theorem source_card_eq_sum_target_fibers :
    Nat.card (Source N Residual) =
      ∑ y : Target N Cold,
        Nat.card {H : Source N Residual // T.target H = y} := by
  calc
    Nat.card (Source N Residual) =
        Nat.card (Σ y : Target N Cold,
          {H : Source N Residual // T.target H = y}) :=
      (Nat.card_congr (Equiv.sigmaFiberEquiv T.target)).symm
    _ = _ := Nat.card_sigma

/-- Joint injectivity first bounds the complete source by the decoration
space times the exact physical target. -/
theorem source_card_le_decoration_mul_target :
    Nat.card (Source N Residual) ≤
      Nat.card T.Decoration * Nat.card (Target N Cold) := by
  letI : Finite T.Decoration := T.decorationFinite
  calc
    Nat.card (Source N Residual) ≤
        Nat.card (T.Decoration × Target N Cold) :=
      Nat.card_le_card_of_injective
        (fun H ↦ (T.decoration H, T.target H)) T.joint_injective
    _ = Nat.card T.Decoration * Nat.card (Target N Cold) :=
      Nat.card_prod _ _

include T in
/-- The same bound after inserting the uniform decoration estimate. -/
theorem source_card_le_bound_mul_target :
    Nat.card (Source N Residual) ≤
      (2 * N + 2) ^ (K * (2 * Cold)) * Nat.card (Target N Cold) := by
  calc
    Nat.card (Source N Residual) ≤
        Nat.card T.Decoration * Nat.card (Target N Cold) :=
      T.source_card_le_decoration_mul_target
    _ ≤ (2 * N + 2) ^ (K * (2 * Cold)) * Nat.card (Target N Cold) :=
      Nat.mul_le_mul_right (Nat.card (Target N Cold)) T.decoration_card_le

/-- The sigma target has exactly the sum of the literal physical bin
cardinalities. -/
theorem target_card_eq_sum :
    Nat.card (Target N Cold) =
      ∑ b : RetainedBin N Cold,
        Nat.card (PhysicalFamily
          (N - binSupport b.1) b.1.1.1 b.1.1.2 (Fin (2 * N))) :=
  Nat.card_sigma

include T in
/-- Final abstract transport consequence in the form consumed by a per-bin
weighted estimate.  The target has not been replaced by the full union. -/
theorem source_card_le_bound_mul_sum :
    Nat.card (Source N Residual) ≤
      (2 * N + 2) ^ (K * (2 * Cold)) *
        ∑ b : RetainedBin N Cold,
          Nat.card (PhysicalFamily
            (N - binSupport b.1) b.1.1.1 b.1.1.2 (Fin (2 * N))) := by
  calc
    Nat.card (Source N Residual) ≤
        (2 * N + 2) ^ (K * (2 * Cold)) * Nat.card (Target N Cold) :=
      T.source_card_le_bound_mul_target
    _ = _ := by rw [target_card_eq_sum]

end Transport

end SymmetricSubgroupAsymptotics.BinaryCarrierActualDecoratedTransport
