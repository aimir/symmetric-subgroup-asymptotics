import SymmetricSubgroupAsymptotics.BinaryDegreeEightSixteenPhysicalDecoration

/-!
# Physical encoding for the mixed degree-eight/degree-sixteen carrier table

The mixed block table has already been packed injectively into
`DecorationCode N Cold 10`.  This file supplies the matching physical
encoding interface.  An actual source is determined jointly by its canonical
mixed table and one member of the common retained-bin target; neither
component is required to be injective by itself.

The resulting count has exactly one `K = 10` decoration factor and the
literal sum of the retained physical bins.  Thus the mixed degree-eight and
degree-sixteen application no longer passes through the degree-eight-only
`K = 6` interface.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryDegreeEightSixteenPhysicalEncoding

open SymmetricSubgroupAsymptotics
open BinaryCarrierActualDecoratedTransport
open BinaryCarrierDecorationCode
open BinaryCarrierParameterProfiles
open BinaryDegreeEightSixteenPhysicalDecoration

/-- A mixed physical source code.  The block table records only bounded
degree-eight/degree-sixteen chart and route data, while `target` is one actual
subgroup in one retained physical parameter bin. -/
structure PhysicalEncoding
    (Actual : Type*) (N Cold : ℕ) (hN : 4 ≤ N) where
  blocks : Actual → CanonicalMixedBlockTable N Cold
  target : Actual → Target N Cold
  joint_injective : Function.Injective (fun x => (blocks x,target x))

/-- The literal source fibre over one mixed table and one physical target.
All dependent orbit indices, action types, quotients, and carrier products may
be chosen separately inside this fibre. -/
abbrev KeyFibre {Actual : Type*} {N Cold : ℕ}
    (blocks : Actual → CanonicalMixedBlockTable N Cold)
    (target : Actual → Target N Cold)
    (d : CanonicalMixedBlockTable N Cold) (t : Target N Cold) :=
  {x : Actual // blocks x = d ∧ target x = t}

/-- Fibrewise uniqueness gives the global joint table/target injection.  This
is the dependent-profile aggregation step: no common coordinate index is
required across distinct keys, and the number of keys is not multiplied into
the count. -/
theorem blocks_target_injective_of_keyFibre_subsingleton
    {Actual : Type*} {N Cold : ℕ}
    (blocks : Actual → CanonicalMixedBlockTable N Cold)
    (target : Actual → Target N Cold)
    (hfibre : ∀ d t, Subsingleton (KeyFibre blocks target d t)) :
    Function.Injective (fun x => (blocks x,target x)) := by
  intro x y h
  have hblocks : blocks x = blocks y := congrArg Prod.fst h
  have htarget : target x = target y := congrArg Prod.snd h
  let X : KeyFibre blocks target (blocks x) (target x) :=
    ⟨x,rfl,rfl⟩
  let Y : KeyFibre blocks target (blocks x) (target x) :=
    ⟨y,hblocks.symm,htarget.symm⟩
  exact congrArg Subtype.val (@Subsingleton.elim _ (hfibre _ _) X Y)

/-- Conversely, a global joint injection makes every literal key fibre a
subsingleton. -/
theorem keyFibre_subsingleton_of_blocks_target_injective
    {Actual : Type*} {N Cold : ℕ}
    (blocks : Actual → CanonicalMixedBlockTable N Cold)
    (target : Actual → Target N Cold)
    (hinjective : Function.Injective (fun x => (blocks x,target x)))
    (d : CanonicalMixedBlockTable N Cold) (t : Target N Cold) :
    Subsingleton (KeyFibre blocks target d t) := by
  constructor
  intro x y
  apply Subtype.ext
  apply hinjective
  exact Prod.ext (x.2.1.trans y.2.1.symm) (x.2.2.trans y.2.2.symm)

/-- The strongest generic count supplied by fibrewise reconstruction keeps
the literal mixed-table cardinality.  It is valid in every degree; the
lower bound on `N` is needed only by the later explicit alphabet packing. -/
theorem card_le_table_mul_sum_of_keyFibre_subsingleton
    {Actual : Type*} {N Cold : ℕ} [Finite Actual]
    (blocks : Actual → CanonicalMixedBlockTable N Cold)
    (target : Actual → Target N Cold)
    (hfibre : ∀ d t, Subsingleton (KeyFibre blocks target d t)) :
    Nat.card Actual ≤
      Nat.card (CanonicalMixedBlockTable N Cold) *
        ∑ b : RetainedBin N Cold,
          Nat.card (PhysicalFamily
            (N - binSupport b.1) b.1.1.1 b.1.1.2 (Fin (2 * N))) := by
  calc
    Nat.card Actual ≤
        Nat.card (CanonicalMixedBlockTable N Cold × Target N Cold) :=
      Nat.card_le_card_of_injective (fun x => (blocks x,target x))
        (blocks_target_injective_of_keyFibre_subsingleton blocks target hfibre)
    _ = Nat.card (CanonicalMixedBlockTable N Cold) * Nat.card (Target N Cold) :=
      Nat.card_prod _ _
    _ = Nat.card (CanonicalMixedBlockTable N Cold) *
        ∑ b : RetainedBin N Cold,
          Nat.card (PhysicalFamily
            (N - binSupport b.1) b.1.1.1 b.1.1.2 (Fin (2 * N))) := by
      rw [BinaryCarrierActualDecoratedTransport.Transport.target_card_eq_sum]

/-- Package fibrewise reconstruction directly as the mixed physical
encoding. -/
def physicalEncodingOfKeyFibreSubsingleton
    {Actual : Type*} {N Cold : ℕ} {hN : 4 ≤ N}
    (blocks : Actual → CanonicalMixedBlockTable N Cold)
    (target : Actual → Target N Cold)
    (hfibre : ∀ d t, Subsingleton (KeyFibre blocks target d t)) :
    PhysicalEncoding Actual N Cold hN where
  blocks := blocks
  target := target
  joint_injective :=
    blocks_target_injective_of_keyFibre_subsingleton blocks target hfibre

namespace PhysicalEncoding

variable {Actual : Type*} {N Cold : ℕ} {hN : 4 ≤ N}
  (E : PhysicalEncoding Actual N Cold hN)

/-- Pack the canonical mixed table into the standard finite alphabet. -/
def decoration (x : Actual) : DecorationCode N Cold 10 :=
  packMixedTable hN (E.blocks x).1

/-- Packing the mixed table preserves the joint reconstruction theorem. -/
theorem decoration_target_injective :
    Function.Injective (fun x => (E.decoration x,E.target x)) := by
  intro x y h
  have hblocks : E.blocks x = E.blocks y := by
    apply canonicalMixedPack_injective hN
    exact congrArg
      (fun z : DecorationCode N Cold 10 × Target N Cold => z.1) h
  have htarget : E.target x = E.target y :=
    congrArg (fun z : DecorationCode N Cold 10 × Target N Cold => z.2) h
  apply E.joint_injective
  exact Prod.ext hblocks htarget

/-- The mixed source has one explicit `K = 10` decoration factor and the
exact retained-bin sum. -/
theorem card_le_bound_mul_sum [Finite Actual]
    (E : PhysicalEncoding Actual N Cold hN) :
    Nat.card Actual ≤
      (2 * N + 2) ^ (10 * (2 * Cold)) *
        ∑ b : RetainedBin N Cold,
          Nat.card (PhysicalFamily
            (N - binSupport b.1) b.1.1.1 b.1.1.2 (Fin (2 * N))) := by
  letI : Finite (DecorationCode N Cold 10) := inferInstance
  calc
    Nat.card Actual ≤ Nat.card (DecorationCode N Cold 10 × Target N Cold) :=
      Nat.card_le_card_of_injective
        (fun x => (E.decoration x,E.target x))
        E.decoration_target_injective
    _ = Nat.card (DecorationCode N Cold 10) * Nat.card (Target N Cold) :=
      Nat.card_prod _ _
    _ = (2 * N + 2) ^ (10 * (2 * Cold)) *
        ∑ b : RetainedBin N Cold,
          Nat.card (PhysicalFamily
            (N - binSupport b.1) b.1.1.1 b.1.1.2 (Fin (2 * N))) := by
      rw [decorationCode_card,Nat.card_sigma]

/-- Exact mixed bound from reconstruction proved separately in every
dependent table/target fibre. -/
theorem card_le_bound_mul_sum_of_keyFibre_subsingleton [Finite Actual]
    {hN : 4 ≤ N}
    (blocks : Actual → CanonicalMixedBlockTable N Cold)
    (target : Actual → Target N Cold)
    (hfibre : ∀ d t, Subsingleton (KeyFibre blocks target d t)) :
    Nat.card Actual ≤
      (2 * N + 2) ^ (10 * (2 * Cold)) *
        ∑ b : RetainedBin N Cold,
          Nat.card (PhysicalFamily
            (N - binSupport b.1) b.1.1.1 b.1.1.2 (Fin (2 * N))) :=
  card_le_bound_mul_sum
    (physicalEncodingOfKeyFibreSubsingleton
      (hN := hN) blocks target hfibre)

/-- Install the mixed code in the existing abstract transport interface. -/
def toTransport
    {Residual : Subgroup (Equiv.Perm (Fin (2 * N))) → Prop}
    (E : PhysicalEncoding (Source N Residual) N Cold hN) :
    Transport N Cold 10 Residual where
  Decoration := DecorationCode N Cold 10
  decorationFinite := inferInstance
  decoration := E.decoration
  target := E.target
  joint_injective := E.decoration_target_injective
  decoration_card_le := (decorationCode_card N Cold 10).le

end PhysicalEncoding

end SymmetricSubgroupAsymptotics.BinaryDegreeEightSixteenPhysicalEncoding
