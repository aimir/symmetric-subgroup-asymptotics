import SymmetricSubgroupAsymptotics.PrimitiveAffineNonsolubleSmallSource
import SymmetricSubgroupAsymptotics.ChiefAbelianSeriesTransport
import SymmetricSubgroupAsymptotics.PrimitiveStrictHeadReceipt

/-!
# The published small affine catalogue, separated from its checked receipts

Roney--Dougal and Unger, *The affine primitive permutation groups of degree
less than 1000*, J. Symbolic Comput. 35 (2003), 421--439, classify the
irreducible subgroups of `GL(d,p)` for `p^d < 1000`.  Equivalently, they
classify the primitive affine permutation groups in that range (DOI
`10.1016/S0747-7171(03)00031-2`).  The locator is pinned to the PrimGrp
`3.4.4` representatives and its documented ordering: soluble affine rows,
then insoluble affine rows, before the nonaffine O'Nan--Scott classes.

This file records exactly the slice used at degrees `8`, `16`, and `27`.
The first published input says that a literal primitive affine complement is
isomorphic to one of the classified representatives.  The exact orders,
solubility decisions, and named nonabelian cores of those representatives are
kept in the separate `SmallAffineCatalogueReceipt` so the two published
claims remain auditable independently.  Lean derives the composition
inequalities from those exact representative facts.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- The affine rows of the published primitive catalogue in the three
degrees needed by the exceptional primitive-affine consumer.  Catalogue
indices are one-based; the `Fin` coordinates below are zero-based. -/
inductive SmallAffineCatalogueRow
  | degreeEight (index : Fin 3)
  | degreeSixteen (index : Fin 20)
  | degreeTwentySeven (index : Fin 11)
  deriving DecidableEq

namespace SmallAffineCatalogueRow

def degree : SmallAffineCatalogueRow → ℕ
  | .degreeEight _ => 8
  | .degreeSixteen _ => 16
  | .degreeTwentySeven _ => 27

def catalogueIndex : SmallAffineCatalogueRow → ℕ
  | .degreeEight i => i + 1
  | .degreeSixteen i => i + 1
  | .degreeTwentySeven i => i + 1

/-- Point-stabilizer orders in the pinned Roney--Dougal/PrimGrp ordering.
These values agree with the quotient-order column already used in
`PrimitiveStrictHeadReceipt`; unlike that numerical receipt, the structure
below will bind them to literal representative groups. -/
def complementOrder : SmallAffineCatalogueRow → ℕ
  | .degreeEight i => ![7, 21, 168] i
  | .degreeSixteen i =>
      ![5, 10, 15, 18, 20, 30, 36, 36, 60, 72,
        20160, 360, 120, 180, 60, 720, 360, 120, 60, 2520] i
  | .degreeTwentySeven i =>
      ![12, 13, 24, 24, 24, 26, 39, 48, 78, 5616, 11232] i

/-- The nonsoluble rows.  This is table metadata only; a project-owned
representative certificate must prove that the selected group has the
indicated solubility status. -/
def nonsoluble : SmallAffineCatalogueRow → Bool
  | .degreeEight i => ![false, false, true] i
  | .degreeSixteen i =>
      ![false, false, false, false, false, false, false, false, false, false,
        true, true, true, true, true, true, true, true, true, true] i
  | .degreeTwentySeven i =>
      ![false, false, false, false, false, false, false, false, false,
        true, true] i

/-- Exact upper budgets for the number of abelian composition factors on
the nonsoluble rows.  Values on soluble rows are unused and set to zero.
The degree-sixteen list is sharper than the consumer needs; it records the
literal representative calculations. -/
def nonsolubleAbelianCap : SmallAffineCatalogueRow → ℕ
  | .degreeEight _ => 0
  | .degreeSixteen i =>
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 2, 1, 1, 0, 1, 0, 1, 0, 0] i
  | .degreeTwentySeven i =>
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] i

/-- Orders of the quotient by the distinguished nonabelian unique minimal
normal subgroup on a nonsoluble row.  Values on soluble rows are unused and
set to one. -/
def nonsolubleCoreQuotientOrder : SmallAffineCatalogueRow → ℕ
  | .degreeEight _ => 1
  | .degreeSixteen i =>
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        1, 6, 2, 3, 1, 2, 1, 2, 1, 1] i
  | .degreeTwentySeven i =>
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2] i

/-- The position of this affine row in the existing complete strict-head
receipt.  The offsets are the first PrimGrp rows of degrees `8`, `16`, and
`27`; the affine rows are the initial rows at each of those degrees. -/
def strictHeadIndex : SmallAffineCatalogueRow → Fin 253
  | .degreeEight i => ⟨21 + i, by omega⟩
  | .degreeSixteen i => ⟨81 + i, by omega⟩
  | .degreeTwentySeven i => ⟨189 + i, by omega⟩

/-- The small-affine table is literally a slice of the already checked
`PrimitiveStrictHeadReceipt`, rather than a second unaudited order table. -/
theorem strictHeadRow_spec (r : SmallAffineCatalogueRow) :
    (primitiveStrictHeadRow r.strictHeadIndex).degree = r.degree ∧
    (primitiveStrictHeadRow r.strictHeadIndex).catalogueIndex =
      r.catalogueIndex ∧
    (primitiveStrictHeadRow r.strictHeadIndex).quotientOrder =
      r.complementOrder := by
  rcases r with ⟨i⟩ | ⟨i⟩ | ⟨i⟩ <;>
    fin_cases i <;> decide +kernel

theorem degreeTwentySeven_order_le_of_solubleFlag
    (r : SmallAffineCatalogueRow) (hd : r.degree = 27)
    (hs : r.nonsoluble = false) :
    r.complementOrder ≤ 78 := by
  rcases r with ⟨i⟩ | ⟨i⟩ | ⟨i⟩ <;>
    fin_cases i <;> simp_all [degree, complementOrder, nonsoluble]

theorem degreeEight_cap_le
    (r : SmallAffineCatalogueRow) (hd : r.degree = 8)
    (hn : r.nonsoluble = true) :
    r.nonsolubleAbelianCap ≤ 0 := by
  rcases r with ⟨i⟩ | ⟨i⟩ | ⟨i⟩ <;>
    fin_cases i <;> simp_all [degree, nonsoluble, nonsolubleAbelianCap]

theorem degreeSixteen_cap_le
    (r : SmallAffineCatalogueRow) (hd : r.degree = 16)
    (hn : r.nonsoluble = true) :
    r.nonsolubleAbelianCap ≤ 2 := by
  rcases r with ⟨i⟩ | ⟨i⟩ | ⟨i⟩ <;>
    fin_cases i <;> simp_all [degree, nonsoluble, nonsolubleAbelianCap]

theorem degreeTwentySeven_cap_le
    (r : SmallAffineCatalogueRow) (hd : r.degree = 27)
    (hn : r.nonsoluble = true) :
    r.nonsolubleAbelianCap ≤ 1 := by
  rcases r with ⟨i⟩ | ⟨i⟩ | ⟨i⟩ <;>
    fin_cases i <;> simp_all [degree, nonsoluble, nonsolubleAbelianCap]

/-- The exact quotient orders have at most the advertised number of prime
factors, counted with multiplicity.  This is the sole numerical input needed
by the generic unique-minimal-normal theorem. -/
theorem nonsolubleCoreQuotient_cardFactors_le
    (r : SmallAffineCatalogueRow) (hn : r.nonsoluble = true) :
    ArithmeticFunction.cardFactors r.nonsolubleCoreQuotientOrder ≤
      r.nonsolubleAbelianCap := by
  rcases r with ⟨i⟩ | ⟨i⟩ | ⟨i⟩ <;>
    fin_cases i <;> decide +kernel

end SmallAffineCatalogueRow

/-- One chosen concrete representative of a published affine row. -/
structure SmallAffineCatalogueRepresentative where
  Carrier : Type
  [groupCarrier : Group Carrier]
  [finiteCarrier : Finite Carrier]

attribute [instance]
  SmallAffineCatalogueRepresentative.groupCarrier
  SmallAffineCatalogueRepresentative.finiteCarrier

/-- The explicit group-theoretic certificate behind one nonsoluble row.
It identifies a nonabelian normal subgroup contained in every nontrivial
normal subgroup and records the order of its quotient.  The generic
unique-minimal-normal theorem then bounds every chosen chief series; no
chief-series invariance is assumed in this finite receipt. -/
structure SmallAffineUniqueNonabelianCoreCertificate
    (G : Type) [Group G] [Finite G] (quotientOrder : ℕ) where
  core : Subgroup G
  [normal : core.Normal]
  ne_bot : core ≠ ⊥
  noncommutative : ¬ IsMulCommutative core
  le_every_nontrivial_normal : ∀ N : Subgroup G,
    N.Normal → N ≠ ⊥ → core ≤ N
  quotient_card_eq : Nat.card (G ⧸ core) = quotientOrder

/-- **Published Roney--Dougal--Unger catalogue locator.**

The only mathematical assertion imported from the classification is that
every literal complement in the three stated primitive-affine degrees is
isomorphic to the pinned representative of one published row.  Properties
of those representatives are not fields of this structure. -/
structure PublishedSmallAffineCatalogueLocator where
  representative :
    SmallAffineCatalogueRow → SmallAffineCatalogueRepresentative
  locate : ∀ {G Ω : Type} [Group G] [Finite G] [Fintype Ω]
    [MulAction G Ω] [FaithfulSMul G Ω],
    (_hprimitive : MulAction.IsPreprimitive G Ω) →
    (P : PrimitiveAffineProfile G Ω) →
    (x : Ω) →
    (Nat.card Ω = 8 ∨ Nat.card Ω = 16 ∨ Nat.card Ω = 27) →
      ∃ r : SmallAffineCatalogueRow,
        r.degree = Nat.card Ω ∧
          Nonempty
            (P.complement x ≃*
              (representative r).Carrier)

/-- The exact finite-group facts for one selected published representative.
This is intentionally separate from the catalogue-completeness locator.

The nonsoluble field is the concrete unique-minimal-normal certificate used
by the generic trace theorem. -/
structure SmallAffineCatalogueRepresentativeCertificate
    (L : PublishedSmallAffineCatalogueLocator)
    (r : SmallAffineCatalogueRow) where
  card_eq : Nat.card (L.representative r).Carrier = r.complementOrder
  solvable_iff :
    IsSolvable (L.representative r).Carrier ↔ r.nonsoluble = false
  nonsolubleCore : r.nonsoluble = true →
    SmallAffineUniqueNonabelianCoreCertificate
      (L.representative r).Carrier r.nonsolubleCoreQuotientOrder

/-- The complete published representative-fact receipt: 34 small affine
rows, of which thirteen nonsoluble rows carry their standard named
unique-minimal-normal subgroup. -/
abbrev SmallAffineCatalogueReceipt
    (L : PublishedSmallAffineCatalogueLocator) :=
  ∀ r : SmallAffineCatalogueRow,
    SmallAffineCatalogueRepresentativeCertificate L r

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
