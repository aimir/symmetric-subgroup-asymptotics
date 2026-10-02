import SymmetricSubgroupAsymptotics.PrimitiveBoundedIndexCatalogueMatch
import Mathlib.GroupTheory.GroupAction.Primitive

/-!
# Published bounded primitive locators and checked order transport

Roney--Dougal's primitive classification, represented by the pinned PrimGrp
table, identifies a faithful primitive action and its actual one-factor
nonabelian socle by a degree/index locator.  The published input below retains
only that locator and the exact orders of the literal action and socle.

The generated Lean receipt independently stores those two orders for all 116
simple-socle rows.  Lean derives the quotient order by Lagrange's theorem and
therefore does not import the final `outerOrder` equality from the catalogue.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- The exact naturality facts suppressed by the purely numerical outer-log
profile.  In the one-factor branch the displayed semisimple subgroup is the
actual unique minimal normal subgroup and the parameter is its literal
quotient order. -/
structure ExactPrimitiveSemisimpleOuterLogProfile
    (L : Type) [Group L] (r : ℕ) where
  profile : PrimitiveSemisimpleOuterLogProfile L r
  factorCount_eq_chart : profile.factorCount = Fintype.card profile.chart.ι
  oneFactor_socle_nontrivial : profile.factorCount = 1 → profile.E ≠ ⊥
  oneFactor_socle_le : profile.factorCount = 1 →
    ∀ N : Subgroup L, N.Normal → N ≠ ⊥ → profile.E ≤ N
  oneFactor_quotientOrder : profile.factorCount = 1 →
    Nat.card (L ⧸ profile.E) = profile.outerOrder

/-- A published PrimGrp locator for one literal faithful primitive action and
its actual simple nonabelian socle.  Only isomorphism-invariant cardinalities
cross the literature boundary. -/
structure PublishedBoundedPrimitiveCatalogueLocator
    (L X : Type) [Group L] [Finite L] [Finite X]
    (E : Subgroup L) [E.Normal] where
  row : Fin 116
  degree_eq : (primitiveBoundedIndexRow row).degree = Nat.card X
  groupOrder_eq : Nat.card L = (primitiveBoundedIndexRow row).groupOrder
  socleOrder_eq : Nat.card E = (primitiveBoundedIndexRow row).socleOrder

/-- **Published bounded primitive classification input.**

Every faithful primitive action of degree `5 ≤ r < 30` whose displayed
nontrivial normal subgroup is the unique minimal normal subgroup and is a
single centerless simple factor has one of the 116 simple-socle PrimGrp
locators.  This is precisely the relevant slice of Roney--Dougal's
classification; it contains no numerical compression inequality and no
project ownership predicate. -/
def PublishedBoundedPrimitiveCatalogueClassification : Prop :=
  ∀ (L X : Type) [Group L] [Finite L] [Finite X] [MulAction L X]
    [FaithfulSMul L X] [MulAction.IsPreprimitive L X] [Nontrivial X]
    (E : Subgroup L) [E.Normal] (chart : SemisimpleNormalChart E),
    5 ≤ Nat.card X → Nat.card X < 30 → E ≠ ⊥ →
    (∀ N : Subgroup L, N.Normal → N ≠ ⊥ → E ≤ N) →
    Fintype.card chart.ι = 1 →
    Nonempty (PublishedBoundedPrimitiveCatalogueLocator L X E)

namespace PublishedBoundedPrimitiveCatalogueLocator

variable {L X : Type} [Group L] [Finite L] [Finite X]
  {E : Subgroup L} [E.Normal]
  (M : PublishedBoundedPrimitiveCatalogueLocator L X E)

include M

/-- The exact quotient order is a Lean consequence of the two published
cardinalities and the kernel-checked row factorization. -/
theorem quotientOrder_eq :
    Nat.card (L ⧸ E) = (primitiveBoundedIndexRow M.row).outerOrder := by
  have hsocle : (primitiveBoundedIndexRow M.row).socleOrder ≠ 0 := by
    rw [← M.socleOrder_eq]
    exact Nat.card_pos.ne'
  apply mul_right_cancel₀ hsocle
  calc
    Nat.card (L ⧸ E) * (primitiveBoundedIndexRow M.row).socleOrder =
        Nat.card (L ⧸ E) * Nat.card E := by rw [M.socleOrder_eq]
    _ = Nat.card L :=
      (Subgroup.card_eq_card_quotient_mul_card_subgroup E).symm
    _ = (primitiveBoundedIndexRow M.row).groupOrder := M.groupOrder_eq
    _ = (primitiveBoundedIndexRow M.row).outerOrder *
        (primitiveBoundedIndexRow M.row).socleOrder :=
      (primitiveBoundedIndexRow M.row).order_factorization

end PublishedBoundedPrimitiveCatalogueLocator

namespace ExactPrimitiveSemisimpleOuterLogProfile

variable {L X : Type} [Group L] [Finite L] [Finite X]
  {r : ℕ} (D : ExactPrimitiveSemisimpleOuterLogProfile L r)

/-- Bind an exact natural one-factor profile to the checked numerical row.
The profile contributes only the theorem that its parameter is the literal
quotient order. -/
def profileMatch
    (hone : D.profile.factorCount = 1)
    (hdegree : Nat.card X = r)
    (M : PublishedBoundedPrimitiveCatalogueLocator L X D.profile.E) :
    PrimitiveBoundedIndexCatalogueMatch D.profile where
  row := M.row
  degree_eq := M.degree_eq.trans hdegree
  outerOrder_eq := by
    rw [← D.oneFactor_quotientOrder hone]
    exact M.quotientOrder_eq.symm

end ExactPrimitiveSemisimpleOuterLogProfile

end SymmetricSubgroupAsymptotics

end
