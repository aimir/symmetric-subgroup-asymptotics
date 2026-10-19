import SymmetricSubgroupAsymptotics.MarkedC4LargeOrbitOrdinaryGeneration
import Mathlib.GroupTheory.Perm.Subgroup
import Mathlib.Order.Preorder.Finite

/-! Literal containers for the soluble large-orbit reduction. An original
orbit partition is encoded by a function on the original points, and each
nonempty fibre is enlarged to a maximal soluble TRANSITIVE permutation
group. The physical container is the range of the product of those actual
fibre actions. No marked estimate or container cover is postulated.

Counting this finite family using the published maximal-transitive count
is separate from its construction here. Empty fibres cause no exception:
their unique permutation group is a maximal soluble group and transitivity
is vacuous. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.LiteralSolubleOrbitContainers

variable (X : Type) [Fintype X]

/-- Maximality is among actual soluble subgroups on these same points. -/
abbrev LocalContainer :=
  {H : Subgroup (Equiv.Perm X) // Maximal (fun K : Subgroup (Equiv.Perm X) => IsSolvable K) H ∧
    ∀ x y : X, ∃ g : H, g.val x = y}

theorem exists_local (H : Subgroup (Equiv.Perm X)) (hH : IsSolvable H)
    (htrans : ∀ x y : X, ∃ g : H, g.val x = y) :
    ∃ D : LocalContainer X, H ≤ D.val := by
  obtain ⟨M,hHM,hmax⟩ := Finite.exists_le_maximal (p := fun K : Subgroup (Equiv.Perm X) => IsSolvable K) hH
  refine ⟨⟨M,hmax,?_⟩,hHM⟩
  intro x y
  obtain ⟨g,hg⟩ := htrans x y
  exact ⟨⟨g.val,hHM g.property⟩,hg⟩

variable {X}

/-- A block is the literal fibre of an original point-label function. -/
abbrev Fiber (label : X → X) (i : X) := {x : X // label x = i}

variable (label : X → X)

def coordinateMap (D : ∀ i, LocalContainer (Fiber label i)) :
    (∀ i, (D i).val) →* ∀ i, Equiv.Perm (Fiber label i) where
  toFun a i := (a i).val
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The original point labels, rather than an abstract product action. -/
def physicalMap (D : ∀ i, LocalContainer (Fiber label i)) :
    (∀ i, (D i).val) →* Equiv.Perm X :=
  (Equiv.sigmaFiberEquiv label).permCongrHom.toMonoidHom.comp
    ((Equiv.Perm.sigmaCongrRightHom (Fiber label)).comp (coordinateMap label D))

abbrev container (D : ∀ i, LocalContainer (Fiber label i)) := (physicalMap label D).range

omit [Fintype X] in
theorem physicalMap_apply (D : ∀ i, LocalContainer (Fiber label i))
    (a : ∀ i, (D i).val) (x : X) :
    physicalMap label D a x = ((a (label x)).val ⟨x,rfl⟩).val := rfl

variable {label} (H : Subgroup (Equiv.Perm X))
  (hlabel : ∀ (g : H) (x : X), label (g.val x) = label x)

def fiberAction (i : X) : H →* Equiv.Perm (Fiber label i) where
  toFun g := {
    toFun := fun x => ⟨g.val x.val,(hlabel g x.val).trans x.property⟩
    invFun := fun x => ⟨g.val⁻¹ x.val,(hlabel g⁻¹ x.val).trans x.property⟩
    left_inv := by intro x; apply Subtype.ext; exact g.val.symm_apply_apply x.val
    right_inv := by intro x; apply Subtype.ext; exact g.val.apply_symm_apply x.val }
  map_one' := by ext x; rfl
  map_mul' _ _ := by ext x; rfl

include hlabel in
omit [Fintype X] in
theorem le_container (D : ∀ i, LocalContainer (Fiber label i))
    (hD : ∀ i, (fiberAction H hlabel i).range ≤ (D i).val) :
    H ≤ container label D := by
  intro g hg
  let a : ∀ i, (D i).val := fun i =>
    ⟨fiberAction H hlabel i ⟨g,hg⟩,hD i ⟨⟨g,hg⟩,rfl⟩⟩
  refine ⟨a,?_⟩
  ext x
  rfl

/-- One representative of each actual orbit, still an ORIGINAL point. -/
def orbitLabel : X → X := fun x =>
  (Quotient.mk'' x : MulAction.orbitRel.Quotient H X).out

omit [Fintype X] in
theorem orbitLabel_invariant (g : H) (x : X) :
    orbitLabel H (g.val x) = orbitLabel H x := by
  apply congrArg Quotient.out
  exact Quotient.sound (MulAction.mem_orbit x g)

omit [Fintype X] in
theorem orbitLabel_transitive (i : X)
    (x y : Fiber (orbitLabel H) i) :
    ∃ g : H, (fiberAction H (orbitLabel_invariant H) i g) x = y := by
  have ho : (Quotient.mk'' x.val : MulAction.orbitRel.Quotient H X) = Quotient.mk'' y.val := by
    calc
      Quotient.mk'' x.val = Quotient.mk'' (orbitLabel H x.val) :=
        (Quotient.out_eq' (Quotient.mk'' x.val)).symm
      _ = Quotient.mk'' (orbitLabel H y.val) := congrArg Quotient.mk'' (x.property.trans y.property.symm)
      _ = Quotient.mk'' y.val := Quotient.out_eq' _
  obtain ⟨g,hg⟩ := (Quotient.exact ho.symm : y.val ∈ MulAction.orbit H x.val)
  exact ⟨g,Subtype.ext hg⟩

/-- The actual soluble source lies in one of the constructed physical
containers. Every component comes from one literal orbit fibre. -/
theorem exists_container [IsSolvable H] :
    ∃ D : ∀ i, LocalContainer (Fiber (orbitLabel H) i),
      H ≤ container (orbitLabel H) D := by
  let f := fiberAction H (orbitLabel_invariant H)
  have hlocal (i : X) : ∃ D : LocalContainer (Fiber (orbitLabel H) i),
      (f i).range ≤ D.val := by
    letI : IsSolvable (f i).range :=
      solvable_of_surjective (f := (f i).rangeRestrict) (f i).rangeRestrict_surjective
    apply exists_local _ (f i).range inferInstance
    intro x y
    obtain ⟨g,hg⟩ := orbitLabel_transitive H i x y
    exact ⟨(f i).rangeRestrict g,hg⟩
  choose D hD using hlocal
  exact ⟨D,le_container H (orbitLabel_invariant H) D hD⟩

end SymmetricSubgroupAsymptotics.MarkedC4.LiteralSolubleOrbitContainers
end
