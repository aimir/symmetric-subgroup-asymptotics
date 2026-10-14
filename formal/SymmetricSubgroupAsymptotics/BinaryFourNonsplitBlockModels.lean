import SymmetricSubgroupAsymptotics.BinaryFourFullBlockActions

/-! Literal subgroups for the two nonsplit A4 block extensions.
The quadratic coordinate constraint is part of the subgroup definition;
no complement to its translation kernel is assumed. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryFourFullBlockCoordinates

open BinaryFourBlockAugmentation SemidirectProduct

def rotate (z : Ternary) (p : Local) : Local :=
  (kleinCyclicAction z (Multiplicative.ofAdd p)).toAdd

theorem rotate_cycle (z : Ternary) (p : Local) :
    rotate z (localCycle p) = localCycle (rotate z p) := by
  revert z p
  decide +kernel

theorem augmentation_add (x y : FullCoordinates) :
    augmentation (x + y) = augmentation x + augmentation y := by
  ext i
  fin_cases i <;> rfl

theorem augmentation_mul (g h : Ambient) :
    augmentation (g * h).left.toAdd = augmentation g.left.toAdd +
      rotate g.right.right (augmentation h.left.toAdd) := by
  change augmentation (g.left.toAdd + fullComplementLinear g.right h.left.toAdd) = _
  rw [augmentation_add, fullLinear_augmentation]
  rfl

/-- A finite multiplicatively closed set containing one is already a
subgroup. This only uses powers of an individual element. -/
def finiteSubmonoidSubgroup {G : Type} [Group G] [Finite G]
    (S : Submonoid G) : Subgroup G where
  carrier := S
  one_mem' := S.one_mem
  mul_mem' := S.mul_mem
  inv_mem' := by
    intro a ha
    change a⁻¹ ∈ S
    rw [← one_mul a⁻¹, ← pow_one a, ← pow_orderOf_eq_one a,
      ← pow_sub a (orderOf_pos a)]
    exact S.pow_mem ha (orderOf a - 1)

def row10Condition (g : Ambient) : Prop :=
  augmentation g.left.toAdd = g.right.left.toAdd ∧
    g.left.toAdd 5 = quadratic g.right.left.toAdd

theorem row10Condition_one : row10Condition 1 := by
  change augmentation (0 : FullCoordinates) = (0 : Local) ∧
    (0 : Scalar) = quadratic 0
  constructor
  · ext i
    fin_cases i <;> rfl
  · rfl

theorem row10Condition_mul {g h : Ambient}
    (hg : row10Condition g) (hh : row10Condition h) : row10Condition (g * h) := by
  constructor
  · rw [augmentation_mul, hg.1, hh.1]
    rfl
  · change g.left.toAdd 5 + fullComplementLinear g.right h.left.toAdd 5 =
      quadratic (g.right.left.toAdd + rotate g.right.right h.right.left.toAdd)
    rw [fullLinear_fifth, hh.1, hg.2, hh.2, quadratic_polarize]
    rw [show quadratic (rotate g.right.right h.right.left.toAdd) =
      quadratic h.right.left.toAdd from quadratic_rotate _ _]
    simp only [rotate]
    ring

def row10Submonoid : Submonoid Ambient where
  carrier := row10Condition
  one_mem' := row10Condition_one
  mul_mem' := row10Condition_mul

def row10Subgroup : Subgroup Ambient := finiteSubmonoidSubgroup row10Submonoid

abbrev Row10Model := row10Subgroup

def row12Condition (g : Ambient) : Prop :=
  augmentation g.left.toAdd = localCycle g.right.left.toAdd

theorem row12Condition_one : row12Condition 1 := by
  change augmentation (0 : FullCoordinates) = localCycle 0
  ext i
  fin_cases i <;> rfl

theorem row12Condition_mul {g h : Ambient}
    (hg : row12Condition g) (hh : row12Condition h) : row12Condition (g * h) := by
  change augmentation (g * h).left.toAdd =
    localCycle (g.right.left.toAdd + rotate g.right.right h.right.left.toAdd)
  rw [augmentation_mul, hg, hh, rotate_cycle, localCycle.map_add]

def row12Submonoid : Submonoid Ambient where
  carrier := row12Condition
  one_mem' := row12Condition_one
  mul_mem' := row12Condition_mul

def row12Subgroup : Subgroup Ambient := finiteSubmonoidSubgroup row12Submonoid

abbrev Row12Model := row12Subgroup

def row10Projection : Row10Model →* Complement :=
  (SemidirectProduct.rightHom : Ambient →* Complement).comp row10Subgroup.subtype

def row12Projection : Row12Model →* Complement :=
  (SemidirectProduct.rightHom : Ambient →* Complement).comp row12Subgroup.subtype

theorem row10Projection_surjective : Function.Surjective row10Projection := by
  intro r
  let x : FullCoordinates :=
    ![0, 0, 0, 0, 0, quadratic r.left.toAdd, r.left.toAdd 0, r.left.toAdd 1]
  have hx : row10Condition (⟨Multiplicative.ofAdd x, r⟩ : Ambient) := by
    constructor
    · ext i
      fin_cases i <;> rfl
    · rfl
  exact ⟨⟨⟨Multiplicative.ofAdd x, r⟩, hx⟩, rfl⟩

theorem row12Projection_surjective : Function.Surjective row12Projection := by
  intro r
  let x : FullCoordinates :=
    ![0, 0, 0, 0, 0, 0, localCycle r.left.toAdd 0, localCycle r.left.toAdd 1]
  have hx : row12Condition (⟨Multiplicative.ofAdd x, r⟩ : Ambient) := by
    ext i
    fin_cases i <;> rfl
  exact ⟨⟨⟨Multiplicative.ofAdd x, r⟩, hx⟩, rfl⟩

/-- The extra scalar of the larger nonsplit extension. The quadratic
correction makes this a homomorphism on the actual constrained subgroup. -/
def row12Delta : Row12Model →* Multiplicative Scalar where
  toFun g := Multiplicative.ofAdd
    (tailSum g.val.left.toAdd + quadratic g.val.right.left.toAdd)
  map_one' := by decide +kernel
  map_mul' g h := by
    apply Multiplicative.toAdd.injective
    change tailSum (g.val.left.toAdd + fullComplementLinear g.val.right h.val.left.toAdd) +
      quadratic (g.val.right.left.toAdd + rotate g.val.right.right h.val.right.left.toAdd) =
      (tailSum g.val.left.toAdd + quadratic g.val.right.left.toAdd) +
        (tailSum h.val.left.toAdd + quadratic h.val.right.left.toAdd)
    rw [tailSum_add, tailSum_fullLinear, quadratic_polarize]
    have hrot : (kleinCyclicAction g.val.right.right
        (Multiplicative.ofAdd (augmentation h.val.left.toAdd))).toAdd =
        localCycle (rotate g.val.right.right h.val.right.left.toAdd) := by
      change rotate g.val.right.right (augmentation h.val.left.toAdd) = _
      rw [show augmentation h.val.left.toAdd = localCycle h.val.right.left.toAdd
        from h.property, rotate_cycle]
    rw [hrot, show quadratic (rotate g.val.right.right h.val.right.left.toAdd) =
      quadratic h.val.right.left.toAdd from quadratic_rotate _ _]
    simp [localCycle]
    ring_nf
    simp only [show (2 : Scalar) = 0 from by decide +kernel,
      mul_zero, zero_add, add_zero]

def row12Quotient : Row12Model →* Complement × Multiplicative Scalar :=
  row12Projection.prod row12Delta

theorem row12Quotient_surjective : Function.Surjective row12Quotient := by
  rintro ⟨r, d⟩
  let x : FullCoordinates := ![0, 0, 0, 0, 0,
    d.toAdd + quadratic r.left.toAdd,
    localCycle r.left.toAdd 0, localCycle r.left.toAdd 1]
  have hx : row12Condition (⟨Multiplicative.ofAdd x, r⟩ : Ambient) := by
    ext i
    fin_cases i <;> rfl
  refine ⟨⟨⟨Multiplicative.ofAdd x, r⟩, hx⟩, Prod.ext rfl ?_⟩
  apply Multiplicative.toAdd.injective
  change (d.toAdd + quadratic r.left.toAdd + 0 + 0 + 0) +
    quadratic r.left.toAdd = d.toAdd
  ring_nf
  simp only [show (2 : Scalar) = 0 from by decide +kernel, mul_zero, add_zero]

theorem row10Projection_kernel (g : Row10Model) :
    g ∈ row10Projection.ker ↔ g.val.right = 1 := Iff.rfl

theorem row12Projection_kernel (g : Row12Model) :
    g ∈ row12Projection.ker ↔ g.val.right = 1 := Iff.rfl

theorem row12Quotient_kernel (g : Row12Model) :
    g ∈ row12Quotient.ker ↔ g.val.right = 1 ∧ tailSum g.val.left.toAdd = 0 := by
  change (g.val.right, row12Delta g) = (1, 1) ↔ _
  rw [Prod.mk.injEq]
  constructor
  · rintro ⟨hr, hd⟩
    refine ⟨hr, ?_⟩
    have hh := congrArg Multiplicative.toAdd hd
    change tailSum g.val.left.toAdd + quadratic g.val.right.left.toAdd = 0 at hh
    simpa [hr, quadratic] using hh
  · rintro ⟨hr, hd⟩
    refine ⟨hr, ?_⟩
    apply Multiplicative.toAdd.injective
    change tailSum g.val.left.toAdd + quadratic g.val.right.left.toAdd = 0
    simp [hr, hd, quadratic]

end BinaryFourFullBlockCoordinates
end SymmetricSubgroupAsymptotics

end
