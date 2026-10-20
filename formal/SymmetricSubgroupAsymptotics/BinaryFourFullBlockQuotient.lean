import SymmetricSubgroupAsymptotics.BinaryFourNonsplitKernelGenerators
import SymmetricSubgroupAsymptotics.BinaryKleinTernaryNormalChain
import SymmetricSubgroupAsymptotics.FixedPointFreeSemidirectNormalGenerators
import Mathlib.Algebra.CharP.Two

/-! The literal quotient of the full block source by augmentation
translations. Its four-dimensional binary kernel consists of the two
block-sum coordinates and the two Klein coordinates, both carrying the
displayed ternary action. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryFourFullBlockCoordinates

open BinaryFourBlockAugmentation SemidirectProduct

abbrev DoubleLocal := Local × Local

def doubleCycle : DoubleLocal ≃ₗ[Scalar] DoubleLocal := localCycle.prodCongr localCycle

theorem doubleCycle_cube : doubleCycle ^ 3 = 1 := by
  apply LinearEquiv.ext
  intro x
  apply Prod.ext
  · exact congrArg (fun f : Local ≃ₗ[Scalar] Local => f x.1) localCycle_cube
  · exact congrArg (fun f : Local ≃ₗ[Scalar] Local => f x.2) localCycle_cube

def doubleLinear : Ternary →* (DoubleLocal ≃ₗ[Scalar] DoubleLocal) :=
  powersHom 3 doubleCycle doubleCycle_cube

abbrev FullBlockQuotient := LinearSemidirectCoprimeSocleBounds.Model doubleLinear

theorem doubleLinear_apply (z : Ternary) (x : DoubleLocal) :
    doubleLinear z x = (rotate z x.1, rotate z x.2) := by
  change (doubleCycle ^ z.toAdd.val) x =
    (((localCycle.toAddEquiv.toMultiplicative ^ z.toAdd.val)
        (Multiplicative.ofAdd x.1)).toAdd,
     ((localCycle.toAddEquiv.toMultiplicative ^ z.toAdd.val)
        (Multiplicative.ofAdd x.2)).toAdd)
  generalize z.toAdd.val = n
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [pow_succ', LinearEquiv.mul_apply, MulAut.mul_apply]
      rw [ih]
      rfl

def fullBlockQuotientMap : Ambient →* FullBlockQuotient where
  toFun g := ⟨Multiplicative.ofAdd (augmentation g.left.toAdd, g.right.left.toAdd),
    g.right.right⟩
  map_one' := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      apply Prod.ext
      · ext i; fin_cases i <;> rfl
      · rfl
    · rfl
  map_mul' g h := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      change (augmentation (g * h).left.toAdd, (g.right * h.right).left.toAdd) =
        (augmentation g.left.toAdd, g.right.left.toAdd) +
          doubleLinear g.right.right (augmentation h.left.toAdd, h.right.left.toAdd)
      rw [augmentation_mul, doubleLinear_apply]
      rfl
    · rfl

theorem fullBlockQuotientMap_surjective : Function.Surjective fullBlockQuotientMap := by
  intro g
  refine ⟨⟨Multiplicative.ofAdd ![0, 0, 0, 0, 0, 0, g.left.toAdd.1 0, g.left.toAdd.1 1],
      ⟨Multiplicative.ofAdd g.left.toAdd.2, g.right⟩⟩, ?_⟩
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    apply Prod.ext
    · ext i
      fin_cases i <;> rfl
    · rfl
  · rfl

theorem fullBlockQuotientMap_kernel (g : Ambient) :
    g ∈ fullBlockQuotientMap.ker ↔ g.right = 1 ∧ augmentation g.left.toAdd = 0 := by
  constructor
  · intro h
    have hl := congrArg (fun q : FullBlockQuotient => q.left.toAdd) h
    have hr := congrArg (fun q : FullBlockQuotient => q.right) h
    refine ⟨SemidirectProduct.ext ?_ hr, ?_⟩
    · exact Multiplicative.toAdd.injective (congrArg Prod.snd hl)
    · exact congrArg Prod.fst hl
  · rintro ⟨hr, ha⟩
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      change (augmentation g.left.toAdd, g.right.left.toAdd) = (0, 0)
      rw [hr, ha]
      rfl
    · change g.right.right = 1
      rw [hr]
      rfl

def tailToLocal : tailSpace true →ₗ[Scalar] Local where
  toFun w := ![(w : TailCoordinates) 0 + (w : TailCoordinates) 2,
    (w : TailCoordinates) 0 + (w : TailCoordinates) 1 + (w : TailCoordinates) 3]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' a x := by ext i; fin_cases i <;> simp <;> ring

theorem tailToLocal_cycle (w : tailSpace true) :
    tailToLocal (tailCycle true w) = localCycle (tailToLocal w) := by
  ext i
  fin_cases i <;> simp [tailToLocal, tailCycle, localCycle] <;> ring_nf <;>
    simp only [show (2 : Scalar) = 0 from by decide, mul_zero, add_zero]

def quotientToDouble : QuotientVector true →ₗ[Scalar] DoubleLocal :=
  tailToLocal.prodMap LinearMap.id

theorem quotientToDouble_cycle (w : QuotientVector true) :
    quotientToDouble (quotientCycle true w) = doubleCycle (quotientToDouble w) := by
  exact Prod.ext (tailToLocal_cycle w.1) rfl

def quotientToDouble_intertwiner :
    (LinearSemidirectCoprimeSocleBounds.linearRepresentation (quotientLinear true)).IntertwiningMap
      (LinearSemidirectCoprimeSocleBounds.linearRepresentation doubleLinear) where
  toLinearMap := quotientToDouble
  isIntertwining' z := by
    apply LinearMap.ext
    intro w
    change quotientToDouble ((quotientCycle true ^ z.toAdd.val) w) =
      (doubleCycle ^ z.toAdd.val) (quotientToDouble w)
    generalize z.toAdd.val = n
    induction n with
    | zero => rfl
    | succ n ih =>
        simp only [pow_succ', LinearEquiv.mul_apply]
        rw [quotientToDouble_cycle, ih]

theorem quotientToDouble_surjective : Function.Surjective quotientToDouble_intertwiner := by
  rintro ⟨a, b⟩
  refine ⟨(⟨![0, a 1, a 0, 0], by intro h; cases h⟩, b), ?_⟩
  apply Prod.ext
  · ext i
    fin_cases i <;> simp [quotientToDouble_intertwiner, quotientToDouble, tailToLocal]
  · rfl

theorem doubleRepresentation_generated : RepresentationGeneratedBy
    (LinearSemidirectCoprimeSocleBounds.linearRepresentation doubleLinear) 2 :=
  representationGeneratedBy_of_surjective _ _ quotientToDouble_intertwiner
    quotientToDouble_surjective (quotientRepresentation_generated true)

theorem doubleRepresentation_uniform : UniformSubrepresentationGeneratorBound
    (LinearSemidirectCoprimeSocleBounds.linearRepresentation doubleLinear) 2 := by
  have hcard : Nat.card Ternary = 3 := by
    rw [Nat.card_congr (Multiplicative.toAdd : Ternary ≃ ZMod 3), Nat.card_zmod]
  letI : NeZero (Nat.card Ternary : Scalar) := ⟨by rw [hcard]; decide⟩
  exact RepresentationGeneratedBy.uniform_of_invertible_order (k := Scalar) _
    doubleRepresentation_generated

theorem doubleLinear_difference_surjective (z : Ternary) (hz : z ≠ 1) :
    Function.Surjective (fun x : DoubleLocal => doubleLinear z x - x) := by
  intro x
  refine ⟨doubleLinear z x, ?_⟩
  change (doubleCycle ^ z.toAdd.val) ((doubleCycle ^ z.toAdd.val) x) -
    (doubleCycle ^ z.toAdd.val) x = x
  have hz0 : z.toAdd ≠ 0 := fun h => hz (Multiplicative.toAdd.injective h)
  generalize hzval : z.toAdd = a at hz0 ⊢
  fin_cases a
  · exact False.elim (hz0 rfl)
  · change doubleCycle (doubleCycle x) - doubleCycle x = x
    apply Prod.ext <;> ext i <;> fin_cases i <;>
      simp [doubleCycle, localCycle, sub_eq_add_neg,
        CharTwo.neg_eq] <;> ring_nf <;>
      simp [show (2 : Scalar) = 0 from by decide +kernel,
        show (3 : Scalar) = 1 from by decide +kernel]
  · change doubleCycle (doubleCycle (doubleCycle (doubleCycle x))) -
      doubleCycle (doubleCycle x) = x
    apply Prod.ext <;> ext i <;> fin_cases i <;>
      simp [doubleCycle, localCycle, sub_eq_add_neg,
        CharTwo.neg_eq] <;> ring_nf <;>
      simp [show (3 : Scalar) = 1 from by decide +kernel,
        show (4 : Scalar) = 0 from by decide +kernel,
        show (7 : Scalar) = 1 from by decide +kernel]

theorem fullBlockQuotient_normalGen_le_two (N : Subgroup FullBlockQuotient) [N.Normal] :
    MarkedC4.normalGen N ≤ 2 := by
  apply FixedPointFreeSemidirectNormalGenerators.normalGen_le doubleLinear
    doubleRepresentation_uniform ?_ doubleLinear_difference_surjective N
  intro K hK
  letI := hK
  obtain ⟨x, hx⟩ := normal_generating_singletons_of_finite_normal_total
    (fun A B _ _ => BinaryKleinTernaryNormalChain.ternary_subgroup_total A B) K hK
  exact (normalGen_le_of_fin_tuple x hx).trans (by decide)

end BinaryFourFullBlockCoordinates
end SymmetricSubgroupAsymptotics

end
