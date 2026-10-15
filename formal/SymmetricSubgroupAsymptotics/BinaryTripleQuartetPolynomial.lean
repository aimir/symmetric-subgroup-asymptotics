import SymmetricSubgroupAsymptotics.ModuleGeneratorPolynomialBlocks
import SymmetricSubgroupAsymptotics.BinaryCoordinateBasisChecks
import SymmetricSubgroupAsymptotics.LiteralPolynomialSpanWitness
import SymmetricSubgroupAsymptotics.RepresentationModuleGeneratorTransport

/-! Uniform cyclicity for three quartet fibres with an even Klein base.
Two ternary operators split twelve coordinates into dimensions 6,2,2,2.
The six-dimensional block uses a block rotation plus the sum of the three
local Klein norms; the other blocks are quadratic cyclic constituents.
All four projectors and operators belong to the original acting algebra.
The blocks need not be invariant under the entire original group. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra Polynomial

namespace SymmetricSubgroupAsymptotics.BinaryTripleQuartetPolynomial

abbrev Vector := Fin 12 → ZMod 2

def basisMask : Fin 12 → ℕ :=
  ![8, 713, 2048, 2348, 128, 3218, 1638, 819, 854, 1589, 1904, 1799]

def dualMask : Fin 12 → ℕ :=
  ![877, 577, 3382, 292, 1747, 1042, 819, 1638, 1589, 854, 1799, 1904]

def fullCoordinates : Vector ≃ₗ[ZMod 2] Vector where
  toFun := binaryMaskCoordinates 12 12 dualMask
  invFun := binaryMaskInclusion 12 12 basisMask
  left_inv x := by
    have h : (binaryMaskInclusion 12 12 basisMask).comp
        (binaryMaskCoordinates 12 12 dualMask) = LinearMap.id := by
      apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
      intro i
      rw [Pi.basisFun_apply]
      funext j
      revert i j
      decide +kernel
    exact LinearMap.congr_fun h x
  right_inv x := by
    have h : (binaryMaskCoordinates 12 12 dualMask).comp
        (binaryMaskInclusion 12 12 basisMask) = LinearMap.id := by
      apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
      intro i
      rw [Pi.basisFun_apply]
      funext j
      revert i j
      decide +kernel
    exact LinearMap.congr_fun h x
  map_add' := (binaryMaskCoordinates 12 12 dualMask).map_add
  map_smul' := (binaryMaskCoordinates 12 12 dualMask).map_smul

def dimension : Fin 4 → ℕ := ![6, 2, 2, 2]
abbrev Fibre (i : Fin 4) := Fin (dimension i) → ZMod 2
abbrev Blocks := ∀ i : Fin 4, Fibre i

def blockIndex : ∀ i : Fin 4, Fin (dimension i) → Fin 12 :=
  Fin.cases ![0, 1, 2, 3, 4, 5]
    (Fin.cases ![6, 7] (Fin.cases ![8, 9] (Fin.cases ![10, 11] (fun i ↦ Fin.elim0 i))))

def blockOwner : Fin 12 → Fin 4 := ![0, 0, 0, 0, 0, 0, 1, 1, 2, 2, 3, 3]

def blockPosition (x : Fin 12) : Fin (dimension (blockOwner x)) :=
  ⟨(![0, 1, 2, 3, 4, 5, 0, 1, 0, 1, 0, 1] : Fin 12 → ℕ) x,
    by fin_cases x <;> decide +kernel⟩

def splitCoordinates : Vector ≃ₗ[ZMod 2] Blocks where
  toFun x i j := x (blockIndex i j)
  invFun x p := x (blockOwner p) (blockPosition p)
  left_inv x := by
    funext p
    exact congrArg x (show blockIndex (blockOwner p) (blockPosition p) = p from by
      revert p
      decide +kernel)
  right_inv x := by
    funext i j
    fin_cases i <;> fin_cases j <;> rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coordinates : Vector ≃ₗ[ZMod 2] Blocks := fullCoordinates.trans splitCoordinates

def sixCycleOperator : Module.End (ZMod 2) (Fin 6 → ZMod 2) :=
  LinearMap.pi fun i ↦ LinearMap.proj (![5, 0, 1, 2, 3, 4] i : Fin 6)

def quadraticOperator : Module.End (ZMod 2) (Fin 2 → ZMod 2) :=
  LinearMap.pi fun (i : Fin 2) ↦
    if i = 0 then (LinearMap.proj 1 : (Fin 2 → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    else (LinearMap.proj 0 : (Fin 2 → ZMod 2) →ₗ[ZMod 2] ZMod 2) +
      (LinearMap.proj 1 : (Fin 2 → ZMod 2) →ₗ[ZMod 2] ZMod 2)

def sixCycleWitness : LiteralPolynomialSpanWitness sixCycleOperator 1 5 where
  vectors _ m := Pi.single m 1
  step := by intro j m; funext x; revert j m x; decide +kernel
  selected i := (0, i)
  coefficient i := Pi.single i 1
  point_eq := by decide +kernel

def quadraticWitness : LiteralPolynomialSpanWitness quadraticOperator 1 1 where
  vectors _ m := Pi.single m 1
  step := by intro j m; funext x; revert j m x; decide +kernel
  selected i := (0, i)
  coefficient i := Pi.single i 1
  point_eq := by decide +kernel

def fibreOperator : ∀ i : Fin 4, Module.End (ZMod 2) (Fibre i) :=
  Fin.cases sixCycleOperator
    (Fin.cases quadraticOperator
      (Fin.cases quadraticOperator (Fin.cases quadraticOperator (fun i ↦ Fin.elim0 i))))

def fibreWitness : (i : Fin 4) →
    LiteralPolynomialSpanWitness (fibreOperator i) 1 (dimension i - 1) :=
  Fin.cases sixCycleWitness
    (Fin.cases quadraticWitness
      (Fin.cases quadraticWitness (Fin.cases quadraticWitness (fun i ↦ Fin.elim0 i))))

variable {G : Type} [Group G]

def normOperator (rho : Representation (ZMod 2) G Vector) (k a c : G) :
    Module.End (ZMod 2) Vector :=
  let L := (1 + rho k) *
    (1 + rho c * rho a * rho k * rho a ^ 2 * rho c ^ 2)
  L + rho c * L * rho c ^ 2 + rho c ^ 2 * L * rho c

def normScalar (k a c : G) : (ZMod 2)[G] :=
  let K := MonoidAlgebra.single k 1
  let A := MonoidAlgebra.single a 1
  let C := MonoidAlgebra.single c 1
  let L := (1 + K) * (1 + C * A * K * A ^ 2 * C ^ 2)
  L + C * L * C ^ 2 + C ^ 2 * L * C

def projectionOperator (rho : Representation (ZMod 2) G Vector) (a c : G)
    (i : Fin 4) : Module.End (ZMod 2) Vector :=
  let A := rho a
  let C := rho c
  let E := 1 + A + A ^ 2
  let F := 1 + C + C ^ 2
  let H := 1 + A * C + (A * C) ^ 2
  ![E, (1 + E) * F, (1 + E) * (1 + F) * H,
    (1 + E) * (1 + F) * (1 + H)] i

def projectionScalar (a c : G) (i : Fin 4) : (ZMod 2)[G] :=
  let A := MonoidAlgebra.single a 1
  let C := MonoidAlgebra.single c 1
  let E := 1 + A + A ^ 2
  let F := 1 + C + C ^ 2
  let H := 1 + A * C + (A * C) ^ 2
  ![E, (1 + E) * F, (1 + E) * (1 + F) * H,
    (1 + E) * (1 + F) * (1 + H)] i

def actualOperator (rho : Representation (ZMod 2) G Vector) (k a c : G)
    (i : Fin 4) : Module.End (ZMod 2) Vector :=
  if i = 0 then rho c + normOperator rho k a c else rho a

def operatorScalar (k a c : G) (i : Fin 4) : (ZMod 2)[G] :=
  if i = 0 then MonoidAlgebra.single c 1 + normScalar k a c else MonoidAlgebra.single a 1

theorem projectionOperator_eq (rho : Representation (ZMod 2) G Vector) (a c : G)
    (i : Fin 4) :
    projectionOperator rho a c i = rho.asAlgebraHom (projectionScalar a c i) := by
  fin_cases i <;>
    simp only [projectionOperator, projectionScalar, Matrix.cons_val_zero',
      Matrix.cons_val_succ', map_add, map_mul, map_pow, map_one,
      Representation.asAlgebraHom_single, one_smul]

theorem actualOperator_eq (rho : Representation (ZMod 2) G Vector) (k a c : G)
    (i : Fin 4) :
    actualOperator rho k a c i = rho.asAlgebraHom (operatorScalar k a c i) := by
  by_cases hi : i = 0 <;>
    simp [actualOperator, operatorScalar, hi, normOperator, normScalar,
      Representation.asAlgebraHom_single]

/-- Four actual coordinate projectors and their cyclic polynomial
operators give one generator for every original subrepresentation. -/
theorem uniform_of_basis (rho : Representation (ZMod 2) G Vector) (k a c : G)
    (hprojection : ∀ (i b : Fin 4) (q : Fin 12) (x : Fin (dimension b)),
      coordinates (projectionOperator rho a c i (Pi.single q 1)) b x =
        (Pi.single i (coordinates (Pi.single q 1) i) : Blocks) b x)
    (hoperator : ∀ (i : Fin 4) (q : Fin 12) (x : Fin (dimension i)),
      coordinates (actualOperator rho k a c i (Pi.single q 1)) i x =
        fibreOperator i (coordinates (Pi.single q 1) i) x) :
    UniformSubrepresentationGeneratorBound rho 1 := by
  apply (uniformSubrepresentationGeneratorBound_iff_submodule rho 1).mpr
  intro W
  let e := rho.asModuleEquiv.trans coordinates
  refine ModuleGeneratedBy.one_of_polynomial_blocks Fibre e
    (projectionScalar a c) (operatorScalar k a c) fibreOperator ?_ ?_
    (fun i j ↦ Module.AEval'.of (fibreOperator i) ((fibreWitness i).vectors j 0)) ?_ W
  · intro i x
    change coordinates (rho.asAlgebraHom (projectionScalar a c i) x) =
      Pi.single i (coordinates x i)
    rw [← projectionOperator_eq]
    have h : coordinates.toLinearMap.comp (projectionOperator rho a c i) =
        ((LinearMap.single (ZMod 2) Fibre i).comp
          (LinearMap.proj i : Blocks →ₗ[ZMod 2] Fibre i)).comp
          coordinates.toLinearMap := by
      apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
      intro q
      rw [Pi.basisFun_apply]
      funext b z
      exact hprojection i b q z
    exact LinearMap.congr_fun h x
  · intro i x
    change coordinates (rho.asAlgebraHom (operatorScalar k a c i) x) i =
      fibreOperator i (coordinates x i)
    rw [← actualOperator_eq]
    have h : (LinearMap.proj i : Blocks →ₗ[ZMod 2] Fibre i).comp
          (coordinates.toLinearMap.comp (actualOperator rho k a c i)) =
        (fibreOperator i).comp
          ((LinearMap.proj i : Blocks →ₗ[ZMod 2] Fibre i).comp coordinates.toLinearMap) := by
      apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
      intro q
      rw [Pi.basisFun_apply]
      exact funext (hoperator i q)
    exact LinearMap.congr_fun h x
  · exact fun i ↦ (fibreWitness i).polynomial_span

end SymmetricSubgroupAsymptotics.BinaryTripleQuartetPolynomial

end
