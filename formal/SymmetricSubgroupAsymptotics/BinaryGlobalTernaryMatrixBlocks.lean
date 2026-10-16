import SymmetricSubgroupAsymptotics.ModuleGeneratorPolynomialMatrixBlocks
import SymmetricSubgroupAsymptotics.BinaryCoordinateBasisChecks
import SymmetricSubgroupAsymptotics.LiteralPolynomialSpanWitness
import SymmetricSubgroupAsymptotics.RepresentationModuleGeneratorTransport
import SymmetricSubgroupAsymptotics.PermutationSubrepresentationHead

/-! A global ternary action on twelve binary coordinates splits into a
four-dimensional cyclic block and a two-row matrix block with four-dimensional
fibres. A four-cycle generates the first fibre; two swap cycles generate the
second. The polynomial matrix-block theorem gives one generator for every
invariant subspace, from operator identities on the original point basis. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra Polynomial

namespace SymmetricSubgroupAsymptotics.BinaryGlobalTernaryMatrixBlocks

abbrev Vector := Fin 12 → ZMod 2
def basisMask : Fin 12 → ℕ := ![273, 546, 2184, 1092, 393, 2448, 34, 68, 2328, 153, 514, 1028]
def dualMask : Fin 12 → ℕ := ![273, 546, 2184, 1092, 153, 2328, 514, 1028, 2448, 393, 34, 68]

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

def rowCount : Fin 2 → ℕ := ![1, 2]
instance (i : Fin 2) : NeZero (rowCount i) := ⟨by fin_cases i <;> decide +kernel⟩
abbrev Fibre (_ : Fin 2) := Fin 4 → ZMod 2
abbrev Blocks := ∀ i : Fin 2, Fin (rowCount i) → Fibre i

def blockIndex : ∀ i : Fin 2, Fin (rowCount i) → Fin 4 → Fin 12 :=
  Fin.cases ![![0, 1, 2, 3]] (Fin.cases ![![4, 5, 6, 7], ![8, 9, 10, 11]] (fun i ↦ Fin.elim0 i))

def blockOwner : Fin 12 → Fin 2 := ![0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1]
def blockRow (x : Fin 12) : Fin (rowCount (blockOwner x)) :=
  ⟨(![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1] : Fin 12 → ℕ) x, by fin_cases x <;> decide +kernel⟩
def blockPosition : Fin 12 → Fin 4 := ![0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3]

def splitCoordinates : Vector ≃ₗ[ZMod 2] Blocks where
  toFun x i r j := x (blockIndex i r j)
  invFun x p := x (blockOwner p) (blockRow p) (blockPosition p)
  left_inv x := by
    funext p
    exact congrArg x (show blockIndex (blockOwner p) (blockRow p) (blockPosition p) = p from by
      revert p
      decide +kernel)
  right_inv x := by
    funext i r j
    fin_cases i <;> fin_cases r <;> fin_cases j <;> rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coordinates : Vector ≃ₗ[ZMod 2] Blocks := fullCoordinates.trans splitCoordinates

def cycleOperator : Module.End (ZMod 2) (Fin 4 → ZMod 2) :=
  LinearMap.pi fun i ↦
    (LinearMap.proj ((![3, 0, 1, 2] : Fin 4 → Fin 4) i) :
      (Fin 4 → ZMod 2) →ₗ[ZMod 2] ZMod 2)

def swapOperator : Module.End (ZMod 2) (Fin 4 → ZMod 2) :=
  LinearMap.pi fun i ↦
    (LinearMap.proj ((![1, 0, 3, 2] : Fin 4 → Fin 4) i) :
      (Fin 4 → ZMod 2) →ₗ[ZMod 2] ZMod 2)

def cycleWitness : LiteralPolynomialSpanWitness cycleOperator 1 3 where
  vectors _ m := Pi.single m 1
  step := by intro j m; funext x; revert j m x; decide +kernel
  selected i := (0, i)
  coefficient i := Pi.single i 1
  point_eq := by decide +kernel

def swapWitness : LiteralPolynomialSpanWitness swapOperator 2 1 where
  vectors j m := Pi.single (⟨2 * j.val + m.val, by omega⟩ : Fin 4) 1
  step := by intro j m; funext x; revert j m x; decide +kernel
  selected i := (⟨i.val / 2, by omega⟩, ⟨i.val % 2, by omega⟩)
  coefficient i := Pi.single i 1
  point_eq := by decide +kernel

def fibreOperator (i : Fin 2) : Module.End (ZMod 2) (Fibre i) :=
  if i = 0 then cycleOperator else swapOperator

def fibreHeight : Fin 2 → ℕ := ![3, 1]

def fibreWitness : (i : Fin 2) →
    LiteralPolynomialSpanWitness (fibreOperator i) (rowCount i) (fibreHeight i) :=
  Fin.cases cycleWitness (Fin.cases swapWitness (fun i ↦ Fin.elim0 i))

def unitIndex : ∀ i : Fin 2, Fin (rowCount i) → Fin (rowCount i) → Fin 5 :=
  Fin.cases ![![0]] (Fin.cases ![![1, 2], ![3, 4]] (fun i ↦ Fin.elim0 i))

variable {G : Type} [Group G]

def unitsOperator (rho : Representation (ZMod 2) G Vector) (c b : G) :
    Fin 5 → Module.End (ZMod 2) Vector :=
  let C := rho c
  let B := rho b
  let E := 1 + C + C ^ 2
  let Q := 1 + E
  let P := Q * (C + B)
  ![E, P, P * B, B * P, B * P * B]

def unitsScalar (c b : G) : Fin 5 → (ZMod 2)[G] :=
  let C := MonoidAlgebra.single c 1
  let B := MonoidAlgebra.single b 1
  let E := 1 + C + C ^ 2
  let Q := 1 + E
  let P := Q * (C + B)
  ![E, P, P * B, B * P, B * P * B]

def matrixUnitOperator (rho : Representation (ZMod 2) G Vector) (c b : G)
    (i : Fin 2) (r s : Fin (rowCount i)) : Module.End (ZMod 2) Vector :=
  unitsOperator rho c b (unitIndex i r s)

def matrixUnitScalar (c b : G) (i : Fin 2) (r s : Fin (rowCount i)) : (ZMod 2)[G] :=
  unitsScalar c b (unitIndex i r s)

def actualOperator (rho : Representation (ZMod 2) G Vector) (c b d f : G)
    (i : Fin 2) : Module.End (ZMod 2) Vector :=
  let E := 1 + rho c + rho c ^ 2
  if i = 0 then E * rho b * rho d * E else rho f

def operatorScalar (c b d f : G) (i : Fin 2) : (ZMod 2)[G] :=
  let E := 1 + MonoidAlgebra.single c 1 + MonoidAlgebra.single c 1 ^ 2
  if i = 0 then E * MonoidAlgebra.single b 1 * MonoidAlgebra.single d 1 * E
    else MonoidAlgebra.single f 1

theorem matrixUnitOperator_eq (rho : Representation (ZMod 2) G Vector) (c b : G)
    (i : Fin 2) (r s : Fin (rowCount i)) :
    matrixUnitOperator rho c b i r s = rho.asAlgebraHom (matrixUnitScalar c b i r s) := by
  have h : ∀ j, unitsOperator rho c b j = rho.asAlgebraHom (unitsScalar c b j) := by
    intro j
    fin_cases j <;>
      simp only [unitsOperator, unitsScalar, Matrix.cons_val_zero', Matrix.cons_val_succ',
        map_add, map_mul, map_pow, map_one, Representation.asAlgebraHom_single, one_smul]
  exact h (unitIndex i r s)

theorem actualOperator_eq (rho : Representation (ZMod 2) G Vector) (c b d f : G)
    (i : Fin 2) : actualOperator rho c b d f i =
      rho.asAlgebraHom (operatorScalar c b d f i) := by
  by_cases hi : i = 0 <;>
    simp [actualOperator, operatorScalar, hi, map_add, map_mul, map_pow,
      Representation.asAlgebraHom_single]

theorem uniform_of_basis (rho : Representation (ZMod 2) G Vector) (c b d f : G)
    (hmatrix : ∀ (i : Fin 2) (r s : Fin (rowCount i)) (q : Fin 12)
      (j : Fin 2) (t : Fin (rowCount j)) (z : Fin 4),
      coordinates (matrixUnitOperator rho c b i r s (Pi.single q 1)) j t z =
        (Pi.single i (Pi.single r (coordinates (Pi.single q 1) i s)) : Blocks) j t z)
    (hoperator : ∀ (i : Fin 2) (r : Fin (rowCount i)) (q : Fin 12) (z : Fin 4),
      coordinates (actualOperator rho c b d f i (Pi.single q 1)) i r z =
        fibreOperator i (coordinates (Pi.single q 1) i r) z) :
    UniformSubrepresentationGeneratorBound rho 1 := by
  apply (uniformSubrepresentationGeneratorBound_iff_submodule rho 1).mpr
  intro W
  let e := rho.asModuleEquiv.trans coordinates
  refine ModuleGeneratedBy.one_of_polynomial_matrix_blocks rowCount Fibre e
    (matrixUnitScalar c b) (operatorScalar c b d f) fibreOperator ?_ ?_
    (fun i r ↦ Module.AEval'.of (fibreOperator i) ((fibreWitness i).vectors r 0)) ?_ W
  · intro i r s x
    change coordinates (rho.asAlgebraHom (matrixUnitScalar c b i r s) x) =
      Pi.single i (Pi.single r (coordinates x i s))
    rw [← matrixUnitOperator_eq]
    have h : coordinates.toLinearMap.comp (matrixUnitOperator rho c b i r s) =
        ((LinearMap.single (ZMod 2) (fun j ↦ Fin (rowCount j) → Fibre j) i).comp
          ((LinearMap.single (ZMod 2) (fun _ : Fin (rowCount i) ↦ Fibre i) r).comp
            ((LinearMap.proj s : (Fin (rowCount i) → Fibre i) →ₗ[ZMod 2] Fibre i).comp
              (LinearMap.proj i : Blocks →ₗ[ZMod 2] (Fin (rowCount i) → Fibre i))))).comp
          coordinates.toLinearMap := by
      apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
      intro q
      rw [Pi.basisFun_apply]
      funext j t z
      exact hmatrix i r s q j t z
    exact LinearMap.congr_fun h x
  · intro i r x
    change coordinates (rho.asAlgebraHom (operatorScalar c b d f i) x) i r =
      fibreOperator i (coordinates x i r)
    rw [← actualOperator_eq]
    have h : (LinearMap.proj r : (Fin (rowCount i) → Fibre i) →ₗ[ZMod 2] Fibre i).comp
        ((LinearMap.proj i : Blocks →ₗ[ZMod 2] (Fin (rowCount i) → Fibre i)).comp
          (coordinates.toLinearMap.comp (actualOperator rho c b d f i))) =
        (fibreOperator i).comp
          ((LinearMap.proj r : (Fin (rowCount i) → Fibre i) →ₗ[ZMod 2] Fibre i).comp
            ((LinearMap.proj i : Blocks →ₗ[ZMod 2] (Fin (rowCount i) → Fibre i)).comp
              coordinates.toLinearMap)) := by
      apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
      intro q
      rw [Pi.basisFun_apply]
      exact funext (hoperator i r q)
    exact LinearMap.congr_fun h x
  · exact fun i ↦ (fibreWitness i).polynomial_span

end SymmetricSubgroupAsymptotics.BinaryGlobalTernaryMatrixBlocks

end
