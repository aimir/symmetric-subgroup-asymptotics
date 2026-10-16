import SymmetricSubgroupAsymptotics.ModuleGeneratorPolynomialMatrixBlocks
import SymmetricSubgroupAsymptotics.BinaryCoordinateBasisChecks
import SymmetricSubgroupAsymptotics.LiteralPolynomialSpanWitness
import SymmetricSubgroupAsymptotics.RepresentationModuleGeneratorTransport
import SymmetricSubgroupAsymptotics.PermutationSubrepresentationHead

/-! Two local ternary actions split a twelve-point binary module into a
cyclic four-dimensional block and four equivalent two-dimensional rows.
Writing Q=C+C², P=Q(C+S), and E=1+Q+D Q D⁻¹, the four transports
1,S,D,DS realize matrix units on the complement of E. The compressed
operator E S D E is cyclic on E. The existing matrix-block/PID theorem
therefore gives one generator for every original invariant subspace.
Only the displayed basis identities are required; no group or module census
and no new literature hypothesis enters the result. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra Polynomial

namespace SymmetricSubgroupAsymptotics.BinaryTwoTernaryMatrixBlocks

abbrev Vector := Fin 12 → ZMod 2
def basisMask : Fin 12 → ℕ := ![546, 273, 1092, 2184, 34, 68, 514, 1028, 2056, 17, 136, 272]
def dualMask : Fin 12 → ℕ := ![546, 273, 1092, 2184, 514, 1028, 34, 68, 136, 272, 2056, 17]

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

def rowCount : Fin 2 → ℕ := ![1, 4]
def dimension : Fin 2 → ℕ := ![4, 2]
instance (i : Fin 2) : NeZero (rowCount i) := ⟨by fin_cases i <;> decide +kernel⟩
abbrev Fibre (i : Fin 2) := Fin (dimension i) → ZMod 2
abbrev Blocks := ∀ i : Fin 2, Fin (rowCount i) → Fibre i

def blockIndex : ∀ i : Fin 2, Fin (rowCount i) → Fin (dimension i) → Fin 12 :=
  Fin.cases ![![0, 1, 2, 3]]
    (Fin.cases ![![4, 5], ![6, 7], ![8, 9], ![10, 11]] (fun i ↦ Fin.elim0 i))

def blockOwner : Fin 12 → Fin 2 := ![0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1]
def blockRow (x : Fin 12) : Fin (rowCount (blockOwner x)) :=
  ⟨(![0, 0, 0, 0, 0, 0, 1, 1, 2, 2, 3, 3] : Fin 12 → ℕ) x,
    by fin_cases x <;> decide +kernel⟩
def blockPosition (x : Fin 12) : Fin (dimension (blockOwner x)) :=
  ⟨(![0, 1, 2, 3, 0, 1, 0, 1, 0, 1, 0, 1] : Fin 12 → ℕ) x,
    by fin_cases x <;> decide +kernel⟩

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

def fourCycleOperator : Module.End (ZMod 2) (Fin 4 → ZMod 2) :=
  LinearMap.pi fun i ↦
    (LinearMap.proj ((![3, 0, 1, 2] : Fin 4 → Fin 4) i) :
      (Fin 4 → ZMod 2) →ₗ[ZMod 2] ZMod 2)

def fourCycleWitness : LiteralPolynomialSpanWitness fourCycleOperator 1 3 where
  vectors _ m := Pi.single m 1
  step := by intro j m; funext x; revert j m x; decide +kernel
  selected i := (0, i)
  coefficient i := Pi.single i 1
  point_eq := by decide +kernel

def zeroWitness : LiteralPolynomialSpanWitness
    (0 : Module.End (ZMod 2) (Fin 2 → ZMod 2)) 4 0 where
  vectors j _ := Pi.single ((![0, 1, 0, 1] : Fin 4 → Fin 2) j) 1
  step _ m := Fin.elim0 m
  selected := ![(0, 0), (1, 0)]
  coefficient i := Pi.single i 1
  point_eq := by decide +kernel

def fibreOperator : ∀ i : Fin 2, Module.End (ZMod 2) (Fibre i) :=
  Fin.cases fourCycleOperator (Fin.cases 0 (fun i ↦ Fin.elim0 i))

def fibreWitness : (i : Fin 2) →
    LiteralPolynomialSpanWitness (fibreOperator i) (rowCount i) (3 * (1 - i.val)) :=
  Fin.cases fourCycleWitness (Fin.cases zeroWitness (fun i ↦ Fin.elim0 i))

def rowChoice : ∀ i : Fin 2, Fin (rowCount i) → Fin 4 :=
  Fin.cases ![0] (Fin.cases id (fun i ↦ Fin.elim0 i))

variable {G : Type} [Group G]

def transport (d s : G) : Fin 4 → G := ![1, s, d, d * s]

def projectionOperator (rho : Representation (ZMod 2) G Vector) (c d : G) :
    Module.End (ZMod 2) Vector :=
  let Q := rho c + rho c ^ 2
  1 + Q + rho d * Q * rho (d⁻¹)

def projectionScalar (c d : G) : (ZMod 2)[G] :=
  let C := MonoidAlgebra.single c 1
  let Q := C + C ^ 2
  1 + Q + MonoidAlgebra.single d 1 * Q * MonoidAlgebra.single (d⁻¹) 1

def localOperator (rho : Representation (ZMod 2) G Vector) (c s : G) :
    Module.End (ZMod 2) Vector := (rho c + rho c ^ 2) * (rho c + rho s)

def localScalar (c s : G) : (ZMod 2)[G] :=
  let C := MonoidAlgebra.single c 1
  (C + C ^ 2) * (C + MonoidAlgebra.single s 1)

def matrixUnitOperator (rho : Representation (ZMod 2) G Vector) (c d s : G)
    (i : Fin 2) (r t : Fin (rowCount i)) : Module.End (ZMod 2) Vector :=
  if i = 0 then projectionOperator rho c d else
    rho (transport d s (rowChoice i r)) * localOperator rho c s *
      rho ((transport d s (rowChoice i t))⁻¹)

def matrixUnitScalar (c d s : G) (i : Fin 2) (r t : Fin (rowCount i)) : (ZMod 2)[G] :=
  if i = 0 then projectionScalar c d else
    MonoidAlgebra.single (transport d s (rowChoice i r)) 1 * localScalar c s *
      MonoidAlgebra.single ((transport d s (rowChoice i t))⁻¹) 1

def actualOperator (rho : Representation (ZMod 2) G Vector) (c d s : G)
    (i : Fin 2) : Module.End (ZMod 2) Vector :=
  if i = 0 then projectionOperator rho c d * rho s * rho d * projectionOperator rho c d else 0

def operatorScalar (c d s : G) (i : Fin 2) : (ZMod 2)[G] :=
  if i = 0 then projectionScalar c d * MonoidAlgebra.single s 1 *
    MonoidAlgebra.single d 1 * projectionScalar c d else 0

theorem matrixUnitOperator_eq (rho : Representation (ZMod 2) G Vector) (c d s : G)
    (i : Fin 2) (r t : Fin (rowCount i)) :
    matrixUnitOperator rho c d s i r t = rho.asAlgebraHom (matrixUnitScalar c d s i r t) := by
  by_cases hi : i = 0 <;>
    simp [matrixUnitOperator, matrixUnitScalar, hi, projectionOperator, projectionScalar,
      localOperator, localScalar, Representation.asAlgebraHom_single]

theorem actualOperator_eq (rho : Representation (ZMod 2) G Vector) (c d s : G)
    (i : Fin 2) : actualOperator rho c d s i = rho.asAlgebraHom (operatorScalar c d s i) := by
  by_cases hi : i = 0 <;>
    simp [actualOperator, operatorScalar, hi, projectionOperator, projectionScalar,
      Representation.asAlgebraHom_single]

theorem uniform_of_basis (rho : Representation (ZMod 2) G Vector) (c d s : G)
    (hmatrix : ∀ (i : Fin 2) (r t : Fin (rowCount i)) (q : Fin 12)
      (j : Fin 2) (u : Fin (rowCount j)) (z : Fin (dimension j)),
      coordinates (matrixUnitOperator rho c d s i r t (Pi.single q 1)) j u z =
        (Pi.single i (Pi.single r (coordinates (Pi.single q 1) i t)) : Blocks) j u z)
    (hoperator : ∀ (i : Fin 2) (r : Fin (rowCount i)) (q : Fin 12) (z : Fin (dimension i)),
      coordinates (actualOperator rho c d s i (Pi.single q 1)) i r z =
        fibreOperator i (coordinates (Pi.single q 1) i r) z) :
    UniformSubrepresentationGeneratorBound rho 1 := by
  apply (uniformSubrepresentationGeneratorBound_iff_submodule rho 1).mpr
  intro W
  let e := rho.asModuleEquiv.trans coordinates
  refine ModuleGeneratedBy.one_of_polynomial_matrix_blocks rowCount Fibre e
    (matrixUnitScalar c d s) (operatorScalar c d s) fibreOperator ?_ ?_
    (fun i r ↦ Module.AEval'.of (fibreOperator i) ((fibreWitness i).vectors r 0)) ?_ W
  · intro i r t x
    change coordinates (rho.asAlgebraHom (matrixUnitScalar c d s i r t) x) =
      Pi.single i (Pi.single r (coordinates x i t))
    rw [← matrixUnitOperator_eq]
    have h : coordinates.toLinearMap.comp (matrixUnitOperator rho c d s i r t) =
        ((LinearMap.single (ZMod 2) (fun j ↦ Fin (rowCount j) → Fibre j) i).comp
          ((LinearMap.single (ZMod 2) (fun _ : Fin (rowCount i) ↦ Fibre i) r).comp
            ((LinearMap.proj t : (Fin (rowCount i) → Fibre i) →ₗ[ZMod 2] Fibre i).comp
              (LinearMap.proj i : Blocks →ₗ[ZMod 2] (Fin (rowCount i) → Fibre i))))).comp
          coordinates.toLinearMap := by
      apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
      intro q
      rw [Pi.basisFun_apply]
      funext j u z
      exact hmatrix i r t q j u z
    exact LinearMap.congr_fun h x
  · intro i r x
    change coordinates (rho.asAlgebraHom (operatorScalar c d s i) x) i r =
      fibreOperator i (coordinates x i r)
    rw [← actualOperator_eq]
    have h : (LinearMap.proj r : (Fin (rowCount i) → Fibre i) →ₗ[ZMod 2] Fibre i).comp
        ((LinearMap.proj i : Blocks →ₗ[ZMod 2] (Fin (rowCount i) → Fibre i)).comp
          (coordinates.toLinearMap.comp (actualOperator rho c d s i))) =
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

end SymmetricSubgroupAsymptotics.BinaryTwoTernaryMatrixBlocks

end
