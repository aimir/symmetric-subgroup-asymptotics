import SymmetricSubgroupAsymptotics.ModuleGeneratorPolynomialMatrixBlocks
import SymmetricSubgroupAsymptotics.BinaryCoordinateBasisChecks
import SymmetricSubgroupAsymptotics.LiteralPolynomialSpanWitness
import SymmetricSubgroupAsymptotics.RepresentationModuleGeneratorTransport
import SymmetricSubgroupAsymptotics.PermutationSubrepresentationHead

/-! The binary regular six-point S3 module has one cyclic two-dimensional
block and a two-by-two matrix block. The ternary norm projects onto the
first block. On its complement, c+b is a rank-two idempotent, and b
interchanges the two matrix rows. The matrix-block/PID theorem therefore
gives one generator for every actual invariant subspace. The conclusion
requires only the displayed operator identities, not a group identification. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra Polynomial

namespace SymmetricSubgroupAsymptotics.BinarySixPointSymmetricMatrixBlocks

abbrev Vector := Fin 6 → ZMod 2
def basisMask : Fin 6 → ℕ := ![21, 42, 15, 54, 60, 27]
def dualMask : Fin 6 → ℕ := ![21, 42, 27, 60, 54, 15]

def fullCoordinates : Vector ≃ₗ[ZMod 2] Vector where
  toFun := binaryMaskCoordinates 6 6 dualMask
  invFun := binaryMaskInclusion 6 6 basisMask
  left_inv x := by
    have h : (binaryMaskInclusion 6 6 basisMask).comp
        (binaryMaskCoordinates 6 6 dualMask) = LinearMap.id := by
      apply (Pi.basisFun (ZMod 2) (Fin 6)).ext
      intro i
      rw [Pi.basisFun_apply]
      funext j
      revert i j
      decide +kernel
    exact LinearMap.congr_fun h x
  right_inv x := by
    have h : (binaryMaskCoordinates 6 6 dualMask).comp
        (binaryMaskInclusion 6 6 basisMask) = LinearMap.id := by
      apply (Pi.basisFun (ZMod 2) (Fin 6)).ext
      intro i
      rw [Pi.basisFun_apply]
      funext j
      revert i j
      decide +kernel
    exact LinearMap.congr_fun h x
  map_add' := (binaryMaskCoordinates 6 6 dualMask).map_add
  map_smul' := (binaryMaskCoordinates 6 6 dualMask).map_smul

def rowCount : Fin 2 → ℕ := ![1, 2]
instance (i : Fin 2) : NeZero (rowCount i) := ⟨by fin_cases i <;> decide +kernel⟩
abbrev Fibre (_ : Fin 2) := Fin 2 → ZMod 2
abbrev Blocks := ∀ i : Fin 2, Fin (rowCount i) → Fibre i

def blockIndex : ∀ i : Fin 2, Fin (rowCount i) → Fin 2 → Fin 6 :=
  Fin.cases ![![0, 1]] (Fin.cases ![![2, 3], ![4, 5]] (fun i ↦ Fin.elim0 i))

def blockOwner : Fin 6 → Fin 2 := ![0, 0, 1, 1, 1, 1]
def blockRow (x : Fin 6) : Fin (rowCount (blockOwner x)) :=
  ⟨(![0, 0, 0, 0, 1, 1] : Fin 6 → ℕ) x, by fin_cases x <;> decide +kernel⟩
def blockPosition : Fin 6 → Fin 2 := ![0, 1, 0, 1, 0, 1]

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

def swapOperator : Module.End (ZMod 2) (Fin 2 → ZMod 2) :=
  LinearMap.pi fun i ↦
    (LinearMap.proj ((![1, 0] : Fin 2 → Fin 2) i) : (Fin 2 → ZMod 2) →ₗ[ZMod 2] ZMod 2)

def swapWitness : LiteralPolynomialSpanWitness swapOperator 1 1 where
  vectors _ m := Pi.single m 1
  step := by intro j m; funext x; revert j m x; decide +kernel
  selected i := (0, i)
  coefficient i := Pi.single i 1
  point_eq := by decide +kernel

def zeroWitness : LiteralPolynomialSpanWitness (0 : Module.End (ZMod 2) (Fin 2 → ZMod 2)) 2 0 where
  vectors j _ := Pi.single j 1
  step _ m := Fin.elim0 m
  selected i := (i, 0)
  coefficient i := Pi.single i 1
  point_eq := by decide +kernel

def fibreOperator (i : Fin 2) : Module.End (ZMod 2) (Fibre i) :=
  if i = 0 then swapOperator else 0

def fibreWitness : (i : Fin 2) →
    LiteralPolynomialSpanWitness (fibreOperator i) (rowCount i) (1 - i.val) :=
  Fin.cases swapWitness (Fin.cases zeroWitness (fun i ↦ Fin.elim0 i))

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
  let P' := Q + P
  ![E, P', P' * B * P, P * B * P', P]

def unitsScalar (c b : G) : Fin 5 → (ZMod 2)[G] :=
  let C := MonoidAlgebra.single c 1
  let B := MonoidAlgebra.single b 1
  let E := 1 + C + C ^ 2
  let Q := 1 + E
  let P := Q * (C + B)
  let P' := Q + P
  ![E, P', P' * B * P, P * B * P', P]

def matrixUnitOperator (rho : Representation (ZMod 2) G Vector) (c b : G)
    (i : Fin 2) (r s : Fin (rowCount i)) : Module.End (ZMod 2) Vector :=
  unitsOperator rho c b (unitIndex i r s)

def matrixUnitScalar (c b : G) (i : Fin 2) (r s : Fin (rowCount i)) : (ZMod 2)[G] :=
  unitsScalar c b (unitIndex i r s)

def actualOperator (rho : Representation (ZMod 2) G Vector) (b : G)
    (i : Fin 2) : Module.End (ZMod 2) Vector := if i = 0 then rho b else 0
def operatorScalar (b : G) (i : Fin 2) : (ZMod 2)[G] :=
  if i = 0 then MonoidAlgebra.single b 1 else 0

theorem matrixUnitOperator_eq (rho : Representation (ZMod 2) G Vector) (c b : G)
    (i : Fin 2) (r s : Fin (rowCount i)) :
    matrixUnitOperator rho c b i r s = rho.asAlgebraHom (matrixUnitScalar c b i r s) := by
  have h : ∀ j, unitsOperator rho c b j = rho.asAlgebraHom (unitsScalar c b j) := by
    intro j
    fin_cases j <;>
      simp only [unitsOperator, unitsScalar, Matrix.cons_val_zero', Matrix.cons_val_succ',
        map_add, map_mul, map_pow, map_one, Representation.asAlgebraHom_single, one_smul]
  exact h (unitIndex i r s)

theorem actualOperator_eq (rho : Representation (ZMod 2) G Vector) (b : G)
    (i : Fin 2) : actualOperator rho b i = rho.asAlgebraHom (operatorScalar b i) := by
  by_cases hi : i = 0 <;>
    simp [actualOperator, operatorScalar, hi, Representation.asAlgebraHom_single]

theorem uniform_of_basis (rho : Representation (ZMod 2) G Vector) (c b : G)
    (hmatrix : ∀ (i : Fin 2) (r s : Fin (rowCount i)) (q : Fin 6)
      (j : Fin 2) (t : Fin (rowCount j)) (z : Fin 2),
      coordinates (matrixUnitOperator rho c b i r s (Pi.single q 1)) j t z =
        (Pi.single i (Pi.single r (coordinates (Pi.single q 1) i s)) : Blocks) j t z)
    (hoperator : ∀ (i : Fin 2) (r : Fin (rowCount i)) (q : Fin 6) (z : Fin 2),
      coordinates (actualOperator rho b i (Pi.single q 1)) i r z =
        fibreOperator i (coordinates (Pi.single q 1) i r) z) :
    UniformSubrepresentationGeneratorBound rho 1 := by
  apply (uniformSubrepresentationGeneratorBound_iff_submodule rho 1).mpr
  intro W
  let e := rho.asModuleEquiv.trans coordinates
  refine ModuleGeneratedBy.one_of_polynomial_matrix_blocks rowCount Fibre e
    (matrixUnitScalar c b) (operatorScalar b) fibreOperator ?_ ?_
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
      apply (Pi.basisFun (ZMod 2) (Fin 6)).ext
      intro q
      rw [Pi.basisFun_apply]
      funext j t z
      exact hmatrix i r s q j t z
    exact LinearMap.congr_fun h x
  · intro i r x
    change coordinates (rho.asAlgebraHom (operatorScalar b i) x) i r =
      fibreOperator i (coordinates x i r)
    rw [← actualOperator_eq]
    have h : (LinearMap.proj r : (Fin (rowCount i) → Fibre i) →ₗ[ZMod 2] Fibre i).comp
        ((LinearMap.proj i : Blocks →ₗ[ZMod 2] (Fin (rowCount i) → Fibre i)).comp
          (coordinates.toLinearMap.comp (actualOperator rho b i))) =
        (fibreOperator i).comp
          ((LinearMap.proj r : (Fin (rowCount i) → Fibre i) →ₗ[ZMod 2] Fibre i).comp
            ((LinearMap.proj i : Blocks →ₗ[ZMod 2] (Fin (rowCount i) → Fibre i)).comp
              coordinates.toLinearMap)) := by
      apply (Pi.basisFun (ZMod 2) (Fin 6)).ext
      intro q
      rw [Pi.basisFun_apply]
      exact funext (hoperator i r q)
    exact LinearMap.congr_fun h x
  · exact fun i ↦ (fibreWitness i).polynomial_span

def rotation : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 4, 5, 0, 1]
  invFun := ![4, 5, 0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def reflection : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 3, 2, 1, 0]
  invFun := ![5, 4, 3, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def representation : Representation (ZMod 2) (Equiv.Perm (Fin 6)) Vector :=
  permutationFunctionRepresentation (ZMod 2) (Equiv.Perm (Fin 6)) (Fin 6)

private theorem matrix_checked : ∀ (i : Fin 2) (r s : Fin (rowCount i)) (q : Fin 6)
    (j : Fin 2) (t : Fin (rowCount j)) (z : Fin 2),
    coordinates (matrixUnitOperator representation rotation reflection i r s (Pi.single q 1)) j t z =
      (Pi.single i (Pi.single r (coordinates (Pi.single q 1) i s)) : Blocks) j t z := by
  intro i
  fin_cases i <;> decide +kernel

private theorem operator_checked : ∀ (i : Fin 2) (r : Fin (rowCount i)) (q : Fin 6) (z : Fin 2),
    coordinates (actualOperator representation reflection i (Pi.single q 1)) i r z =
      fibreOperator i (coordinates (Pi.single q 1) i r) z := by
  decide +kernel

theorem uniform_of_actions (rho : Representation (ZMod 2) G Vector) (c b : G)
    (hc : rho c = representation rotation) (hb : rho b = representation reflection) :
    UniformSubrepresentationGeneratorBound rho 1 := by
  apply uniform_of_basis rho c b
  · intro i r s q j t z
    have h : matrixUnitOperator rho c b i r s =
        matrixUnitOperator representation rotation reflection i r s := by
      simp only [matrixUnitOperator, unitsOperator, hc, hb]
    rw [h]
    exact matrix_checked i r s q j t z
  · intro i r q z
    have h : actualOperator rho b i = actualOperator representation reflection i := by
      simp only [actualOperator, hb]
    rw [h]
    exact operator_checked i r q z

theorem uniform_subgroup (H : Subgroup (Equiv.Perm (Fin 6))) (c b : H)
    (hc : (c : Equiv.Perm (Fin 6)) = rotation)
    (hb : (b : Equiv.Perm (Fin 6)) = reflection) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) H (Fin 6)) 1 := by
  have action_eq (g : H) (p : Equiv.Perm (Fin 6))
      (h : (g : Equiv.Perm (Fin 6)) = p) :
      permutationFunctionRepresentation (ZMod 2) H (Fin 6) g = representation p := by
    apply LinearMap.ext
    intro v
    funext x
    change v ((g : Equiv.Perm (Fin 6))⁻¹ x) = v (p⁻¹ x)
    rw [h]
  exact uniform_of_actions _ c b (action_eq c _ hc) (action_eq b _ hb)

end SymmetricSubgroupAsymptotics.BinarySixPointSymmetricMatrixBlocks

end
