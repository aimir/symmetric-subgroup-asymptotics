import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow7OddNormalizerModule
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameGeneratedTopTable
import SymmetricSubgroupAsymptotics.BinaryPlaneOrderThreeRepresentation
import SymmetricSubgroupAsymptotics.PrimitiveAffineFrameGeneratorFormulaBasis

/-! Generated local quotient and Schreier binding for one degree-sixteen frame row. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow7InducedBinding

abbrev Source := PrimitiveAffineSixteenFrameRow7TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow7TopCertificate.group

def inStabilizer (i : Fin 192) : Prop :=
  (#[true,true,false,false,true,true,false,false,true,false,false,false,false,false,false,false,true,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] : Array (Bool))[i.val]! = true

local instance inStabilizerDecidable (i : Fin 192) : Decidable (inStabilizer i) := by
  unfold inStabilizer
  infer_instance

private theorem one_inStabilizer : inStabilizer (1 : Source).index := by
  native_decide +revert
private theorem mul_inStabilizer : ∀ x y : Source,
    inStabilizer x.index → inStabilizer y.index →
      inStabilizer (x * y).index := by
  native_decide +revert
private theorem inv_inStabilizer : ∀ x : Source,
    inStabilizer x.index → inStabilizer x⁻¹.index := by
  native_decide +revert

def sourceStabilizer : Subgroup Source where
  carrier := {x | inStabilizer x.index}
  one_mem' := one_inStabilizer
  mul_mem' := by intro x y hx hy; exact mul_inStabilizer x y hx hy
  inv_mem' := by intro x hx; exact inv_inStabilizer x hx

local instance sourceStabilizerMembership (x : Source) : Decidable (x ∈ sourceStabilizer) :=
  inStabilizerDecidable x.index

theorem sourceStabilizer_card : Nat.card sourceStabilizer = 12 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  native_decide +revert

private def localForwardRow (i : Fin 192) (q : Fin 3) : Fin 3 :=
  (#[0,1,2,1,2,0,0,1,2,0,1,2,0,1,2,2,0,1,0,1,2,0,1,2,1,2,0,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,2,0,1,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,1,2,0,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,2,0,1,0,1,2,0,1,2,1,2,0,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,2,0,1,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2] : Array (Fin 3))[3 * i.val + q.val]!
private def localInverseRow (i : Fin 192) (q : Fin 3) : Fin 3 :=
  (#[0,1,2,2,0,1,0,1,2,0,1,2,0,1,2,1,2,0,0,1,2,0,1,2,2,0,1,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,1,2,0,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,2,0,1,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,1,2,0,0,1,2,0,1,2,2,0,1,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,1,2,0,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2] : Array (Fin 3))[3 * i.val + q.val]!
private def localPermutation (i : Fin 192) : Equiv.Perm (Fin 3) where
  toFun := localForwardRow i
  invFun := localInverseRow i
  left_inv := by native_decide +revert
  right_inv := by native_decide +revert
private theorem localPermutation_one : localPermutation (1 : Source).index = 1 := by
  native_decide +revert
private theorem localPermutation_mul : ∀ x y : sourceStabilizer,
    localPermutation (x * y).1.index = localPermutation x.1.index * localPermutation y.1.index := by
  native_decide +revert

def rawLocalMap : sourceStabilizer →* Equiv.Perm (Fin 3) where
  toFun x := localPermutation x.1.index
  map_one' := localPermutation_one
  map_mul' := localPermutation_mul

abbrev LocalTarget := MonoidHom.range rawLocalMap

def sourceLocalMap : sourceStabilizer →* LocalTarget := rawLocalMap.rangeRestrict

theorem sourceLocalMap_surjective : Function.Surjective sourceLocalMap :=
  rawLocalMap.rangeRestrict_surjective

theorem localTarget_card : Nat.card LocalTarget = 3 := by
  rw [Nat.card_eq_fintype_card]
  native_decide +revert

private def representativeRows (a : Fin 16) : Fin 192 :=
  (#[0,2,3,9,10,11,12,13,28,29,30,31,33,37,39,72] : Array (Fin 192))[a.val]!

def representative (a : Fin 16) : Source := ⟨representativeRows a⟩

theorem representative_factor : ∀ x : Source,
    ∃ h : Source, h ∈ sourceStabilizer ∧ ∃ a : Fin 16, x = h * representative a := by
  native_decide +revert

private def nextRows (j : Fin 4) (a : Fin 16) : Fin 16 :=
  (#[0,3,6,4,11,10,1,13,15,12,8,2,14,5,9,7,1,0,4,8,2,12,10,13,3,15,6,14,5,7,11,9,2,4,0,9,1,6,5,14,15,3,12,13,10,11,7,8,0,5,7,10,8,1,13,2,4,9,3,15,12,6,14,11] : Array (Fin 16))[16 * j.val + a.val]!

def next (j : Fin 4) (a : Fin 16) : Fin 16 := nextRows j a

def twist (j : Fin 4) (a : Fin 16) : sourceStabilizer :=
  ⟨representative a * PrimitiveAffineSixteenFrameRow7TopCertificate.ambient j *
      (representative (next j a))⁻¹,
    by fin_cases j <;> fin_cases a <;> native_decide +revert⟩

theorem representative_mul_generator (j : Fin 4) (a : Fin 16) :
    representative a * PrimitiveAffineSixteenFrameRow7TopCertificate.ambient j =
      (twist j a : Source) * representative (next j a) := by
  simp [twist]

private def localPointMask (q : Fin 3) : ℕ :=
  (#[3,1,2] : Array ℕ)[q.val]!
private def localForwardColumns (z : LocalTarget) (i : Fin 2) : ℕ :=
  localPointMask (z.1 i.succ)
private def localInverseColumns (z : LocalTarget) (i : Fin 2) : ℕ :=
  localPointMask ((z.1)⁻¹ i.succ)
private def localBasisForwardColumns (i : Fin 2) : ℕ :=
  (#[1,2] : Array (ℕ))[i.val]!
private def localBasisInverseColumns (i : Fin 2) : ℕ :=
  (#[1,2] : Array (ℕ))[i.val]!
private def baseLocalForwardMatrix (z : LocalTarget) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  binaryMatrixOfColumnMasks 2 (localForwardColumns z)
private def baseLocalInverseMatrix (z : LocalTarget) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  binaryMatrixOfColumnMasks 2 (localInverseColumns z)
private def localBasisForwardMatrix : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  binaryMatrixOfColumnMasks 2 localBasisForwardColumns
private def localBasisInverseMatrix : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  binaryMatrixOfColumnMasks 2 localBasisInverseColumns
def localForwardMatrix (z : LocalTarget) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  (localBasisForwardMatrix * baseLocalForwardMatrix z) * localBasisInverseMatrix
def localInverseMatrix (z : LocalTarget) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  (localBasisForwardMatrix * baseLocalInverseMatrix z) * localBasisInverseMatrix
def localUnit (z : LocalTarget) : Units (Matrix (Fin 2) (Fin 2) (ZMod 2)) :=
  checkedMatrixUnit (localForwardMatrix z) (localInverseMatrix z)
    (by native_decide +revert) (by native_decide +revert)
private theorem localUnit_one : localUnit 1 = 1 := by native_decide
private theorem localUnit_mul : ∀ x y : LocalTarget,
    localUnit (x * y) = localUnit x * localUnit y := by native_decide

def localMatrixHom : LocalTarget →* Units (Matrix (Fin 2) (Fin 2) (ZMod 2)) where
  toFun := localUnit
  map_one' := localUnit_one
  map_mul' := localUnit_mul

def localRepresentation : Representation (ZMod 2) LocalTarget OrderThreeBinaryPlane :=
  matrixUnitRepresentation localMatrixHom

@[simp] theorem localRepresentation_apply (z : LocalTarget) (v : OrderThreeBinaryPlane) :
    localRepresentation z v = (localForwardMatrix z).mulVec v := rfl

theorem localMatrixHom_injective : Function.Injective localMatrixHom := by native_decide

theorem localRepresentation_injective : Function.Injective localRepresentation := by
  intro x y hxy
  apply localMatrixHom_injective
  apply Units.ext
  apply Matrix.ext
  intro i j
  have h := LinearMap.congr_fun hxy (Pi.single j 1)
  simpa [localRepresentation, matrixUnitRepresentation,
    Matrix.mulVec, Pi.single_apply] using congrFun h i

private theorem generatorFormulaBasis : ∀ (j : Fin 4)
    (a : Fin 16) (i : Fin 2) (k : Fin 32),
    PrimitiveAffineSixteenFrameRow7OddNormalizerModule.representation
        (PrimitiveAffineSixteenFrameRow7TopCertificate.ambient j)
        (Pi.single k (1 : ZMod 2) : Fin 32 → ZMod 2)
        (CoinducedLeadingCoordinates.label a i) =
      localRepresentation (sourceLocalMap (twist j a))
        (fun q ↦ (Pi.single k (1 : ZMod 2) : Fin 32 → ZMod 2)
          (CoinducedLeadingCoordinates.label (next j a) q)) i := by
  native_decide

private theorem generatorFormula : ∀ (j : Fin 4)
    (v : PrimitiveAffineSixteenFrameRow7OddNormalizerModule.ModelModule)
    (a : Fin 16) (i : Fin 2),
    PrimitiveAffineSixteenFrameRow7OddNormalizerModule.representation
        (PrimitiveAffineSixteenFrameRow7TopCertificate.ambient j) v
        (CoinducedLeadingCoordinates.label a i) =
      localRepresentation (sourceLocalMap (twist j a))
        (fun q ↦ v (CoinducedLeadingCoordinates.label (next j a) q)) i :=
  binaryInducedFrameGeneratorFormula_of_basis 16
    PrimitiveAffineSixteenFrameRow7OddNormalizerModule.representation
    localRepresentation PrimitiveAffineSixteenFrameRow7TopCertificate.ambient
    (fun j a ↦ sourceLocalMap (twist j a)) next generatorFormulaBasis

theorem representation_generator_formula (j : Fin 4)
    (v : PrimitiveAffineSixteenFrameRow7OddNormalizerModule.ModelModule)
    (a : Fin 16) (i : Fin 2) :
    PrimitiveAffineSixteenFrameRow7OddNormalizerModule.representation
        (PrimitiveAffineSixteenFrameRow7TopCertificate.ambient j) v
        (CoinducedLeadingCoordinates.label a i) =
      localRepresentation (sourceLocalMap (twist j a))
        (fun q ↦ v (CoinducedLeadingCoordinates.label (next j a) q)) i :=
  generatorFormula j v a i

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow7InducedBinding

end
