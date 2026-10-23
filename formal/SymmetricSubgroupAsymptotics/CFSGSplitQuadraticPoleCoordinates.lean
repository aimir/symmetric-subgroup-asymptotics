import SymmetricSubgroupAsymptotics.CFSGQuadraticHyperbolicShear
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailCoordinates
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexBundledQuadratic
import Mathlib.Algebra.BigOperators.Fin

/-! The actual split-D coordinates decompose into the first hyperbolic
pair and its literal tail. The all-characteristic quadratic shear is
transported through this linear equivalence, retaining its precise
natural-vector action and companion normalization. Root-group
membership of these shears is a separate obligation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSplitQuadraticPoleCoordinates
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexTailCoordinates
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexQuadraticForm
open CFSGQuadraticHyperbolicShear
variable (K : Type) [Field K]

def coordinates (n : ℕ) (v : Index (n + 1) → K) : K × ((Index n → K) × K) :=
  (v (Sum.inl 0), (v ∘ tailIndex n, v (Sum.inr 0)))

def fromCoordinates (n : ℕ) (x : K × ((Index n → K) × K)) : Index (n + 1) → K
  | Sum.inl i => (Fin.cons x.1 (fun j : Fin n => x.2.1 (Sum.inl j)) : Fin (n + 1) → K) i
  | Sum.inr i => (Fin.cons x.2.2 (fun j : Fin n => x.2.1 (Sum.inr j)) : Fin (n + 1) → K) i

theorem from_coordinates (n : ℕ) (v : Index (n + 1) → K) :
    fromCoordinates K n (coordinates K n v) = v := by
  funext x
  cases x with
  | inl i => exact Fin.cases rfl (fun j => rfl) i
  | inr i => exact Fin.cases rfl (fun j => rfl) i

theorem coordinates_from (n : ℕ) (x : K × ((Index n → K) × K)) :
    coordinates K n (fromCoordinates K n x) = x := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext i
      cases i <;> rfl
    · rfl

def coordinateEquiv (n : ℕ) :
    (Index (n + 1) → K) ≃ₗ[K] (K × ((Index n → K) × K)) where
  toFun := coordinates K n
  invFun := fromCoordinates K n
  left_inv := from_coordinates K n
  right_inv := coordinates_from K n
  map_add' v w := rfl
  map_smul' a v := rfl

theorem splitQ_coordinates (n : ℕ) (v : Index (n + 1) → K) :
    splitQ K v = CFSGQuadraticHyperbolicShear.norm (splitQuadraticForm K n) (coordinates K n v) := by
  rw [CFSGQuadraticHyperbolicShear.norm, splitQuadraticForm_apply]
  change (∑ i : Fin (n + 1), v (Sum.inl i) * v (Sum.inr i)) =
    v (Sum.inl 0) * v (Sum.inr 0) +
      ∑ i : Fin n, v (Sum.inl i.succ) * v (Sum.inr i.succ)
  rw [Fin.sum_univ_succ]

def poleShear (n : ℕ) (z : Index n → K) :
    (Index (n + 1) → K) ≃ₗ[K] (Index (n + 1) → K) :=
  (coordinateEquiv K n).trans
    ((transformEquiv (splitQuadraticForm K n) z).trans (coordinateEquiv K n).symm)

theorem coordinates_poleShear (n : ℕ) (z : Index n → K) (v : Index (n + 1) → K) :
    coordinates K n (poleShear K n z v) =
      transform (splitQuadraticForm K n) z (coordinates K n v) := by
  change coordinateEquiv K n ((coordinateEquiv K n).symm
    (transform (splitQuadraticForm K n) z (coordinates K n v))) = _
  exact (coordinateEquiv K n).apply_symm_apply _

theorem poleShear_preserves_splitQ (n : ℕ) (z : Index n → K) (v : Index (n + 1) → K) :
    splitQ K (poleShear K n z v) = splitQ K v := by
  rw [splitQ_coordinates K n (poleShear K n z v), coordinates_poleShear,
    transform_preserves, ← splitQ_coordinates K n v]

theorem coordinates_negative_axis (n : ℕ) :
    coordinates K n (Pi.single (Sum.inr 0) 1) = (0, (0, 1)) := by
  apply Prod.ext
  · simp [coordinates, Pi.single_apply]
  · apply Prod.ext
    · funext i
      cases i <;> simp [coordinates, tailIndex, Function.comp_apply, Pi.single_apply]
    · simp [coordinates]

theorem poleShear_normalize_companion (n : ℕ) (v : Index (n + 1) → K)
    (hy : v (Sum.inr 0) = 1) (hQ : splitQ K v = 0) :
    poleShear K n (-(v ∘ tailIndex n)) v = Pi.single (Sum.inr 0) 1 := by
  apply (coordinateEquiv K n).injective
  change coordinates K n (poleShear K n (-(v ∘ tailIndex n)) v) =
    coordinates K n (Pi.single (Sum.inr 0) 1)
  rw [coordinates_poleShear, coordinates_negative_axis]
  exact normalize_companion (splitQuadraticForm K n) (coordinates K n v)
    hy ((splitQ_coordinates K n v).symm.trans hQ)

end SymmetricSubgroupAsymptotics.CFSGSplitQuadraticPoleCoordinates
