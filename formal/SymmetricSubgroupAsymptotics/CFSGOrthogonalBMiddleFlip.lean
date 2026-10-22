import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOpposedGraphShear
import SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBNonzeroMiddleCommonNeighbour

/-! The literal paired-minus, middle-fixed isometry, on the original
natural space and its singular points. On the middle-one slice this is
exactly the antipode. On every zero-middle point it is projectively the
identity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBMiddleFlip
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBVectorCoordinates
open CFSGOrthogonalBOpposedGraphShear CFSGPolarSubspacePoints CFSGSingularPlaneTriangle
open CFSGOrthogonalBNonzeroMiddleCommonNeighbour
variable (K : Type) [Field K]

def vectorEquiv (n : ℕ) : (Index n → K) ≃ₗ[K] (Index n → K) where
  toFun v i := if i = middle n then v i else -v i
  invFun v i := if i = middle n then v i else -v i
  left_inv v := by
    funext i
    by_cases hi : i = middle n <;> simp [hi]
  right_inv v := by
    funext i
    by_cases hi : i = middle n <;> simp [hi]
  map_add' v w := by
    funext i
    by_cases hi : i = middle n <;> simp [hi, add_comm]
  map_smul' c v := by
    funext i
    by_cases hi : i = middle n <;> simp [hi]

@[simp] theorem vector_positive (n : ℕ) (v : Index n → K) (i : Fin n) :
    vectorEquiv K n v (pos n i) = -v (pos n i) := rfl

@[simp] theorem vector_negative (n : ℕ) (v : Index n → K) (i : Fin n) :
    vectorEquiv K n v (neg n i) = -v (neg n i) := rfl

@[simp] theorem vector_middle (n : ℕ) (v : Index n → K) :
    vectorEquiv K n v (middle n) = v (middle n) := by simp [vectorEquiv]

theorem pairing_map (n : ℕ) (v w : Index n → K) :
    (gram K n).toBilin' (vectorEquiv K n v) (vectorEquiv K n w) =
      (gram K n).toBilin' v w := by
  rw [gram_pairing_coordinates, gram_pairing_coordinates]
  simp only [positivePart, negativePart, vector_positive, vector_negative, vector_middle,
    neg_mul, mul_neg, neg_neg]

theorem eq_antipode (n : ℕ) (v : Index n → K) (hm : v (middle n) = 1) :
    vectorEquiv K n v = antipode K n v := by
  funext i
  rcases i with (i | i) | ⟨⟩
  · change -v (pos n i) = 2 * 0 - v (pos n i)
    simp only [mul_zero, zero_sub]
  · change -v (neg n i) = 2 * 0 - v (neg n i)
    simp only [mul_zero, zero_sub]
  · change v (middle n) = 2 * 1 - v (middle n)
    rw [hm]
    ring

theorem zeroOn_map_iff (n : ℕ) (P Q : Submodule K (Index n → K)) :
    ZeroOn (gram K n).toBilin' (P.map (vectorEquiv K n).toLinearMap)
      (Q.map (vectorEquiv K n).toLinearMap) ↔ ZeroOn (gram K n).toBilin' P Q := by
  constructor
  · intro h x hx y hy
    rw [← pairing_map K n x y]
    exact h _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  · rintro h x ⟨x, hx, rfl⟩ y ⟨y, hy, rfl⟩
    exact (pairing_map K n x y).trans (h x hx y hy)

def pointEquiv (n : ℕ) : Points (gram K n).toBilin' ≃ Points (gram K n).toBilin' :=
  Equiv.subtypeEquiv (Submodule.orderIsoMapComap (vectorEquiv K n)).toEquiv (fun P => by
    change (Module.finrank K P = 1 ∧ ZeroOn (gram K n).toBilin' P P) ↔
      (Module.finrank K (P.map (vectorEquiv K n).toLinearMap) = 1 ∧
        ZeroOn (gram K n).toBilin' (P.map (vectorEquiv K n).toLinearMap)
          (P.map (vectorEquiv K n).toLinearMap))
    rw [(vectorEquiv K n).finrank_map_eq, zeroOn_map_iff])

theorem image_mem (n : ℕ) (P : Points (gram K n).toBilin') (v : Index n → K)
    (hv : v ∈ P.val) : vectorEquiv K n v ∈ (pointEquiv K n P).val :=
  ⟨v, hv, rfl⟩

theorem fixes_zero_middle (n : ℕ) (P : Points (gram K n).toBilin')
    (hm : ∀ v ∈ P.val, v (middle n) = 0) : pointEquiv K n P = P := by
  obtain ⟨v, hv, hv0⟩ := point_nonzero (gram K n).toBilin' P
  have he : vectorEquiv K n v = -v := by
    funext i
    rcases i with (i | i) | ⟨⟩
    · rfl
    · rfl
    · change v (middle n) = -v (middle n)
      simp only [hm v hv, neg_zero]
  apply point_eq_of_common_nonzero (gram K n).toBilin' _ P (-v)
  · rw [← he]
    exact image_mem K n P v hv
  · exact P.val.neg_mem hv
  · exact neg_ne_zero.mpr hv0

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBMiddleFlip
