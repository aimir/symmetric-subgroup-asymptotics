import SymmetricSubgroupAsymptotics.CFSGSymplecticNaturalPairingPreservation
import Mathlib.Algebra.BigOperators.Fin

/-! Fixing an actual hyperbolic coordinate pair forces both corresponding
rows and columns to be the identity. Deleting this pair then preserves the
same alternating pairing. These are literal matrix identities, with no
classical-group recognition premise. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticStabilizerCoordinates
open CFSGSymplecticSerreMatrices CFSGSymplecticTransvectionGeometry
variable {K : Type} [Field K]

def PreservesPairing (r : ℕ) (A : Mat K r) : Prop :=
  ∀ v w : Index r → K, pairing r (A *ᵥ v) (A *ᵥ w) = pairing r v w

theorem preservesPairing_of_form (r : ℕ) (A : Mat K r)
    (hA : A ∈ Matrix.symplecticGroup (Fin r) K) : PreservesPairing r A := by
  intro v w
  have hform := _root_.SymplecticGroup.mem_iff'.mp hA
  rw [pairing_eq_neg_dot_J, pairing_eq_neg_dot_J]
  congr 1
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hform, ← Matrix.dotProduct_mulVec]

theorem fixed_basis_column (r : ℕ) (A : Mat K r) (i : Index r)
    (hi : A *ᵥ Pi.single i 1 = Pi.single i 1) (j : Index r) :
    A j i = (Pi.single i 1 : Index r → K) j := by
  have h := congrFun hi j
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using h

theorem fixed_negative_basis_row (r : ℕ) (A : Mat K r) (hA : PreservesPairing r A)
    (i : Fin r) (hi : A *ᵥ Pi.single (Sum.inr i) 1 = Pi.single (Sum.inr i) 1)
    (j : Index r) : A (Sum.inl i) j = (Pi.single j 1 : Index r → K) (Sum.inl i) := by
  have h := hA (Pi.single j 1) (Pi.single (Sum.inr i) 1)
  rw [hi, pairing_neg_basis, pairing_neg_basis] at h
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using h

theorem fixed_positive_basis_row (r : ℕ) (A : Mat K r) (hA : PreservesPairing r A)
    (i : Fin r) (hi : A *ᵥ Pi.single (Sum.inl i) 1 = Pi.single (Sum.inl i) 1)
    (j : Index r) : A (Sum.inr i) j = (Pi.single j 1 : Index r → K) (Sum.inr i) := by
  have h := hA (Pi.single j 1) (Pi.single (Sum.inl i) 1)
  rw [hi, pairing_pos_basis, pairing_pos_basis] at h
  have h' := neg_injective h
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using h'

def tailIndex (r : ℕ) : Index r → Index (r + 1) := Sum.map Fin.succ Fin.succ

def tailMatrix (r : ℕ) (A : Mat K (r + 1)) : Mat K r :=
  A.submatrix (tailIndex r) (tailIndex r)

def tailExtend (r : ℕ) (v : Index r → K) : Index (r + 1) → K :=
  Sum.elim (Fin.cases 0 (fun i => v (Sum.inl i)))
    (Fin.cases 0 (fun i => v (Sum.inr i)))

@[simp] theorem tailExtend_tail (r : ℕ) (v : Index r → K) (i : Index r) :
    tailExtend r v (tailIndex r i) = v i := by
  cases i <;> rfl

@[simp] theorem tailExtend_pos_zero (r : ℕ) (v : Index r → K) :
    tailExtend r v (Sum.inl 0) = 0 := rfl

@[simp] theorem tailExtend_neg_zero (r : ℕ) (v : Index r → K) :
    tailExtend r v (Sum.inr 0) = 0 := rfl

theorem pairing_tailExtend (r : ℕ) (v w : Index r → K) :
    pairing (r + 1) (tailExtend r v) (tailExtend r w) = pairing r v w := by
  simp [pairing, Fin.sum_univ_succ, tailExtend]

theorem pairing_eq_tail (r : ℕ) (v w : Index (r + 1) → K)
    (hv : v (Sum.inl 0) = 0) (hv' : v (Sum.inr 0) = 0) :
    pairing (r + 1) v w = pairing r (v ∘ tailIndex r) (w ∘ tailIndex r) := by
  simp [pairing, Fin.sum_univ_succ, hv, hv', tailIndex]

theorem tailMatrix_mulVec (r : ℕ) (A : Mat K (r + 1)) (v : Index r → K) :
    tailMatrix r A *ᵥ v = (A *ᵥ tailExtend r v) ∘ tailIndex r := by
  funext i
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_succ,
    tailMatrix, Matrix.submatrix_apply, tailIndex, tailExtend]

theorem tailMatrix_preserves_pairing (r : ℕ) (A : Mat K (r + 1))
    (hA : PreservesPairing (r + 1) A)
    (he : A *ᵥ Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inl 0) 1)
    (hf : A *ᵥ Pi.single (Sum.inr 0) 1 = Pi.single (Sum.inr 0) 1) :
    PreservesPairing r (tailMatrix r A) := by
  intro v w
  have hpos : (A *ᵥ tailExtend r v) (Sum.inl 0) = 0 := by
    have h := hA (tailExtend r v) (Pi.single (Sum.inr 0) 1)
    rw [hf, pairing_neg_basis, pairing_neg_basis] at h
    exact h.trans (tailExtend_pos_zero r v)
  have hneg : (A *ᵥ tailExtend r v) (Sum.inr 0) = 0 := by
    have h := hA (tailExtend r v) (Pi.single (Sum.inl 0) 1)
    rw [he, pairing_pos_basis, pairing_pos_basis] at h
    exact (neg_injective h).trans (tailExtend_neg_zero r v)
  rw [tailMatrix_mulVec, tailMatrix_mulVec, ← pairing_eq_tail r _ _ hpos hneg,
    hA, pairing_tailExtend]

end SymmetricSubgroupAsymptotics.CFSGSymplecticStabilizerCoordinates
