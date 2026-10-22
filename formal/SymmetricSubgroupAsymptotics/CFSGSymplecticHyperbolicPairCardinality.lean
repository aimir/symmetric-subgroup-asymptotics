import SymmetricSubgroupAsymptotics.CFSGSymplecticHyperbolicPairAction
import SymmetricSubgroupAsymptotics.CFSGSymplecticProjectiveRootLift
import SymmetricSubgroupAsymptotics.CFSGLinearFunctionalFibres

/-! Exact finite-field hyperbolic-pair count from literal affine
functional fibres. Combined with the actual stabilizer recurrence, this
counts the same elementary symplectic group without a published order
formula. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticStabilizerCoordinates
open CFSGSymplecticSerreMatrices CFSGSymplecticTransvectionGeometry
variable (K : Type) [Field K] [Finite K]

 theorem pairing_fibre_card (n : ℕ) (v : Index n → K) (hv : v ≠ 0) (a : K) :
    Nat.card {w : Index n → K // pairing n v w = a} = Nat.card K ^ (2 * n - 1) := by
  obtain ⟨x, hx⟩ := exists_pairing_ne_zero n v hv
  let w : Index n → K := (pairing n v x)⁻¹ • x
  have hw : pairingDual n v w = 1 := by
    change pairing n v ((pairing n v x)⁻¹ • x) = 1
    rw [pairing_smul_right, inv_mul_cancel₀ hx]
  have h := CFSGLinearFunctionalFibres.card_fibre (pairingDual n v) w hw a
  simpa only [Fintype.card_sum, Fintype.card_fin, ← two_mul] using h

 abbrev NonzeroVectors (n : ℕ) := {v : Index n → K // v ≠ 0}

 def hyperbolicPairsSigmaEquiv (n : ℕ) :
    HyperbolicPairs K n ≃ Σ v : NonzeroVectors K n,
      {w : Index n → K // pairing n v.val w = 1} where
  toFun p := ⟨⟨p.val.1, by
    intro hz
    have h := p.property
    rw [hz, pairing_zero_left] at h
    exact zero_ne_one h⟩, ⟨p.val.2, p.property⟩⟩
  invFun p := ⟨(p.1.val, p.2.val), p.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

 theorem nonzeroVectors_card (n : ℕ) :
    Nat.card (NonzeroVectors K n) = Nat.card K ^ (2 * n) - 1 := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  have h := Fintype.card_subtype_compl (fun v : Index n → K => v = 0)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype_eq, Fintype.card_fun,
    Fintype.card_sum, Fintype.card_fin, ← two_mul] using h

 theorem hyperbolicPairs_card (n : ℕ) :
    Nat.card (HyperbolicPairs K n) =
      (Nat.card K ^ (2 * n) - 1) * Nat.card K ^ (2 * n - 1) := by
  classical
  letI : Fintype (NonzeroVectors K n) := Fintype.ofFinite _
  have hf (v : NonzeroVectors K n) :
      Nat.card {w : Index n → K // pairing n v.val w = 1} =
        Nat.card K ^ (2 * n - 1) := pairing_fibre_card K n v.val v.property 1
  calc
    Nat.card (HyperbolicPairs K n) = Nat.card
        (Σ v : NonzeroVectors K n, {w : Index n → K // pairing n v.val w = 1}) :=
      Nat.card_congr (hyperbolicPairsSigmaEquiv K n)
    _ = ∑ v : NonzeroVectors K n, Nat.card {w : Index n → K // pairing n v.val w = 1} :=
      Nat.card_sigma
    _ = Fintype.card (NonzeroVectors K n) * Nat.card K ^ (2 * n - 1) := by
      simp only [hf, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, Nat.cast_id]
    _ = (Nat.card K ^ (2 * n) - 1) * Nat.card K ^ (2 * n - 1) := by
      rw [← Nat.card_eq_fintype_card, nonzeroVectors_card]

 theorem elementary_card_recurrence (r : ℕ) (hr : 0 < r) :
    Nat.card (elementaryRootGroup K (r + 1)) =
      ((Nat.card K ^ (2 * (r + 1)) - 1) * Nat.card K ^ (2 * (r + 1) - 1)) *
        Nat.card (elementaryRootGroup K r) := by
  rw [elementary_card_hyperbolicPair_recurrence K r hr, hyperbolicPairs_card]

end SymmetricSubgroupAsymptotics.CFSGSymplecticStabilizerCoordinates
