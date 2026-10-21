import SymmetricSubgroupAsymptotics.CFSGSymplecticCoxeter

/-! The actual ordered chain-prefix action, proved by its exact
successor recurrence. Natural-coordinate basis vectors avoid dependent
index rewrites during the induction. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

def naturalCoordinateBasis (K : Type) [Field K] (r : ℕ) (side : Bool) (j : ℕ) :
    Index (r + 1) → K := fun x => match side, x with
  | false, Sum.inl i => if i.val = j then 1 else 0
  | true, Sum.inr i => if i.val = j then 1 else 0
  | _, _ => 0

theorem naturalCoordinateBasis_val (K : Type) [Field K] (r : ℕ) (side : Bool)
    (j : Fin (r + 1)) :
    naturalCoordinateBasis K r side j.val = coordinateBasis K r side j := by
  cases side <;> funext x <;> cases x <;>
    simp [naturalCoordinateBasis, coordinateBasis, Pi.single_apply, Fin.ext_iff, eq_comm]

theorem chain_step_left (K : Type) [Field K] (r k : ℕ) (hk : k < r) (side : Bool) :
    ((simpleWeyl K (r + 1) (⟨k, hk⟩ : Fin r).castSucc).val : Mat K (r + 1)) *ᵥ
      naturalCoordinateBasis K r side k = naturalCoordinateBasis K r side (k + 1) := by
  have h := simpleWeyl_chain_basis_left K r side (⟨k, hk⟩ : Fin r)
  simpa only [← naturalCoordinateBasis_val] using h

theorem chain_step_right (K : Type) [Field K] (r k : ℕ) (hk : k < r) (side : Bool) :
    ((simpleWeyl K (r + 1) (⟨k, hk⟩ : Fin r).castSucc).val : Mat K (r + 1)) *ᵥ
      naturalCoordinateBasis K r side (k + 1) = -naturalCoordinateBasis K r side k := by
  have h := simpleWeyl_chain_basis_right K r side (⟨k, hk⟩ : Fin r)
  simpa only [← naturalCoordinateBasis_val] using h

theorem chain_step_other (K : Type) [Field K] (r k : ℕ) (hk : k < r) (side : Bool)
    (j : ℕ) (hjr : j ≤ r) (hjk : j ≠ k) (hjk' : j ≠ k + 1) :
    ((simpleWeyl K (r + 1) (⟨k, hk⟩ : Fin r).castSucc).val : Mat K (r + 1)) *ᵥ
      naturalCoordinateBasis K r side j = naturalCoordinateBasis K r side j := by
  let v : Fin (r + 1) := ⟨j, Nat.lt_succ_of_le hjr⟩
  have hne : v ≠ (⟨k, hk⟩ : Fin r).castSucc := fun h => hjk (congrArg Fin.val h)
  have hne' : v ≠ (⟨k, hk⟩ : Fin r).succ := fun h => hjk' (congrArg Fin.val h)
  have h := simpleWeyl_chain_basis_other K r side (⟨k, hk⟩ : Fin r) v hne hne'
  simpa only [← naturalCoordinateBasis_val] using h

theorem chainWeylPrefix_basis (K : Type) [Field K] (r : ℕ) :
    ∀ k : ℕ, k ≤ r → ∀ (side : Bool) (j : ℕ), j ≤ r →
    ((chainWeylPrefix K r k).val : Mat K (r + 1)) *ᵥ naturalCoordinateBasis K r side j =
      if j < k then naturalCoordinateBasis K r side (j + 1)
      else if j = k then (-1 : K) ^ k • naturalCoordinateBasis K r side 0
      else naturalCoordinateBasis K r side j := by
  intro k
  induction k with
  | zero =>
    intro hk side j hj
    rw [chainWeylPrefix_zero]
    change (1 : Mat K (r + 1)) *ᵥ naturalCoordinateBasis K r side j = _
    rw [Matrix.one_mulVec]
    by_cases hz : j = 0
    · subst j
      simp only [lt_self_iff_false, if_false, if_true, pow_zero, one_smul]
    · simp only [Nat.not_lt_zero, if_false, hz]
  | succ k ih =>
    intro hk side j hj
    have hkr : k < r := by omega
    have hkle : k ≤ r := by omega
    rw [chainWeylPrefix_succ K r k hkr]
    change (((chainWeylPrefix K r k).val : Mat K (r + 1)) *
      ((simpleWeyl K (r + 1) (⟨k, hkr⟩ : Fin r).castSucc).val : Mat K (r + 1))) *ᵥ
      naturalCoordinateBasis K r side j = _
    rw [← Matrix.mulVec_mulVec]
    by_cases hjk : j = k
    · subst j
      rw [chain_step_left, ih hkle side (k + 1) (by omega)]
      simp only [show ¬k + 1 < k by omega, show k + 1 ≠ k by omega, if_false,
        show k < k + 1 by omega, if_true]
    · by_cases hjk' : j = k + 1
      · subst j
        rw [chain_step_right, Matrix.mulVec_neg, ih hkle side k hkle]
        simp only [lt_self_iff_false, if_false, if_true, pow_succ, mul_neg_one, neg_smul]
      · rw [chain_step_other K r k hkr side j hj hjk hjk', ih hkle side j hj]
        by_cases hlt : j < k
        · simp only [hlt, show j < k + 1 by omega, if_true]
        · have hlt' : ¬j < k + 1 := by omega
          simp only [hlt, hlt', hjk, hjk', if_false]

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
