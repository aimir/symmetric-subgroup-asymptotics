import SymmetricSubgroupAsymptotics.CFSGUpperUnitriangular
import Mathlib.Data.Matrix.Basis
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! The standard complete flag is recovered intrinsically from the actual
upper-unitriangular action. Consequently every normalizer preserves the flag
and is upper triangular. This argument is valid over every field. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGUpperUnitriangular
open Matrix
variable {F : Type*} [Field F] {n : ℕ}

def prefixFlag (F : Type*) [Field F] (n k : ℕ) : Submodule F (Fin n → F) where
  carrier := {v | ∀ i, k ≤ i.val → v i = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun hv hw i hi => by simp only [Pi.add_apply, hv i hi, hw i hi, add_zero]
  smul_mem' := fun a v hv i hi => by simp only [Pi.smul_apply, hv i hi, smul_zero]

abbrev flagAction (A : SL F n) : (Fin n → F) ≃ₗ[F] (Fin n → F) :=
  Matrix.SpecialLinearGroup.toLin' A

theorem flagAction_eq_mulVec (A : SL F n) (v : Fin n → F) :
    flagAction A v = A.val *ᵥ v := rfl

theorem flagAction_mul (A B : SL F n) (v : Fin n → F) :
    flagAction (A * B) v = flagAction A (flagAction B v) := by
  exact congrArg (fun e : (Fin n → F) ≃ₗ[F] (Fin n → F) => e v)
    (Matrix.SpecialLinearGroup.toLin'.map_mul A B)

theorem elementary_flag_displacement {i j : Fin n} (hij : i < j) (v : Fin n → F) :
    (flagAction (CFSGTypeAElementaryMatrices.elementary (ne_of_lt hij) (1 : F)) v - v) i = v j := by
  change ((Matrix.transvection i j (1 : F) *ᵥ v) i - v i) = v j
  rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
  simp only [Pi.add_apply, Function.update_self, one_mul]
  exact add_sub_cancel_left (v i) (v j)

/-- The next member of the flag consists exactly of the vectors whose every
unitriangular displacement belongs to the preceding member. -/
theorem mem_prefixFlag_succ_iff (k : ℕ) (v : Fin n → F) :
    v ∈ prefixFlag F n (k + 1) ↔
      ∀ u : SL F n, u ∈ upperUnitriangular F n →
        flagAction u v - v ∈ prefixFlag F n k := by
  constructor
  · intro hv u hu i hi
    have hcoord : (u.val *ᵥ v) i = v i := by
      change (∑ j, u.val i j * v j) = v i
      calc
        (∑ j, u.val i j * v j) = u.val i i * v i := by
          refine Finset.sum_eq_single i ?_ ?_
          · intro j _ hji
            rcases lt_or_gt_of_ne hji with hj | hj
            · rw [hu.1 hj, zero_mul]
            · have hz : v j = 0 := hv j (by change k ≤ i.val at hi; change i.val < j.val at hj; omega)
              rw [hz, mul_zero]
          · intro hni
            exact False.elim (hni (Finset.mem_univ i))
        _ = 1 * v i := congrArg (fun z : F => z * v i) (hu.2 i)
        _ = v i := one_mul _
    change (u.val *ᵥ v) i - v i = 0
    rw [hcoord, sub_self]
  · intro hv j hj
    have hk : k < n := by omega
    let i : Fin n := ⟨k, hk⟩
    have hij : i < j := by change k < j.val; omega
    have h := hv (CFSGTypeAElementaryMatrices.elementary (ne_of_lt hij) (1 : F))
      (elementary_mem_upperUnitriangular hij 1) i (by exact le_rfl)
    rw [elementary_flag_displacement hij] at h
    exact h

/-- A normalizer of U preserves every member of the actual standard flag. -/
theorem normalizer_preserves_prefixFlag (A : SL F n)
    (hA : A ∈ Subgroup.normalizer (upperUnitriangular F n : Set (SL F n))) :
    ∀ (k : ℕ) (v : Fin n → F), v ∈ prefixFlag F n k →
      flagAction A v ∈ prefixFlag F n k := by
  intro k
  induction k with
  | zero =>
    intro v hv
    have hz : v = 0 := funext fun i => hv i (Nat.zero_le _)
    rw [hz, map_zero]
    exact (prefixFlag F n 0).zero_mem
  | succ k ih =>
    intro v hv
    apply (mem_prefixFlag_succ_iff k _).mpr
    intro u hu
    have hconj : A⁻¹ * u * A ∈ upperUnitriangular F n :=
      (Subgroup.mem_normalizer_iff''.mp hA u).mp hu
    have hmove := (mem_prefixFlag_succ_iff k v).mp hv (A⁻¹ * u * A) hconj
    have h := ih (flagAction (A⁻¹ * u * A) v - v) hmove
    have he : A * (A⁻¹ * u * A) = u * A := by simp only [← mul_assoc, mul_inv_cancel, one_mul]
    have hact : flagAction A (flagAction (A⁻¹ * u * A) v) =
        flagAction u (flagAction A v) := by
      rw [← flagAction_mul, he, flagAction_mul]
    simpa only [map_sub, hact] using h

/-- The normalizer of the literal upper-unitriangular subgroup is contained
in the literal upper-triangular subgroup. No finiteness is required. -/
theorem normalizer_upperUnitriangular_le_borel (F : Type*) [Field F] (n : ℕ) :
    Subgroup.normalizer (upperUnitriangular F n : Set (SL F n)) ≤ borel F n := by
  intro A hA i j hij
  have hv : Pi.single j (1 : F) ∈ prefixFlag F n (j.val + 1) := by
    intro k hk
    have hkj : k ≠ j := by intro he; subst k; omega
    exact Pi.single_eq_of_ne hkj 1
  have h := normalizer_preserves_prefixFlag A hA (j.val + 1) (Pi.single j 1) hv i
    (by change j.val < i.val at hij; omega)
  change (A.val *ᵥ Pi.single j 1) i = 0 at h
  rw [Matrix.mulVec_single_one] at h
  exact h

end SymmetricSubgroupAsymptotics.CFSGUpperUnitriangular
