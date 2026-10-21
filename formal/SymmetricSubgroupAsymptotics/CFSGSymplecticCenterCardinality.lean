import SymmetricSubgroupAsymptotics.CFSGSymplecticFormPreservation
import SymmetricSubgroupAsymptotics.CFSGSymplecticElementaryCenter
import Mathlib.Algebra.CharP.Two

/-! The actual elementary symplectic centre has at most two elements.
In characteristic two it is trivial. Both conclusions use the original
scalar commutant and the same preserved alternating form. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
variable (K : Type*) [Field K]

theorem central_scalar_sq (r : ℕ) (u : elementaryRootGroup K (r + 1))
    (c : K) (hc : (u.val : Mat K (r + 1)) = c • 1) : c ^ 2 = 1 := by
  have hp := elementaryRootGroup_le_formPreserving K (r + 1) u.property
  change (u.val : Mat K (r + 1)) * Matrix.J (Fin (r + 1)) K *
    (u.val : Mat K (r + 1)).transpose = Matrix.J (Fin (r + 1)) K at hp
  rw [hc] at hp
  have hs : (c * c) • Matrix.J (Fin (r + 1)) K = Matrix.J (Fin (r + 1)) K := by
    simpa only [Matrix.transpose_smul, Matrix.transpose_one, smul_mul_assoc,
      mul_smul_comm, one_mul, mul_one, smul_smul] using hp
  have he := congrArg (fun M : Mat K (r + 1) => M (Sum.inr 0) (Sum.inl 0)) hs
  simpa [Matrix.J, Matrix.fromBlocks, pow_two] using he

theorem center_matrix_eq_one_or_neg_one (r : ℕ) (u : elementaryRootGroup K (r + 1))
    (hu : u ∈ Subgroup.center (elementaryRootGroup K (r + 1))) :
    (u.val : Mat K (r + 1)) = 1 ∨ (u.val : Mat K (r + 1)) = -1 := by
  obtain ⟨c, hc⟩ := (elementaryRootGroup_center_iff_scalar K r u).mp hu
  rcases sq_eq_one_iff.mp (central_scalar_sq K r u c hc) with h | h
  · exact Or.inl (by simpa only [h, one_smul] using hc)
  · exact Or.inr (by simpa only [h, neg_one_smul] using hc)

theorem center_card_le_two [Finite K] (r : ℕ) :
    Nat.card (Subgroup.center (elementaryRootGroup K (r + 1))) ≤ 2 := by
  classical
  let f : Subgroup.center (elementaryRootGroup K (r + 1)) → Fin 2 :=
    fun u => if u.val = 1 then 0 else 1
  have hneg (u : Subgroup.center (elementaryRootGroup K (r + 1))) (hu : u.val ≠ 1) :
      (u.val.val : Mat K (r + 1)) = -1 := by
    rcases center_matrix_eq_one_or_neg_one K r u.val u.property with h | h
    · exact False.elim (hu (Subtype.ext (Units.ext h)))
    · exact h
  have hi : Function.Injective f := by
    intro u v h
    by_cases hu : u.val = 1
    · have hv : v.val = 1 := by
        by_contra hv
        have hh : (0 : Fin 2) = 1 := by simpa only [f, if_pos hu, if_neg hv] using h
        exact (by decide : (0 : Fin 2) ≠ 1) hh
      exact Subtype.ext (hu.trans hv.symm)
    · have hv : v.val ≠ 1 := by
        intro hv
        have hh : (1 : Fin 2) = 0 := by simpa only [f, if_neg hu, if_pos hv] using h
        exact (by decide : (1 : Fin 2) ≠ 0) hh
      apply Subtype.ext
      apply Subtype.ext
      apply Units.ext
      exact (hneg u hu).trans (hneg v hv).symm
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hi

theorem center_eq_bot_of_char_two [CharP K 2] (r : ℕ) :
    Subgroup.center (elementaryRootGroup K (r + 1)) = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro u hu
  change u = 1
  apply Subtype.ext
  apply Units.ext
  rcases center_matrix_eq_one_or_neg_one K r u hu with h | h
  · exact h
  · rw [h]
    ext i j
    simp only [Matrix.neg_apply]
    exact CharTwo.neg_eq _

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
