import SymmetricSubgroupAsymptotics.CFSGSymplecticProjectiveRealization
import SymmetricSubgroupAsymptotics.CFSGMatrixPairRotation
import SymmetricSubgroupAsymptotics.CFSGProjectiveLinearEvenOrder

/-! A literal terminal root word is a noncentral fourth-root of one in
the actual elementary symplectic group, uniformly in the field and its
characteristic. Its projective image forces even order. The genuine
Serre-projective realization transports this to each actual simple
type-C model. No full symplectic group identification is needed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
open CFSG.Models.Chevalley

def terminalWeyl (K : Type) [Field K] (r : ℕ) : elementaryRootGroup K (r + 1) :=
  elementaryRoot K (r + 1) false (Fin.last r) (-1) *
    elementaryRoot K (r + 1) true (Fin.last r) 1 *
    elementaryRoot K (r + 1) false (Fin.last r) (-1)

theorem terminalWeyl_val (K : Type) [Field K] (r : ℕ) :
    ((terminalWeyl K r).val : Mat K (r + 1)) =
      CFSGMatrixPairRotation.rotation K (Sum.inl (Fin.last r)) (Sum.inr (Fin.last r)) := by
  change (1 + (-1 : K) • rootMatrix K (r + 1) false (Fin.last r)) *
      (1 + (1 : K) • rootMatrix K (r + 1) true (Fin.last r)) *
      (1 + (-1 : K) • rootMatrix K (r + 1) false (Fin.last r)) = _
  have hE : rootMatrix K (r + 1) false (Fin.last r) =
      Matrix.single (Sum.inl (Fin.last r)) (Sum.inr (Fin.last r)) 1 := by
    simp [rootMatrix, positive]
  have hF : rootMatrix K (r + 1) true (Fin.last r) =
      Matrix.single (Sum.inr (Fin.last r)) (Sum.inl (Fin.last r)) 1 := by
    simp [rootMatrix, negative, positive, Matrix.transpose_single]
  rw [hE, hF]
  simp only [neg_one_smul, one_smul, ← sub_eq_add_neg]
  exact CFSGMatrixPairRotation.word_eq_rotation K _ _ (by intro h; cases h)

theorem terminalWeyl_four (K : Type) [Field K] (r : ℕ) : terminalWeyl K r ^ 4 = 1 := by
  apply Subtype.ext
  apply Units.ext
  change (((terminalWeyl K r).val : Mat K (r + 1)) ^ 4) = 1
  rw [terminalWeyl_val]
  exact CFSGMatrixPairRotation.rotation_four K _ _ (by intro h; cases h)

theorem terminalWeyl_not_center (K : Type) [Field K] (r : ℕ) :
    terminalWeyl K r ∉ Subgroup.center (elementaryRootGroup K (r + 1)) := by
  intro h
  obtain ⟨c, hc⟩ := (elementaryRootGroup_center_iff_scalar K r (terminalWeyl K r)).mp h
  have he := congrArg (fun M : Mat K (r + 1) =>
    M (Sum.inr (Fin.last r)) (Sum.inl (Fin.last r))) hc
  dsimp only at he
  rw [terminalWeyl_val, CFSGMatrixPairRotation.rotation_entry K _ _ (by intro h; cases h)] at he
  have hz : (c • (1 : Mat K (r + 1))) (Sum.inr (Fin.last r)) (Sum.inl (Fin.last r)) = 0 := by
    simp [Matrix.one_apply]
  rw [hz] at he
  exact one_ne_zero he

theorem elementaryProjective_even_card (K : Type) [Field K] (r : ℕ) :
    Even (Nat.card (elementaryProjective K (r + 1))) := by
  let q := QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (r + 1)))
  apply CFSGProjectiveLinearEvenOrder.even_card_of_nontrivial_fourth_root (q (terminalWeyl K r))
  · intro h
    exact terminalWeyl_not_center K r ((QuotientGroup.eq_one_iff _).mp h)
  · rw [← map_pow, terminalWeyl_four, map_one]

theorem serreTypeC_even_card (K : Type) [Field K] (r : ℕ)
    [IsSimpleGroup (Projective (CartanMatrix.C (r + 1)).transpose K)] :
    Even (Nat.card (Projective (CartanMatrix.C (r + 1)).transpose K)) := by
  rw [Nat.card_congr (serreProjectiveEquivElementaryProjective K r).toEquiv]
  exact elementaryProjective_even_card K r

theorem typeC_even_card (r : ℕ) (q : CFSG.PrimePower) (hr : 1 ≤ r)
    [IsSimpleGroup (CFSG.Models.C r q)] : Even (Nat.card (CFSG.Models.C r q)) := by
  cases r with
  | zero => omega
  | succ s => exact serreTypeC_even_card q.Field s

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
