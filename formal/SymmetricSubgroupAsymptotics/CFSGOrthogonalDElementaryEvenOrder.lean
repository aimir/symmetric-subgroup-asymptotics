import SymmetricSubgroupAsymptotics.CFSGOrthogonalDElementaryCenter
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDMatrixWeylParity
import SymmetricSubgroupAsymptotics.CFSGProjectiveLinearEvenOrder

/-! A literal chain word is noncentral and has fourth power one in
the actual elementary type-D group, uniformly in the field. Its image
proves that the elementary central quotient has even cardinality. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices

def chainWeyl (K : Type) [Field K] (r : ℕ) : elementaryRootGroup K (r + 2) :=
  ⟨rootTransvection K (r + 2) false (Fin.last r).castSucc (-1) *
      rootTransvection K (r + 2) true (Fin.last r).castSucc 1 *
      rootTransvection K (r + 2) false (Fin.last r).castSucc (-1),
    (elementaryRootGroup K (r + 2)).mul_mem
      ((elementaryRootGroup K (r + 2)).mul_mem
        (rootTransvection_mem K (r + 2) false (Fin.last r).castSucc (-1))
        (rootTransvection_mem K (r + 2) true (Fin.last r).castSucc 1))
      (rootTransvection_mem K (r + 2) false (Fin.last r).castSucc (-1))⟩

theorem chainWeyl_val (K : Type) [Field K] (r : ℕ) :
    ((chainWeyl K r).val : Mat K (r + 2)) =
      chainWeylMatrix K (r + 1) (Fin.last r) := by
  change (1 + (-1 : K) • rootMatrix K (r + 2) false (Fin.last r).castSucc) *
      (1 + (1 : K) • rootMatrix K (r + 2) true (Fin.last r).castSucc) *
      (1 + (-1 : K) • rootMatrix K (r + 2) false (Fin.last r).castSucc) = _
  simp only [rootMatrix, Bool.false_eq_true, if_false, if_true,
    neg_one_smul, one_smul, ← sub_eq_add_neg, chainWeylMatrix]

theorem chainWeyl_four (K : Type) [Field K] (r : ℕ) : chainWeyl K r ^ 4 = 1 := by
  apply Subtype.ext
  apply Units.ext
  change (((chainWeyl K r).val : Mat K (r + 2)) ^ 4) = 1
  rw [chainWeyl_val]
  exact chainWeylMatrix_four K (r + 1) (Fin.last r)

theorem chainWeyl_not_center (K : Type) [Field K] (r : ℕ) :
    chainWeyl K r ∉ Subgroup.center (elementaryRootGroup K (r + 2)) := by
  intro h
  obtain ⟨c, hc⟩ := (elementaryRootGroup_center_iff_scalar K r (chainWeyl K r)).mp h
  rw [chainWeyl_val] at hc
  exact chainWeylMatrix_nonscalar K (r + 1) (Fin.last r) c hc

theorem elementaryProjective_even_card (K : Type) [Field K] (r : ℕ) :
    Even (Nat.card (elementaryProjective K (r + 2))) := by
  let q := QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (r + 2)))
  apply CFSGProjectiveLinearEvenOrder.even_card_of_nontrivial_fourth_root (q (chainWeyl K r))
  · intro h
    exact chainWeyl_not_center K r ((QuotientGroup.eq_one_iff _).mp h)
  · rw [← map_pow, chainWeyl_four, map_one]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
