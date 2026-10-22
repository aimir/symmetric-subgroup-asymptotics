import SymmetricSubgroupAsymptotics.CFSGTwistedDPairedTorusImages
import SymmetricSubgroupAsymptotics.CFSGDiagonalUnitRootAction

/-! Exact natural conjugation of the paired positive root by the image
of the original fixed torus word. The two conjugate parameters remain
linked by the genuine field automorphism. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDPairedTorusAction
open CFSGSerreOrdinaryTwists CFSGOrthogonalDSerreMatrices
open CFSGOrthogonalDGenerationForkTorus CFSGTwistedDNaturalFork
open CFSGTwistedDPairedRootImages CFSGTwistedDPairedTorusImages

theorem pairedDiagonal_values (s : ℕ) (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ) :
    pairedDiagonal s q c (Sum.inl (pen (s + 2))) =
        (c : q.Extension 2) * (frobeniusUnit q c : q.Extension 2) ∧
    pairedDiagonal s q c (Sum.inl (last (s + 2))) =
        (c : q.Extension 2)⁻¹ * (frobeniusUnit q c : q.Extension 2) ∧
    pairedDiagonal s q c (Sum.inr (pen (s + 2))) =
        (c : q.Extension 2)⁻¹ * (frobeniusUnit q c : q.Extension 2)⁻¹ ∧
    pairedDiagonal s q c (Sum.inr (last (s + 2))) =
        (c : q.Extension 2) * (frobeniusUnit q c : q.Extension 2)⁻¹ := by
  simp only [pairedDiagonal, chainDiagonal, forkDiagonal, if_true,
    if_neg (Ne.symm (pen_ne_last (s + 2)))]
  trivial

private theorem sparse_conjugation {I : Type*} [Fintype I] [DecidableEq I]
    {K : Type*} [Field K] (T U V : (Matrix I I K)ˣ) (d : I → K)
    (i j k l : I) (a c : K)
    (hT : (T : Matrix I I K) = Matrix.diagonal d)
    (hU : (U : Matrix I I K) = 1 + a •
      (Matrix.single i j 1 - Matrix.single k l 1))
    (hV : (V : Matrix I I K) = 1 + (c * a) •
      (Matrix.single i j 1 - Matrix.single k l 1))
    (hp : d i = c * d j) (hn : d k = c * d l) : T * U * T⁻¹ = V := by
  apply CFSGDiagonalUnitRootAction.root_line_conjugation T U V d
    (Matrix.single i j 1 - Matrix.single k l 1) c a hT hU hV
  intro x y hxy
  by_cases hpos : i = x ∧ j = y
  · rcases hpos with ⟨rfl, rfl⟩
    exact hp
  · by_cases hneg : k = x ∧ l = y
    · rcases hneg with ⟨rfl, rfl⟩
      exact hn
    · exact (hxy (by simp only [Matrix.sub_apply, Matrix.single_apply,
        if_neg hpos, if_neg hneg, sub_self])).elim

private theorem pen_root_val (s : ℕ) (q : CFSG.PrimePower) (a : q.Extension 2) :
    ((naturalRoot s q false (pen (s + 2)) a).val : Mat (q.Extension 2) (s + 4)) =
      1 + a • (Matrix.single (Sum.inl (pen (s + 2))) (Sum.inl (last (s + 2))) 1 -
        Matrix.single (Sum.inr (last (s + 2))) (Sum.inr (pen (s + 2))) 1) := by
  change 1 + a • positive (q.Extension 2) (s + 4) (pen (s + 2)) = _
  have hi : (pen (s + 2)).val + 1 < s + 4 := by dsimp [pen]; omega
  have hn : (⟨(pen (s + 2)).val + 1, hi⟩ : Fin (s + 4)) = last (s + 2) := by
    apply Fin.ext
    rfl
  rw [positive, dif_pos hi, hn]

private theorem last_root_val (s : ℕ) (q : CFSG.PrimePower) (a : q.Extension 2) :
    ((naturalRoot s q false (last (s + 2)) a).val : Mat (q.Extension 2) (s + 4)) =
      1 + a • (Matrix.single (Sum.inl (pen (s + 2))) (Sum.inr (last (s + 2))) 1 -
        Matrix.single (Sum.inl (last (s + 2))) (Sum.inr (pen (s + 2))) 1) := by
  change 1 + a • positive (q.Extension 2) (s + 4) (last (s + 2)) = _
  have hi : ¬(last (s + 2)).val + 1 < s + 4 := by dsimp [last]; omega
  rw [positive, dif_neg hi, previous_last]

theorem pen_conjugation (s : ℕ) (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ)
    (a : q.Extension 2) :
    pairedNaturalTorus s q c * naturalRoot s q false (pen (s + 2)) a *
        (pairedNaturalTorus s q c)⁻¹ =
      naturalRoot s q false (pen (s + 2)) ((c : q.Extension 2)^2 * a) := by
  have hv := pairedDiagonal_values s q c
  apply Subtype.ext
  apply sparse_conjugation (pairedNaturalTorus s q c).val
    (naturalRoot s q false (pen (s + 2)) a).val
    (naturalRoot s q false (pen (s + 2)) ((c : q.Extension 2)^2 * a)).val
    (pairedDiagonal s q c) _ _ _ _ a ((c : q.Extension 2)^2)
    (pairedNaturalTorus_val s q c) (pen_root_val s q a)
    (pen_root_val s q ((c : q.Extension 2)^2 * a))
  · rw [hv.1, hv.2.1]
    field_simp [Units.ne_zero c]
  · rw [hv.2.2.2, hv.2.2.1]
    field_simp [Units.ne_zero c]

theorem last_conjugation (s : ℕ) (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ)
    (a : q.Extension 2) :
    pairedNaturalTorus s q c * naturalRoot s q false (last (s + 2)) a *
        (pairedNaturalTorus s q c)⁻¹ =
      naturalRoot s q false (last (s + 2)) ((frobeniusUnit q c : q.Extension 2)^2 * a) := by
  have hv := pairedDiagonal_values s q c
  apply Subtype.ext
  apply sparse_conjugation (pairedNaturalTorus s q c).val
    (naturalRoot s q false (last (s + 2)) a).val
    (naturalRoot s q false (last (s + 2))
      ((frobeniusUnit q c : q.Extension 2)^2 * a)).val
    (pairedDiagonal s q c) _ _ _ _ a ((frobeniusUnit q c : q.Extension 2)^2)
    (pairedNaturalTorus_val s q c) (last_root_val s q a)
    (last_root_val s q ((frobeniusUnit q c : q.Extension 2)^2 * a))
  · rw [hv.1, hv.2.2.2]
    field_simp [Units.ne_zero (frobeniusUnit q c)]
  · rw [hv.2.1, hv.2.2.1]
    field_simp [Units.ne_zero (frobeniusUnit q c)]

theorem paired_conjugation (s : ℕ) (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ)
    (a : q.Extension 2) :
    pairedNaturalTorus s q c * pairedNaturalRoot s q false a *
        (pairedNaturalTorus s q c)⁻¹ =
      pairedNaturalRoot s q false ((c : q.Extension 2)^2 * a) := by
  have hpow : ((c : q.Extension 2)^2 * a)^q.order =
      (frobeniusUnit q c : q.Extension 2)^2 * a^q.order := by
    rw [frobeniusUnit_val]
    have h := (definingFieldAutomorphism q 2).map_mul ((c : q.Extension 2)^2) a
    rw [map_pow] at h
    simpa only [definingFieldAutomorphism_apply] using h
  change pairedNaturalTorus s q c *
      (naturalRoot s q false (pen (s + 2)) a *
        naturalRoot s q false (last (s + 2)) (a^q.order)) *
        (pairedNaturalTorus s q c)⁻¹ = _
  calc
    _ = (pairedNaturalTorus s q c * naturalRoot s q false (pen (s + 2)) a *
          (pairedNaturalTorus s q c)⁻¹) *
        (pairedNaturalTorus s q c * naturalRoot s q false (last (s + 2)) (a^q.order) *
          (pairedNaturalTorus s q c)⁻¹) := by group
    _ = _ := by
      rw [pen_conjugation, last_conjugation]
      exact congrArg
        (fun z : q.Extension 2 =>
          naturalRoot s q false (pen (s + 2)) ((c : q.Extension 2)^2 * a) *
            naturalRoot s q false (last (s + 2)) z) hpow.symm

end SymmetricSubgroupAsymptotics.CFSGTwistedDPairedTorusAction
