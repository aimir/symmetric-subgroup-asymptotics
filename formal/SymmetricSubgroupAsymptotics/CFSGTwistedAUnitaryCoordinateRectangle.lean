import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOpposedPairing
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryPairReciprocity
import Mathlib.Tactic.Ring

/-! One literal four-axis singular rectangle works in every original
unitary rank at least three and every characteristic. Its nonzero cross
value will detect that a common mixed ratio is fixed by the involution. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGTwistedAUnitaryParameters

private theorem axis_ne_zero (q : CFSG.PrimePower) (r : ℕ) (i : Fin (r+1)) :
    (Pi.single i (1 : q.Extension 2) : Fin (r+1) → q.Extension 2) ≠ 0 := by
  intro he
  have hh := congrFun he i
  simp only [Pi.single_eq_same,Pi.zero_apply] at hh
  exact one_ne_zero hh

private theorem axis_pair (q : CFSG.PrimePower) (r : ℕ) (i j : Fin (r+1)) :
    unitaryNaturalPair q r (Pi.single i 1) (Pi.single j 1) =
      if i.rev = j then signWeight (q.Extension 2) r i else 0 := by
  rw [unitaryNaturalPair_basis]
  by_cases he : i.rev = j <;> simp [Pi.single_apply,he]

theorem exists_unitary_coordinate_rectangle (q : CFSG.PrimePower) (s : ℕ) :
    ∃ x u y z : Fin (s+4) → q.Extension 2,
      x ∈ unitaryStandardSingularSpace q (s+3) ∧
      u ∈ unitaryStandardSingularSpace q (s+3) ∧
      y ∈ unitaryOppositeSingularSpace q (s+3) ∧
      z ∈ unitaryOppositeSingularSpace q (s+3) ∧
      x ≠ 0 ∧ u ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧
      unitaryNaturalPair q (s+3) y x = 0 ∧
      unitaryNaturalPair q (s+3) z u = 0 ∧
      unitaryNaturalPair q (s+3) x z ≠ 0 ∧
      unitaryNaturalPair q (s+3) (x+y) (u+z) = 0 := by
  let a : Fin (s+4) := ⟨0,by omega⟩
  let b : Fin (s+4) := ⟨1,by omega⟩
  have haval : a.val = 0 := rfl
  have hbval : b.val = 1 := rfl
  let X : Fin (s+4) → q.Extension 2 := Pi.single a 1
  let U : Fin (s+4) → q.Extension 2 := Pi.single b 1
  let Y : Fin (s+4) → q.Extension 2 := Pi.single b.rev 1
  let Z : Fin (s+4) → q.Extension 2 := Pi.single a.rev 1
  let e : q.Extension 2 := (-1)^(s+3)
  have he : e ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hab : a ≠ b := by intro h; have hh := congrArg Fin.val h; change 0 = 1 at hh; omega
  have hba : b ≠ a := Ne.symm hab
  have hcross : unitaryNaturalPair q (s+3) X Z = 1 := by
    rw [axis_pair,if_pos rfl]
    rfl
  have hYu : unitaryNaturalPair q (s+3) Y U = -e := by
    rw [axis_pair,Fin.rev_rev,if_pos rfl,signWeight_rev]
    change e * (-1)^1 = -e
    simp only [pow_one,mul_neg_one]
  have hYX : unitaryNaturalPair q (s+3) Y X = 0 := by
    rw [axis_pair,Fin.rev_rev,if_neg hba]
  have hZU : unitaryNaturalPair q (s+3) Z U = 0 := by
    rw [axis_pair,Fin.rev_rev,if_neg hab]
  have hXu : unitaryNaturalPair q (s+3) X U = 0 := by
    apply unitaryStandardSingularSpace_pair_zero q (s+3)
    · exact unitaryStandard_single_mem q (s+3) a (by change 2 * a.val + 1 ≤ s+3; omega)
    · exact unitaryStandard_single_mem q (s+3) b (by change 2 * b.val + 1 ≤ s+3; omega)
  have hYZ : unitaryNaturalPair q (s+3) Y Z = 0 := by
    apply unitaryOppositeSingularSpace_pair_zero q (s+3)
    · exact unitaryOpposite_single_mem q (s+3) b.rev (by rw [Fin.rev_rev]; change 2 * b.val + 1 ≤ s+3; omega)
    · exact unitaryOpposite_single_mem q (s+3) a.rev (by rw [Fin.rev_rev]; change 2 * a.val + 1 ≤ s+3; omega)
  have hscaled (v w : Fin (s+4) → q.Extension 2) :
      unitaryNaturalPair q (s+3) v (e • w) = e * unitaryNaturalPair q (s+3) v w := by
    have hh := hermitianPair_smul (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s+3) : Mat (q.Extension 2) (s+3)) 1 e v w
    simpa only [one_smul,map_one,one_mul] using hh
  have hscaledLeft : unitaryNaturalPair q (s+3) (e • Z) U = 0 := by
    have hh := hermitianPair_smul (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s+3) : Mat (q.Extension 2) (s+3)) e 1 Z U
    simp only [one_smul,mul_one] at hh
    change unitaryNaturalPair q (s+3) (e • Z) U =
      definingFieldAutomorphism q 2 e * unitaryNaturalPair q (s+3) Z U at hh
    simpa only [mul_one,hZU,mul_zero] using hh
  refine ⟨X,U,Y,e • Z,unitaryStandard_single_mem q (s+3) a (by change 2 * a.val + 1 ≤ s+3; omega),
    unitaryStandard_single_mem q (s+3) b (by change 2 * b.val + 1 ≤ s+3; omega),
    unitaryOpposite_single_mem q (s+3) b.rev (by rw [Fin.rev_rev]; change 2 * b.val + 1 ≤ s+3; omega),
    (unitaryOppositeSingularSpace q (s+3)).smul_mem e
      (unitaryOpposite_single_mem q (s+3) a.rev (by rw [Fin.rev_rev]; change 2 * a.val + 1 ≤ s+3; omega)),
    axis_ne_zero q (s+3) a,axis_ne_zero q (s+3) b,axis_ne_zero q (s+3) b.rev,
    smul_ne_zero he (axis_ne_zero q (s+3) a.rev),hYX,hscaledLeft,?_,?_⟩
  · rw [hscaled,hcross,mul_one]
    exact he
  · change hermitianPair _ _ (X+Y) (U+e • Z) = 0
    rw [hermitianPair_add_left,hermitianPair_add_right,hermitianPair_add_right]
    change unitaryNaturalPair q (s+3) X U + unitaryNaturalPair q (s+3) X (e • Z) +
      (unitaryNaturalPair q (s+3) Y U + unitaryNaturalPair q (s+3) Y (e • Z)) = 0
    rw [hXu,hscaled,hscaled,hcross,hYu,hYZ]
    ring

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
