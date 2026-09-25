import SymmetricSubgroupAsymptotics.NaturalAlternatingChief

/-! Pointwise identification of the original even-degree generator.
Cancelling the last adjacent swap from the full rotation gives precisely
the cycle of the first n−1 points, with the last point fixed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem naturalAlternating_generator_eq_cycleRange (k:ℕ) :
    finRotate (k+5)*Equiv.swap (naturalAlternatingSecond k) (naturalAlternatingLast k)=
      (naturalAlternatingSecond k).cycleRange := by
  apply Equiv.ext
  intro i
  by_cases hib : i=naturalAlternatingSecond k
  · subst i
    rw [Equiv.Perm.mul_apply,Equiv.swap_apply_left,Fin.cycleRange_self]
    exact finRotate_last
  by_cases hic : i=naturalAlternatingLast k
  · subst i
    rw [Equiv.Perm.mul_apply,Equiv.swap_apply_right,
      naturalAlternating_rotation_second,
      Fin.cycleRange_of_gt (show naturalAlternatingSecond k<naturalAlternatingLast k by
        change k+3<k+4
        omega)]
  have hi : i<naturalAlternatingSecond k := by
    have hb : i.val≠k+3 := by
      intro he
      exact hib (Fin.ext he)
    have hc : i.val≠k+4 := by
      intro he
      exact hic (Fin.ext he)
    have hn := i.isLt
    change i.val<k+3
    omega
  rw [Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hib hic,
    Fin.cycleRange_of_lt hi]
  exact finRotate_apply i

/-- The literal (n−1)-cycle and final three-cycle have an actual
zero-weight chief series in every even degree at least six. -/
theorem naturalEvenAlternatingLiteralChiefSeries_zero (k:ℕ) :
    ∃z:ActualChiefSeries
      (Subgroup.closure
        ({(naturalAlternatingSecond (2*k+1)).cycleRange,naturalAlternatingTriple (2*k+1)}:
          Set (Equiv.Perm (Fin (2*k+1+5))))),actualChiefSeriesTernaryWeight z=0 := by
  have h := naturalEvenAlternatingChiefSeries_zero k
  rw [naturalAlternating_generator_eq_cycleRange (2*k+1)] at h
  exact h

end SymmetricSubgroupAsymptotics
