import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryFirstColumn
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryParabolicFactorization
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMiddleOpposite
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRankOneGeneration
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRankTwoGeneration

/-! Actual Gaussian generation of the SAME natural defining-fixed
group by its literal U and signed-reversal opposite. The induction drops
rank by two, retaining the genuine rank-one fixed-field and all-q raw
rank-two bases. It does not assert perfectness of the rank-two q=2 base. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent

theorem rank_zero_mem_join (q : CFSG.PrimePower) (g : naturalFixed 0 q) :
    g.val ∈ naturalUpperOppositeJoin q 0 := by
  have he : g.val = 1 := by
    have hd := naturalElementary_det (q.Extension 2) 0 g.val
    change Matrix.det (g.val.val : Matrix (Fin 1) (Fin 1) (q.Extension 2)) = 1 at hd
    rw [Matrix.det_fin_one] at hd
    apply Subtype.ext
    apply Units.ext
    ext i j
    rw [Fin.eq_zero i, Fin.eq_zero j]
    change (g.val.val : Matrix (Fin 1) (Fin 1) (q.Extension 2)) 0 0 =
      (1 : Matrix (Fin 1) (Fin 1) (q.Extension 2)) 0 0
    simpa only [Matrix.one_apply, if_true] using hd
  rw [he]
  exact (naturalUpperOppositeJoin q 0).one_mem

theorem naturalFixed_mem_join (q : CFSG.PrimePower) (r : ℕ) (g : naturalFixed r q) :
    g.val ∈ naturalUpperOppositeJoin q r := by
  revert g
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro g
    cases r with
    | zero => exact rank_zero_mem_join q g
    | succ r =>
      cases r with
      | zero => exact rank_one_mem_join q g
      | succ r =>
        cases r with
        | zero => exact rank_two_mem_join q g
        | succ s =>
          obtain ⟨h, hh, hcol⟩ := exists_join_first_column_one q s g
          obtain ⟨u, m, hfac⟩ := normalized_radical_middle_factor q (s + 1) (h * g) hcol
          have hm : (naturalFixedMiddleHom q (s + 1) m).val ∈
              naturalUpperOppositeJoin q (s + 3) :=
            middle_join_le q (s + 1) (ih (s + 1) (by omega) m)
          have hprod : (h * g).val ∈ naturalUpperOppositeJoin q (s + 3) := by
            rw [hfac]
            exact (naturalUpperOppositeJoin q (s + 3)).mul_mem
              ((show naturalUnipotent (s + 3) q ≤ naturalUpperOppositeJoin q (s + 3)
                from le_sup_left) u.property) hm
          have hcancel := (naturalUpperOppositeJoin q (s + 3)).mul_mem
            ((naturalUpperOppositeJoin q (s + 3)).inv_mem hh) hprod
          change h.val⁻¹ * (h.val * g.val) ∈ _ at hcancel
          simpa only [inv_mul_cancel_left] using hcancel

theorem naturalUpperOppositeJoin_eq_fixed (q : CFSG.PrimePower) (r : ℕ) :
    naturalUpperOppositeJoin q r = naturalFixed r q := by
  apply le_antisymm
  · apply sup_le
    · intro u hu
      exact hu.2
    · rintro g ⟨u, hu, rfl⟩
      exact (naturalFixed r q).mul_mem
        ((naturalFixed r q).mul_mem (reversalFixed q r).property hu.2)
        ((naturalFixed r q).inv_mem (reversalFixed q r).property)
  · intro g hg
    exact naturalFixed_mem_join q r ⟨g, hg⟩

theorem reversal_mem_join (q : CFSG.PrimePower) (r : ℕ) :
    (reversalFixed q r).val ∈ naturalUpperOppositeJoin q r :=
  naturalFixed_mem_join q r (reversalFixed q r)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
