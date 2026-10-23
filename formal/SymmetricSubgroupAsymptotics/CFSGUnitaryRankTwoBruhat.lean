import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoUpperFlag
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNaturalColumnClearing
import SymmetricSubgroupAsymptotics.CFSGTwistedA2IsometricColumns

/-! A literal two-cell cover of the rank-two natural fixed group.
The nontriangular cell is obtained by an actual upper clearing word and
the same signed reversal, not an assumed Bruhat presentation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent CFSGSerreOrdinaryTwists

theorem rankTwo_zero_pivot_mem_flag (q : CFSG.PrimePower) (g : naturalFixed 2 q)
    (hzero : (g.val.val : Mat (q.Extension 2) 2) 2 0 = 0) : g ∈ rankTwoUpperFlag q := by
  apply (rankTwoUpperFlag_mem_iff q g).mpr
  exact CFSGTwistedA2UnipotentArrays.isometric_upper_of_lower_pivot_zero
    (definingFieldAutomorphism q 2) g.val.val
    (fixed_unit_isometric (q.Extension 2) 2 (definingFieldAutomorphism q 2).toRingHom
      g.val.val g.property) hzero

theorem rankTwo_upper_or_reversal_cell (q : CFSG.PrimePower) (g : naturalFixed 2 q) :
    g ∈ rankTwoUpperFlag q ∨
      ∃ (u : rankTwoUpperSubgroup q) (b : rankTwoUpperFlag q),
        g = u.val * (reversalFixed q 2)⁻¹ * b.val := by
  by_cases hz : (g.val.val : Mat (q.Extension 2) 2) 2 0 = 0
  · exact Or.inl (rankTwo_zero_pivot_mem_flag q g hz)
  right
  obtain ⟨u, hclear⟩ := upper_clear_natural_column q 0 g hz
  let uf : naturalFixed 2 q := ⟨u.val, u.property.2⟩
  let k : naturalFixed 2 q := reversalFixed q 2 * uf * g
  have hm0 : ((u.val.val : Mat (q.Extension 2) 2) *
      (g.val.val : Mat (q.Extension 2) 2)) 0 0 = 0 := by
    have hh := congrFun hclear (0 : Fin 3)
    simpa [Pi.single_apply] using hh
  have hk20 : (k.val.val : Mat (q.Extension 2) 2) 2 0 = 0 := by
    change (((signedReversalUnit (q.Extension 2) 2 : Mat (q.Extension 2) 2) *
      (u.val.val : Mat (q.Extension 2) 2)) * (g.val.val : Mat (q.Extension 2) 2)) 2 0 = 0
    rw [mul_assoc]
    simpa [Matrix.mul_apply, Fin.sum_univ_three, signedReversalUnit_apply,
      Fin.rev, signWeight] using hm0
  refine ⟨⟨uf⁻¹, (rankTwoUpperSubgroup q).inv_mem u.property⟩,
    ⟨k, rankTwo_zero_pivot_mem_flag q k hk20⟩, ?_⟩
  change g = uf⁻¹ * (reversalFixed q 2)⁻¹ * (reversalFixed q 2 * uf * g)
  group

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
