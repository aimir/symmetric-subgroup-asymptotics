import SymmetricSubgroupAsymptotics.CFSGUnitaryCoprimeProjectiveKernel
import SymmetricSubgroupAsymptotics.CFSGUnitaryCompleteOuterBudget
import SymmetricSubgroupAsymptotics.ClassicalClassEquationSmallParameters

/-! Actual semilinear reconstruction with the genuine coprime cover
kernel gives the outer bound2f. No extra automorphism-recognition or
centre formula is supplied. Binary ranks3/4 are direct arithmetic uses. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGUnitaryCoprimeOuterCardinality
open PrimitiveSocleRawStructure CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryCoordinates

theorem outer_card_le_twice_exponent (q : CFSG.PrimePower) (s : ℕ)
    [IsSimpleGroup (CFSG.Models.TwistedA (s+3) q)]
    (hn : ¬ IsMulCommutative (CFSG.Models.TwistedA (s+3) q))
    (hc : (s+4).Coprime (q.order^2-1)) :
    Nat.card (Outer (CFSG.Models.TwistedA (s+3) q)) ≤ 2*q.exponent := by
  let f := unitaryProjectiveCover q s
  letI : Finite (CFSG.Models.TwistedA (s+3) q) :=
    Finite.of_surjective f (unitaryProjectiveCover_surjective q s)
  have hkernel := CFSGUnitaryCoprimeProjectiveKernel.unitaryProjectiveCover_kernel_card_eq_one q s hc
  have hcard : Nat.card (naturalFixed (s+3) q) = Nat.card (CFSG.Models.TwistedA (s+3) q) := by
    have hh : Nat.card (naturalFixed (s+3) q) = Nat.card f.ker*Nat.card f.range := by
      rw [←f.ker.card_mul_index,Subgroup.index_ker]
    change Nat.card (naturalFixed (s+3) q) =
      Nat.card (unitaryProjectiveCover q s).ker*Nat.card (unitaryProjectiveCover q s).range at hh
    rw [hkernel,MonoidHom.range_eq_top.mpr (unitaryProjectiveCover_surjective q s),
      Subgroup.card_top,Nat.one_mul] at hh
    exact hh
  have hAut := unitary_card_aut_le_of_field_linear_factor q s (unitary_exists_field_linear_factor q s)
  rw [hcard] at hAut
  exact CFSGOuterCardinalityCancellation.outer_card_le_of_automorphism_bound hn (2*q.exponent)
    (by simpa only [Nat.mul_comm] using hAut)

theorem binary_rank_three_or_four_outer_card_le_two (q : CFSG.PrimePower) (hq : q.order = 2)
    (s : ℕ) (hs : s = 0 ∨ s = 1) [IsSimpleGroup (CFSG.Models.TwistedA (s+3) q)]
    (hn : ¬ IsMulCommutative (CFSG.Models.TwistedA (s+3) q)) :
    Nat.card (Outer (CFSG.Models.TwistedA (s+3) q)) ≤ 2 := by
  have he := ClassicalClassEquationCapacity.exponent_eq_one_of_prime_order q (by rw [hq]; decide)
  have hc : (s+4).Coprime (q.order^2-1) := by
    rcases hs with rfl | rfl <;> norm_num [hq]
  simpa only [he,Nat.mul_one] using outer_card_le_twice_exponent q s hn hc

end SymmetricSubgroupAsymptotics.CFSGUnitaryCoprimeOuterCardinality
