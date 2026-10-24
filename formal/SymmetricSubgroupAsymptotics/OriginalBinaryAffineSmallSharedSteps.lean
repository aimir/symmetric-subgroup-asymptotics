import SymmetricSubgroupAsymptotics.OriginalBinaryAffineJointWindowStep
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeEightSubnormalOrdinaryGenerators

/-! Three scalar exceptions repaired by actual group structure.
The degree-two top has order at most two. In degree-eight fibres every
actual subnormal coordinate image has the proved ordinary rank at most
three. No smaller MN input, local rank certificate, or group catalogue
is supplied. The four-point/four-block case is deliberately not included
because its existing sharing theorem has a stronger smaller-MN premise. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffineSmallSharedSteps
open OriginalAffineBlockCharacteristicHead OriginalBlockClassBound
open NaturalSquareRootQuotientCeiling BinaryAffineJointSelectedWindowNumerics

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

private theorem tracey_ceiling_power (k : ℕ) (hk : 0 < k) :
    traceyPermutationGeneratorCeiling (2^k) = quotientCeiling (2^k) k := by
  have hl : Real.logb 2 ((2 : ℝ)^k) = (k : ℝ) := by
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]
  rw [quotientCeiling_eq _ _ hk]
  simp only [traceyPermutationGeneratorCeiling, Nat.cast_pow, Nat.cast_ofNat, hl]

/-- The actual two-point top saves the one generator lost by the coarse
ceiling in the d=2,e=1 scalar calculation. -/
theorem two_dim_two_blocks (hp : P.p = 2)
    (hd : translationDimension J block P = 2) (ht : Fintype.card block.Points = 2)
    (i : block.Points) : MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  have htcard : Nat.card block.Points = 2 := by
    simpa only [Fintype.card_eq_nat_card] using ht
  have htopcard : Nat.card block.Top ≤ 2 := by
    have hh := Nat.card_le_card_of_injective
      (Subtype.val : block.Top → Equiv.Perm block.Points) Subtype.val_injective
    have hh' : Nat.card block.Top ≤ (Nat.card block.Points).factorial := by
      simpa only [Nat.card_perm] using hh
    exact hh'.trans_eq (by rw [htcard]; decide)
  have htop : MarkedC4.genRank block.Top ≤ 1 :=
    FiniteGroupBinaryOrderGenerators.genRank_le_of_card_le_two_pow block.Top 1
      (by simpa using htopcard)
  have hGL : Nat.log 2 (Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2))) = 2 := by
    rw [matrix_GL_card_eq_order]
    decide +kernel
  have hh := OriginalBinaryAffineJointCharacteristicCost.genRank_le_joint_primary_cost
    J block P hp 1 (by simpa using ht) i
  rw [hd] at hh
  simp only [hGL] at hh
  norm_num at hh
  have htopR : (MarkedC4.genRank block.Top : ℝ) ≤ 1 := by exact_mod_cast htop
  have hsource : MarkedC4.genRank J ≤ 5 := by
    have hhR : (MarkedC4.genRank J : ℝ) ≤ 5 := by linarith
    exact_mod_cast hhR
  have hf : Nat.card block.Fibre = 4 := by
    simpa only [hp, hd] using fibre_card_eq_prime_pow_dimension J block P
  have hn : n = 8 := by
    have hh := block.degree_product
    rw [hf, htcard, Nat.card_fin] at hh
    omega
  have hceil : traceyPermutationGeneratorCeiling 8 = 5 := by
    rw [show (8 : ℕ) = 2^3 by decide, tracey_ceiling_power 3 (by decide)]
    decide +kernel
  have htarget : traceyPermutationGeneratorCeiling n = 5 :=
    (congrArg traceyPermutationGeneratorCeiling hn).trans hceil
  exact hsource.trans_eq htarget.symm

include P in
/-- Both d=3,e=1 and d=3,e=2 are paid by the actual subnormal rank-three
budget. The existing coarse top ceilings already suffice. -/
theorem degreeEight_two_or_four_blocks (hdegree : Nat.card block.Fibre = 8)
    (e : ℕ) (he : e = 1 ∨ e = 2) (ht : Fintype.card block.Points = 2^e)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  let x : block.Fibre := ⟨x₀, block.map_base⟩
  let K := Kernel (A := J) (X := block.Points)
  have hK := BlockSubnormalOrdinaryGeneratorInduction.kernel_genRank_le_subnormal_budget
    block.map block.map_equivariant block.base 3
    (fun L hL => P.subnormal_genRank_le_three_of_degreeEight
      block.component_preprimitive x hdegree L hL)
  have hquot : MarkedC4.genRank (J ⧸ K) = MarkedC4.genRank block.Top :=
    CoprimeNilpotentProductGenerators.genRank_mulEquiv
      (QuotientGroup.quotientKerEquivRange (topMap (A := J) (X := block.Points)))
  have hsource := MarkedC4.genRank_le_of_normal K
  rw [hquot] at hsource
  have htcard : Nat.card block.Points = 2^e := by
    simpa only [Fintype.card_eq_nat_card] using ht
  have hepos : 0 < e := by rcases he with rfl | rfl <;> omega
  have htop' : MarkedC4.genRank block.Top ≤ quotientCeiling (2^e) e := by
    rw [htcard, tracey_ceiling_power e hepos] at htop
    exact htop
  have hbound : MarkedC4.genRank J ≤ (2^e)*3 + quotientCeiling (2^e) e := by
    rw [htcard] at hK
    nlinarith
  have hnum : (2^e)*3 + quotientCeiling (2^e) e ≤
      quotientCeiling (2^(3+e)) (3+e) := by
    rcases he with rfl | rfl <;> decide +kernel
  have hn : n = 2^(3+e) := by
    calc
      n = Nat.card block.Fibre * Nat.card block.Points := by
        simpa only [Nat.card_fin] using block.degree_product.symm
      _ = 8*2^e := by rw [hdegree, htcard]
      _ = _ := by rw [pow_add]; norm_num
  have htarget : traceyPermutationGeneratorCeiling n =
      quotientCeiling (2^(3+e)) (3+e) :=
    (congrArg traceyPermutationGeneratorCeiling hn).trans
      (tracey_ceiling_power (3+e) (by omega))
  exact (hbound.trans hnum).trans_eq htarget.symm

end SymmetricSubgroupAsymptotics.OriginalBinaryAffineSmallSharedSteps
