import SymmetricSubgroupAsymptotics.OriginalBinaryAffineFourResidualSteps
import SymmetricSubgroupAsymptotics.FourPointBlockFourLabelsOrdinaryGenerators

/-! The actual four-point/four-block sharing proof removes (d,e)=(2,2)
without strengthening the existing smaller-top hypothesis. The only
remaining pure-binary-top pairs are (4,1),(4,2),(5,1). No assertion is
made for those three pairs or for arbitrary non-binary top degrees. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffineThreeResidualSteps
open OriginalAffineBlockCharacteristicHead NaturalSquareRootQuotientCeiling

def unpaidThree (d e : ℕ) : Bool :=
  (d == 4 && (e == 1 || e == 2)) || (d == 5 && e == 1)

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

theorem two_dim_four_blocks (hp : P.p = 2)
    (hd : translationDimension J block P = 2) (ht : Fintype.card block.Points = 4) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  have hf := fibre_card_eq_prime_pow_dimension J block P
  change Nat.card block.Fibre = P.p ^ translationDimension J block P at hf
  rw [hp,hd] at hf
  have hfour : Nat.card block.Fibre = 4 := hf
  have hlabels : Nat.card block.Points = 4 := by
    simpa only [Fintype.card_eq_nat_card] using ht
  have hsource := FourPointBlockFourLabelsOrdinaryGenerators.genRank_le_eight
    block.map block.map_equivariant block.base hfour hlabels
  have hn : n = 16 := by
    have hh := block.degree_product
    rw [hfour,hlabels,Nat.card_fin] at hh
    omega
  have hceil : traceyPermutationGeneratorCeiling 16 = 8 := by
    have hl : Real.logb 2 ((2 : ℝ)^4) = (4 : ℝ) := by
      rw [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one]
      norm_num
    rw [show (16 : ℕ) = 2^4 by decide]
    simp only [traceyPermutationGeneratorCeiling,Nat.cast_pow,Nat.cast_ofNat,hl]
    norm_num
  have htarget : traceyPermutationGeneratorCeiling n = 8 :=
    (congrArg traceyPermutationGeneratorCeiling hn).trans hceil
  exact hsource.trans_eq htarget.symm

theorem genRank_le_ceiling_outside_three (hp : P.p = 2) (e : ℕ) (he : 1 ≤ e)
    (ht : Fintype.card block.Points = 2^e) (i : block.Points)
    (hpaid : unpaidThree (translationDimension J block P) e = false)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  let d := translationDimension J block P
  by_cases hold : OriginalBinaryAffineFourResidualSteps.unpaidFour d e = false
  · exact OriginalBinaryAffineFourResidualSteps.genRank_le_ceiling_outside_four
      J block P hp e he ht i hold htop
  · have hbad : OriginalBinaryAffineFourResidualSteps.unpaidFour d e = true := by
      cases hx : OriginalBinaryAffineFourResidualSteps.unpaidFour d e
      · exact False.elim (hold hx)
      · rfl
    have hcases : d = 2 ∧ e = 2 := by
      have hb : (d = 2 ∧ e = 2) ∨ (d = 4 ∧ (e = 1 ∨ e = 2)) ∨
          (d = 5 ∧ e = 1) := by
        simpa [OriginalBinaryAffineFourResidualSteps.unpaidFour,and_assoc,or_assoc] using hbad
      have hp' : ¬((d = 4 ∧ (e = 1 ∨ e = 2)) ∨ (d = 5 ∧ e = 1)) := by
        simpa [unpaidThree,d,and_assoc,or_assoc] using hpaid
      omega
    have ht4 : Fintype.card block.Points = 4 := by
      simpa only [hcases.2,show (2 : ℕ)^2 = 4 by decide] using ht
    exact two_dim_four_blocks J block P hp hcases.1 ht4

theorem exists_generating_finset (hp : P.p = 2) (e : ℕ) (he : 1 ≤ e)
    (ht : Fintype.card block.Points = 2^e) (i : block.Points)
    (hpaid : unpaidThree (translationDimension J block P) e = false)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧
      S.card ≤ traceyPermutationGeneratorCeiling n := by
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G := J)
  exact ⟨S,hgen,hS.le.trans
    (genRank_le_ceiling_outside_three J block P hp e he ht i hpaid htop)⟩

end SymmetricSubgroupAsymptotics.OriginalBinaryAffineThreeResidualSteps
