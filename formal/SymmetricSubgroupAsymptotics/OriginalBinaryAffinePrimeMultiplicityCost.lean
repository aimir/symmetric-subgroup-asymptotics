import SymmetricSubgroupAsymptotics.ActualWreathChiefPrimeMultiplicityBudget
import SymmetricSubgroupAsymptotics.OriginalBinaryAffineJointCharacteristicCost

/-! Joint prime-multiplicity costs on the ORIGINAL binary affine block
component. The quotient order divides its literal faithful GL order; its
actual chief trace is used, including all nonabelian selected factors.
No solvability or CFSG model hypothesis is imposed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffinePrimeMultiplicityCost
open OriginalAffineBlockCharacteristicHead ActualWreathChiefPrimeMultiplicityBudget

def primeMultiplicityCost (d e : ℕ) : ℕ :=
  d*e.choose (e/2) + (d*(d-1)/2)*(e.choose (e/2)-1) +
    ArithmeticFunction.cardFactors
      (Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2)))

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

theorem translation_tail_cost_le (e : ℕ)
    (ht : Fintype.card block.Points = 2^e) (i : block.Points) {c : ℕ}
    (hc : ActualWreathOrdinaryChiefRecurrence.ChiefCost i (quotientState J block P) c) :
    c ≤ binaryOrderCost (Nat.card (block.Component ⧸ P.V)) e := by
  have hI : 2 ≤ Fintype.card block.Points := by
    simpa only [Fintype.card_eq_nat_card] using block.degrees_ge_two.2
  exact cost_le_binaryOrderCost hc hI e ht

theorem genRank_le_primeMultiplicityCost (hp : P.p = 2) (e : ℕ)
    (ht : Fintype.card block.Points = 2^e) (i : block.Points) :
    MarkedC4.genRank J ≤ primeMultiplicityCost (translationDimension J block P) e +
      MarkedC4.genRank block.Top := by
  let d := translationDimension J block P
  obtain ⟨c,hc,_,hhead,hrank⟩ := exists_translation_head_and_tail J block P i
  have htail := translation_tail_cost_le J block P e ht i hc
  have hdvd := OriginalBinaryAffineJointCharacteristicCost.translation_quotient_card_dvd_GL
    J block P hp
  have hGL := htail.trans (binaryOrderCost_mono_of_dvd
    (Nat.card_pos (α := block.Component ⧸ P.V)).ne'
    (Nat.card_pos (α := Matrix.GeneralLinearGroup (Fin d) (ZMod 2))).ne' hdvd e)
  have hheadCost := (headCharge J block P i).primePower 2 e Nat.prime_two ht
  simp only [show 2-1 = (1 : ℕ) by omega,mul_one,headCharge_dimension] at hheadCost
  have htR : (Fintype.card block.Points : ℝ) = (2 : ℝ)^e := by exact_mod_cast ht
  have cancel (a b : ℝ) : a*(2 : ℝ)^e*b/(2 : ℝ)^e = a*b := by
    rw [mul_right_comm,mul_div_cancel_right₀ _ (by positivity : (2 : ℝ)^e ≠ 0)]
  rw [htR,cancel] at hheadCost
  have hheadNat : (headCharge J block P i).capacity ≤ d*e.choose (e/2) := by
    exact_mod_cast hheadCost
  have hh := hrank.trans (Nat.add_le_add_right (Nat.add_le_add hheadNat hGL) _)
  have heq : d*e.choose (e/2) +
      binaryOrderCost (Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2))) e =
        primeMultiplicityCost d e := by
    simp only [binaryOrderCost,primeMultiplicityCost,
      PrimeGeneralLinearDefiningValuation.matrix_GL_defining_factorization 2 d Nat.prime_two]
    omega
  exact hh.trans_eq (congrArg (fun k : ℕ => k + MarkedC4.genRank block.Top) heq)

theorem exists_generating_finset (hp : P.p = 2) (e : ℕ)
    (ht : Fintype.card block.Points = 2^e) (i : block.Points) :
    ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧
      S.card ≤ primeMultiplicityCost (translationDimension J block P) e +
        MarkedC4.genRank block.Top := by
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G := J)
  exact ⟨S,hgen,hS.le.trans (genRank_le_primeMultiplicityCost J block P hp e ht i)⟩

end SymmetricSubgroupAsymptotics.OriginalBinaryAffinePrimeMultiplicityCost
