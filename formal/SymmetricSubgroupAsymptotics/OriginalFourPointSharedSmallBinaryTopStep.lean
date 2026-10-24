import SymmetricSubgroupAsymptotics.OriginalFourPointSharedTwoDivisorCost
import SymmetricSubgroupAsymptotics.FourPointSharedSmallBinaryTopCeiling

/-! The original four-point shared-head family t=3*2^a at the small
exponents. Both divisors belong to the actual top degree; no claim that
the binary divisor is dominant is needed or imposed. The only inductive
generation input is the actual smaller-top coarse ceiling. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalFourPointSharedSmallBinaryTopStep
open OriginalAffineBlockCharacteristicHead

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

theorem genRank_le_ceiling_of_three_mul_binary (hp : P.p = 2)
    (hdim : translationDimension J block P = 2) (i : block.Points)
    (a : ℕ) (ha1 : 1 ≤ a) (ha5 : a ≤ 5)
    (hshape : Fintype.card block.Points = 3*2^a)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  have hfour : Nat.card block.Fibre = 4 := by
    calc
      Nat.card block.Fibre = P.p^translationDimension J block P :=
        fibre_card_eq_prime_pow_dimension J block P
      _ = 2^translationDimension J block P :=
        congrArg (fun p : ℕ => p^translationDimension J block P) hp
      _ = 2^(2 : ℕ) := congrArg (fun d : ℕ => 2^d) hdim
      _ = 4 := by decide
  have h2 : 2^a ∣ Fintype.card block.Points := by
    rw [hshape]
    exact ⟨3,by ring⟩
  have h3 : 3 ∣ Fintype.card block.Points := by
    rw [hshape]
    exact dvd_mul_right 3 (2^a)
  have hh := OriginalFourPointSharedTwoDivisorCost.genRank_le_five_sixths_add_primeTo
    J block P hfour hp hdim i a h2 h3
  have htopR : (MarkedC4.genRank block.Top : ℝ) ≤
      (traceyPermutationGeneratorCeiling (Fintype.card block.Points) : ℝ) := by
    exact_mod_cast (show MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Fintype.card block.Points) by
        simpa only [Fintype.card_eq_nat_card] using htop)
  have hcost := hh.trans (add_le_add le_rfl htopR)
  rw [hshape] at hcost
  have hfinal := FourPointSharedSmallBinaryTopCeiling.aggregate_small a (MarkedC4.genRank J) ha1 ha5 hcost
  have hn : n = 12*2^a := by
    calc
      n = Nat.card block.Fibre*Nat.card block.Points := by
        simpa only [Nat.card_fin] using block.degree_product.symm
      _ = 4*Fintype.card block.Points := by
        rw [hfour]
        simp only [Fintype.card_eq_nat_card]
      _ = 12*2^a := by rw [hshape]; ring
  simpa only [hn] using hfinal

end SymmetricSubgroupAsymptotics.OriginalFourPointSharedSmallBinaryTopStep
