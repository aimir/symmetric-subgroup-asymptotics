import SymmetricSubgroupAsymptotics.OriginalBinaryAffineSolvableCharacteristicCost
import SymmetricSubgroupAsymptotics.OriginalBinaryAffineThreeResidualSteps

/-! All three remaining pure-binary-top windows are paid when the
ACTUAL complement quotient is solvable. This is a structural branch,
not a claim about nonsolvable complements. The actual original subgroup,
point degree and smaller top are retained, with the same coarse top
ceiling hypothesis as the existing three-residual theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffineSolvableResidualSteps
open OriginalAffineBlockCharacteristicHead OriginalBinaryAffineSolvableCharacteristicCost
open BinaryGeneralLinearPrimeMultiplicity NaturalSquareRootQuotientCeiling

private theorem tracey_ceiling_power (k : ℕ) (hk : 0 < k) :
    traceyPermutationGeneratorCeiling (2^k) = quotientCeiling (2^k) k := by
  have hl : Real.logb 2 ((2 : ℝ)^k) = (k : ℝ) := by
    rw [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one]
  rw [quotientCeiling_eq _ _ hk]
  simp only [traceyPermutationGeneratorCeiling,Nat.cast_pow,Nat.cast_ofNat,hl]

private theorem ceiling_four : traceyPermutationGeneratorCeiling 4 = 3 := by
  rw [show (4 : ℕ) = 2^2 by decide,tracey_ceiling_power 2 (by decide)]
  decide +kernel

private theorem ceiling_thirty_two : traceyPermutationGeneratorCeiling 32 = 15 := by
  rw [show (32 : ℕ) = 2^5 by decide,tracey_ceiling_power 5 (by decide)]
  decide +kernel

private theorem ceiling_sixty_four : traceyPermutationGeneratorCeiling 64 = 27 := by
  rw [show (64 : ℕ) = 2^6 by decide,tracey_ceiling_power 6 (by decide)]
  decide +kernel

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

private theorem two_label_top_rank (ht : Nat.card block.Points = 2) :
    MarkedC4.genRank block.Top ≤ 1 := by
  have hc := Nat.card_le_card_of_injective
    (Subtype.val : block.Top → Equiv.Perm block.Points) Subtype.val_injective
  have hc' : Nat.card block.Top ≤ (Nat.card block.Points).factorial := by
    simpa only [Nat.card_perm] using hc
  have htwo : Nat.card block.Top ≤ 2 := hc'.trans_eq (by rw [ht]; decide)
  exact FiniteGroupBinaryOrderGenerators.genRank_le_of_card_le_two_pow block.Top 1
    (by simpa using htwo)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

private theorem degree_eq_binary_pow (hp : P.p = 2) (e : ℕ)
    (ht : Fintype.card block.Points = 2^e) :
    n = 2^(translationDimension J block P + e) := by
  calc
    n = Nat.card block.Fibre * Nat.card block.Points := by
      simpa only [Nat.card_fin] using block.degree_product.symm
    _ = 2^(translationDimension J block P) * 2^e := by
      rw [fibre_card_eq_prime_pow_dimension J block P,hp,
        show Nat.card block.Points = 2^e by
          simpa only [Fintype.card_eq_nat_card] using ht]
    _ = _ := (pow_add _ _ _).symm

theorem small_residual_genRank_le (hp : P.p = 2) (e : ℕ)
    (ht : Fintype.card block.Points = 2^e) (i : block.Points)
    (hcases : (translationDimension J block P = 4 ∧ (e = 1 ∨ e = 2)) ∨
      (translationDimension J block P = 5 ∧ e = 1))
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points))
    (hsolv : IsSolvable (block.Component ⧸ P.V)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  have hc := genRank_le_solvable_cost J block P hp e ht i hsolv
  have hn := degree_eq_binary_pow J block P hp e ht
  rcases hcases with ⟨hd,he⟩ | ⟨hd,rfl⟩
  · rcases he with rfl | rfl
    · rw [hd] at hc
      simp only [solvablePrimaryCost,GL_four_odd_multiplicity] at hc
      norm_num at hc
      have ht2 : Nat.card block.Points = 2 := by
        simpa only [Fintype.card_eq_nat_card,pow_one] using ht
      have htop1 := two_label_top_rank J block ht2
      have hbound : MarkedC4.genRank J ≤ 15 := by omega
      have hn32 : n = 32 := by simpa only [hd] using hn
      exact hbound.trans_eq
        ((congrArg traceyPermutationGeneratorCeiling hn32).trans ceiling_thirty_two).symm
    · rw [hd] at hc
      simp only [solvablePrimaryCost,GL_four_odd_multiplicity] at hc
      norm_num at hc
      have ht4 : Nat.card block.Points = 4 := by
        simpa only [Fintype.card_eq_nat_card,show (2 : ℕ)^2 = 4 by decide] using ht
      have htop3 : MarkedC4.genRank block.Top ≤ 3 := by
        simpa only [ht4,ceiling_four] using htop
      have hbound : MarkedC4.genRank J ≤ 27 := by omega
      have hn64 : n = 64 := by simpa only [hd] using hn
      exact hbound.trans_eq
        ((congrArg traceyPermutationGeneratorCeiling hn64).trans ceiling_sixty_four).symm
  · rw [hd] at hc
    simp only [solvablePrimaryCost,GL_five_odd_multiplicity] at hc
    norm_num at hc
    have ht2 : Nat.card block.Points = 2 := by
      simpa only [Fintype.card_eq_nat_card,pow_one] using ht
    have htop1 := two_label_top_rank J block ht2
    have hbound : MarkedC4.genRank J ≤ 27 := by omega
    have hn64 : n = 64 := by simpa only [hd] using hn
    exact hbound.trans_eq
      ((congrArg traceyPermutationGeneratorCeiling hn64).trans ceiling_sixty_four).symm

theorem genRank_le_ceiling_of_solvable (hp : P.p = 2) (e : ℕ) (he : 1 ≤ e)
    (ht : Fintype.card block.Points = 2^e) (i : block.Points)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points))
    (hsolv : IsSolvable (block.Component ⧸ P.V)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  by_cases hpaid : OriginalBinaryAffineThreeResidualSteps.unpaidThree
      (translationDimension J block P) e = false
  · exact OriginalBinaryAffineThreeResidualSteps.genRank_le_ceiling_outside_three
      J block P hp e he ht i hpaid htop
  · have hbad : OriginalBinaryAffineThreeResidualSteps.unpaidThree
        (translationDimension J block P) e = true := by
      cases hx : OriginalBinaryAffineThreeResidualSteps.unpaidThree
          (translationDimension J block P) e
      · exact False.elim (hpaid hx)
      · rfl
    have hcases : (translationDimension J block P = 4 ∧ (e = 1 ∨ e = 2)) ∨
        (translationDimension J block P = 5 ∧ e = 1) := by
      simpa [OriginalBinaryAffineThreeResidualSteps.unpaidThree,and_assoc,or_assoc] using hbad
    exact small_residual_genRank_le J block P hp e ht i hcases htop hsolv

theorem exists_generating_finset_of_solvable (hp : P.p = 2) (e : ℕ) (he : 1 ≤ e)
    (ht : Fintype.card block.Points = 2^e) (i : block.Points)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points))
    (hsolv : IsSolvable (block.Component ⧸ P.V)) :
    ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧
      S.card ≤ traceyPermutationGeneratorCeiling n := by
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G := J)
  exact ⟨S,hgen,hS.le.trans (genRank_le_ceiling_of_solvable J block P hp e he ht i htop hsolv)⟩

end SymmetricSubgroupAsymptotics.OriginalBinaryAffineSolvableResidualSteps
