import SymmetricSubgroupAsymptotics.OriginalBinaryBoundedSharpStep
import SymmetricSubgroupAsymptotics.OriginalTernaryBoundedSharpStep
import SymmetricSubgroupAsymptotics.OriginalFourPointBoundedSharpStep
import SymmetricSubgroupAsymptotics.OriginalAffineFiveSevenBoundedSharpStep
import SymmetricSubgroupAsymptotics.OriginalAffineNineBoundedSharpStep

/-! Bounded ORIGINAL affine minimal-block sharp reduction. Literal
prime-power local-degree arithmetic leaves sizes2/3/4/5/7/8/9. Their
actual correlated chief/kernel consumers pay every total degree below22
except the coupled degree16 shapes, or return a precise global minimal
primitive sporadic failed action of degree at most10. The latter witness
is not asserted to be a subquotient. No sharp/half/global Tracey/MN input,
action catalogue, or local capacity certificate is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpCFSGReduction
open OriginalAffineBlockCharacteristicHead TraceySharpHalfDegreeNumerics
open EightPointHalfDegreeFiniteModelReduction

private theorem prime_le_ten_cases (p : ℕ) (hp : p.Prime) (hlo : 2 ≤ p) (hhi : p ≤ 10) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
  interval_cases p <;> norm_num at hp <;> norm_num

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]
local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by have h := block.degrees_ge_two.1; omega)
variable (P : PrimitiveAffineProfile block.Component block.Fibre)

include P in
theorem affine_fibre_cases (hsmall : n < 22) :
    Nat.card block.Fibre = 2 ∨ Nat.card block.Fibre = 3 ∨ Nat.card block.Fibre = 4 ∨
      Nat.card block.Fibre = 5 ∨ Nat.card block.Fibre = 7 ∨ Nat.card block.Fibre = 8 ∨
        Nat.card block.Fibre = 9 := by
  have hproduct : Nat.card block.Fibre*Nat.card block.Points = n := by
    simpa only [Nat.card_fin] using block.degree_product
  have hr2 := block.degrees_ge_two.1
  have ht2 := block.degrees_ge_two.2
  have hr10 : Nat.card block.Fibre ≤ 10 := by nlinarith only [hproduct,hr2,ht2,hsmall]
  by_cases h2 : Nat.card block.Fibre = 2
  · exact Or.inl h2
  by_cases h3 : Nat.card block.Fibre = 3
  · exact Or.inr (Or.inl h3)
  have hr4 : 4 ≤ Nat.card block.Fibre := by omega
  have he := fibre_card_eq_prime_pow_dimension J block P
  rcases PrimitiveBoundedSharpCFSGReduction.prime_power_band P.p
    (translationDimension J block P) (Nat.card block.Fibre) P.p_prime he hr4 (by omega) with
      hp | h4 | h8 | h9 | h16
  · have hc := prime_le_ten_cases (Nat.card block.Fibre) hp hr2 hr10
    omega
  · omega
  · omega
  · omega
  · omega

include P in
theorem genRank_le_sharpFloor_or_sixteen_or_sporadic_counterexample
    (hCFSG : CFSG.CFSGClassification) (hsmall : n < 22) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ n = 16 ∨
      Nonempty (PrimitiveSporadicCounterexample 10) := by
  rcases affine_fibre_cases J block P hsmall with h2 | h3 | h4 | h5 | h7 | h8 | h9
  · exact OriginalBinaryBoundedSharpStep.genRank_le_sharpFloor_or_sixteen_or_sporadic_counterexample
      J block hCFSG h2 hsmall
  · rcases OriginalTernaryBoundedSharpStep.genRank_le_sharpFloor_or_sporadic_counterexample
      J block hCFSG h3 hsmall with hpaid | hbad
    · exact Or.inl hpaid
    · exact Or.inr (Or.inr (EightPointFaithfulActionHalfDegreeReduction.counterexample_mono
        (by decide : 8 ≤ 10) hbad))
  · exact OriginalFourPointBoundedSharpStep.genRank_le_sharpFloor_or_sixteen_or_sporadic_counterexample
      J block P hCFSG h4 hsmall
  · exact Or.inl (OriginalAffineFiveSevenBoundedSharpStep.genRank_le_sharpFloor J block P (Or.inl h5) hsmall)
  · exact Or.inl (OriginalAffineFiveSevenBoundedSharpStep.genRank_le_sharpFloor J block P (Or.inr h7) hsmall)
  · have hproduct : 8*Nat.card block.Points = n := by
      simpa only [h8,Nat.card_fin] using block.degree_product
    have ht := block.degrees_ge_two.2
    exact Or.inr (Or.inl (by omega))
  · rcases OriginalAffineNineBoundedSharpStep.genRank_le_sharpFloor_or_sporadic_counterexample
      J block P hCFSG h9 hsmall with hpaid | hbad
    · exact Or.inl hpaid
    · exact Or.inr (Or.inr (EightPointFaithfulActionHalfDegreeReduction.counterexample_mono
        (by decide : 8 ≤ 10) hbad))

include P in
theorem exists_generating_finset_or_sixteen_or_sporadic_counterexample
    (hCFSG : CFSG.CFSGClassification) (hsmall : n < 22) :
    (∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧ S.card ≤ sharpFloor n) ∨ n = 16 ∨
      Nonempty (PrimitiveSporadicCounterexample 10) := by
  rcases genRank_le_sharpFloor_or_sixteen_or_sporadic_counterexample J block P hCFSG hsmall with hpaid | h16 | hbad
  · obtain ⟨S,hcard,hgen⟩ := MarkedC4.genRank_spec (G := J)
    exact Or.inl ⟨S,hgen,hcard.le.trans hpaid⟩
  · exact Or.inr (Or.inl h16)
  · exact Or.inr (Or.inr hbad)

end SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpCFSGReduction
