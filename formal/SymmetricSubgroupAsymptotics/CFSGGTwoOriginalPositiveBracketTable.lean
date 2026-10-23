import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalPositiveSerreStrings
import Mathlib.Tactic.FinCases

/-! Completion of the six-positive-root bracket table in the literal
original rational Serre quotient. The highest vector is central in the
positive algebra; no matrix basis or representation faithfulness is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalPositiveBracketTable
open CFSGGTwoOriginalPositiveSerreStrings CFSG.Models.Chevalley
local notation "A" => CartanMatrix.G₂
local notation "L" => RationalLie A

private theorem short_highest_eq (neg : Bool) :
    ⁅shortVector neg,highestVector neg⁆=⁅stringVector neg 1,stringVector neg 3⁆ := by
  rw [highestVector,leibniz_lie,←string_one,short_string_three,lie_zero,add_zero]

theorem short_highest_zero (neg : Bool) : ⁅shortVector neg,highestVector neg⁆=0 := by
  have he := congrArg (fun v:L=>⁅shortVector neg,v⁆) (string_one_two neg)
  dsimp only at he
  rw [leibniz_lie,short_string_one,short_string_two,smul_lie,lie_smul,lie_self,
    smul_zero,zero_add,lie_smul,←short_highest_eq] at he
  have hz : (6:ℚ) • ⁅shortVector neg,highestVector neg⁆=0 := by
    calc
      _=(3:ℚ) • ⁅shortVector neg,highestVector neg⁆ -
          (-3:ℚ) • ⁅shortVector neg,highestVector neg⁆ := by module
      _=0 := sub_eq_zero.mpr he
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

theorem string_one_three_zero (neg : Bool) : ⁅stringVector neg 1,stringVector neg 3⁆=0 := by
  rw [←short_highest_eq,short_highest_zero]

theorem long_highest_zero (neg : Bool) : ⁅longVector neg,highestVector neg⁆=0 := by
  have he := congrArg (fun v:L=>⁅longVector neg,v⁆) (string_one_two neg)
  dsimp only at he
  rw [leibniz_lie,long_string_one,long_string_two,zero_lie,lie_zero,zero_add,lie_smul] at he
  exact (smul_eq_zero.mp he.symm).resolve_left (by norm_num)

theorem string_highest_zero (neg : Bool) (k : ℕ) : ⁅stringVector neg k,highestVector neg⁆=0 := by
  have hpow (j:ℕ) : ⁅(LieAlgebra.ad ℚ L (shortVector neg)^j) (longVector neg),highestVector neg⁆=0 := by
    induction j with
    | zero => simpa only [pow_zero,Module.End.one_apply] using long_highest_zero neg
    | succ j ih =>
      rw [pow_succ',Module.End.mul_apply,LieAlgebra.ad_apply,lie_lie,ih,short_highest_zero,
        lie_zero,lie_zero,sub_self]
  change ⁅((k.factorial:ℚ)⁻¹) • (LieAlgebra.ad ℚ L (shortVector neg)^k) (longVector neg),highestVector neg⁆=0
  rw [smul_lie,hpow,smul_zero]

theorem string_two_three_zero (neg : Bool) : ⁅stringVector neg 2,stringVector neg 3⁆=0 := by
  have he := congrArg (fun v:L=>⁅shortVector neg,v⁆) (string_one_three_zero neg)
  dsimp only at he
  rw [lie_zero,leibniz_lie,short_string_one,short_string_three,smul_lie,lie_zero,add_zero] at he
  exact (smul_eq_zero.mp he).resolve_left (by norm_num)

/-- Ordered roots: alpha, beta, alpha+beta, 2alpha+beta,
3alpha+beta, 3alpha+2beta, with the original divided-power signs. -/
def positiveVector (neg : Bool) (i : Fin 6) : L :=
  match i.val with
  | 0 => shortVector neg
  | 1 => longVector neg
  | 2 => stringVector neg 1
  | 3 => stringVector neg 2
  | 4 => stringVector neg 3
  | _ => highestVector neg

def positiveSpace (neg : Bool) : Submodule ℚ L :=
  Submodule.span ℚ (Set.range (positiveVector neg))

theorem short_vector_mem (neg : Bool) : shortVector neg∈positiveSpace neg :=
  Submodule.subset_span ⟨0,rfl⟩

theorem long_vector_mem (neg : Bool) : longVector neg∈positiveSpace neg :=
  Submodule.subset_span ⟨1,rfl⟩

theorem string_vector_mem (neg : Bool) (i : Fin 3) : stringVector neg (i.val+1)∈positiveSpace neg := by
  fin_cases i
  · exact Submodule.subset_span ⟨2,rfl⟩
  · exact Submodule.subset_span ⟨3,rfl⟩
  · exact Submodule.subset_span ⟨4,rfl⟩

theorem highest_vector_mem (neg : Bool) : highestVector neg∈positiveSpace neg :=
  Submodule.subset_span ⟨5,rfl⟩

theorem short_preserves_positiveSpace (neg : Bool) :
    ∀v∈positiveSpace neg,⁅shortVector neg,v⁆∈positiveSpace neg := by
  apply Submodule.span_induction
  · rintro _ ⟨i,rfl⟩
    fin_cases i
    · change ⁅shortVector neg,shortVector neg⁆∈positiveSpace neg
      rw [lie_self]
      exact (positiveSpace neg).zero_mem
    · change ⁅shortVector neg,longVector neg⁆∈positiveSpace neg
      rw [←string_one]
      exact string_vector_mem neg 0
    · change ⁅shortVector neg,stringVector neg 1⁆∈positiveSpace neg
      rw [short_string_one]
      exact (positiveSpace neg).smul_mem (2:ℚ) (string_vector_mem neg 1)
    · change ⁅shortVector neg,stringVector neg 2⁆∈positiveSpace neg
      rw [short_string_two]
      exact (positiveSpace neg).smul_mem (3:ℚ) (string_vector_mem neg 2)
    · change ⁅shortVector neg,stringVector neg 3⁆∈positiveSpace neg
      rw [short_string_three]
      exact (positiveSpace neg).zero_mem
    · change ⁅shortVector neg,highestVector neg⁆∈positiveSpace neg
      rw [short_highest_zero]
      exact (positiveSpace neg).zero_mem
  · simpa only [lie_zero] using (positiveSpace neg).zero_mem
  · intro x y _ _ hx hy
    rw [lie_add]
    exact (positiveSpace neg).add_mem hx hy
  · intro c x _ hx
    rw [lie_smul]
    exact (positiveSpace neg).smul_mem c hx


theorem long_preserves_positiveSpace (neg : Bool) :
    ∀v∈positiveSpace neg,⁅longVector neg,v⁆∈positiveSpace neg := by
  apply Submodule.span_induction
  · rintro _ ⟨i,rfl⟩
    fin_cases i
    · change ⁅longVector neg,shortVector neg⁆∈positiveSpace neg
      rw [←lie_skew (longVector neg) (shortVector neg),←string_one]
      exact (positiveSpace neg).neg_mem (string_vector_mem neg 0)
    · change ⁅longVector neg,longVector neg⁆∈positiveSpace neg
      rw [lie_self]
      exact (positiveSpace neg).zero_mem
    · change ⁅longVector neg,stringVector neg 1⁆∈positiveSpace neg
      rw [long_string_one]
      exact (positiveSpace neg).zero_mem
    · change ⁅longVector neg,stringVector neg 2⁆∈positiveSpace neg
      rw [long_string_two]
      exact (positiveSpace neg).zero_mem
    · change ⁅longVector neg,stringVector neg 3⁆∈positiveSpace neg
      exact highest_vector_mem neg
    · change ⁅longVector neg,highestVector neg⁆∈positiveSpace neg
      rw [long_highest_zero]
      exact (positiveSpace neg).zero_mem
  · simpa only [lie_zero] using (positiveSpace neg).zero_mem
  · intro x y _ _ hx hy
    rw [lie_add]
    exact (positiveSpace neg).add_mem hx hy
  · intro c x _ hx
    rw [lie_smul]
    exact (positiveSpace neg).smul_mem c hx

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalPositiveBracketTable
