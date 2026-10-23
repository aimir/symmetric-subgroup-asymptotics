import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalStringWeights

/-! Opposite simple-generator actions on all six original G2 positive
root vectors. These are literal Jacobi/Serre computations over Q, for
both signs, with coefficients 3,2,1 on the short string. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalSimpleLowering
open CFSGGTwoOriginalPositiveSerreStrings CFSGGTwoOriginalStringWeights
open CFSG.Models.Chevalley
local notation "A" => CartanMatrix.G₂
local notation "L" => RationalLie A

private theorem short_same (neg : Bool) :
    ⁅oppositeVector neg 0,shortVector neg⁆= -coroot neg 0 := opposite_same neg 0
private theorem short_long (neg : Bool) : ⁅oppositeVector neg 0,longVector neg⁆=0 :=
  opposite_distinct neg 0 1 (by decide)
private theorem long_short (neg : Bool) : ⁅oppositeVector neg 1,shortVector neg⁆=0 :=
  opposite_distinct neg 1 0 (by decide)
private theorem long_same (neg : Bool) :
    ⁅oppositeVector neg 1,longVector neg⁆= -coroot neg 1 := opposite_same neg 1

theorem opposite_short_string_one (neg : Bool) :
    ⁅oppositeVector neg 0,stringVector neg 1⁆=(3:ℚ) • longVector neg := by
  have hw : ⁅coroot neg 0,longVector neg⁆=(A 0 1:ℚ) • longVector neg := coroot_simple neg 0 1
  rw [string_one,leibniz_lie,short_same,short_long,neg_lie,hw,lie_zero,add_zero]
  norm_num [CartanMatrix.G₂] <;> module

theorem opposite_short_string_two (neg : Bool) :
    ⁅oppositeVector neg 0,stringVector neg 2⁆=(2:ℚ) • stringVector neg 1 := by
  have he := congrArg (fun v:L=>⁅oppositeVector neg 0,v⁆) (short_string_one neg)
  dsimp only at he
  rw [leibniz_lie,short_same,neg_lie,coroot_string neg 0 1,
    opposite_short_string_one,lie_smul,←string_one,lie_smul] at he
  norm_num [CartanMatrix.G₂] at he
  apply smul_right_injective L (by norm_num : (2:ℚ)≠0)
  exact he.symm.trans (by module)

theorem opposite_short_string_three (neg : Bool) :
    ⁅oppositeVector neg 0,stringVector neg 3⁆=stringVector neg 2 := by
  have he := congrArg (fun v:L=>⁅oppositeVector neg 0,v⁆) (short_string_two neg)
  dsimp only at he
  rw [leibniz_lie,short_same,neg_lie,coroot_string neg 0 2,
    opposite_short_string_two,lie_smul,short_string_one,lie_smul] at he
  norm_num [CartanMatrix.G₂] at he
  apply smul_right_injective L (by norm_num : (3:ℚ)≠0)
  exact he.symm.trans (by module)

theorem opposite_short_highest (neg : Bool) : ⁅oppositeVector neg 0,highestVector neg⁆=0 := by
  rw [highestVector,leibniz_lie,short_long,opposite_short_string_three,zero_lie,long_string_two,zero_add]

theorem opposite_long_string_one (neg : Bool) :
    ⁅oppositeVector neg 1,stringVector neg 1⁆= -shortVector neg := by
  have hw : ⁅coroot neg 1,shortVector neg⁆=(A 1 0:ℚ) • shortVector neg := coroot_simple neg 1 0
  rw [string_one,leibniz_lie,long_short,long_same,zero_lie,zero_add,lie_neg,
    ←lie_skew (shortVector neg) (coroot neg 1),neg_neg,hw]
  norm_num [CartanMatrix.G₂] <;> module

theorem opposite_long_string_two (neg : Bool) : ⁅oppositeVector neg 1,stringVector neg 2⁆=0 := by
  have he := congrArg (fun v:L=>⁅oppositeVector neg 1,v⁆) (short_string_one neg)
  dsimp only at he
  rw [leibniz_lie,long_short,zero_lie,opposite_long_string_one,lie_neg,lie_self,neg_zero,
    zero_add,lie_smul] at he
  apply smul_right_injective L (by norm_num : (2:ℚ)≠0)
  simpa only [smul_zero] using he.symm

theorem opposite_long_string_three (neg : Bool) : ⁅oppositeVector neg 1,stringVector neg 3⁆=0 := by
  have he := congrArg (fun v:L=>⁅oppositeVector neg 1,v⁆) (short_string_two neg)
  dsimp only at he
  rw [leibniz_lie,long_short,zero_lie,opposite_long_string_two,lie_zero,zero_add,lie_smul] at he
  apply smul_right_injective L (by norm_num : (3:ℚ)≠0)
  simpa only [smul_zero] using he.symm

theorem opposite_long_highest (neg : Bool) :
    ⁅oppositeVector neg 1,highestVector neg⁆=stringVector neg 3 := by
  rw [highestVector,leibniz_lie,long_same,neg_lie,coroot_string neg 1 3,
    opposite_long_string_three,lie_zero,add_zero]
  norm_num [CartanMatrix.G₂]

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalSimpleLowering
