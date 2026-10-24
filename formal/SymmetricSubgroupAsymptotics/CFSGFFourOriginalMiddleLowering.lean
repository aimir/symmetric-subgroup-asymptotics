import SymmetricSubgroupAsymptotics.CFSGFFourOriginalMiddleSerreStrings
import SymmetricSubgroupAsymptotics.CFSGSerreSignedRootWeights

/-! Opposite simple lowering on the original F4 middle B2 string.
All equations are in the same rational Serre quotient. In particular,
the top divided vector lowers with coefficient one, before any
characteristic-two base change. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalMiddleLowering
open CFSGFFourOriginalMiddleSerreStrings CFSGSerreSignedRootWeights
open CFSG.Models.Chevalley
local notation "A" => CartanMatrix.F₄
local notation "L" => RationalLie A

private theorem middle_short_long : A (1:Fin 4) 2= -2 := rfl
private theorem middle_long_short : A (2:Fin 4) 1= -1 := rfl

theorem coroot_string (neg:Bool) (i:Fin 4) (k:ℕ) :
    ⁅coroot A neg i,stringVector neg k⁆=
      ((k:ℚ)*(A i 1:ℚ)+(A i 2:ℚ)) • stringVector neg k :=
  coroot_dividedPower A neg i 1 (longVector neg) (A i 2:ℚ)
    (coroot_root A neg i 2) k

theorem opposite_short_string_one (neg:Bool) :
    ⁅oppositeVector A neg 1,stringVector neg 1⁆=(2:ℚ) • longVector neg := by
  have hw:⁅coroot A neg 1,longVector neg⁆=(-2:ℚ) • longVector neg := by
    simpa only [middle_short_long,Int.cast_neg,Int.cast_ofNat] using coroot_root A neg 1 2
  have hs:⁅oppositeVector A neg 1,shortVector neg⁆= -coroot A neg 1:=opposite_same A neg 1
  have hl:⁅oppositeVector A neg 1,longVector neg⁆=0:=opposite_distinct A neg 1 2 (by decide)
  rw [string_one,leibniz_lie,hs,hl,neg_lie,hw,lie_zero,add_zero]
  module

theorem opposite_short_string_two (neg:Bool) :
    ⁅oppositeVector A neg 1,stringVector neg 2⁆=stringVector neg 1 := by
  have hw:⁅coroot A neg 1,stringVector neg 1⁆=0 := by
    have h:=coroot_string neg (1:Fin 4) 1
    simpa only [Nat.cast_one,CartanMatrix.F₄_diag,middle_short_long,Int.cast_neg,
      Int.cast_ofNat,one_mul,add_neg_cancel,zero_smul] using h
  have hs:⁅oppositeVector A neg 1,shortVector neg⁆= -coroot A neg 1:=opposite_same A neg 1
  have he:=congrArg (fun v:L=>⁅oppositeVector A neg 1,v⁆) (short_string_one neg)
  dsimp only at he
  rw [leibniz_lie,hs,neg_lie,hw,opposite_short_string_one,lie_smul,
    ←string_one,neg_zero,zero_add,lie_smul] at he
  exact (smul_right_injective L (by norm_num : (2:ℚ)≠0)) he.symm

theorem opposite_long_string_one (neg:Bool) :
    ⁅oppositeVector A neg 2,stringVector neg 1⁆= -shortVector neg := by
  have hw:⁅coroot A neg 2,shortVector neg⁆=(-1:ℚ) • shortVector neg := by
    simpa only [middle_long_short,Int.cast_neg,Int.cast_one] using coroot_root A neg 2 1
  have hs:⁅oppositeVector A neg 2,shortVector neg⁆=0:=opposite_distinct A neg 2 1 (by decide)
  have hl:⁅oppositeVector A neg 2,longVector neg⁆= -coroot A neg 2:=opposite_same A neg 2
  rw [string_one,leibniz_lie,hs,hl,zero_lie,zero_add,lie_neg,
    ←lie_skew (shortVector neg) (coroot A neg 2),neg_neg,hw,neg_one_smul]

theorem opposite_long_string_two (neg:Bool) :
    ⁅oppositeVector A neg 2,stringVector neg 2⁆=0 := by
  have hs:⁅oppositeVector A neg 2,shortVector neg⁆=0:=opposite_distinct A neg 2 1 (by decide)
  have he:=congrArg (fun v:L=>⁅oppositeVector A neg 2,v⁆) (short_string_one neg)
  dsimp only at he
  rw [leibniz_lie,hs,zero_lie,opposite_long_string_one,lie_neg,lie_self,neg_zero,
    zero_add,lie_smul] at he
  apply smul_right_injective L (by norm_num : (2:ℚ)≠0)
  simpa only [smul_zero] using he.symm

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalMiddleLowering
