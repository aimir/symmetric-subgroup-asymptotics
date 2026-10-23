import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalPositiveSerreStrings

/-! Actual Cartan weights and opposite simple brackets for the original
G2 six-root strings. Negating the Cartan vector when signs are reversed
keeps the SAME Serre normalization on both halves. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalStringWeights
open CFSGGTwoOriginalPositiveSerreStrings CFSG.Models.Chevalley CFSGSerreLocalNilpotence
local notation "A" => CartanMatrix.G₂
local notation "L" => RationalLie A

def coroot (neg : Bool) (i : Fin 2) : L :=
  if neg then -generator A (.H i) else generator A (.H i)

def oppositeVector (neg : Bool) (i : Fin 2) : L := rootVector A (!neg) i

theorem opposite_same (neg : Bool) (i : Fin 2) :
    ⁅oppositeVector neg i,rootVector A neg i⁆= -coroot neg i := by
  cases neg
  · change ⁅generator A (.F i),generator A (.E i)⁆= -generator A (.H i)
    rw [←lie_skew (generator A (.F i)) (generator A (.E i)),generator_EF_same]
  · change ⁅generator A (.E i),generator A (.F i)⁆= -(-generator A (.H i))
    rw [generator_EF_same,neg_neg]

theorem opposite_distinct (neg : Bool) (i j : Fin 2) (hij : i≠j) :
    ⁅oppositeVector neg i,rootVector A neg j⁆=0 := by
  cases neg
  · change ⁅generator A (.F i),generator A (.E j)⁆=0
    rw [←lie_skew (generator A (.F i)) (generator A (.E j)),generator_EF_ne A j i hij.symm,neg_zero]
  · exact generator_EF_ne A i j hij

theorem coroot_simple (neg : Bool) (i j : Fin 2) :
    ⁅coroot neg i,rootVector A neg j⁆=(A i j : ℚ) • rootVector A neg j := by
  cases neg
  · change ⁅generator A (.H i),generator A (.E j)⁆=(A i j : ℚ) • generator A (.E j)
    simpa only [Int.cast_smul_eq_zsmul] using generator_HE A i j
  · change ⁅-generator A (.H i),generator A (.F j)⁆=(A i j : ℚ) • generator A (.F j)
    rw [neg_lie,generator_HF,neg_neg,Int.cast_smul_eq_zsmul]

theorem coroots_commute (neg : Bool) (i j : Fin 2) : ⁅coroot neg i,coroot neg j⁆=0 := by
  cases neg
  · exact generator_HH A i j
  · simpa only [coroot,if_true,neg_lie,lie_neg,neg_neg] using generator_HH A i j

private theorem weight_ad_pow (h x y : L) (a b : ℚ)
    (hx : ⁅h,x⁆=a • x) (hy : ⁅h,y⁆=b • y) (k : ℕ) :
    ⁅h,(LieAlgebra.ad ℚ L x^k) y⁆=((k:ℚ)*a+b) • (LieAlgebra.ad ℚ L x^k) y := by
  induction k with
  | zero => simpa only [pow_zero,Module.End.one_apply,Nat.cast_zero,zero_mul,zero_add] using hy
  | succ k ih =>
    rw [pow_succ',Module.End.mul_apply,LieAlgebra.ad_apply,leibniz_lie,hx,ih,smul_lie,lie_smul]
    simp only [Nat.cast_add,Nat.cast_one]
    module

theorem coroot_string (neg : Bool) (i : Fin 2) (k : ℕ) :
    ⁅coroot neg i,stringVector neg k⁆=
      ((k:ℚ)*(A i 0 : ℚ)+(A i 1 : ℚ)) • stringVector neg k := by
  change ⁅coroot neg i,((k.factorial:ℚ)⁻¹) •
      (LieAlgebra.ad ℚ L (shortVector neg)^k) (longVector neg)⁆=_
  have hx : ⁅coroot neg i,shortVector neg⁆=(A i 0 : ℚ) • shortVector neg := coroot_simple neg i 0
  have hy : ⁅coroot neg i,longVector neg⁆=(A i 1 : ℚ) • longVector neg := coroot_simple neg i 1
  rw [lie_smul,weight_ad_pow (coroot neg i) (shortVector neg) (longVector neg)
    (A i 0 : ℚ) (A i 1 : ℚ) hx hy]
  change _=((k:ℚ)*(A i 0 : ℚ)+(A i 1 : ℚ)) •
    (((k.factorial:ℚ)⁻¹) • (LieAlgebra.ad ℚ L (shortVector neg)^k) (longVector neg))
  module

theorem coroot_highest (neg : Bool) (i : Fin 2) :
    ⁅coroot neg i,highestVector neg⁆=
      ((3:ℚ)*(A i 0 : ℚ)+(2:ℚ)*(A i 1 : ℚ)) • highestVector neg := by
  have hy : ⁅coroot neg i,longVector neg⁆=(A i 1 : ℚ) • longVector neg := coroot_simple neg i 1
  rw [highestVector,leibniz_lie,hy,coroot_string,smul_lie,lie_smul]
  module

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalStringWeights
