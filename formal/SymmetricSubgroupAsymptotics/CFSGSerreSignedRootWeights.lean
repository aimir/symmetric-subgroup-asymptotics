import SymmetricSubgroupAsymptotics.CFSGSerreGeneratorRelations
import Mathlib.Tactic.Module

/-! Signed Cartan weights and opposite simple brackets in the actual
original rational Serre quotient. Divided-power weights are proved by
Jacobi and induction for arbitrary Cartan data, without finite-type or
representation assumptions. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreSignedRootWeights
open CFSG.Models.Chevalley CFSGSerreLocalNilpotence
variable {n:ℕ} (A:Matrix (Fin n) (Fin n) ℤ)
local notation "L" => RationalLie A

def coroot (neg:Bool) (i:Fin n) : L :=
  if neg then -generator A (.H i) else generator A (.H i)

def oppositeVector (neg:Bool) (i:Fin n) : L := rootVector A (!neg) i

theorem opposite_same (neg:Bool) (i:Fin n) :
    ⁅oppositeVector A neg i,rootVector A neg i⁆= -coroot A neg i := by
  cases neg
  · change ⁅generator A (.F i),generator A (.E i)⁆= -generator A (.H i)
    rw [←lie_skew (generator A (.F i)) (generator A (.E i)),generator_EF_same]
  · change ⁅generator A (.E i),generator A (.F i)⁆= -(-generator A (.H i))
    rw [generator_EF_same,neg_neg]

theorem opposite_distinct (neg:Bool) (i j:Fin n) (hij:i≠j) :
    ⁅oppositeVector A neg i,rootVector A neg j⁆=0 := by
  cases neg
  · change ⁅generator A (.F i),generator A (.E j)⁆=0
    rw [←lie_skew (generator A (.F i)) (generator A (.E j)),generator_EF_ne A j i hij.symm,neg_zero]
  · exact generator_EF_ne A i j hij

theorem coroot_root (neg:Bool) (i j:Fin n) :
    ⁅coroot A neg i,rootVector A neg j⁆=(A i j:ℚ) • rootVector A neg j := by
  cases neg
  · change ⁅generator A (.H i),generator A (.E j)⁆=(A i j:ℚ) • generator A (.E j)
    simpa only [Int.cast_smul_eq_zsmul] using generator_HE A i j
  · change ⁅-generator A (.H i),generator A (.F j)⁆=(A i j:ℚ) • generator A (.F j)
    rw [neg_lie,generator_HF,neg_neg,Int.cast_smul_eq_zsmul]

theorem coroots_commute (neg:Bool) (i j:Fin n) :
    ⁅coroot A neg i,coroot A neg j⁆=0 := by
  cases neg
  · exact generator_HH A i j
  · simpa only [coroot,if_true,neg_lie,lie_neg,neg_neg] using generator_HH A i j

private theorem weight_ad_pow (h x y:L) (a b:ℚ)
    (hx:⁅h,x⁆=a • x) (hy:⁅h,y⁆=b • y) (k:ℕ) :
    ⁅h,(LieAlgebra.ad ℚ L x^k) y⁆=((k:ℚ)*a+b) • (LieAlgebra.ad ℚ L x^k) y := by
  induction k with
  | zero=>simpa only [pow_zero,Module.End.one_apply,Nat.cast_zero,zero_mul,zero_add] using hy
  | succ k ih=>
    rw [pow_succ',Module.End.mul_apply,LieAlgebra.ad_apply,leibniz_lie,hx,ih,smul_lie,lie_smul]
    simp only [Nat.cast_add,Nat.cast_one]
    module

theorem coroot_dividedPower (neg:Bool) (i j:Fin n) (v:L) (b:ℚ)
    (hv:⁅coroot A neg i,v⁆=b • v) (k:ℕ) :
    ⁅coroot A neg i,dividedPower A neg j k v⁆=
      ((k:ℚ)*(A i j:ℚ)+b) • dividedPower A neg j k v := by
  change ⁅coroot A neg i,((k.factorial:ℚ)⁻¹) •
    (LieAlgebra.ad ℚ L (rootVector A neg j)^k) v⁆=_
  rw [lie_smul,weight_ad_pow A _ _ _ (A i j:ℚ) b (coroot_root A neg i j) hv]
  change _=((k:ℚ)*(A i j:ℚ)+b) •
    (((k.factorial:ℚ)⁻¹) • (LieAlgebra.ad ℚ L (rootVector A neg j)^k) v)
  module

end SymmetricSubgroupAsymptotics.CFSGSerreSignedRootWeights
