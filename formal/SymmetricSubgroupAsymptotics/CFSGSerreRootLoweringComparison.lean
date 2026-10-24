import SymmetricSubgroupAsymptotics.CFSGSerrePositiveLowestWeight

/-! Sparse comparison of genuine original source root expressions.
Equal positive weights and one equal opposite lowering imply equality.
The simple raising/lowering identity reduces the lowering of a new
bracket to smaller-height brackets by Jacobi. No matrix representation
or source faithfulness hypothesis enters either statement. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreRootLoweringComparison
open CFSG.Models.Chevalley CFSGSerreSignedRootWeights CFSGSerrePositiveLowestWeight
variable {r:ℕ} (A:Matrix (Fin r) (Fin r) ℤ)
local notation "L" => RationalLie A

theorem eq_of_positive_weight_of_opposite_eq (neg:Bool) (i:Fin r)
    (hii:A i i=2) (v w:L) (mu:ℚ) (hmu:0<mu)
    (hv:⁅coroot A neg i,v⁆=mu • v)
    (hw:⁅coroot A neg i,w⁆=mu • w)
    (hl:⁅oppositeVector A neg i,v⁆=⁅oppositeVector A neg i,w⁆) : v=w := by
  apply sub_eq_zero.mp
  apply eq_zero_of_positive_weight_of_opposite_zero A neg i hii (v-w) mu hmu
  · rw [lie_sub,hv,hw,smul_sub]
  · rw [lie_sub,hl,sub_self]

theorem opposite_raising (neg:Bool) (i j:Fin r) (v:L) (mu:ℚ)
    (hv:⁅coroot A neg j,v⁆=mu • v) :
    ⁅oppositeVector A neg j,⁅rootVector A neg i,v⁆⁆=
      (if j=i then -(mu • v) else 0)+
        ⁅rootVector A neg i,⁅oppositeVector A neg j,v⁆⁆ := by
  by_cases hji:j=i
  · subst j
    rw [leibniz_lie,opposite_same,neg_lie,hv,if_pos rfl]
  · rw [leibniz_lie,opposite_distinct A neg j i hji,zero_lie,if_neg hji]

end SymmetricSubgroupAsymptotics.CFSGSerreRootLoweringComparison
