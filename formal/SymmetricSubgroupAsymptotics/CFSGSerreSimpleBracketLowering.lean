import SymmetricSubgroupAsymptotics.CFSGSerreSignedRootWeights

/-! Exact opposite lowering and Cartan weight of a bracket of two
signed original simple generators. These are quotient identities proved
by Jacobi and the original EF/Cartan relations. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreSimpleBracketLowering
open CFSG.Models.Chevalley CFSGSerreSignedRootWeights
variable {r:ℕ} (A:Matrix (Fin r) (Fin r) ℤ)

theorem coroot_simple_bracket (neg:Bool) (k i j:Fin r) :
    ⁅coroot A neg k,⁅rootVector A neg i,rootVector A neg j⁆⁆=
      ((A k i:ℚ)+(A k j:ℚ)) • ⁅rootVector A neg i,rootVector A neg j⁆ := by
  rw [leibniz_lie,coroot_root,coroot_root,smul_lie,lie_smul,add_smul]

theorem opposite_simple_bracket (neg:Bool) (k i j:Fin r) :
    ⁅oppositeVector A neg k,⁅rootVector A neg i,rootVector A neg j⁆⁆=
      (if k=i then -(A i j:ℚ) • rootVector A neg j else 0)+
        (if k=j then (A j i:ℚ) • rootVector A neg i else 0) := by
  by_cases hij:i=j
  · subst j
    simp only [lie_self,lie_zero]
    by_cases hki:k=i
    · simp only [if_pos hki,neg_smul,neg_add_cancel]
    · simp only [if_neg hki,zero_add]
  · by_cases hki:k=i
    · subst k
      rw [leibniz_lie,opposite_same,opposite_distinct A neg i j hij,
        neg_lie,coroot_root,lie_zero,add_zero]
      simp only [if_true,if_neg hij,add_zero,neg_smul]
    · by_cases hkj:k=j
      · subst k
        rw [leibniz_lie,opposite_distinct A neg j i (Ne.symm hij),opposite_same,
          zero_lie,zero_add,lie_neg,←lie_skew (rootVector A neg i) (coroot A neg j),
          neg_neg,coroot_root]
        simp only [if_neg (Ne.symm hij),if_true,zero_add]
      · rw [leibniz_lie,opposite_distinct A neg k i hki,
          opposite_distinct A neg k j hkj,zero_lie,lie_zero,zero_add]
        simp only [if_neg hki,if_neg hkj,zero_add]

end SymmetricSubgroupAsymptotics.CFSGSerreSimpleBracketLowering
