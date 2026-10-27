import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalPositiveActionTables
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalChevalleyPaths
import SymmetricSubgroupAsymptotics.CFSGSerreFiniteRationalFirstActionSpan

/-! The literal signed-root/Cartan family spans the WHOLE original rational
D Serre quotient. This proves actual first-action stability; it assumes no
source table, natural faithfulness, or integral-span equality. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalRationalFirstActionSpan
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGSerreSignedRootWeights
open CFSGSerreLocalNilpotence CFSGSerreChevalleyInvolution
open CFSGOrthogonalDOriginalRootCandidates CFSGOrthogonalDUniformPositiveProfile
open CFSGOrthogonalDOriginalPositiveSourceWeights CFSGOrthogonalDOriginalChevalleyPaths
variable (r : ℕ) (hr : 4 ≤ r)

def family (j : BasisIndex r) : RationalLie (CartanMatrix.D r):=(vector r hr j).val

def span : Submodule ℚ (RationalLie (CartanMatrix.D r)):=
  Submodule.span ℚ (Set.range (family r hr))

private theorem integral_mem (x : Source r)
    (hx : x∈Submodule.span ℤ (Set.range (vector r hr))) : x.val∈span r hr := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨j,rfl⟩:=hx;exact Submodule.subset_span ⟨j,rfl⟩
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul z x _ hx =>
    change z • x.val∈span r hr
    rw [←Int.cast_smul_eq_zsmul ℚ]
    exact Submodule.smul_mem _ (z:ℚ) hx

private theorem positive_combination_mem (a : PositiveIndex r→ℚ) :
    Fintype.linearCombination ℚ (source r hr) a∈span r hr := by
  rw [Fintype.linearCombination_apply]
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨fullIndex r j,by cases j <;> rfl⟩

private theorem map_mem (x : RationalLie (CartanMatrix.D r)) (hx : x∈span r hr) :
    rationalMap (CartanMatrix.D r) x∈span r hr := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j,rfl⟩:=hx
    rcases j with i | ⟨neg,j⟩
    · change rationalMap (CartanMatrix.D r) (generator (CartanMatrix.D r) (.H i))∈_
      rw [rationalMap_H]
      exact Submodule.neg_mem _ (Submodule.subset_span ⟨.inl i,rfl⟩)
    · obtain ⟨z,hz⟩:=map_root_swap r hr neg j
      have h:=congrArg Subtype.val hz
      change rationalMap (CartanMatrix.D r) (root r hr neg j).val=
        z • (root r hr (!neg) j).val at h
      change rationalMap (CartanMatrix.D r) (root r hr neg j).val∈_
      rw [h,←Int.cast_smul_eq_zsmul ℚ]
      exact Submodule.smul_mem _ (z:ℚ) (Submodule.subset_span ⟨.inr (!neg,j),rfl⟩)
  | zero => rw [map_zero];exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add];exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul];exact Submodule.smul_mem _ a hx

private theorem positive_root_first (neg : Bool) (i : Fin r) (j : RootIndex r) :
    ⁅rootVector (CartanMatrix.D r) neg i,(root r hr false j).val⁆∈span r hr := by
  have ht:=CFSGOrthogonalDOriginalPositiveActionTables.source_tables r hr
  cases neg
  · rw [show (root r hr false j).val=source r hr (.inr j) from rfl,ht.1]
    exact positive_combination_mem r hr _
  · have h:=ht.2 i (.inr j) (rootHeight_pos r j)
    change ⁅rootVector (CartanMatrix.D r) true i,(root r hr false j).val⁆=_ at h
    rw [h]
    exact positive_combination_mem r hr _

private theorem negative_root_first (neg : Bool) (i : Fin r) (j : RootIndex r) :
    ⁅rootVector (CartanMatrix.D r) neg i,(root r hr true j).val⁆∈span r hr := by
  have he : rationalMap (CartanMatrix.D r)
      ⁅rootVector (CartanMatrix.D r) (!neg) i,
        rationalMap (CartanMatrix.D r) (root r hr true j).val⁆=
      ⁅rootVector (CartanMatrix.D r) neg i,(root r hr true j).val⁆ := by
    rw [LieHom.map_lie,rationalMap_root,Bool.not_not,rationalMap_involutive]
  rw [←he]
  apply map_mem
  obtain ⟨z,hz⟩:=map_root_swap r hr true j
  have h:=congrArg Subtype.val hz
  change rationalMap (CartanMatrix.D r) (root r hr true j).val=
    z • (root r hr false j).val at h
  rw [h,←Int.cast_smul_eq_zsmul ℚ,lie_smul]
  exact Submodule.smul_mem _ (z:ℚ) (positive_root_first r hr (!neg) i j)

theorem first_action_mem (neg : Bool) (i : Fin r) (j : BasisIndex r) :
    ⁅rootVector (CartanMatrix.D r) neg i,family r hr j⁆∈span r hr := by
  rcases j with b | ⟨sgn,j⟩
  · change ⁅rootVector (CartanMatrix.D r) neg i,generator (CartanMatrix.D r) (.H b)⁆∈_
    cases neg
    · have ht:=(CFSGOrthogonalDOriginalPositiveActionTables.source_tables r hr).1 i (.inl b)
      change ⁅rootVector (CartanMatrix.D r) false i,generator (CartanMatrix.D r) (.H b)⁆=_ at ht
      rw [ht]
      exact positive_combination_mem r hr _
    · rw [←lie_skew (rootVector (CartanMatrix.D r) true i)
        (generator (CartanMatrix.D r) (.H b))]
      change -⁅generator (CartanMatrix.D r) (.H b),generator (CartanMatrix.D r) (.F i)⁆∈_
      rw [generator_HF,neg_neg]
      rw [←Int.cast_smul_eq_zsmul ℚ]
      exact Submodule.smul_mem _ _ (integral_mem r hr _ (original_generators_mem r hr (.F i)))
  · cases sgn
    · exact positive_root_first r hr neg i j
    · exact negative_root_first r hr neg i j

theorem span_eq_top : Submodule.span ℚ (Set.range (family r hr))=⊤ :=
  CFSGSerreFiniteRationalFirstActionSpan.span_eq_top (CartanMatrix.D r) (family r hr)
    (fun g=>integral_mem r hr _ (original_generators_mem r hr g)) (first_action_mem r hr)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalRationalFirstActionSpan
