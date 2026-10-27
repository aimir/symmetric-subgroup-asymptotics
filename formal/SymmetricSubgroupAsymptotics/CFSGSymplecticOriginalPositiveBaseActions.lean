import SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalPositiveSpanCoefficients

/-! The base cases of the finite SOURCE induction, proved from original
HE/EF relations and the literal Cartan tails. No action table is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalPositiveBaseActions
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGSerreSignedRootWeights
open CFSGSymplecticOriginalRootCandidates CFSGSymplecticOriginalCartanTail
open CFSGSymplecticUniformPositiveProfile CFSGSymplecticUniformPositiveTables
open CFSGSymplecticOriginalPositiveSourceWeights
open CFSGSymplecticOriginalPositiveSpanCoefficients
variable (r : ℕ)
local instance : DecidableEq (PositiveIndex r) := Classical.decEq _

private theorem tail_mem (a : ℕ) : (tail r a).val∈span r := by
  by_cases ha : a < r
  · exact Submodule.subset_span ⟨.inl ⟨a,ha⟩,rfl⟩
  · have hz : r-a=0 := by omega
    simp only [tail,hz,Finset.range_zero,Finset.sum_empty,Submodule.coe_zero]
    exact Submodule.zero_mem _

theorem cartan_mem (i : Fin r) :
    generator (CartanMatrix.C r).transpose (.H i)∈span r := by
  have h:=congrArg Subtype.val (generator_H_from_tails r i)
  change generator (CartanMatrix.C r).transpose (.H i)=
    (tail r i.val).val-(tail r (i.val+1)).val at h
  rw [h]
  exact Submodule.sub_mem _ (tail_mem r _) (tail_mem r _)

theorem simple_occurs (i : Fin r) : ∃ j : PositiveIndex r,
    height r j=1 ∧ source r j=rootVector (CartanMatrix.C r).transpose false i := by
  by_cases hi : i.val+1 < r
  · let next : Fin r:=⟨i.val+1,hi⟩
    let ij : Pair r:=⟨(i,next),by dsimp [next]; omega⟩
    refine ⟨.inr (.inl ij),?_,?_⟩
    · simp [height,rootHeight,ij,next]
    · simp [source,root,difference,path,steps,descend,ij,next,
        CFSGSerreDividedPowerPaths.pathVector,CFSGSerreDividedPowerPaths.applySteps,
        latticeGenerator,CFSG.Models.Chevalley.rootVector]
  · refine ⟨.inr (.inr (.inl i)),?_,?_⟩
    · have hr : r-i.val=1 := by have h:=i.isLt; omega
      simp [height,rootHeight,hr]
    · have hl : (⟨r-1,by have h:=i.isLt; omega⟩ : Fin r)=i := by
        apply Fin.ext
        change r-1=i.val
        have h:=i.isLt
        omega
      simp [source,root,long,hl,descend_self,steps,path,
        CFSGSerreDividedPowerPaths.pathVector,CFSGSerreDividedPowerPaths.applySteps,
        latticeGenerator,CFSG.Models.Chevalley.rootVector]

theorem simple_mem (i : Fin r) :
    rootVector (CartanMatrix.C r).transpose false i∈span r := by
  obtain ⟨j,hj,he⟩:=simple_occurs r i
  rw [←he]
  exact Submodule.subset_span ⟨j,rfl⟩

theorem height_one_simple (j : PositiveIndex r) (hj : height r j=1) :
    ∃ i : Fin r,source r j=rootVector (CartanMatrix.C r).transpose false i := by
  rcases j with b | (ij | (i | ij))
  · simp [height] at hj
  · have hh:=ij.property
    have hn : ij.val.2.val=ij.val.1.val+1 := by
      simp only [height,rootHeight] at hj
      omega
    have hs : (⟨ij.val.2.val-1,by have h:=ij.val.2.isLt; omega⟩ : Fin r)=ij.val.1 := by
      apply Fin.ext
      change ij.val.2.val-1=ij.val.1.val
      omega
    refine ⟨ij.val.1,?_⟩
    simp [source,root,difference,hs,descend_self,steps,path,
      CFSGSerreDividedPowerPaths.pathVector,CFSGSerreDividedPowerPaths.applySteps,
      latticeGenerator,CFSG.Models.Chevalley.rootVector]
  · have hi:=i.isLt
    have hn : r-1=i.val := by
      simp only [height,rootHeight] at hj
      omega
    have hs : (⟨r-1,by omega⟩ : Fin r)=i := Fin.ext hn
    refine ⟨i,?_⟩
    simp [source,root,long,hs,descend_self,steps,path,
      CFSGSerreDividedPowerPaths.pathVector,CFSGSerreDividedPowerPaths.applySteps,
      latticeGenerator,CFSG.Models.Chevalley.rootVector]
  · have hi:=ij.val.1.isLt
    have hk:=ij.val.2.isLt
    have hij:=ij.property
    simp only [height,rootHeight] at hj
    omega

theorem raising_base (i : Fin r) (j : PositiveIndex r) (hj : height r j=0) :
    ⁅rootVector (CartanMatrix.C r).transpose false i,source r j⁆=
      Fintype.linearCombination ℚ (source r) (raising r i j) := by
  apply raising_of_mem
  obtain ⟨b,rfl⟩:=height_zero_is_cartan r j hj
  change ⁅rootVector (CartanMatrix.C r).transpose false i,(tail r b.val).val⁆∈span r
  simp only [tail,Submodule.coe_sum,lie_sum]
  apply Submodule.sum_mem
  intro a ha
  unfold Hnat
  split_ifs with h
  · have he : ⁅rootVector (CartanMatrix.C r).transpose false i,
        generator (CartanMatrix.C r).transpose (.H ⟨b.val+a,h⟩)⁆=
        -((CartanMatrix.C r).transpose ⟨b.val+a,h⟩ i:ℚ) •
          rootVector (CartanMatrix.C r).transpose false i := by
      rw [←lie_skew (rootVector (CartanMatrix.C r).transpose false i)
        (generator (CartanMatrix.C r).transpose (.H ⟨b.val+a,h⟩))]
      simpa only [coroot,Bool.false_eq_true,if_false,neg_smul] using
        congrArg Neg.neg (coroot_root (CartanMatrix.C r).transpose false ⟨b.val+a,h⟩ i)
    change ⁅rootVector (CartanMatrix.C r).transpose false i,
      generator (CartanMatrix.C r).transpose (.H ⟨b.val+a,h⟩)⁆∈span r
    rw [he]
    exact Submodule.smul_mem _ _ (simple_mem r i)
  · simp only [Submodule.coe_zero,lie_zero]
    exact Submodule.zero_mem _

theorem lowering_base (a : Fin r) (j : PositiveIndex r) (hj : height r j=1) :
    ⁅oppositeVector (CartanMatrix.C r).transpose false a,source r j⁆=
      Fintype.linearCombination ℚ (source r) (lowering r a j) := by
  apply lowering_of_mem
  obtain ⟨i,hi⟩:=height_one_simple r j hj
  rw [hi]
  by_cases ha : a=i
  · subst a
    rw [opposite_same]
    exact Submodule.neg_mem _ (cartan_mem r i)
  · rw [opposite_distinct (CartanMatrix.C r).transpose false a i ha]
    exact Submodule.zero_mem _

end SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalPositiveBaseActions
