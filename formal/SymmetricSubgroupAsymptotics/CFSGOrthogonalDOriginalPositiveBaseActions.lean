import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalPositiveSpanCoefficients

/-! Actual source induction bases from the original D HE and EF relations.
All Cartans are original generators, and height-one fork paths are literal
simple roots. No realization injectivity is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalPositiveBaseActions
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGSerreSignedRootWeights
open CFSGOrthogonalDOriginalRootCandidates CFSGOrthogonalDUniformPositiveProfile
open CFSGOrthogonalDUniformPositiveTables CFSGOrthogonalDOriginalPositiveSourceWeights
open CFSGOrthogonalDOriginalPositiveSpanCoefficients
variable (r : ℕ) (hr : 4 ≤ r)

theorem cartan_mem (i : Fin r) : generator (CartanMatrix.D r) (.H i)∈span r hr :=
  Submodule.subset_span ⟨.inl i,rfl⟩

theorem simple_occurs (i : Fin r) : ∃ j : PositiveIndex r,
    height r j=1 ∧ source r hr j=rootVector (CartanMatrix.D r) false i := by
  by_cases hi : i.val+1 < r
  · let next : Fin r:=⟨i.val+1,hi⟩
    let ij : Pair r:=⟨(i,next),by dsimp [next];omega⟩
    refine ⟨.inr (.inl ij),?_,?_⟩
    · simp [height,rootHeight,ij,next]
    · simp [source,root,difference,path,steps,descend,ij,next,
        CFSGSerreDividedPowerPaths.pathVector,CFSGSerreDividedPowerPaths.applySteps,
        latticeGenerator,CFSG.Models.Chevalley.rootVector]
  · let prev : Fin r:=⟨r-2,by omega⟩
    have hil : i.val=r-1:=by have hh:=i.isLt;omega
    let ij : Pair r:=⟨(prev,i),by dsimp [prev];omega⟩
    have hl : (⟨r-1,by omega⟩ : Fin r)=i:=Fin.ext hil.symm
    refine ⟨.inr (.inr ij),?_,?_⟩
    · simp [height,rootHeight,ij,prev,hil]
    · simp [source,root,sumRoot,ij,prev,hl,descend_self,steps,path,
        CFSGSerreDividedPowerPaths.pathVector,CFSGSerreDividedPowerPaths.applySteps,
        latticeGenerator,CFSG.Models.Chevalley.rootVector]

theorem simple_mem (i : Fin r) : rootVector (CartanMatrix.D r) false i∈span r hr := by
  obtain ⟨j,hj,he⟩:=simple_occurs r hr i
  rw [←he]
  exact Submodule.subset_span ⟨j,rfl⟩

theorem height_one_simple (j : PositiveIndex r) (hj : height r j=1) :
    ∃ i : Fin r,source r hr j=rootVector (CartanMatrix.D r) false i := by
  rcases j with b | (ij | ij)
  · simp [height] at hj
  · have hh:=ij.property
    have hn : ij.val.2.val=ij.val.1.val+1 := by
      simp only [height,rootHeight] at hj
      omega
    have hs : (⟨ij.val.2.val-1,by have h:=ij.val.2.isLt;omega⟩ : Fin r)=ij.val.1 := by
      apply Fin.ext
      change ij.val.2.val-1=ij.val.1.val
      omega
    refine ⟨ij.val.1,?_⟩
    simp [source,root,difference,hs,descend_self,steps,path,
      CFSGSerreDividedPowerPaths.pathVector,CFSGSerreDividedPowerPaths.applySteps,
      latticeGenerator,CFSG.Models.Chevalley.rootVector]
  · have hi:=ij.val.1.isLt
    have hk:=ij.val.2.isLt
    have hij:=ij.property
    have hn : ij.val.1.val=r-2 ∧ ij.val.2.val=r-1 := by
      simp only [height,rootHeight] at hj
      omega
    let last : Fin r:=⟨r-1,by omega⟩
    let prev : Fin r:=⟨r-2,by omega⟩
    have hlast : ij.val.2=last:=Fin.ext hn.2
    have hprev : ij.val.1=prev:=Fin.ext hn.1
    refine ⟨last,?_⟩
    simp [source,root,sumRoot,hlast,hprev,last,prev,descend_self,steps,path,
      CFSGSerreDividedPowerPaths.pathVector,CFSGSerreDividedPowerPaths.applySteps,
      latticeGenerator,CFSG.Models.Chevalley.rootVector]

theorem raising_base (i : Fin r) (j : PositiveIndex r) (hj : height r j=0) :
    ⁅rootVector (CartanMatrix.D r) false i,source r hr j⁆=
      Fintype.linearCombination ℚ (source r hr) (raising r hr i j) := by
  apply raising_of_mem
  obtain ⟨b,rfl⟩:=height_zero_is_cartan r j hj
  change ⁅rootVector (CartanMatrix.D r) false i,generator (CartanMatrix.D r) (.H b)⁆∈span r hr
  rw [←lie_skew (rootVector (CartanMatrix.D r) false i)
    (generator (CartanMatrix.D r) (.H b))]
  have h:=coroot_root (CartanMatrix.D r) false b i
  simp only [coroot,Bool.false_eq_true,if_false] at h
  rw [h]
  exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (simple_mem r hr i))

theorem lowering_base (a : Fin r) (j : PositiveIndex r) (hj : height r j=1) :
    ⁅oppositeVector (CartanMatrix.D r) false a,source r hr j⁆=
      Fintype.linearCombination ℚ (source r hr) (lowering r hr a j) := by
  apply lowering_of_mem
  obtain ⟨i,hi⟩:=height_one_simple r hr j hj
  rw [hi]
  by_cases ha : a=i
  · subst a
    rw [opposite_same]
    exact Submodule.neg_mem _ (cartan_mem r hr i)
  · rw [opposite_distinct (CartanMatrix.D r) false a i ha]
    exact Submodule.zero_mem _

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalPositiveBaseActions
