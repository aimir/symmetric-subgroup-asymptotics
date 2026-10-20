import SymmetricSubgroupAsymptotics.Selected1542FirstCenterReceipts
import SymmetricSubgroupAsymptotics.Selected1542OriginalKernelPGroup
import SymmetricSubgroupAsymptotics.BinaryKernelCentralizerMonolith

/-! The first original monolith is forced by literal sixteen-point orbit
words, not by a list of metadata normal subgroups. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1542QuotientStructure

local instance : originalBinaryKernel.Normal := inferInstanceAs originalCubic.ker.Normal

private def signedOriginal (i : Fin 6) : Original :=
  if h : i.val<3 then source ⟨i.val,h⟩ else (source ⟨i.val-3,by omega⟩)⁻¹

private theorem signedOriginal_val (i : Fin 6) :
    (signedOriginal i).val=signedSource i := by
  unfold signedOriginal signedSource
  split <;> rfl

private theorem originalCubic_source (j : Fin 3) :
    originalCubic (source j)=NaturalA4ScalarFourHead.top (alternatingGenerator j 0) := by
  change ActualRepeatedAlternatingCentralCoordinates.top targetAlternating 0
    (originalToTarget (source j))=_
  rw [originalToTarget_source]
  change NaturalA4ScalarFourHead.top (targetAlternating (targetSource j) 0)=_
  rw [targetAlternating_generator]

private theorem originalCubic_signed (i : Fin 6) :
    originalCubic (signedOriginal i)=firstCenterCubicLetter i := by
  unfold signedOriginal firstCenterCubicLetter
  split
  · exact originalCubic_source _
  · rw [map_inv,originalCubic_source]

def firstCenterOriginalGenerator (j : Fin 9) : Original :=
  ((firstCenterSourceWord j).map signedOriginal).prod

theorem firstCenterOriginalGenerator_val (j : Fin 9) :
    (firstCenterOriginalGenerator j).val=firstCenterGenerator j := by
  change Original.subtype (((firstCenterSourceWord j).map signedOriginal).prod)=_
  rw [map_list_prod,List.map_map]
  change ((firstCenterSourceWord j).map (fun i => (signedOriginal i).val)).prod=
    ((firstCenterSourceWord j).map signedSource).prod
  simp only [signedOriginal_val]

theorem firstCenterOriginalGenerator_mem (j : Fin 9) :
    firstCenterOriginalGenerator j∈originalBinaryKernel := by
  change originalCubic (((firstCenterSourceWord j).map signedOriginal).prod)=1
  rw [map_list_prod,List.map_map]
  change ((firstCenterSourceWord j).map (fun i => originalCubic (signedOriginal i))).prod=1
  have hf : (fun i => originalCubic (signedOriginal i))=firstCenterCubicLetter :=
    funext originalCubic_signed
  rw [hf]
  exact firstCenter_cubic j

def originalCentralInvolution : Original := preimageOriginal 26

theorem originalCentralInvolution_val : originalCentralInvolution.val=firstCenterZ := rfl

theorem originalCentralInvolution_mem : originalCentralInvolution∈originalBinaryKernel := by
  have hz : originalToTarget originalCentralInvolution=1 := by
    apply MonoidHom.mem_ker.mp
    rw [originalToTarget_ker]
    exact (preimageTable.chart 26).property
  change ActualRepeatedAlternatingCentralCoordinates.top targetAlternating 0
    (originalToTarget originalCentralInvolution)=1
  rw [hz,map_one]

theorem originalBinaryKernel_centralizer (p : Original)
    (hp : p∈Subgroup.centralizer (originalBinaryKernel : Set Original)) :
    p=1 ∨ p=originalCentralInvolution := by
  have hcomm : ∀ j : Fin 9, Commute p.val (firstCenterGenerator j) := by
    intro j
    have he := Subgroup.mem_centralizer_iff.mp hp
      (firstCenterOriginalGenerator j) (firstCenterOriginalGenerator_mem j)
    have hv := congrArg Subtype.val he.symm
    change p.val*(firstCenterOriginalGenerator j).val=
      (firstCenterOriginalGenerator j).val*p.val at hv
    rw [firstCenterOriginalGenerator_val] at hv
    exact hv
  rcases OrbitWordCentralizer.eq_one_or_of_orbit_words firstCenterGenerator 0
      firstCenterOrbitWord firstCenter_orbit firstCenterZ firstCenter_candidates p.val hcomm with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

/-- Every nontrivial original denominator contains the same literal involution. -/
theorem original_first_monolith (N : Subgroup Original) (hN : N.Normal) (hne : N≠⊥) :
    Subgroup.zpowers originalCentralInvolution≤N :=
  normal_cover_of_binary_kernel_centralizer originalBinaryKernel originalBinaryKernel_isPGroup
    originalCentralInvolution originalCentralInvolution_mem originalBinaryKernel_centralizer N hN hne

end SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
