import SymmetricSubgroupAsymptotics.SixPairFullKernelCenter

/-! A single physical central indicator in an original normal subgroup
forces the whole actual coarse center. This also detects centralizers in
proper original central quotients without enumerating normal subgroups. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SixPairCentralIndicatorClosure
open SixPairCoarseCenterTransport SixPairFullKernelCenter
open BinaryTwoLayerLocalClassTwo BinaryTwoLayerLocalCommutators
variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U I)
  (E : ProductBlockFrame F.top.range (Fin 3) (ZMod 2))

private def indicator (j : Fin 3) : Fin 3 → ZMod 2 := fun i => if i=j then 1 else 0

private theorem bits_of_indicator
    (z : (SixPairNestedTopFrames.nestedFrame F E).top.ker) (j : Fin 3)
    (hz : ∀ i,(SixPairNestedTopFrames.nestedFrame F E).kernelCoordinate i z=
      if i=j then diagonal else 1) : HasBits F E z (indicator j) := by
  intro i a b
  rw [hz i]
  by_cases hi : i=j
  · simp [indicator,hi,diagonal]
  · simp [indicator,hi]

private theorem hasBits_one :
    HasBits F E (1 : (SixPairNestedTopFrames.nestedFrame F E).top.ker) 0 := by
  intro j a b
  simp only [map_one,Equiv.Perm.one_apply,Pi.zero_apply,add_zero]

private theorem hasBits_mul
    (x y : (SixPairNestedTopFrames.nestedFrame F E).top.ker)
    (s t : Fin 3 → ZMod 2) (hx : HasBits F E x s) (hy : HasBits F E y t) :
    HasBits F E (x*y) (s+t) := by
  intro j a b
  rw [map_mul,Equiv.Perm.mul_apply,hy j a b,hx j a (b+t j)]
  simp only [Pi.add_apply]
  congr 1
  ac_rfl

private theorem hasBits_injective
    (x y : (SixPairNestedTopFrames.nestedFrame F E).top.ker)
    (s : Fin 3 → ZMod 2) (hx : HasBits F E x s) (hy : HasBits F E y s) : x=y := by
  apply (SixPairNestedTopFrames.nestedFrame F E).kernelCoordinates_joint_injective
  funext j
  apply Equiv.ext
  rintro ⟨a,b⟩
  rw [hx j a b,hy j a b]

private theorem all_indicators_mem [MulAction.IsPretransitive U X]
    (N : Subgroup U) [N.Normal]
    (z : (SixPairNestedTopFrames.nestedFrame F E).top.ker) (hz : z.val∈N)
    (j₀ : Fin 3) (hs : HasBits F E z (indicator j₀)) :
    ∀ j,∃ v : (SixPairNestedTopFrames.nestedFrame F E).top.ker,
      v.val∈N ∧ HasBits F E v (indicator j) := by
  let C := SixPairNestedTopFrames.nestedFrame F E
  intro j
  obtain ⟨p,hp⟩ := C.top_range_transitive
    (fun x y => MulAction.exists_smul_eq U x y) j₀ j
  obtain ⟨g,hg⟩ := p.property
  have hg' : C.top g j₀=j := by rw [hg]; exact hp
  let v : C.top.ker := MulAut.conjNormal g z
  have hv : v.val∈N := Subgroup.Normal.conj_mem inferInstance _ hz g
  refine ⟨v,hv,?_⟩
  have hvbits := hasBits_conjugate F E g z (indicator j₀) hs
  have heq : (fun i => indicator j₀ ((C.top g)⁻¹ i))=indicator j := by
    funext i
    have hc : ((C.top g)⁻¹ i=j₀) ↔ i=j := by
      constructor
      · intro h
        calc i=(C.top g) ((C.top g)⁻¹ i) := ((C.top g).apply_symm_apply i).symm
             _=(C.top g) j₀ := congrArg (C.top g) h
             _=j := hg'
      · intro h
        apply (C.top g).injective
        change (C.top g) ((C.top g).symm i)=(C.top g) j₀
        rw [(C.top g).apply_symm_apply,h]
        exact hg'.symm
    simp only [indicator,hc]
  rw [heq] at hvbits
  exact hvbits

private theorem central_mem_of_indicators
    (N : Subgroup U)
    (hN : ∀ j,∃ v : (SixPairNestedTopFrames.nestedFrame F E).top.ker,
      v.val∈N ∧ HasBits F E v (indicator j))
    (x : (SixPairNestedTopFrames.nestedFrame F E).top.ker)
    (s : Fin 3 → ZMod 2) (hx : HasBits F E x s) : x.val∈N := by
  choose z hz hb using hN
  let w : Fin 3 → (SixPairNestedTopFrames.nestedFrame F E).top.ker :=
    fun j => if s j=0 then 1 else z j
  let t (j : Fin 3) : Fin 3 → ZMod 2 := fun i => if i=j then s j else 0
  have hw (j : Fin 3) : HasBits F E (w j) (t j) := by
    by_cases hs0 : s j=0
    · simpa [w,t,hs0] using hasBits_one F E
    · have hs1 : s j=1 := by
        have hcases : ∀ a : ZMod 2,a=0 ∨ a=1 := by decide +kernel
        exact (hcases (s j)).resolve_left hs0
      simpa [w,t,hs0,hs1,indicator] using hb j
  have hwN (j : Fin 3) : (w j).val∈N := by
    by_cases hs0 : s j=0
    · simp [w,hs0]
    · simpa only [w,if_neg hs0] using hz j
  let y := w 0*w 1*w 2
  have hyN : y.val∈N := N.mul_mem (N.mul_mem (hwN 0) (hwN 1)) (hwN 2)
  have hybits := hasBits_mul F E (w 0*w 1) (w 2) (t 0+t 1) (t 2)
    (hasBits_mul F E (w 0) (w 1) (t 0) (t 1) (hw 0) (hw 1)) (hw 2)
  have ht : t 0+t 1+t 2=s := by
    funext i
    fin_cases i <;> simp [t]
  rw [ht] at hybits
  have he : y=x := hasBits_injective F E y x s hybits hx
  exact he ▸ hyN

/-- One original physical indicator normally spans the whole center. -/
theorem center_le_of_indicator [MulAction.IsPretransitive U X]
    (hfull : SixPairIndependentKernelNormalCommutators.Independent F E)
    (N : Subgroup U) [N.Normal]
    (z : (SixPairNestedTopFrames.nestedFrame F E).top.ker) (hz : z.val∈N)
    (j : Fin 3) (hs : ∀ i,
      (SixPairNestedTopFrames.nestedFrame F E).kernelCoordinate i z=
        if i=j then diagonal else 1) : centerImage F E≤N := by
  have hall := all_indicators_mem F E N z hz j (bits_of_indicator F E z j hs)
  rintro _ ⟨x,hx,rfl⟩
  obtain ⟨s,hs⟩ := (hasBits_iff_center F E hfull x).mpr hx
  exact central_mem_of_indicators F E N hall x s hs

end SymmetricSubgroupAsymptotics.SixPairCentralIndicatorClosure
