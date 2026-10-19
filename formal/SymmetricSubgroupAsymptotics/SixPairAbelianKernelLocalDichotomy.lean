import SymmetricSubgroupAsymptotics.BinaryTwoLayerLocalAbelianDichotomy
import SymmetricSubgroupAsymptotics.SixPairLocalKernelConjugation
import SymmetricSubgroupAsymptotics.SixPairCyclicLocalKernelCoordinates

/-! An actual abelian coarse kernel either has cyclic projections in
all three physical four-point fibres, or is killed by two. Original
transitivity transports the local order-four witness; no normal census or
uniform local type is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixPairAbelianKernelLocalDichotomy
variable {X I : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
  [MulAction.IsPretransitive U X]
  (F : BinaryPairFrame U I)
  (E : ProductBlockFrame F.top.range (Fin 3) (ZMod 2))

 theorem cyclic_local_or_square_one
    (hcomm : ∀ a b : (SixPairNestedTopFrames.nestedFrame F E).top.ker,a*b=b*a) :
    (∀ i,IsCyclic (SixPairCyclicLocalKernelCoordinates.localRange F E i)) ∨
      ∀ a : (SixPairNestedTopFrames.nestedFrame F E).top.ker,a^2=1 := by
  classical
  let C := SixPairNestedTopFrames.nestedFrame F E
  by_cases hs : ∀ a : C.top.ker,a^2=1
  · exact Or.inr hs
  · obtain ⟨a,ha⟩ := not_forall.mp hs
    have hpoint : ∃ j : Fin 3,(C.kernelCoordinate j a)^2≠1 := by
      by_contra hn
      push Not at hn
      apply ha
      apply C.kernelCoordinates_joint_injective
      funext j
      change C.kernelCoordinate j (a^2)=C.kernelCoordinate j 1
      rw [map_pow,map_one]
      exact hn j
    obtain ⟨j,hj⟩ := hpoint
    apply Or.inl
    intro i
    obtain ⟨t,ht⟩ := C.top_range_transitive (fun x y => MulAction.exists_smul_eq U x y) j i
    obtain ⟨g,hg⟩ := t.property
    have hgi : C.top g j=i := by simpa only [hg] using ht
    have hinv : (C.top g)⁻¹ i=j := by
      rw [←hgi]
      exact (C.top g).symm_apply_apply j
    let b := MulAut.conjNormal g a
    let l := (C.wreathEmbedding g).left i
    let e := MulAut.conj l
    have he : e (C.kernelCoordinate j a)=C.kernelCoordinate i b := by
      rw [SixPairLocalKernelConjugation.coordinate_conjugate F E,hinv]
      rfl
    have hb : (C.kernelCoordinate i b)^2≠1 := by
      intro h
      apply hj
      apply e.injective
      rw [map_pow,map_one,he]
      exact h
    let L := SixPairCyclicLocalKernelCoordinates.localRange F E i
    have hp (x : L) : BinaryTwoLayerLocalClassTwo.Preserves x.val := by
      obtain ⟨u,hu⟩ := x.property
      rw [←hu]
      exact SixPairThreePairKernelClassTwo.coordinate_preserves F E i u
    have hc (x y : L) : x*y=y*x := by
      apply Subtype.ext
      obtain ⟨u,hu⟩ := x.property
      obtain ⟨v,hv⟩ := y.property
      change x.val*y.val=y.val*x.val
      rw [←hu,←hv,←map_mul,←map_mul,hcomm]
    rcases BinaryTwoLayerLocalAbelianDichotomy.cyclic_or_square_one L hp hc with hc | hc
    · exact hc
    · exact False.elim (hb (congrArg Subtype.val
        (hc ((C.kernelCoordinate i).rangeRestrict b))))

 theorem coordinates_or_square_one
    (hcomm : ∀ a b : (SixPairNestedTopFrames.nestedFrame F E).top.ker,a*b=b*a) :
    (∃ j : (SixPairNestedTopFrames.nestedFrame F E).top.ker →*
      (Fin 3 → C4CoordinateHomCount.C4),Function.Injective j) ∨
      ∀ a : (SixPairNestedTopFrames.nestedFrame F E).top.ker,a^2=1 := by
  rcases cyclic_local_or_square_one F E hcomm with hc | hc
  · exact Or.inl (SixPairCyclicLocalKernelCoordinates.exists_coordinates F E hc)
  · exact Or.inr hc

end SymmetricSubgroupAsymptotics.SixPairAbelianKernelLocalDichotomy
