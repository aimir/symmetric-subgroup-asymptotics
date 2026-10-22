import SymmetricSubgroupAsymptotics.CFSGOrthogonalBPositiveSubspace
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBElementaryGroup

/-! Every original simple B root word moves the positive maximal space
across an intersection of codimension at most one. The proof fixes the
kernel of one actual coordinate functional, including the quadratic
coefficient of the short root. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBSimpleMaximalOverlap
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBPositiveSubspace
variable (K : Type) [Field K]

theorem root_fixes_coordinate_kernel (r : ℕ) (ε : Bool) (i : Fin r) (t : K) :
    ∃k : Fin r,∀v∈positiveSubspace K r,v (pos r k)=0 →
      (rootTransvection K r ε i t : Mat K r)*ᵥv=v := by
  by_cases h : i.val+1<r
  · cases ε
    · refine ⟨⟨i.val+1,h⟩,?_⟩
      intro v hv hk
      obtain ⟨hn,hm⟩ := (mem_positiveSubspace K r v).mp hv
      ext j
      simp [rootTransvection_val,rootMatrix,rootSecond,positive,positiveSecond,h,
        Matrix.add_mulVec,Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.single_mulVec,
        hn,hk]
    · refine ⟨i,?_⟩
      intro v hv hk
      obtain ⟨hn,hm⟩ := (mem_positiveSubspace K r v).mp hv
      ext j
      simp [rootTransvection_val,rootMatrix,rootSecond,negative,negativeSecond,h,
        Matrix.add_mulVec,Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.single_mulVec,
        hn,hk]
  · cases ε
    · refine ⟨i,?_⟩
      intro v hv hk
      obtain ⟨hn,hm⟩ := (mem_positiveSubspace K r v).mp hv
      ext j
      simp [rootTransvection_val,rootMatrix,rootSecond,positive,positiveSecond,h,
        Matrix.add_mulVec,Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.single_mulVec,
        hn,hm]
    · refine ⟨i,?_⟩
      intro v hv hk
      obtain ⟨hn,hm⟩ := (mem_positiveSubspace K r v).mp hv
      ext j
      simp [rootTransvection_val,rootMatrix,rootSecond,negative,negativeSecond,h,
        Matrix.add_mulVec,Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.single_mulVec,
        hm,hk]

theorem root_positive_intersection_finrank (r : ℕ) (ε : Bool) (i : Fin r) (t : K) :
    r≤Module.finrank K ((positiveSubspace K r)⊓
      (positiveSubspace K r).map (Matrix.mulVecLin (rootTransvection K r ε i t : Mat K r)) :
        Submodule K (Index r→K))+1 := by
  obtain ⟨k,hk⟩ := root_fixes_coordinate_kernel K r ε i t
  let P := positiveSubspace K r
  let ℓ : P→ₗ[K]K := (LinearMap.proj (pos r k)).comp P.subtype
  let L := ℓ.ker.map P.subtype
  have hle : L≤P⊓P.map (Matrix.mulVecLin (rootTransvection K r ε i t : Mat K r)) := by
    rintro v ⟨w,hw,rfl⟩
    have hz : w.val (pos r k)=0 := hw
    exact ⟨w.property,⟨w.val,w.property,hk w.val w.property hz⟩⟩
  have hdim := ℓ.finrank_range_add_finrank_ker
  have hrange : Module.finrank K ℓ.range≤1 := by
    simpa using Submodule.finrank_le ℓ.range
  have hL : Module.finrank K L=Module.finrank K ℓ.ker :=
    Submodule.finrank_map_subtype_eq P ℓ.ker
  have hP : Module.finrank K P=r := positiveSubspace_finrank K r
  have hmono := Submodule.finrank_mono hle
  change r≤Module.finrank K (P⊓P.map
    (Matrix.mulVecLin (rootTransvection K r ε i t : Mat K r)) : Submodule K (Index r→K))+1
  omega

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBSimpleMaximalOverlap
