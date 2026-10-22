import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveSpace
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Every original D simple-root word moves the actual positive singular
space across an intersection of codimension at most two. This is an
explicit coordinate-kernel calculation, valid also in characteristic two. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDSimpleMaximalOverlap
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPositiveSpace
open CFSGOrthogonalDIndexQuadraticForm
variable (K : Type) [Field K]

theorem root_fixes_two_coordinate_kernel (r : ℕ) (ε : Bool) (i : Fin r) (t : K) :
    ∃j k : Fin r,∀v∈positiveSpace K r,v (Sum.inl j)=0 → v (Sum.inl k)=0 →
      (rootTransvection K r ε i t : Mat K r)*ᵥv=v := by
  by_cases h : i.val+1<r
  · refine ⟨i,⟨i.val+1,h⟩,?_⟩
    intro v hv hi hj
    have hn : ∀j,v (Sum.inr j)=0 := hv
    cases ε <;> ext a <;>
      simp [rootTransvection,rootMatrix,negative,positive,h,
        Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.sub_mulVec,
        Matrix.single_mulVec,hi,hj,hn]
  · refine ⟨i,previous r i,?_⟩
    intro v hv hi hj
    have hn : ∀j,v (Sum.inr j)=0 := hv
    cases ε <;> ext a <;>
      simp [rootTransvection,rootMatrix,negative,positive,h,
        Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.sub_mulVec,
        Matrix.single_mulVec,hi,hj,hn]

theorem root_positive_intersection_finrank (r : ℕ) (ε : Bool) (i : Fin r) (t : K) :
    r≤Module.finrank K ((positiveSpace K r)⊓
      (positiveSpace K r).map (Matrix.mulVecLin (rootTransvection K r ε i t : Mat K r)) :
        Submodule K (Index r→K))+2 := by
  obtain ⟨j,k,hfix⟩ := root_fixes_two_coordinate_kernel K r ε i t
  let P := positiveSpace K r
  let f : P→ₗ[K]K×K :=
    ((LinearMap.proj (Sum.inl j)).comp P.subtype).prod
      ((LinearMap.proj (Sum.inl k)).comp P.subtype)
  let T := f.ker.map P.subtype
  have hle : T≤P⊓P.map (Matrix.mulVecLin (rootTransvection K r ε i t : Mat K r)) := by
    rintro v ⟨x,hx,rfl⟩
    have h1 : x.val (Sum.inl j)=0 := congrArg Prod.fst hx
    have h2 : x.val (Sum.inl k)=0 := congrArg Prod.snd hx
    exact ⟨x.property,⟨x.val,x.property,hfix x.val x.property h1 h2⟩⟩
  have hd := f.finrank_range_add_finrank_ker
  have hrange : Module.finrank K f.range≤2 := by
    simpa using Submodule.finrank_le f.range
  have hT : Module.finrank K T=Module.finrank K f.ker :=
    Submodule.finrank_map_subtype_eq P f.ker
  have hP : Module.finrank K P=r := positiveSpace_finrank K r
  have hmono := Submodule.finrank_mono hle
  change r≤Module.finrank K (P⊓P.map
    (Matrix.mulVecLin (rootTransvection K r ε i t : Mat K r)) : Submodule K (Index r→K))+2
  omega

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDSimpleMaximalOverlap
