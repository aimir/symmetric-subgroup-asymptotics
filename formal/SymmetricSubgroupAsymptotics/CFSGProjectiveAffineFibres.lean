import SymmetricSubgroupAsymptotics.CFSGProjectiveAffinePermutation
import SymmetricSubgroupAsymptotics.CFSGProjectiveSpanVectors
import SymmetricSubgroupAsymptotics.CFSGCoordinateSpanMembership

/-! Coordinate fibres in the original affine chart are the spans of an
actual affine point and the corresponding coordinate points at infinity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGProjectiveAffineChart
open CFSGProjectiveFrameCoordinates
variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n]

def directionVector (i : n) (j : {j : n // j≠i}) : Vector (F:=F) (n:=n) :=
  Pi.single (Sum.inr j.val) 1

private theorem directionVector_ne_zero (i : n) (j : {j : n // j≠i}) :
    directionVector (F:=F) i j≠0 := by
  intro he
  have hh := congrArg (fun x : Vector (F:=F) (n:=n) => x (Sum.inr j.val)) he
  simpa only [directionVector,Pi.single_eq_same,Pi.zero_apply,one_ne_zero] using hh

def fibreVector (v : n→F) (i : n) : Option {j : n // j≠i}→Vector (F:=F) (n:=n)
  | none => vector v
  | some j => directionVector i j

private theorem fibreVector_ne_zero (v : n→F) (i : n) (j : Option {j : n // j≠i}) :
    fibreVector v i j≠0 := by
  cases j with
  | none => exact vector_ne_zero v
  | some j => exact directionVector_ne_zero i j

def fibrePoint (v : n→F) (i : n) (j : Option {j : n // j≠i}) : Point (F:=F) (n:=n) :=
  Projectivization.mk F (fibreVector v i j) (fibreVector_ne_zero v i j)

private theorem direction_span (i : n) (x : Vector (F:=F) (n:=n)) :
    x∈Submodule.span F (Set.range (directionVector (F:=F) i))↔
      x (Sum.inl ())=0 ∧ x (Sum.inr i)=0 := by
  have hr : Set.range (directionVector (F:=F) i)=
      (fun k : Unit⊕n => (Pi.single k 1 : Vector (F:=F) (n:=n))) ''
        {k | k≠Sum.inl () ∧ k≠Sum.inr i} := by
    ext y
    constructor
    · rintro ⟨j,rfl⟩
      exact ⟨Sum.inr j.val,⟨Sum.inr_ne_inl,fun he => j.property (Sum.inr_injective he)⟩,rfl⟩
    · rintro ⟨k,hk,rfl⟩
      rcases k with u | j
      · cases u
        exact (hk.1 rfl).elim
      · exact ⟨⟨j,fun he => hk.2 (congrArg Sum.inr he)⟩,rfl⟩
  rw [hr,mem_span_single_image]
  constructor
  · intro hx
    exact ⟨hx (Sum.inl ()) (by simp),hx (Sum.inr i) (by simp)⟩
  · rintro ⟨h0,hi⟩ k hk
    rcases k with u | j
    · cases u
      exact h0
    · by_cases hji : j=i
      · simpa only [hji] using hi
      · exact (hk ⟨Sum.inr_ne_inl,fun he => hji (Sum.inr_injective he)⟩).elim

private theorem fibre_range (v : n→F) (i : n) :
    Set.range (fibreVector v i)=insert (vector v) (Set.range (directionVector (F:=F) i)) := by
  ext x
  constructor
  · rintro ⟨j,rfl⟩
    cases j with
    | none => exact Or.inl rfl
    | some j => exact Or.inr ⟨j,rfl⟩
  · rintro (rfl | ⟨j,rfl⟩)
    · exact ⟨none,rfl⟩
    · exact ⟨some j,rfl⟩

private theorem vector_mem_fibre_span (v w : n→F) (i : n) :
    vector w∈Submodule.span F (Set.range (fibreVector v i))↔w i=v i := by
  rw [fibre_range,Submodule.mem_span_insert]
  constructor
  · rintro ⟨a,z,hz,he⟩
    obtain ⟨hz0,hzi⟩ := (direction_span i z).mp hz
    have h0 := congrArg (fun x : Vector (F:=F) (n:=n) => x (Sum.inl ())) he
    have ha : a=1 := by
      simpa only [vector_zeroCoord,Pi.add_apply,Pi.smul_apply,smul_eq_mul,hz0,mul_one,add_zero] using h0.symm
    have hi := congrArg (fun x : Vector (F:=F) (n:=n) => x (Sum.inr i)) he
    simpa only [vector_coord,Pi.add_apply,Pi.smul_apply,smul_eq_mul,hzi,ha,one_mul,add_zero] using hi
  · intro hi
    refine ⟨1,vector w-vector v,?_,?_⟩
    · apply (direction_span i _).mpr
      constructor
      · simp only [Pi.sub_apply,vector_zeroCoord,sub_self]
      · simp only [Pi.sub_apply,vector_coord,hi,sub_self]
    · simp only [one_smul]
      simp [sub_eq_add_neg,add_comm,add_left_comm]

theorem point_mem_fibre_span (v w : n→F) (i : n) :
    point w∈Projectivization.Subspace.span (Set.range (fibrePoint v i))↔w i=v i := by
  unfold fibrePoint
  rw [←projectivization_span_vectors (fibreVector v i) (fibreVector_ne_zero v i)]
  exact (Submodule.mk_mem_projectivization_iff _ (vector_ne_zero w)).trans
    (vector_mem_fibre_span v w i)

private theorem image_fibre_points
    (f : collineationGroup (F:=F) (n:=Unit⊕n))
    (hf : ∀j : Unit⊕n,f.val (basisPoint (F:=F) j)=basisPoint (F:=F) j)
    (v : n→F) (i : n) :
    f.val '' Set.range (fibrePoint v i)=Set.range (fibrePoint (affinePermutation f hf v) i) := by
  ext p
  constructor
  · rintro ⟨_,⟨j,rfl⟩,rfl⟩
    refine ⟨j,?_⟩
    cases j with
    | none => exact point_affinePermutation f hf v
    | some j => exact (hf (Sum.inr j.val)).symm
  · rintro ⟨j,rfl⟩
    refine ⟨fibrePoint v i j,⟨j,rfl⟩,?_⟩
    cases j with
    | none => exact (point_affinePermutation f hf v).symm
    | some j => exact hf (Sum.inr j.val)

theorem affinePermutation_fibre_iff
    (f : collineationGroup (F:=F) (n:=Unit⊕n))
    (hf : ∀j : Unit⊕n,f.val (basisPoint (F:=F) j)=basisPoint (F:=F) j)
    (v w : n→F) (i : n) : affinePermutation f hf v i=affinePermutation f hf w i↔v i=w i := by
  have hh := mem_mapSubspace f
    (Projectivization.Subspace.span (Set.range (fibrePoint w i))) (f.val (point v))
  simp only [Equiv.symm_apply_apply] at hh
  rw [mapSubspace_span,image_fibre_points f hf w i,←point_affinePermutation f hf v] at hh
  simpa only [point_mem_fibre_span] using hh

end SymmetricSubgroupAsymptotics.CFSGProjectiveAffineChart
