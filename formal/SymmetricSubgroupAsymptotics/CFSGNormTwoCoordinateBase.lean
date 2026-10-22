import SymmetricSubgroupAsymptotics.CFSGNormTwoRootPairingReduced
import SymmetricSubgroupAsymptotics.CFSGIntegralNormTwoSigns
import SymmetricSubgroupAsymptotics.CFSGNonnegativeIntegerCone
import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.LinearAlgebra.StdBasis

/-! A genuine base for the actual norm-two integer lattice. The only matrix
conditions are symmetry, positive definiteness, diagonal two, and nonpositive
off-diagonal entries; every base axiom is derived from those conditions. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoRootPairing
open CFSGIntegerMatrixPairing
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hd : ∀ i,A i i=2)

def coordinateRoot (i : n) : Roots A :=
  ⟨Pi.single i 1,by simpa only [integerPairing,Matrix.toBilin'_single] using hd i⟩

theorem coordinateRoot_injective : Function.Injective (coordinateRoot A hd) := by
  intro i j h
  by_contra hij
  have he := congrFun (congrArg Subtype.val h) i
  simp [coordinateRoot,hij] at he

variable (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)

@[simp] theorem coordinateRoot_root (i : n) :
    (rootPairing A hs hp).root (coordinateRoot A hd i)=(Pi.single i 1:n→ℚ) := by
  ext j
  simp [rootPairing,rootEmbedding,coordinateRoot,castVector,Pi.single_apply]

def coordinateSupport : Finset (Roots A) := by
  classical
  exact Finset.univ.image (coordinateRoot A hd)

theorem coordinateSupport_coe : (coordinateSupport A hd:Set (Roots A))=
    Set.range (coordinateRoot A hd) := by
  classical
  ext i
  simp [coordinateSupport]

theorem coordinate_root_image :
    (rootPairing A hs hp).root '' (coordinateSupport A hd:Set (Roots A))=
      Set.range (fun i:n=>(Pi.single i 1:n→ℚ)) := by
  rw [coordinateSupport_coe]
  ext v
  constructor
  · rintro ⟨a,⟨i,rfl⟩,rfl⟩
    exact ⟨i,(coordinateRoot_root A hd hs hp i).symm⟩
  · rintro ⟨i,rfl⟩
    exact ⟨coordinateRoot A hd i,⟨i,rfl⟩,coordinateRoot_root A hd hs hp i⟩

theorem coordinate_linearIndepOn :
    LinearIndepOn ℚ (rootPairing A hs hp).root (coordinateSupport A hd) := by
  rw [coordinateSupport_coe]
  apply (linearIndepOn_range_iff (coordinateRoot_injective A hd) _).mpr
  have he : (⇑(rootPairing A hs hp).root ∘ coordinateRoot A hd)=⇑(Pi.basisFun ℚ n) := by
    funext i
    rw [Function.comp_apply,coordinateRoot_root,Pi.basisFun_apply]
  rw [he]
  exact (Pi.basisFun ℚ n).linearIndependent

variable (ho : ∀ i j,i≠j→A i j≤0)

include ho in
theorem coordinate_root_mem_or_neg_mem (x : Roots A) :
    (rootPairing A hs hp).root x∈AddSubmonoid.closure
      ((rootPairing A hs hp).root '' (coordinateSupport A hd:Set (Roots A))) ∨
    -(rootPairing A hs hp).root x∈AddSubmonoid.closure
      ((rootPairing A hs hp).root '' (coordinateSupport A hd:Set (Roots A))) := by
  rw [coordinate_root_image]
  rcases CFSGIntegralNormTwoSigns.norm_two_coordinates_one_sign A hs hp
      (fun i=>by rw [hd i];exact even_two) ho x.val x.property with hx|hx
  · left
    exact CFSGNonnegativeIntegerCone.cast_mem_closure x.val hx
  · right
    have hm := CFSGNonnegativeIntegerCone.cast_mem_closure (-x.val)
      (fun i=>neg_nonneg.mpr (hx i))
    simpa only [rootPairing,rootEmbedding,castVector,Pi.neg_apply,Int.cast_neg] using hm

def coordinateBase : (rootPairing A hs hp).Base where
  support := coordinateSupport A hd
  linearIndepOn_root := coordinate_linearIndepOn A hd hs hp
  linearIndepOn_coroot := coordinate_linearIndepOn A hd hs hp
  root_mem_or_neg_mem := coordinate_root_mem_or_neg_mem A hd hs hp ho
  coroot_mem_or_neg_mem := coordinate_root_mem_or_neg_mem A hd hs hp ho

end SymmetricSubgroupAsymptotics.CFSGNormTwoRootPairing
