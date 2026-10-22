import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSimpleRootOrbit
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootWeylAction

/-! Every pair of ORIGINAL norm-two lattice roots is joined by an
actual simple-reflection word. Consequently their actual matrix root
subgroups are conjugate by a literal word in the elementary group.
This is a full root-orbit statement, not normal-closure generation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootOrbitTransitive
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckRootWordOrbit CFSGNormTwoGeckWeylWordAlgebra
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticWordRootTransport
open CFSGNormTwoGeckIntegralWord
open CFSGNormTwoCoordinateSimpleRootOrbit CFSGNormTwoCoordinateRootSubgroup
open CFSGNormTwoCoordinateRootWeylAction
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem exists_word_linear_root_to_root (k l : Roots A) :
    ∃w : List (Fin r),wordLinear A hs hp b₀ s₀ w k.val=l.val := by
  obtain ⟨u,i,hk⟩ := exists_word_linear_negative A hs hp b₀ s₀ k
  obtain ⟨v,j,hl⟩ := exists_word_linear_negative A hs hp b₀ s₀ l
  obtain ⟨w,hw⟩ := exists_word_simple_to_simple A hd hs hp ho i j
  have hu : wordLinear A hs hp b₀ s₀ (inverseWord u) k.val= -(s₀ i : Roots A).val := by
    rw [wordLinear_inverseWord,hk]
    exact (wordLinear A hs hp b₀ s₀ u).symm_apply_apply _
  have hw' : wordLinear A hs hp b₀ s₀ w (-(s₀ i : Roots A).val)= -(s₀ j : Roots A).val := by
    rw [map_neg,hw]
  refine ⟨v++w++inverseWord u,?_⟩
  rw [wordLinear_append,wordLinear_append]
  change wordLinear A hs hp b₀ s₀ v
    (wordLinear A hs hp b₀ s₀ w (wordLinear A hs hp b₀ s₀ (inverseWord u) k.val))=l.val
  rw [hu,hw']
  exact hl.symm

theorem exists_word_root_to_root (k l : Roots A) :
    ∃w : List (Fin r),wordRoot A hs hp b₀ s₀ w k=l := by
  obtain ⟨w,hw⟩ := exists_word_linear_root_to_root A hd hs hp ho k l
  refine ⟨w,Subtype.ext ?_⟩
  rw [←wordLinear_root]
  exact hw

theorem rootSubgroup_conjugate_by_word (K : Type) [Field K] (k l : Roots A) :
    ∃w : List (Fin r),
      (rootSubgroup A hd hs hp ho K k).map
        (MulAut.conj (wordUnit A hs hp b₀ s₀ K w)).toMonoidHom=
          rootSubgroup A hd hs hp ho K l := by
  obtain ⟨w,hw⟩ := exists_word_root_to_root A hd hs hp ho k l
  refine ⟨w,?_⟩
  rw [word_eq_canonicalWord,rootSubgroup_map_word,hw]

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootOrbitTransitive
