import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootSubgroup
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootElementRange
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSelectedRootAdditive
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckBorelEnvelope

/-! The SAME selected root parameters, words and tori as actual elements
of the literal canonical elementary matrix group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateElementaryRootParameters
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckIntegralWord
open CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoGeckRootWordMembership CFSGNormTwoGeckParameterizedTorus
open CFSGNormTwoGeckBorelEnvelope CFSGNormTwoCoordinateRootSubgroup
open CFSGNormTwoCoordinateRootElementRange CFSGNormTwoCoordinateSelectedRootAdditive
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀

abbrev ElementaryGroup (K : Type) [Field K] := canonicalElementaryGroup D K

def elementarySelectedRootHom (K : Type) [Field K] (k : Roots A) :
    Multiplicative K→*ElementaryGroup A hd hs hp ho K :=
  (selectedRootHom A hd hs hp ho K k).codRestrict (ElementaryGroup A hd hs hp ho K) (fun a=>
    rootSubgroup_le_elementary A hd hs hp ho K k
      ((mem_rootSubgroup_iff_selected A hd hs hp ho K k _).mpr ⟨a.toAdd,rfl⟩))

def elementaryWord (K : Type) [Field K] (w : List (Fin r)) : ElementaryGroup A hd hs hp ho K :=
  ⟨wordUnit A hs hp b₀ s₀ K w,word_mem A hs hp b₀ s₀ K w⟩

def elementaryTorus (K : Type) [Field K] (i : Fin r) (t : Kˣ) : ElementaryGroup A hd hs hp ho K :=
  ⟨parameterTorus A hs hp b₀ s₀ K i t,torusGroup_le_canonical A hs hp b₀ s₀ K
    (Subgroup.subset_closure ⟨(i,t),rfl⟩)⟩

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateElementaryRootParameters
