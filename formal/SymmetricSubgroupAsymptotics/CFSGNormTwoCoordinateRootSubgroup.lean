import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootWordIdentity
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticRootSubgroup

/-! Actual root subgroups indexed by the ORIGINAL norm-two lattice roots.
The choice of a reflection word is obtained from the proved root orbit;
the subgroup is independent of that choice by integral-sign recognition.
This is an actual subgroup of matrix units, not abstract root-action data. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootSubgroup
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoGeckIntegralWord CFSGNormTwoGeckWeylWordDegree
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
open CFSGSerreQuadraticWordRootTransport
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀

def rootWitness (k : Roots A) :
    {p : List (Fin r)×Fin r // k.val=wordLinear A hs hp b₀ s₀ p.1 (-(s₀ p.2:Roots A).val)} :=
  Classical.choice (by
    obtain ⟨w,j,h⟩ := CFSGNormTwoGeckRootWordOrbit.exists_word_linear_negative A hs hp b₀ s₀ k
    exact ⟨⟨(w,j),h⟩⟩)

def wordRootSubgroup (K : Type) [Field K] (w : List (Fin r)) (j : Fin r) :
    Subgroup ((Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ) :=
  (canonicalRootSubgroup D K true j).map (MulAut.conj (canonicalWord D K w)).toMonoidHom

theorem mem_wordRootSubgroup_iff (K : Type) [Field K] (w : List (Fin r)) (j : Fin r)
    (x : (Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ) :
    x∈wordRootSubgroup A hd hs hp ho K w j↔∃a : K,rootWord D K w true j a=x := by
  constructor
  · rintro ⟨y,⟨a,rfl⟩,rfl⟩
    exact ⟨a,rfl⟩
  · rintro ⟨a,rfl⟩
    exact ⟨canonicalRoot D K true j a,⟨a,rfl⟩,rfl⟩

def rootSubgroup (K : Type) [Field K] (k : Roots A) :
    Subgroup ((Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ) :=
  wordRootSubgroup A hd hs hp ho K (rootWitness A hd hs hp ho k).val.1
    (rootWitness A hd hs hp ho k).val.2

theorem rootSubgroup_eq_word (K : Type) [Field K] (k : Roots A)
    (w : List (Fin r)) (j : Fin r)
    (hk : k.val=wordLinear A hs hp b₀ s₀ w (-(s₀ j:Roots A).val)) :
    rootSubgroup A hd hs hp ho K k=wordRootSubgroup A hd hs hp ho K w j := by
  let p := rootWitness A hd hs hp ho k
  have hdegree : wordLinear A hs hp b₀ s₀ p.val.1 (-(s₀ p.val.2:Roots A).val)=
      wordLinear A hs hp b₀ s₀ w (-(s₀ j:Roots A).val) := p.property.symm.trans hk
  have hrange := CFSGNormTwoCoordinateRootWordIdentity.same_degree_root_ranges A hd hs hp ho
    K p.val.1 w p.val.2 j hdegree
  apply Subgroup.ext
  intro x
  change x∈wordRootSubgroup A hd hs hp ho K p.val.1 p.val.2↔
    x∈wordRootSubgroup A hd hs hp ho K w j
  rw [mem_wordRootSubgroup_iff,mem_wordRootSubgroup_iff]
  exact Set.ext_iff.mp hrange x

theorem rootSubgroup_le_elementary (K : Type) [Field K] (k : Roots A) :
    rootSubgroup A hd hs hp ho K k≤canonicalElementaryGroup D K := by
  let p := rootWitness A hd hs hp ho k
  intro x hx
  change x∈wordRootSubgroup A hd hs hp ho K p.val.1 p.val.2 at hx
  obtain ⟨a,rfl⟩ := (mem_wordRootSubgroup_iff A hd hs hp ho K p.val.1 p.val.2 x).mp hx
  change canonicalWord D K p.val.1*canonicalRoot D K true p.val.2 a*
    (canonicalWord D K p.val.1)⁻¹∈canonicalElementaryGroup D K
  rw [←word_eq_canonicalWord]
  exact CFSGNormTwoGeckRootWordMembership.word_root_conjugate_mem A hs hp b₀ s₀ K
    p.val.1 true p.val.2 a

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootSubgroup
