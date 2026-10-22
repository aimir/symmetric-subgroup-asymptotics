import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalAllRootLines

/-! Arbitrary automorphisms send EVERY original lattice-labelled root
subgroup, including negative roots, into the conjugacy family of the
literal projected dominant-root subgroup. This combines actual root-word
conjugacy with the proved full Sylow-centre recognition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalRootRecognition
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoCoordinateOriginalRootFamily CFSGNormTwoCoordinateOriginalAllRootLines
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem original_rootLine_mem_dominant_family
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)]
    (i : Fin r) (θ k : Roots A) (hθ : ∀j,0≤θ.val j) :
    ∃g : Projective (cartan b₀ s₀) K,
      originalFullRootLine A hd hs hp ho K i k=originalConjugateRootLine A hd hs hp ho K i θ g := by
  obtain ⟨g,hg⟩ := originalFullRootLine_conjugate A hd hs hp ho K i θ k
  rw [originalFullRootLine_eq_positive A hd hs hp ho K i θ hθ] at hg
  exact ⟨g,hg.symm⟩

theorem automorphism_maps_original_rootLine [Finite K] [Nontrivial (Fin r)]
    (ε : Fin r→ℤ) (hε : ∀j,ε j*ε j=1) (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)→wordLinear A hs hp b₀ s₀ w=1)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) (θ k : Roots A)
    (hθ : ∀j,0≤θ.val j)
    (hdom : ∀j,0 ≤ integerPairing A θ.val (Pi.single j (1:ℤ) : Fin r→ℤ))
    (f : MulAut (Projective (cartan b₀ s₀) K)) :
    ∃h : Projective (cartan b₀ s₀) K,
      (originalFullRootLine A hd hs hp ho K i k).map f.toMonoidHom=
        originalConjugateRootLine A hd hs hp ho K i θ h := by
  obtain ⟨g,hg⟩ := original_rootLine_mem_dominant_family A hd hs hp ho K i θ k hθ
  obtain ⟨h,hh⟩ := automorphism_maps_originalConjugateRootLine A hd hs hp ho K
    ε hε hA hidentity p i θ hθ hdom f g
  exact ⟨h,by rw [hg];exact hh⟩

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalRootRecognition
