import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalSimpleRootAction
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalSignedPermutation

/-! The SAME original automorphism has matching positive and negative
simple-root permutations. Given canonical opposition supplies the
negative permutation; actual signed commutation forces agreement. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalNegativeSimpleAction
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoCoordinateOriginalPositiveCenter
open CFSGNormTwoCoordinateOriginalRootFamily CFSGNormTwoCoordinateOriginalLeadingHom
open CFSGNormTwoCoordinateIntrinsicLeadingAxes CFSGNormTwoCoordinateOriginalLeadingAutomorphism
open CFSGInvariantSubgroupCoordinateImage CFSGSimpleCoordinateAxes
open CFSGNormTwoCoordinateOriginalAxisAction CFSGSimpleCoordinateAxisPermutation
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K] [Finite K] [Nontrivial (Fin r)]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

open CFSGNormTwoCoordinateOriginalComplementAmbient CFSGNormTwoCoordinateOriginalOppositionAut
open CFSGNormTwoCoordinateOriginalOppositionConjugation CFSGNormTwoCoordinateOriginalOppositeAlignment
open CFSGNormTwoCoordinateOriginalCartanAction

open CFSGNormTwoCoordinateOriginalOppositeComplementAction
open CFSGNormTwoCoordinateOriginalOppositeComplementNormalizer
open CFSGNormTwoCoordinateOriginalNormalizerIntersection CFSGNormTwoCoordinateOriginalAllRootLines

open CFSGNormTwoCoordinateOriginalSimpleRootAction CFSGNormTwoCoordinateOriginalSignedPermutation
open CFSGNormTwoCoordinateOriginalOppositePairData CFSGPairSwappingAutomorphism
open CFSGNormTwoCoordinateOriginalComplementNormalizer

theorem exists_negativeSimpleRootGroup_permutation
    (ε : Fin r→ℤ) (hε : ∀j,ε j*ε j=1) (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)→wordLinear A hs hp b₀ s₀ w=1)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) (θ : Roots A)
    (hθ : ∀j,0≤θ.val j)
    (hdom : ∀j,0 ≤ integerPairing A θ.val (Pi.single j (1:ℤ) : Fin r→ℤ))
    (f : MulAut (Projective (cartan b₀ s₀) K))
    (hV : (originalNegative A hd hs hp ho K i).map f.toMonoidHom=originalNegative A hd hs hp ho K i)
    (hU : (originalPositive A hd hs hp ho K i).map f.toMonoidHom=originalPositive A hd hs hp ho K i) :
    ∃ σ : Equiv.Perm (Fin r), (∀ j k, A (σ j) (σ k) = A j k) ∧
      ∀ j, (originalNegativeSimpleRootGroup A hd hs hp ho K i j).map f.toMonoidHom =
        originalNegativeSimpleRootGroup A hd hs hp ho K i (σ j) := by
  let e := originalOppositionAut A hd hs hp ho K i
  let g := e * f * e.symm
  have hUe : (originalPositive A hd hs hp ho K i).map e.symm.toMonoidHom =
      originalNegative A hd hs hp ho K i :=
    inverse_swap _ _ e (originalOpposition_negative A hd hs hp ho K i)
  have hVe : (originalNegative A hd hs hp ho K i).map e.symm.toMonoidHom =
      originalPositive A hd hs hp ho K i :=
    inverse_swap _ _ e (originalOpposition_positive A hd hs hp ho K i)
  have hgU : (originalPositive A hd hs hp ho K i).map g.toMonoidHom =
      originalPositive A hd hs hp ho K i := by
    exact conjugate_preserves_first _ _ e.symm f hUe hV
  have hgV : (originalNegative A hd hs hp ho K i).map g.toMonoidHom =
      originalNegative A hd hs hp ho K i := by
    exact conjugate_preserves_first _ _ e.symm f hVe hU
  obtain ⟨σ, hσ, hR⟩ := exists_simpleRootGroup_permutation A hd hs hp ho K
    ε hε hA hidentity p i θ hθ hdom g hgV hgU
  have hNe (j : Fin r) : (originalNegativeSimpleRootGroup A hd hs hp ho K i j).map
      e.toMonoidHom = originalSimpleRootGroup A hd hs hp ho K i j :=
    originalOpposition_negative_simple A hd hs hp ho K i j
  refine ⟨σ, hσ, ?_⟩
  intro j
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [hNe (σ j)]
  have hcomp : e.toMonoidHom.comp f.toMonoidHom = g.toMonoidHom.comp e.toMonoidHom := by
    ext x
    change e (f x) = e (f (e.symm (e x)))
    rw [e.symm_apply_apply]
  calc
    ((originalNegativeSimpleRootGroup A hd hs hp ho K i j).map f.toMonoidHom).map e.toMonoidHom =
        ((originalNegativeSimpleRootGroup A hd hs hp ho K i j).map e.toMonoidHom).map g.toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map, hcomp]
    _ = _ := by
      rw [hNe j, hR j]

theorem negative_simple_fixed_of_positive_simple_fixed
    (ε : Fin r→ℤ) (hε : ∀j,ε j*ε j=1) (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)→wordLinear A hs hp b₀ s₀ w=1)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) (θ : Roots A)
    (hθ : ∀j,0≤θ.val j)
    (hdom : ∀j,0 ≤ integerPairing A θ.val (Pi.single j (1:ℤ) : Fin r→ℤ))
    (f : MulAut (Projective (cartan b₀ s₀) K))
    (hV : (originalNegative A hd hs hp ho K i).map f.toMonoidHom=originalNegative A hd hs hp ho K i)
    (hU : (originalPositive A hd hs hp ho K i).map f.toMonoidHom=originalPositive A hd hs hp ho K i)
    (hR : ∀ j, (originalSimpleRootGroup A hd hs hp ho K i j).map f.toMonoidHom =
      originalSimpleRootGroup A hd hs hp ho K i j) :
    ∀ j, (originalNegativeSimpleRootGroup A hd hs hp ho K i j).map f.toMonoidHom =
      originalNegativeSimpleRootGroup A hd hs hp ho K i j := by
  obtain ⟨τ, _, hτ⟩ := exists_negativeSimpleRootGroup_permutation A hd hs hp ho K
    ε hε hA hidentity p i θ hθ hdom f hV hU
  have hdisj := (original_opposite_disjoint_and_card A hd hs hp ho K ε hε hA hidentity p i).1
  have he : (1 : Equiv.Perm (Fin r)) = τ :=
    simple_signed_permutations_agree A hd hs hp ho K p i hdisj f 1 τ hR hτ
  intro j
  simpa only [← he, Equiv.Perm.one_apply] using hτ j

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalNegativeSimpleAction
