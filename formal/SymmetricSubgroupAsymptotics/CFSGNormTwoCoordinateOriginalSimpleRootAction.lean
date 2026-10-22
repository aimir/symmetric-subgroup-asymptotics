import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalOppositeComplementNormalizer

/-! A genuine original automorphism fixing BOTH literal opposite
Sylows permutes the literal simple-root subgroups by a genuine Cartan
diagram permutation. Root lifting is now deduced from intrinsic
complement normalizers and proved intersections, not from axes alone. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalSimpleRootAction
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

theorem exists_simpleRootGroup_permutation
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
    ∃σ : Equiv.Perm (Fin r),(∀j k,A (σ j) (σ k)=A j k) ∧
      ∀j,(originalSimpleRootGroup A hd hs hp ho K i j).map f.toMonoidHom=
        originalSimpleRootGroup A hd hs hp ho K i (σ j) := by
  obtain ⟨σ,hCartan,hM,hN⟩ := exists_oppositeComplement_action A hd hs hp ho K
    ε hε hA hidentity p i θ hθ hdom f hV
  have hi (j : Fin r) : originalPositive A hd hs hp ho K i⊓
      Subgroup.normalizer (originalOppositeComplement A hd hs hp ho K p i j : Set _)=
        originalSimpleRootGroup A hd hs hp ho K i j := by
    rw [original_opposite_complement_normalizer A hd hs hp ho K ε hε hA hidentity p i j]
    exact original_opposite_normalizer_intersection A hd hs hp ho K ε hε hA hidentity p i j
  refine ⟨σ,hCartan,?_⟩
  intro j
  rw [←hi j,Subgroup.map_inf _ _ _ f.injective,hU,hN j,hi (σ j)]

theorem exists_simpleFullRootLine_permutation
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
    ∃σ : Equiv.Perm (Fin r),(∀j k,A (σ j) (σ k)=A j k) ∧
      ∀j,(originalFullRootLine A hd hs hp ho K i (s₀ j)).map f.toMonoidHom=
        originalFullRootLine A hd hs hp ho K i (s₀ (σ j)) := by
  obtain ⟨σ,hCartan,hR⟩ := exists_simpleRootGroup_permutation A hd hs hp ho K
    ε hε hA hidentity p i θ hθ hdom f hV hU
  refine ⟨σ,hCartan,?_⟩
  intro j
  simpa only [originalSimpleRootGroup_eq_fullRootLine] using hR j

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalSimpleRootAction
