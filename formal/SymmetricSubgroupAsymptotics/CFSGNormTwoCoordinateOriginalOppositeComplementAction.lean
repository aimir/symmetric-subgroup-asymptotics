import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalComplementAmbient
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalOppositionConjugation
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalCartanAction

/-! Actual original automorphisms preserving V permute the opposite
coordinate complements and their FULL ambient normalizers. The given
opposition is used to transfer the intrinsic positive-axis theorem;
no arbitrary automorphism lift is involved. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalOppositeComplementAction
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

def originalOppositeComplement (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i j : Fin r) :
    Subgroup (Projective (cartan b₀ s₀) K) :=
  (originalComplementAmbient A hd hs hp ho K p i j).map
    (originalOppositionAut A hd hs hp ho K i).toMonoidHom

theorem oppositeComplement_map (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r)
    (f : MulAut (Projective (cartan b₀ s₀) K))
    (hV : (originalNegative A hd hs hp ho K i).map f.toMonoidHom=originalNegative A hd hs hp ho K i)
    (σ : Equiv.Perm (Fin r))
    (hσ : ∀j : Fin r,(axis (K:=K) j).map
      (ambientLeadingAut A hd hs hp ho K p i (oppositionConjugate A hd hs hp ho K i f)
        (oppositionConjugate_preserves_positive A hd hs hp ho K i f hV)).toMonoidHom=
          axis (K:=K) (σ j)) (j : Fin r) :
    (originalOppositeComplement A hd hs hp ho K p i j).map f.toMonoidHom=
      originalOppositeComplement A hd hs hp ho K p i (σ j) := by
  let e := originalOppositionAut A hd hs hp ho K i
  let g := oppositionConjugate A hd hs hp ho K i f
  have hm := originalComplementAmbient_map A hd hs hp ho K p i g
    (oppositionConjugate_preserves_positive A hd hs hp ho K i f hV) σ hσ j
  change ((originalComplementAmbient A hd hs hp ho K p i j).map e.toMonoidHom).map f.toMonoidHom=_
  calc
    _=((originalComplementAmbient A hd hs hp ho K p i j).map g.toMonoidHom).map e.toMonoidHom := by
      rw [Subgroup.map_map,Subgroup.map_map]
      congr 1
      apply MonoidHom.ext
      intro x
      change f (e x)=e (e.symm (f (e x)))
      exact (e.apply_symm_apply _).symm
    _=originalOppositeComplement A hd hs hp ho K p i (σ j) := by rw [hm];rfl

theorem exists_oppositeComplement_action
    (ε : Fin r→ℤ) (hε : ∀j,ε j*ε j=1) (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)→wordLinear A hs hp b₀ s₀ w=1)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) (θ : Roots A)
    (hθ : ∀j,0≤θ.val j)
    (hdom : ∀j,0 ≤ integerPairing A θ.val (Pi.single j (1:ℤ) : Fin r→ℤ))
    (f : MulAut (Projective (cartan b₀ s₀) K))
    (hV : (originalNegative A hd hs hp ho K i).map f.toMonoidHom=originalNegative A hd hs hp ho K i) :
    ∃σ : Equiv.Perm (Fin r),(∀j k,A (σ j) (σ k)=A j k) ∧
      (∀j,(originalOppositeComplement A hd hs hp ho K p i j).map f.toMonoidHom=
        originalOppositeComplement A hd hs hp ho K p i (σ j)) ∧
      ∀j,(Subgroup.normalizer (originalOppositeComplement A hd hs hp ho K p i j : Set _)).map
        f.toMonoidHom=Subgroup.normalizer (originalOppositeComplement A hd hs hp ho K p i (σ j) : Set _) := by
  let g := oppositionConjugate A hd hs hp ho K i f
  have hg := oppositionConjugate_preserves_positive A hd hs hp ho K i f hV
  obtain ⟨σ,hσ,hCartan⟩ := ambientLeadingAut_cartan_permutation A hd hs hp ho K
    ε hε hA hidentity p i θ hθ hdom g hg
  have hm : ∀j,(originalOppositeComplement A hd hs hp ho K p i j).map f.toMonoidHom=
      originalOppositeComplement A hd hs hp ho K p i (σ j) :=
    oppositeComplement_map A hd hs hp ho K p i f hV σ hσ
  refine ⟨σ,hCartan,hm,?_⟩
  intro j
  rw [Subgroup.map_equiv_normalizer_eq,hm j]

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalOppositeComplementAction
