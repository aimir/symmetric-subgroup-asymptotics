import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalDiagramAction
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalAxisPermutation

/-! The actual simple-axis permutation of an original ambient
U-preserving automorphism preserves the FULL original Cartan matrix.
This is a diagram action, not yet a literal-root lifting theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalCartanAction
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoCoordinateOriginalPositiveCenter
open CFSGNormTwoCoordinateRootHeightQuotient CFSGNormTwoCoordinateLeadingHom
open CFSGNormTwoCoordinateDerivedFirstLayer CFSGNormTwoCoordinateRootLeadingAxes
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCoordinateOriginalAllRootLines
open CFSGNormTwoCoordinateOriginalProjection CFSGNormTwoCoordinatePositiveQuotientInjectivity
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K] [Finite K] [Nontrivial (Fin r)]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

open CFSGNormTwoCoordinateOriginalLeadingHom CFSGNormTwoCoordinateLeadingHom

open CFSGNormTwoCoordinateOriginalSimpleElements CFSGNormTwoCoordinateOriginalLeadingAutomorphism
open CFSGNormTwoCoordinateOriginalLeadingNoncommute CFSGSimpleCoordinateAxisParameters
open CFSGSimpleCoordinateAxes CFSGNormTwoGeckOffDiagonalCollecting

open CFSGNormTwoCoordinateOriginalDiagramAction CFSGNormTwoCoordinateOriginalAxisAction
open CFSGNormTwoCoordinateOriginalAxisPermutation CFSGInvariantSubgroupCoordinateImage
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear

include hd hs hp ho in
private theorem coordinate_offDiagonal (j k : Fin r) (hjk : j≠k) :
    A j k=0 ∨ A j k= -1 := by
  have hh := cartan_zero_or_neg_one A hs hp b₀ s₀ j k hjk
  change (b₀).cartanMatrix (s₀ k) (s₀ j)=0 ∨ (b₀).cartanMatrix (s₀ k) (s₀ j)= -1 at hh
  simpa only [coordinate_cartan_transpose A hd hs hp ho] using hh

theorem positiveAut_axes_preserve_cartan (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r)
    (f : MulAut (originalPositive A hd hs hp ho K i)) (σ : Equiv.Perm (Fin r))
    (hσ : ∀j : Fin r,(axis (K:=K) j).map
      (originalLeadingAut A hd hs hp ho K p i f).toMonoidHom=axis (K:=K) (σ j)) :
    ∀j k : Fin r,A (σ j) (σ k)=A j k := by
  intro j k
  by_cases hjk : j=k
  · subst k
    rw [hd (σ j),hd j]
  have hz := positiveAut_axes_preserve_zero A hd hs hp ho K p i f σ hσ j k
  rcases coordinate_offDiagonal A hd hs hp ho j k hjk with h0|h1
  · rw [h0]
    exact hz.mpr h0
  rcases coordinate_offDiagonal A hd hs hp ho (σ j) (σ k)
    (fun h=>hjk (σ.injective h)) with h0|h1'
  · have hc := hz.mp h0
    rw [h1] at hc
    norm_num at hc
  · exact h1'.trans h1.symm

theorem ambientLeadingAut_cartan_permutation
    (ε : Fin r→ℤ) (hε : ∀j,ε j*ε j=1) (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)→wordLinear A hs hp b₀ s₀ w=1)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) (θ : Roots A)
    (hθ : ∀j,0≤θ.val j)
    (hdom : ∀j,0 ≤ integerPairing A θ.val (Pi.single j (1:ℤ) : Fin r→ℤ))
    (f : MulAut (Projective (cartan b₀ s₀) K))
    (hU : (originalPositive A hd hs hp ho K i).map f.toMonoidHom=
      originalPositive A hd hs hp ho K i) :
    ∃σ : Equiv.Perm (Fin r),(∀j : Fin r,(axis (K:=K) j).map
      (ambientLeadingAut A hd hs hp ho K p i f hU).toMonoidHom=axis (K:=K) (σ j)) ∧
      ∀j k : Fin r,A (σ j) (σ k)=A j k := by
  obtain ⟨σ,hσ⟩ := ambientLeadingAut_axis_permutation A hd hs hp ho K
    ε hε hA hidentity p i θ hθ hdom f hU
  refine ⟨σ,hσ,?_⟩
  exact positiveAut_axes_preserve_cartan A hd hs hp ho K p i
    (restrictAut (originalPositive A hd hs hp ho K i) f hU) σ hσ

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalCartanAction
