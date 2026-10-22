import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalSimpleElements
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalLeadingAutomorphism
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalLeadingNoncommute
import SymmetricSubgroupAsymptotics.CFSGSimpleCoordinateAxisParameters
import SymmetricSubgroupAsymptotics.CFSGFinitePermutationRelation
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOffDiagonalCollecting

/-! The simple-axis permutation induced by an ACTUAL original positive
subgroup automorphism preserves the Cartan zero pattern. Orthogonal
source elements are literal commuting elements; adjacent target axes
are excluded by the exact characteristic-free second layer. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalDiagramAction
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

theorem positiveAut_axes_preserve_zero_forward (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r)
    (f : MulAut (originalPositive A hd hs hp ho K i)) (σ : Equiv.Perm (Fin r))
    (hσ : ∀j : Fin r,(axis (K:=K) j).map
      (originalLeadingAut A hd hs hp ho K p i f).toMonoidHom=axis (K:=K) (σ j))
    (j k : Fin r) (hjk : A j k=0) : A (σ j) (σ k)=0 := by
  let F := originalLeadingAut A hd hs hp ho K p i f
  let u := originalSimpleElement A hd hs hp ho K p i j 1
  let v := originalSimpleElement A hd hs hp ho K p i k 1
  obtain ⟨a,ha,heA⟩ := image_single_nonzero F j (σ j) (hσ j) 1 (one_ne_zero : (1:K)≠0)
  obtain ⟨b,hb,heB⟩ := image_single_nonzero F k (σ k) (hσ k) 1 (one_ne_zero : (1:K)≠0)
  have hu : originalLeadingHom A hd hs hp ho K p i (f u)=
      Multiplicative.ofAdd (Pi.single (σ j) a : Fin r→K) := by
    have hh := (originalLeadingAut_apply A hd hs hp ho K p i f u).symm
    change originalLeadingHom A hd hs hp ho K p i (f u)=
      F (originalLeadingHom A hd hs hp ho K p i u) at hh
    dsimp only [u] at hh
    rw [originalSimpleElement_leading] at hh
    exact hh.trans heA
  have hv : originalLeadingHom A hd hs hp ho K p i (f v)=
      Multiplicative.ofAdd (Pi.single (σ k) b : Fin r→K) := by
    have hh := (originalLeadingAut_apply A hd hs hp ho K p i f v).symm
    change originalLeadingHom A hd hs hp ho K p i (f v)=
      F (originalLeadingHom A hd hs hp ho K p i v) at hh
    dsimp only [v] at hh
    rw [originalSimpleElement_leading] at hh
    exact hh.trans heB
  have hc : Commute (f u) (f v) :=
    (originalSimpleElement_commute A hd hs hp ho K p i j k hjk 1 1).map f.toMonoidHom
  have hne : j≠k := by
    intro h
    subst k
    rw [hd j] at hjk
    norm_num at hjk
  rcases cartan_zero_or_neg_one A hs hp b₀ s₀ (σ j) (σ k)
      (fun h=>hne (σ.injective h)) with hz|hn
  · change (b₀).cartanMatrix (s₀ (σ k)) (s₀ (σ j))=0 at hz
    rwa [coordinate_cartan_transpose A hd hs hp ho] at hz
  · change (b₀).cartanMatrix (s₀ (σ k)) (s₀ (σ j))= -1 at hn
    rw [coordinate_cartan_transpose A hd hs hp ho] at hn
    exact False.elim (original_adjacent_leading_not_commute A hd hs hp ho K p i
      (σ j) (σ k) (f u) (f v) a b hn ha hb hu hv hc)

theorem positiveAut_axes_preserve_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r)
    (f : MulAut (originalPositive A hd hs hp ho K i)) (σ : Equiv.Perm (Fin r))
    (hσ : ∀j : Fin r,(axis (K:=K) j).map
      (originalLeadingAut A hd hs hp ho K p i f).toMonoidHom=axis (K:=K) (σ j))
    (j k : Fin r) : A (σ j) (σ k)=0↔A j k=0 :=
  CFSGFinitePermutationRelation.relation_iff_of_forward (fun j k=>A j k=0) σ
    (positiveAut_axes_preserve_zero_forward A hd hs hp ho K p i f σ hσ) j k

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalDiagramAction
