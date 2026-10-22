import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateIntrinsicLeadingAxes
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalLeadingAutomorphism
import SymmetricSubgroupAsymptotics.CFSGInvariantSubgroupCoordinateImage

/-! Actual ambient automorphisms preserving the ORIGINAL positive Sylow
send its intrinsic simple axes to simple axes in the abelianization.
This asserts no literal simple-root lift or semilinearity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalAxisAction
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoCoordinateOriginalPositiveCenter
open CFSGNormTwoCoordinateOriginalRootFamily CFSGNormTwoCoordinateOriginalLeadingHom
open CFSGNormTwoCoordinateIntrinsicLeadingAxes CFSGNormTwoCoordinateOriginalLeadingAutomorphism
open CFSGInvariantSubgroupCoordinateImage CFSGSimpleCoordinateAxes
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K] [Finite K] [Nontrivial (Fin r)]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

def ambientLeadingAut (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r)
    (f : MulAut (Projective (cartan b₀ s₀) K))
    (hU : (originalPositive A hd hs hp ho K i).map f.toMonoidHom=
      originalPositive A hd hs hp ho K i) : MulAut (Multiplicative (Fin r→K)) :=
  originalLeadingAut A hd hs hp ho K p i
    (restrictAut (originalPositive A hd hs hp ho K i) f hU)

theorem ambientLeadingAut_apply (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r)
    (f : MulAut (Projective (cartan b₀ s₀) K))
    (hU : (originalPositive A hd hs hp ho K i).map f.toMonoidHom=
      originalPositive A hd hs hp ho K i) (u : originalPositive A hd hs hp ho K i) :
    ambientLeadingAut A hd hs hp ho K p i f hU (originalLeadingHom A hd hs hp ho K p i u)=
      originalLeadingHom A hd hs hp ho K p i
        (restrictAut (originalPositive A hd hs hp ho K i) f hU u) :=
  originalLeadingAut_apply A hd hs hp ho K p i _ u

theorem ambientLeadingAut_maps_intrinsic
    (ε : Fin r→ℤ) (hε : ∀j,ε j*ε j=1) (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)→wordLinear A hs hp b₀ s₀ w=1)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) (θ : Roots A)
    (hθ : ∀j,0≤θ.val j)
    (hdom : ∀j,0 ≤ integerPairing A θ.val (Pi.single j (1:ℤ) : Fin r→ℤ))
    (f : MulAut (Projective (cartan b₀ s₀) K))
    (hU : (originalPositive A hd hs hp ho K i).map f.toMonoidHom=
      originalPositive A hd hs hp ho K i)
    (L : Subgroup (Multiplicative (Fin r→K)))
    (hL : L∈intrinsicLeadingAxes A hd hs hp ho K p i θ) :
    L.map (ambientLeadingAut A hd hs hp ho K p i f hU).toMonoidHom∈
      intrinsicLeadingAxes A hd hs hp ho K p i θ := by
  obtain ⟨hne,g,hg,hLg⟩ := hL
  obtain ⟨h,he⟩ := automorphism_maps_originalConjugateRootLine A hd hs hp ho K
    ε hε hA hidentity p i θ hθ hdom f g
  have hh : originalConjugateRootLine A hd hs hp ho K i θ h≤originalPositive A hd hs hp ho K i := by
    rw [←he,←hU]
    exact Subgroup.map_mono hg
  refine ⟨map_ne_bot _ L hne,h,hh,?_⟩
  rw [hLg]
  exact coordinate_image_map (originalPositive A hd hs hp ho K i) f hU
    (originalLeadingHom A hd hs hp ho K p i)
    (ambientLeadingAut A hd hs hp ho K p i f hU)
    (ambientLeadingAut_apply A hd hs hp ho K p i f hU)
    (originalConjugateRootLine A hd hs hp ho K i θ g)
    (originalConjugateRootLine A hd hs hp ho K i θ h) hg hh he

theorem ambientLeadingAut_maps_axis
    (ε : Fin r→ℤ) (hε : ∀j,ε j*ε j=1) (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)→wordLinear A hs hp b₀ s₀ w=1)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) (θ : Roots A)
    (hθ : ∀j,0≤θ.val j)
    (hdom : ∀j,0 ≤ integerPairing A θ.val (Pi.single j (1:ℤ) : Fin r→ℤ))
    (f : MulAut (Projective (cartan b₀ s₀) K))
    (hU : (originalPositive A hd hs hp ho K i).map f.toMonoidHom=
      originalPositive A hd hs hp ho K i) (j : Fin r) :
    ∃k : Fin r,(axis (K:=K) j).map
      (ambientLeadingAut A hd hs hp ho K p i f hU).toMonoidHom=axis (K:=K) k := by
  have hj : axis (K:=K) j∈intrinsicLeadingAxes A hd hs hp ho K p i θ := by
    rw [intrinsicLeadingAxes_eq_axes A hd hs hp ho K ε hε hA hidentity p i θ hθ hdom]
    exact ⟨j,rfl⟩
  have hm := ambientLeadingAut_maps_intrinsic A hd hs hp ho K ε hε hA hidentity
    p i θ hθ hdom f hU (axis (K:=K) j) hj
  rw [intrinsicLeadingAxes_eq_axes A hd hs hp ho K ε hε hA hidentity p i θ hθ hdom] at hm
  obtain ⟨k,hk⟩ := hm
  exact ⟨k,hk.symm⟩

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalAxisAction
