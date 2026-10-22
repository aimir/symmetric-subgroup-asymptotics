import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalAxisAction
import SymmetricSubgroupAsymptotics.CFSGSimpleCoordinateAxisPermutation

/-! The actual ambient automorphism acts by a genuine permutation on
the intrinsically recognized simple axes of the original positive
abelianization. No lift of those axes to literal roots is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalAxisPermutation
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

theorem ambientLeadingAut_axis_permutation
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
    ∃σ : Equiv.Perm (Fin r),∀j : Fin r,(axis (K:=K) j).map
      (ambientLeadingAut A hd hs hp ho K p i f hU).toMonoidHom=axis (K:=K) (σ j) :=
  exists_axis_permutation _
    (ambientLeadingAut_maps_axis A hd hs hp ho K ε hε hA hidentity p i θ hθ hdom f hU)

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalAxisPermutation
