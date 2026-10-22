import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveSylow
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalPositiveCenter

/-! The actual original-projective image of U is the displayed mapped
Sylow, not just an unspecified existential good-Sylow witness. Exact
exceptional word/sign installers are to discharge the generic premises. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalPositiveSylow
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoGeckIntegralRealization
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoCoordinateElementaryRootParameters
open CFSGNormTwoCoordinatePositiveSylow CFSGNormTwoCoordinateOriginalProjection
open CFSGNormTwoCoordinateOriginalPositiveCenter CFSGNormTwoCoordinatePositiveQuotientInjectivity
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K] [Finite K]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

def originalPositiveSylow
    (ε : Fin r→ℤ) (hε : ∀j,ε j*ε j=1) (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)→wordLinear A hs hp b₀ s₀ w=1)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) :
    Sylow p (Projective (cartan b₀ s₀) K) := by
  letI : Fintype K := Fintype.ofFinite K
  exact (canonicalPositiveSylow A hd hs hp ho K ε hε hA hidentity p).mapSurjective
    (f:=originalProjection A hd hs hp ho K i) (originalProjection_surjective A hd hs hp ho K i)

theorem originalPositiveSylow_coe
    (ε : Fin r→ℤ) (hε : ∀j,ε j*ε j=1) (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)→wordLinear A hs hp b₀ s₀ w=1)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) :
    (originalPositiveSylow A hd hs hp ho K ε hε hA hidentity p i : Subgroup (Projective (cartan b₀ s₀) K))=
      originalPositive A hd hs hp ho K i := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  calc
    _ = ((rootGroup A hs hp b₀ s₀ K false).subgroupOf (ElementaryGroup A hd hs hp ho K)).map
        (originalProjection A hd hs hp ho K i) := by
      change (canonicalPositiveSylow A hd hs hp ho K ε hε hA hidentity p :
        Subgroup (ElementaryGroup A hd hs hp ho K)).map (originalProjection A hd hs hp ho K i)=_
      rw [canonicalPositiveSylow_coe]
    _ = (positiveInclusion A hd hs hp ho K).range.map (originalProjection A hd hs hp ho K i) := by
      rw [positiveInclusion,Subgroup.inclusion_range]
    _ = originalPositive A hd hs hp ho K i :=
      (MonoidHom.range_comp _ _).symm

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalPositiveSylow
