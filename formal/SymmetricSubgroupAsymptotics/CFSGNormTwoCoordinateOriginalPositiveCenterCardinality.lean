import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveRootCardinality
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalPositiveSylow

/-! Exact field cardinality of the FULL centre, first in matrix U and
then in its literal original-projective image/Sylow. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalPositiveCenterCardinality
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoGeckIntegralRealization
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoCoordinateRootHeightQuotient
open CFSGNormTwoCoordinatePositiveRootGenerators CFSGNormTwoCoordinatePositiveRootCardinality
open CFSGNormTwoCoordinatePositiveCenter CFSGNormTwoCoordinateRootSubgroup
open CFSGNormTwoCoordinateOriginalPositiveCenter CFSGNormTwoCoordinateOriginalPositiveSylow
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem positive_center_card [Nonempty (Fin r)] :
    Nat.card (Subgroup.center (PositiveGroup A hd hs hp ho K))=Nat.card K := by
  obtain ⟨θ,hθ,hdom,hcenter⟩ := exists_root_subgroup_center A hd hs hp ho K
  rw [hcenter]
  calc
    _=Nat.card (rootSubgroup A hd hs hp ho K θ) := Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (positive_root_subgroup_le A hd hs hp ho K θ hθ)).toEquiv
    _=Nat.card K := positive_rootSubgroup_card A hd hs hp ho K θ hθ

theorem original_positive_center_card [Finite K] [Nontrivial (Fin r)]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) :
    Nat.card (Subgroup.center (originalPositive A hd hs hp ho K i))=Nat.card K := by
  calc
    _=Nat.card (Subgroup.center (PositiveGroup A hd hs hp ho K)) :=
      (Nat.card_congr (Subgroup.centerCongr (originalPositiveEquiv A hd hs hp ho K p i)).toEquiv).symm
    _=Nat.card K := positive_center_card A hd hs hp ho K

theorem original_positive_sylow_center_card [Finite K] [Nontrivial (Fin r)]
    (ε : Fin r→ℤ) (hε : ∀j,ε j*ε j=1) (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)→wordLinear A hs hp b₀ s₀ w=1)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) :
    Nat.card (Subgroup.center (originalPositiveSylow A hd hs hp ho K ε hε hA hidentity p i))=Nat.card K := by
  change Nat.card (Subgroup.center ((originalPositiveSylow A hd hs hp ho K ε hε hA hidentity p i) :
    Subgroup (Projective (cartan b₀ s₀) K)))=Nat.card K
  rw [originalPositiveSylow_coe]
  exact original_positive_center_card A hd hs hp ho K p i

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalPositiveCenterCardinality
