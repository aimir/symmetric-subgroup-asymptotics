import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalSimpleRootAction
import SymmetricSubgroupAsymptotics.CFSGSubgroupFamilyIndex
import SymmetricSubgroupAsymptotics.CFSGExceptionalDiagramAutomorphisms

/-! Actual original pair stabilizer and its literal positive simple-root
kernel. Its index is bounded by the actual Cartan diagram group, using
the proved original root action rather than a supplied permutation action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalSimpleStabilizer
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoCoordinateOriginalPositiveCenter
open CFSGNormTwoCoordinateOriginalOppositeAlignment CFSGNormTwoCoordinateOriginalSimpleRootAction
open CFSGNormTwoCoordinateOriginalNormalizerIntersection
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K] [Finite K] [Nontrivial (Fin r)]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

open CFSGSubgroupFamilyStabilizer CFSGSubgroupFamilyIndex CFSGExceptionalDiagramAutomorphisms

def originalPairStabilizer
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) :
    Subgroup (MulAut (Projective (cartan b₀ s₀) K)) :=
  familyStabilizer (fun neg : Bool => if neg then originalNegative A hd hs hp ho K i
    else originalPositive A hd hs hp ho K i)

 theorem pair_preserves_positive
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r)
    (f : originalPairStabilizer A hd hs hp ho K i) :
    (originalPositive A hd hs hp ho K i).map f.val.toMonoidHom =
      originalPositive A hd hs hp ho K i := f.property false

 theorem pair_preserves_negative
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r)
    (f : originalPairStabilizer A hd hs hp ho K i) :
    (originalNegative A hd hs hp ho K i).map f.val.toMonoidHom =
      originalNegative A hd hs hp ho K i := f.property true

 def originalSimpleStabilizer
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) :
    Subgroup (originalPairStabilizer A hd hs hp ho K i) :=
  (familyStabilizer (originalSimpleRootGroup A hd hs hp ho K i)).subgroupOf
    (originalPairStabilizer A hd hs hp ho K i)

 def simpleStabilizerAction
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) :
    originalSimpleStabilizer A hd hs hp ho K i →* MulAut (Projective (cartan b₀ s₀) K) :=
  (originalPairStabilizer A hd hs hp ho K i).subtype.comp
    (originalSimpleStabilizer A hd hs hp ho K i).subtype

 theorem simple_stabilizer_preserves_simple
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r)
    (f : originalSimpleStabilizer A hd hs hp ho K i) (j : Fin r) :
    (originalSimpleRootGroup A hd hs hp ho K i j).map
      (simpleStabilizerAction A hd hs hp ho K i f).toMonoidHom =
        originalSimpleRootGroup A hd hs hp ho K i j := f.property j

theorem simple_stabilizer_index_le_diagram
    (ε : Fin r→ℤ) (hε : ∀j,ε j*ε j=1) (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)→wordLinear A hs hp b₀ s₀ w=1)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) (θ : Roots A)
    (hθ : ∀j,0≤θ.val j)
    (hdom : ∀j,0 ≤ integerPairing A θ.val (Pi.single j (1:ℤ) : Fin r→ℤ))
 :
    (originalSimpleStabilizer A hd hs hp ho K i).index ≤ Nat.card (diagramGroup A) := by
  apply family_index_le_permutations (originalPairStabilizer A hd hs hp ho K i)
    (originalSimpleRootGroup A hd hs hp ho K i) (fun σ => ∀ j k, A (σ j) (σ k) = A j k)
  intro f
  exact exists_simpleRootGroup_permutation A hd hs hp ho K ε hε hA hidentity p i θ hθ hdom
    f.val (pair_preserves_negative A hd hs hp ho K i f)
    (pair_preserves_positive A hd hs hp ho K i f)

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalSimpleStabilizer
