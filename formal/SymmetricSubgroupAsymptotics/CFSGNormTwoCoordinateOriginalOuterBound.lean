import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalTorusStabilizer
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalPairAlignment
import SymmetricSubgroupAsymptotics.CFSGOuterAlignedIndex

/-! Actual original outer automorphisms are bounded by the literal
Cartan monomial-image index, the actual field-automorphism cardinal, and
the actual diagram-group cardinal. Pair alignment, root recognition,
faithfulness and inner torus realization are proved original-model inputs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalOuterBound
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

open CFSGNormTwoCoordinateOriginalSimpleStabilizer CFSGNormTwoCoordinateOriginalStabilizerParameters
open CFSGNormTwoCoordinateOriginalSimpleParameters CFSGNormTwoCoordinateOriginalProductTorus
open CFSGNormTwoCoordinateOriginalProductTorusRoots CFSGNormTwoCoordinateOriginalAllRootLines
open CFSGIntegerMatrixPowerHom CFSGSemilinearRootCosetIndex

open CFSGNormTwoCoordinateOriginalTorusStabilizer CFSGNormTwoCoordinateOriginalPairAlignment
open CFSGNormTwoCoordinateOriginalRootFamily CFSGOuterAlignedIndex PrimitiveSocleRawStructure

private theorem outer_bound_of_inner_lift {G : Type} [Group G] [Finite G]
    {B : Type*} [Group B] (S : Subgroup (MulAut G)) (T : Subgroup S)
    (lift : B →* T)
    (halign : ∀ f : MulAut G, ∃ g, MulAut.conj g * f ∈ S)
    (hinner : ∀ t, ((lift t).val.val : MulAut G) ∈ Inner G)
    (a b : ℕ) (hT : T.index ≤ a) (hlift : lift.range.index ≤ b) :
    Nat.card (Outer G) ≤ b * a := by
  refine outer_card_le_aligned_tower S T lift.range halign ?_ a b hT hlift
  rintro ⟨r, ⟨t, ht⟩⟩
  change (r.val.val : MulAut G) ∈ Inner G
  rw [← ht]
  exact hinner t

theorem original_outer_card_le
    (ε : Fin r→ℤ) (hε : ∀j,ε j*ε j=1) (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)→wordLinear A hs hp b₀ s₀ w=1)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) (θ : Roots A)
    (hθ : ∀j,0≤θ.val j)
    (hdom : ∀j,0 ≤ integerPairing A θ.val (Pi.single j (1:ℤ) : Fin r→ℤ))

    (j₀ k₀ : Fin r) (hjk : A j₀ k₀ = -1)
    (hconn : ∀ j, Relation.ReflTransGen (fun a b => A a b ≠ 0) j₀ j)
    (hneighbors : ∀ j, ∃ k, A j k = -1) :
    Nat.card (Outer (Projective (cartan b₀ s₀) K)) ≤
      ((powerHom (G := Kˣ) A).range.index * Nat.card (K ≃+* K)) * Nat.card (diagramGroup A) := by
  letI : Finite (Projective (cartan b₀ s₀) K) := original_projective_finite A hd hs hp ho K i
  have halign : ∀ f : MulAut (Projective (cartan b₀ s₀) K), ∃ g,
      MulAut.conj g * f ∈ originalPairStabilizer A hd hs hp ho K i := by
    intro f
    obtain ⟨g, hU, hV⟩ := original_exists_inner_fix_pair A hd hs hp ho K ε hε hA hidentity p i f
    refine ⟨g, ?_⟩
    intro neg
    cases neg
    · exact hU
    · exact hV
  exact outer_bound_of_inner_lift (originalPairStabilizer A hd hs hp ho K i)
    (originalSimpleStabilizer A hd hs hp ho K i)
    (productTorusSimpleHom A hd hs hp ho K i) halign
    (product_torus_lift_inner A hd hs hp ho K i)
    (Nat.card (diagramGroup A))
    ((powerHom (G := Kˣ) A).range.index * Nat.card (K ≃+* K))
    (simple_stabilizer_index_le_diagram A hd hs hp ho K ε hε hA hidentity p i θ hθ hdom)
    (simple_stabilizer_torus_index_le A hd hs hp ho K ε hε hA hidentity p i θ hθ hdom
      j₀ k₀ hjk hconn hneighbors)

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalOuterBound
