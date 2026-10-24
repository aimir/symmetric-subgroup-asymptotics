import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDiagramFieldRootTwist
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSelectedRootElement

/-! Actual selected root parameters under a Cartan diagram--field twist.
The parameter sign is obtained once from integral root-word comparison,
before choosing any coefficient ring or field automorphism.  A root-line
range equality is not used as a parameter identity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSelectedRootDiagramParameterTwist
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoGeckColumns
open CFSGNormTwoGeckIntegralWord CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCartanDiagramRoots
open CFSGNormTwoCartanDiagramWords CFSGNormTwoCoordinateDiagramIndices
open CFSGNormTwoCoordinateRootWordIdentity CFSGNormTwoCoordinateSelectedRootElement
open CFSGNormTwoCoordinateDiagramFieldRootTwist CFSGSerreQuadraticWordRootTransport

variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i, A i i = 2)
  (hs : A.transpose = A) (hp : (rationalMatrix A).PosDef)
  (ho : ∀ i j, i ≠ j → A i j ≤ 0)
  [Fintype (Roots A)] [DecidableEq (Roots A)]
  [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
  (p : Equiv.Perm (Fin r)) (hA : ∀ i j, A (p i) (p j) = A i j)

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀

theorem rootWitness_diagram_degree (k : Roots A) :
    (rootPermutation A p hA k).val =
      wordLinear A hs hp b₀ s₀ ((rootWitness A hd hs hp ho k).val.1.map p)
        (-(s₀ (p (rootWitness A hd hs hp ho k).val.2) : Roots A).val) := by
  let z := rootWitness A hd hs hp ho k
  have hw : wordRoot A hs hp b₀ s₀ z.val.1
      (negativeIndex A hs hp (s₀ z.val.2)) = k := by
    apply Subtype.ext
    rw [← wordLinear_root, negative_val]
    exact z.property.symm
  have he := wordRoot_permutation A hd hs hp ho p hA z.val.1
    (negativeIndex A hs hp (s₀ z.val.2))
  change rootPermutation A p hA
      (wordRoot A hs hp b₀ s₀ z.val.1 (negativeIndex A hs hp (s₀ z.val.2))) =
    wordRoot A hs hp b₀ s₀ (z.val.1.map p)
      (rootPermutation A p hA (negativeIndex A hs hp (s₀ z.val.2))) at he
  have hsimple : rootPermutation A p hA (s₀ z.val.2 : Roots A) =
      (s₀ (p z.val.2) : Roots A) := simple_rootPermutation A hd hs hp ho p hA z.val.2
  rw [hw, rootPermutation_negative, hsimple] at he
  rw [congrArg Subtype.val he, ← wordLinear_root, negative_val]

theorem selectedRootElement_twist_sign (k : Roots A) :
    ∃ eps : ℤ, (eps = 1 ∨ eps = -1) ∧
      ∀ (K : Type) [CommRing K] (sigma : K ≃+* K) (a : K),
        unitTwist A hd hs hp ho p hA K sigma
            (selectedRootElement A hd hs hp ho K k a) =
          selectedRootElement A hd hs hp ho K (rootPermutation A p hA k)
            ((eps : K) * sigma a) := by
  let z := rootWitness A hd hs hp ho k
  let t := rootWitness A hd hs hp ho (rootPermutation A p hA k)
  have hdegree : wordLinear A hs hp b₀ s₀ (z.val.1.map p)
      (-(s₀ (p z.val.2) : Roots A).val) =
      wordLinear A hs hp b₀ s₀ t.val.1 (-(s₀ t.val.2 : Roots A).val) :=
    (rootWitness_diagram_degree A hd hs hp ho p hA k).symm.trans t.property
  obtain ⟨eps, heps, he⟩ := same_degree_root_identity A hd hs hp ho
    (z.val.1.map p) t.val.1 (p z.val.2) t.val.2 hdegree
  refine ⟨eps, heps, ?_⟩
  intro K _ sigma a
  change unitTwist A hd hs hp ho p hA K sigma
      (CFSGSerreQuadraticWordRootTransport.rootWord D K z.val.1 true z.val.2 a) =
    CFSGSerreQuadraticWordRootTransport.rootWord D K t.val.1 true t.val.2
      ((eps : K) * sigma a)
  rw [unitTwist_root_word]
  exact he K (sigma a)

end SymmetricSubgroupAsymptotics.CFSGSelectedRootDiagramParameterTwist
