import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWordRootElementSign
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalSignedParameters
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNegativeSimpleRootLine

/-! Literal canonical words act on original root parameters and root
lines through the SAME projection. No original automorphism is lifted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalWordRootAction
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckIntegralWord CFSGNormTwoGeckColumns
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoCoordinateElementaryRootParameters CFSGNormTwoCoordinateOriginalProjection
open CFSGNormTwoCoordinateOriginalSignedParameters CFSGNormTwoCoordinateOriginalAllRootLines
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCoordinateRootWeylAction
open CFSGNormTwoCoordinateWordRootElementSign CFSGSubgroupConjugateRestriction
open CFSGNormTwoCoordinateSelectedRootElement
open CFSGNormTwoCoordinateNegativeSimpleRootLine CFSGNormTwoCoordinateOriginalComplementNormalizer
variable {r:ℕ} (A:Matrix (Fin r) (Fin r) ℤ) (hd:∀i,A i i=2)
    (hs:A.transpose=A) (hp:(rationalMatrix A).PosDef) (ho:∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K:Type) [Field K]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀
local notation "H" => ElementaryGroup A hd hs hp ho K

def originalWord [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i:Fin r)
    (w:List (Fin r)) : Projective (cartan b₀ s₀) K :=
  originalProjection A hd hs hp ho K i (elementaryWord A hd hs hp ho K w)

theorem originalWord_root_parameter_sign
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i:Fin r)
    (w:List (Fin r)) (k:Roots A) :
    ∃epsilon:ℤ,(epsilon=1∨epsilon= -1)∧∀a:K,
      originalWord A hd hs hp ho K i w*
        rootParameterHom A hd hs hp ho K i k (Multiplicative.ofAdd a)*
          (originalWord A hd hs hp ho K i w)⁻¹=
      rootParameterHom A hd hs hp ho K i (wordRoot A hs hp b₀ s₀ w k)
        (Multiplicative.ofAdd ((epsilon:K)*a)) := by
  obtain ⟨epsilon,hepsilon,h⟩ := word_selected_root_sign A hd hs hp ho w k
  refine ⟨epsilon,hepsilon,?_⟩
  intro a
  have he : elementaryWord A hd hs hp ho K w*
      elementarySelectedRootHom A hd hs hp ho K k (Multiplicative.ofAdd a)*
        (elementaryWord A hd hs hp ho K w)⁻¹=
      elementarySelectedRootHom A hd hs hp ho K (wordRoot A hs hp b₀ s₀ w k)
        (Multiplicative.ofAdd ((epsilon:K)*a)) := by
    apply Subtype.ext
    change wordUnit A hs hp b₀ s₀ K w*selectedRootElement A hd hs hp ho K k a*
      (wordUnit A hs hp b₀ s₀ K w)⁻¹=selectedRootElement A hd hs hp ho K
        (wordRoot A hs hp b₀ s₀ w k) ((epsilon:K)*a)
    simpa only [word_eq_canonicalWord] using h K a
  simpa only [originalWord,rootParameterHom,MonoidHom.comp_apply,map_mul,map_inv]
    using congrArg (originalProjection A hd hs hp ho K i) he

theorem originalWord_root_line_map
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i:Fin r)
    (w:List (Fin r)) (k:Roots A) :
    (originalFullRootLine A hd hs hp ho K i k).map
      (MulAut.conj (originalWord A hd hs hp ho K i w)).toMonoidHom=
        originalFullRootLine A hd hs hp ho K i (wordRoot A hs hp b₀ s₀ w k) := by
  have he := rootSubgroup_map_word A hd hs hp ho K w k
  have hr : (elementaryRootSubgroup A hd hs hp ho K k).map
      (MulAut.conj (elementaryWord A hd hs hp ho K w)).toMonoidHom=
      elementaryRootSubgroup A hd hs hp ho K (wordRoot A hs hp b₀ s₀ w k) := by
    apply restrict_conjugate H _ _ (rootSubgroup_le_elementary A hd hs hp ho K k)
      (rootSubgroup_le_elementary A hd hs hp ho K _) (elementaryWord A hd hs hp ho K w)
    simpa only [elementaryWord,word_eq_canonicalWord] using he
  change ((elementaryRootSubgroup A hd hs hp ho K k).map
    (originalProjection A hd hs hp ho K i)).map
      (MulAut.conj (originalProjection A hd hs hp ho K i
        (elementaryWord A hd hs hp ho K w))).toMonoidHom=_
  rw [←map_conjugate,hr]
  rfl

theorem originalWord_negative_simple_map
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i j:Fin r)
    (w:List (Fin r)) :
    (originalNegativeSimpleRootGroup A hd hs hp ho K i j).map
      (MulAut.conj (originalWord A hd hs hp ho K i w)).toMonoidHom=
      originalFullRootLine A hd hs hp ho K i
        (wordRoot A hs hp b₀ s₀ w (negativeIndex A hs hp (s₀ j))) := by
  have he : originalNegativeSimpleRootGroup A hd hs hp ho K i j=
      originalFullRootLine A hd hs hp ho K i (negativeIndex A hs hp (s₀ j)) := by
    change ((canonicalRootSubgroup D K true j).subgroupOf H).map _=
      ((rootSubgroup A hd hs hp ho K (negativeIndex A hs hp (s₀ j))).subgroupOf H).map _
    rw [rootSubgroup_negative_simple_eq_canonical A hd hs hp ho K j]
  rw [he]
  exact originalWord_root_line_map A hd hs hp ho K i w _

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalWordRootAction
