import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleEndpointSourceIndex
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddlePairingIndex

/-! The characteristic-three endpoint index bound on the same original
G2 central quotient. Every normalizer element used in the orbit proof
belongs to the actual fixed-root generated source, and its action here
is the literal original projection. No automorphism lift is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleEndpointIndex
open CFSG.Models.Chevalley PrimitiveSocleRawStructure
open CFSGGTwoD4GeckOriginalProjection CFSGGTwoD4GeckMiddleFixedRadicalCoordinates
open CFSGGTwoD4GeckMiddleCentralExtensionData CFSGGTwoD4GeckMiddlePairingIndex
open CFSGGTwoD4GeckMiddleSourceNormalizer CFSGGTwoD4GeckMiddleEndpointSourceIndex
variable (K : Type) [Field K] [Finite K] [CharP K 3]
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _
local instance [IsSimpleGroup (Projective CartanMatrix.G₂ K)] : Finite (Projective CartanMatrix.G₂ K) :=
  Finite.of_surjective (generatedToOriginal K) (generatedToOriginal_surjective K)

def sourceToOriginal [IsSimpleGroup (Projective CartanMatrix.G₂ K)] :
    sourceNormalizer K →* Projective CartanMatrix.G₂ K :=
  (generatedToOriginal K).comp (Subgroup.inclusion inf_le_right)

theorem source_highest_eq_central [IsSimpleGroup (Projective CartanMatrix.G₂ K)] :
    sourceToOriginal K (highestElement K) =
      originalMiddle K (central K (Multiplicative.ofAdd (1 : K))) := by
  apply congrArg (generatedToOriginal K)
  apply Subtype.ext
  rfl

theorem endpoint_le_proper_index [IsSimpleGroup (Projective CartanMatrix.G₂ K)]
    (hcard : 4 ≤ Nat.card K) (H : Subgroup (Projective CartanMatrix.G₂ K)) (hH : H ≠ ⊤) :
    3*(Nat.card K^2-1) ≤ H.index := by
  obtain ⟨x,hx⟩ := CFSGConjugateSubgroupDegree.exists_moved_coset_of_ne_one H hH
    (originalMiddle K (central K (Multiplicative.ofAdd (1 : K)))) (original_central_one_ne_one K)
  letI : MulAction (sourceNormalizer K) (Projective CartanMatrix.G₂ K ⧸ H) :=
    MulAction.compHom _ (sourceToOriginal K)
  have hm : highestElement K • x ≠ x := by
    change sourceToOriginal K (highestElement K) • x ≠ x
    rw [source_highest_eq_central]
    exact hx
  exact degree_le_of_highest_motion K hcard x hm

theorem typeGTwo_char_three_le_proper_index (q : CFSG.PrimePower) (hchar : q.prime = 3)
    (hq : 4 ≤ q.order) [IsSimpleGroup (CFSG.Models.G2 q)]
    (H : Subgroup (CFSG.Models.G2 q)) (hH : H ≠ ⊤) :
    3*(q.order^2-1) ≤ H.index := by
  letI : CharP q.Field 3 := by rw [←hchar]; infer_instance
  have hk : 4 ≤ Nat.card q.Field := by rw [q.card_field]; exact hq
  have hi := endpoint_le_proper_index q.Field hk H hH
  rw [q.card_field] at hi
  exact hi

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleEndpointIndex
