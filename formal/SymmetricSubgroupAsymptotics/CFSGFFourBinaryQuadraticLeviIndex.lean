import SymmetricSubgroupAsymptotics.CFSGFFourBinaryGraphStabilizerIndex
import SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree
import Mathlib.Algebra.CharP.CharAndCard

/-! The surviving actual central root moves an original simple F4 coset.
Restricting that SAME coset action to the actual conjugation graph gives
index128. Its faithful fifteen-coordinate radical also gives the order
lower bound used in both primitive degree forms. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourBinaryQuadraticLeviIndex
open CFSGFFourBinaryLeviConjugationGraph CFSGFFourBinaryGraphCentralLayers
open CFSGFFourBinaryGraphPointLayers CFSGFFourBinaryGraphStabilizerIndex
open CFSGFFourBinaryActualNormalizerCoordinates CFSGFFourBinaryFixedRadicalEmbedding
open CFSGFFourBinaryRadicalCentralLayers CFSGFFourE6OriginalProjection
open CFSG.Models.Chevalley
local instance fFourBinaryIndexRootsDecidableEq :
    DecidableEq (CFSGNormTwoRootPairing.Roots CartanMatrix.E₆) := Classical.decEq _
variable (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K=2)

private theorem degree_of_central_motion {X : Type*} [Finite X]
    [MulAction (Graph K hK) X] (x : X)
    (hx : ((pointLift K hK (Multiplicative.ofAdd ((0,1) : Point K))) : Graph K hK) • x ≠ x) :
    128 ≤ Nat.card X := by
  let M := MulAction.stabilizer (Graph K hK) x
  have hM : pointLift K hK (Multiplicative.ofAdd ((0,1) : Point K)) ∉
      M.comap (liftedRadical K hK).subtype := hx
  have hi : M.index ≤ Nat.card X := by
    calc
      _ = Nat.card (MulAction.orbit (Graph K hK) x) :=
        (Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (Graph K hK) x)).symm
      _ ≤ Nat.card X := Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  exact (graph_index_lower K hK M hM).trans hi

variable [IsSimpleGroup (Projective CartanMatrix.F₄ K)]

private def graphToOriginal : Graph K hK →* Projective CartanMatrix.F₄ K :=
  (originalProjection K).comp (second K hK)

theorem binary_radical_card_le_original_order :
    Nat.card K^15 ≤ Nat.card (Projective CartanMatrix.F₄ K) := by
  letI : Finite (Projective CartanMatrix.F₄ K) := original_finite K
  have h := Nat.card_le_card_of_injective (originalHom K) (originalHom_injective K)
  simpa only [radical_card] using h

include hK in
theorem binary_levi_le_proper_index
    (H : Subgroup (Projective CartanMatrix.F₄ K)) (hH : H≠⊤) : 128 ≤ H.index := by
  letI : Finite (Projective CartanMatrix.F₄ K) := original_finite K
  let r : Radical K :=
    (CFSGHeisenbergCoordinateGroup.central (Multiplicative.ofAdd (1 : K)),1)
  have hr : r≠1 := by
    intro he
    exact one_ne_zero (congrArg (fun y : Radical K => y.1.c) he)
  have hfr : originalHom K r≠1 := by
    intro he
    exact hr (originalHom_injective K (he.trans (map_one (originalHom K)).symm))
  let z : Graph K hK := (pointLift K hK (Multiplicative.ofAdd ((0,1) : Point K))).val
  have hz : graphToOriginal K hK z=originalHom K r := rfl
  have hnon : graphToOriginal K hK z≠1 := by rw [hz]; exact hfr
  obtain ⟨x,hx⟩ := CFSGConjugateSubgroupDegree.exists_moved_coset_of_ne_one H hH _ hnon
  letI : MulAction (Graph K hK) (Projective CartanMatrix.F₄ K ⧸ H) :=
    MulAction.compHom _ (graphToOriginal K hK)
  have hb := degree_of_central_motion K hK x hx
  simpa only [Subgroup.index_eq_card] using hb

theorem typeFFour_binary_order_fifteen_le (q : CFSG.PrimePower) (hq : q.order=2)
    [IsSimpleGroup (CFSG.Models.F4 q)] : 2^15 ≤ Nat.card (CFSG.Models.F4 q) := by
  letI : Fintype q.Field := Fintype.ofFinite q.Field
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : Nat.card q.Field=2 := q.card_field.trans hq
  letI : CharP q.Field 2 := charP_of_card_eq_prime
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  have h := binary_radical_card_le_original_order q.Field
  simpa only [hc] using h

theorem typeFFour_binary_levi_le_proper_index (q : CFSG.PrimePower) (hq : q.order=2)
    [IsSimpleGroup (CFSG.Models.F4 q)]
    (H : Subgroup (CFSG.Models.F4 q)) (hH : H≠⊤) : 128 ≤ H.index := by
  letI : Fintype q.Field := Fintype.ofFinite q.Field
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : Nat.card q.Field=2 := q.card_field.trans hq
  letI : CharP q.Field 2 := charP_of_card_eq_prime
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  exact binary_levi_le_proper_index q.Field hc H hH

end SymmetricSubgroupAsymptotics.CFSGFFourBinaryQuadraticLeviIndex
