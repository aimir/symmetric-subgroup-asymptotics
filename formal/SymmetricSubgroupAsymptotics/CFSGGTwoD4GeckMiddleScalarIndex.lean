import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleScalarSourceIndex
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddlePairingIndex

/-! The coupled scalar-centre index bound acts on the same original G2
central quotient. Every normalizer element is a genuine generated source
element; original simplicity supplies only a moved coset. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleScalarIndex
open CFSG.Models.Chevalley PrimitiveSocleRawStructure
open CFSGGTwoD4GeckOriginalProjection CFSGGTwoD4GeckMiddlePairingIndex
open CFSGGTwoD4GeckMiddleSourceNormalizer CFSGGTwoD4GeckMiddleScalarSourceIndex
open CFSGGTwoD4GeckMiddleCentralExtensionData
variable (K : Type) [Field K] [Finite K]
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

theorem scalar_le_proper_index (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective CartanMatrix.G₂ K)] (hthree : (3 : K) ≠ 0)
    (H : Subgroup (Projective CartanMatrix.G₂ K)) (hH : H ≠ ⊤) :
    Nat.card K^2*(Nat.card K-1) ≤ H.index := by
  obtain ⟨x,hx⟩ := CFSGConjugateSubgroupDegree.exists_moved_coset_of_ne_one H hH
    (originalMiddle K (central K (Multiplicative.ofAdd (1 : K)))) (original_central_one_ne_one K)
  letI : MulAction (sourceNormalizer K) (Projective CartanMatrix.G₂ K ⧸ H) :=
    MulAction.compHom _ (sourceToOriginal K)
  have hm : highestElement K • x ≠ x := by
    change sourceToOriginal K (highestElement K) • x ≠ x
    rw [source_highest_eq_central]
    exact hx
  exact degree_le_of_highest_motion K hthree p x hm

theorem typeGTwo_scalar_le_proper_index (q : CFSG.PrimePower) (hchar : q.prime ≠ 3)
    [IsSimpleGroup (CFSG.Models.G2 q)] (H : Subgroup (CFSG.Models.G2 q)) (hH : H ≠ ⊤) :
    q.order^2*(q.order-1) ≤ H.index := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  have hthree : (3 : q.Field) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (R := q.Field) (p := q.prime) (by decide : Nat.Prime 3) hchar
  have hi := scalar_le_proper_index q.Field q.prime hthree H hH
  rw [q.card_field] at hi
  exact hi

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleScalarIndex
