import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleCentralExtensionData
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalProjection
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFixedCommutators
import SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex

/-! The actual diagram-fixed middle radical injects into the SAME
original G2 central quotient. Its nondegenerate four-coordinate pairing
forces p*q^2 proper index in characteristic different from three. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddlePairingIndex

open CFSGGTwoD4GeckMiddleFixedRadicalCoordinates CFSGGTwoD4GeckMiddleCentralExtensionData
open CFSGGTwoD4GeckOriginalProjection CFSGTrialityGeckRelativeRootGenerated
open CFSGTrialityGeckRootGeneratedPGroup
open CFSG.Models.Chevalley PrimitiveSocleRawStructure

variable (K : Type) [Field K] [Finite K]
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _
local instance (q : CFSG.PrimePower) : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
local instance [IsSimpleGroup (Projective CartanMatrix.G₂ K)] : Finite (Projective CartanMatrix.G₂ K) :=
  Finite.of_surjective (generatedToOriginal K) (generatedToOriginal_surjective K)

private def middleToGenerated : fixedMiddle K →* fixedRootGenerated K (RingEquiv.refl K) where
  toFun u := ⟨u.val,signedFixed_le_generated K (RingEquiv.refl K) false
    ⟨CFSGTrialityGeckMiddleFixedCommutators.middle_le_positive K u.property.1,u.property.2⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl

omit [Finite K] in
private theorem middleToGenerated_mem_rootPart (u : fixedMiddle K) :
    middleToGenerated K u ∈ rootPart K (RingEquiv.refl K) false :=
  ⟨CFSGTrialityGeckMiddleFixedCommutators.middle_le_positive K u.property.1,u.property.2⟩

def originalMiddle [IsSimpleGroup (Projective CartanMatrix.G₂ K)] :
    fixedMiddle K →* Projective CartanMatrix.G₂ K :=
  (generatedToOriginal K).comp (middleToGenerated K)

theorem originalMiddle_injective [IsSimpleGroup (Projective CartanMatrix.G₂ K)] :
    Function.Injective (originalMiddle K) := by
  intro u v he
  have hJ := generatedToOriginal_injOn_positive K
    (middleToGenerated_mem_rootPart K u) (middleToGenerated_mem_rootPart K v) he
  have hraw : u.val = v.val := congrArg
    (fun z : fixedRootGenerated K (RingEquiv.refl K) => z.val) hJ
  exact Subtype.ext hraw

theorem original_central_one_ne_one [IsSimpleGroup (Projective CartanMatrix.G₂ K)] :
    originalMiddle K (central K (Multiplicative.ofAdd (1 : K))) ≠ 1 := by
  intro he
  have he' := originalMiddle_injective K (he.trans (map_one (originalMiddle K)).symm)
  have hc := central_injective K (he'.trans (map_one (central K)).symm)
  exact one_ne_zero (congrArg Multiplicative.toAdd hc)

theorem middle_le_proper_index (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective CartanMatrix.G₂ K)] (hthree : (3 : K) ≠ 0)
    (H : Subgroup (Projective CartanMatrix.G₂ K)) (hH : H ≠ ⊤) :
    p*Nat.card K^2 ≤ H.index := by
  obtain ⟨x,hx⟩ := CFSGConjugateSubgroupDegree.exists_moved_coset_of_ne_one H hH
    (originalMiddle K (central K (Multiplicative.ofAdd (1 : K)))) (original_central_one_ne_one K)
  letI : MulAction (fixedMiddle K) (Projective CartanMatrix.G₂ K ⧸ H) :=
    MulAction.compHom _ (originalMiddle K)
  exact (extensionData K hthree).degree_le_of_central_motion p 2
    (by simp only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin]) x (Multiplicative.ofAdd (1 : K)) hx

theorem typeGTwo_middle_le_proper_index (q : CFSG.PrimePower) (hchar : q.prime ≠ 3)
    [IsSimpleGroup (CFSG.Models.G2 q)] (H : Subgroup (CFSG.Models.G2 q)) (hH : H ≠ ⊤) :
    q.prime*q.order^2 ≤ H.index := by
  have hthree : (3 : q.Field) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (R := q.Field) (p := q.prime) (by decide : Nat.Prime 3) hchar
  have he := middle_le_proper_index q.Field q.prime hthree H hH
  rw [q.card_field] at he
  exact he

theorem typeGTwo_middle_le_leastProperIndex (q : CFSG.PrimePower) (hchar : q.prime ≠ 3)
    [IsSimpleGroup (CFSG.Models.G2 q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.G2 q) ell) : q.prime*q.order^2 ≤ ell := by
  obtain ⟨H,hH,he⟩ := hell.1
  rw [←he]
  exact typeGTwo_middle_le_proper_index q hchar H hH

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddlePairingIndex
