import SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleSourceRadical
import SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleCentralCoordinates
import SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeCentralGraph
import SymmetricSubgroupAsymptotics.CentralizingJoinIntersection

/-! The full central preimage of one literal source subgroup is invariant
under the actual source involution whenever that involution belongs to
the SAME radical join. No field-linearity of the central intersection
or action is imposed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleCentralJoin
open CFSGGTwoCharacteristicThreeMiddleCoordinateEquiv
open CFSGGTwoCharacteristicThreeMiddleCentralCoordinates
open CFSGGTwoCharacteristicThreeMiddleCentralWords
open CFSGGTwoCharacteristicThreeMiddleSource
open CFSGGTwoCharacteristicThreeMiddleSourceRadical
open CFSGGTwoCharacteristicThreeMiddleSourceInvolution
open CFSGGTwoCharacteristicThreeCentralGraph
variable (K : Type) [Field K] [Finite K] [CharP K 3]

def middleEmbedding : Middle K →* source K := Subgroup.inclusion (middle_le_source K)

def sourceCentralHom : Multiplicative (Fin 3 → K) →* source K :=
  (middleEmbedding K).comp (centralHom K)

theorem sourceCentralHom_val (a : Multiplicative (Fin 3 → K)) :
    (sourceCentralHom K a).val = centralWord K a.toAdd := centralHom_val K a

theorem sourceCentralHom_centralizes (a : Multiplicative (Fin 3 → K))
    (n : source K) (hn : n ∈ radical K) :
    n*sourceCentralHom K a = sourceCentralHom K a*n := by
  have ha : centralHom K a ∈ Subgroup.center (Middle K) := by
    rw [center_eq_endpointKer,←centralHom_range]
    exact ⟨a,rfl⟩
  have he := Subgroup.mem_center_iff.mp ha (⟨n.val,hn⟩ : Middle K)
  have he' : n.val*(centralHom K a).val = (centralHom K a).val*n.val :=
    congrArg (fun u : Middle K => u.val) he
  apply Subtype.ext
  exact he'

theorem sourceCentralHom_flip (a : Multiplicative (Fin 3 → K)) :
    involution K*sourceCentralHom K a*(involution K)⁻¹ =
      sourceCentralHom K (Multiplicative.ofAdd (flip K a.toAdd)) := by
  apply Subtype.ext
  change (involution K).val*(sourceCentralHom K a).val*(involution K).val⁻¹ = _
  rw [sourceCentralHom_val,sourceCentralHom_val]
  exact involution_central_flip K a.toAdd

theorem central_preimage_flip (M : Subgroup (source K))
    (ht : involution K ∈ M ⊔ radical K) :
    ∀ a ∈ M.comap (sourceCentralHom K),
      Multiplicative.ofAdd (flip K a.toAdd) ∈ M.comap (sourceCentralHom K) := by
  letI := radical_normal K
  intro a ha
  have he := CentralizingJoinIntersection.conjugate_mem (radical K) M
    (sourceCentralHom K a) ha (sourceCentralHom_centralizes K a)
    (involution K) ht
  rw [sourceCentralHom_flip] at he
  exact he

theorem central_preimage_third_eq_zero (hcard : Nat.card K = 3)
    (M : Subgroup (source K))
    (hhigh : sourceCentralHom K (Multiplicative.ofAdd (vertical K 1)) ∉ M)
    (ht : involution K ∈ M ⊔ radical K) :
    ∀ a ∈ M.comap (sourceCentralHom K), a.toAdd 2 = 0 := by
  exact third_eq_zero_of_flip K hcard
    (M.comap (sourceCentralHom K)).toAddSubgroup' hhigh
    (central_preimage_flip K M ht)

end SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleCentralJoin
