import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleCubicFixedLifts

/-! The literal two-endpoint projection of the same fixed middle radical.
Its full kernel has order q^3. No centrality, additive decomposition or
quotient-stabilizer separation is inferred from this cardinal statement. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleEndpointProjection

open CFSGGTwoD4GeckMiddleFixedRadicalCoordinates CFSGGTwoD4GeckMiddleCubicFixedLifts

def endpointLinear (K : Type) [Field K] : (Fin 4 → K) →ₗ[K] (Fin 2 → K) where
  toFun c i := if i=0 then c 0 else c 3
  map_add' u v := by funext i; fin_cases i <;> rfl
  map_smul' a u := by funext i; fin_cases i <;> rfl

theorem endpointLinear_surjective (K : Type) [Field K] : Function.Surjective (endpointLinear K) := by
  intro x
  refine ⟨(fun j => if j.val=0 then x 0 else if j.val=3 then x 1 else 0),?_⟩
  funext i
  fin_cases i <;> rfl

def endpointHom (K : Type) [Field K] [Finite K] : fixedMiddle K →* Multiplicative (Fin 2 → K) :=
  (endpointLinear K).toAddMonoidHom.toMultiplicative.comp (projection K)

theorem endpointHom_surjective (K : Type) [Field K] [Finite K] (hcard : 4 ≤ Nat.card K) :
    Function.Surjective (endpointHom K) := by
  intro z
  obtain ⟨c,hc⟩ := endpointLinear_surjective K z.toAdd
  obtain ⟨u,hu⟩ := projection_surjective_of_card_four K hcard (Multiplicative.ofAdd c)
  refine ⟨u,?_⟩
  change Multiplicative.ofAdd (endpointLinear K (projection K u).toAdd) = z
  rw [hu]
  exact congrArg Multiplicative.ofAdd hc

def endpointKernel (K : Type) [Field K] [Finite K] : Subgroup (fixedMiddle K) := (endpointHom K).ker

theorem endpointKernel_card (K : Type) [Field K] [Finite K] (hcard : 4 ≤ Nat.card K) :
    Nat.card (endpointKernel K) = Nat.card K^3 := by
  have hr : (endpointKernel K).subtype.range = (endpointHom K).ker := Subgroup.range_subtype _
  have he := ExactHomSubgroupCardinality.card_comap_mul_card_map (endpointHom K)
    (endpointKernel K).subtype Subtype.val_injective hr (⊤ : Subgroup (fixedMiddle K))
  rw [Subgroup.comap_top,Subgroup.map_top_of_surjective _ (endpointHom_surjective K hcard),
    Subgroup.card_top,Subgroup.card_top,Subgroup.card_top] at he
  change Nat.card (endpointKernel K)*Nat.card (Fin 2 → K) = Nat.card (fixedMiddle K) at he
  rw [Nat.card_fun,Nat.card_fin,fixedMiddle_card_of_card_four K hcard] at he
  apply Nat.eq_of_mul_eq_mul_right (pow_pos (Nat.card_pos (α := K)) 2)
  exact he.trans (by rw [←pow_add])

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleEndpointProjection
