import SymmetricSubgroupAsymptotics.CFSGTrialityBinaryMiddleGeneration
import SymmetricSubgroupAsymptotics.CFSGTrialityBinaryMiddleLayers
import SymmetricSubgroupAsymptotics.BinaryCentralExtensionZeroLayer
import SymmetricSubgroupAsymptotics.ActualNormalLayerOrbitIndex
import Mathlib.Algebra.CharP.CharAndCard

/-! The actual binary normalizer retains one stabilizer M, its literal
middle-radical intersection J, and the same join M sup N. A proper join
pays a factor two; a full join makes the quotient layer invariant under
the displayed regular translations and Weyl, forcing J to be trivial. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityBinaryMiddleStabilizerIndex
open CFSGTrialityMiddleFixedTensorSpan CFSGTrialityMiddleFixedTensorCardinality
open CFSGTrialityBinaryMiddleNormalizer CFSGTrialityBinaryMiddleSource
open CFSGTrialityBinaryMiddleLayers CFSGTrialityBinaryMiddleVectorAction
open CFSGTrialityBinaryMiddleGeneration

private theorem binary_scalar (q : CFSG.PrimePower) (hq : q.order=2) (a : F q) :
    a=0 ∨ a=1 := by
  by_cases ha : a=0
  · exact Or.inl ha
  obtain ⟨b,hb,hu⟩ := (Nat.card_eq_two_iff' (0 : F q)).mp
    ((CFSGTrialityFixedField.fixedField_card q).trans hq)
  exact Or.inr ((hu a ha).trans (hu 1 one_ne_zero).symm)

private def vectorSubmodule (q : CFSG.PrimePower) (hq : q.order=2)
    (J : Subgroup (liftedMiddle q)) : Submodule (F q) (fullEnvelope q) where
  carrier := (layerData q).vectorImage J
  zero_mem' := ((layerData q).vectorImage J).zero_mem
  add_mem' := ((layerData q).vectorImage J).add_mem
  smul_mem' := by
    intro a x hx
    rcases binary_scalar q hq a with rfl | rfl
    · rw [zero_smul]
      exact ((layerData q).vectorImage J).zero_mem
    · rw [one_smul]
      exact hx

theorem carrier_index_lower (q : CFSG.PrimePower) (hq : q.order=2)
    (M : Subgroup (carrier q))
    (hM : (layerData q).central (Multiplicative.ofAdd (1 : F q)) ∉
      M.comap (liftedMiddle q).subtype) : 64 ≤ M.index := by
  let J := M.comap (liftedMiddle q).subtype
  let D := layerData q
  have hF : Nat.card (F q)=2 := (CFSGTrialityFixedField.fixedField_card q).trans hq
  letI : Fintype (F q) := Fintype.ofFinite _
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : CharP (F q) 2 := charP_of_card_eq_prime
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hdim : Module.finrank (F q) (fullEnvelope q)=2*4 := fullEnvelope_finrank q
  have hcentral : ¬D.central.range ≤ J :=
    BinaryCentralExtensionZeroLayer.central_range_not_le D J hM
  have h32 : 32 ≤ J.index := by
    have hi := D.index_least 2 4 hdim J hcentral
    norm_num only [hF] at hi
    exact hi
  have hfactor : M.index=J.index*(M ⊔ liftedMiddle q).index :=
    ActualNormalLayerOrbitIndex.index_factor (liftedMiddle q) M
  by_cases hjoin : M ⊔ liftedMiddle q=⊤
  · let W := vectorSubmodule q hq J
    have hW : ∀ g : carrier q, ∀ x ∈ W, vectorAction q hq g x ∈ W := by
      intro g x hx
      have hg : g ∈ M ⊔ liftedMiddle q := by rw [hjoin]; trivial
      have hv := ActualNormalLayerOrbitIndex.quotient_layer_invariant
        (liftedMiddle q) M D.projection D.projection_surjective (quotientAction q)
        (layer_equivariance q) g hg (Multiplicative.ofAdd x) hx
      change (quotientAction q g (Multiplicative.ofAdd x)).toAdd ∈ D.vectorImage J at hv
      rw [quotientAction_toAdd q hq] at hv
      exact hv
    have hbot : W=⊥ := by
      rcases invariant_eq_bot_or_top q hq W hW with hb | ht
      · exact hb
      · exfalso
        have he : D.vectorImage J=⊤ := by
          ext x
          change x ∈ W ↔ x ∈ (⊤ : AddSubgroup (fullEnvelope q))
          rw [ht]
          rfl
        have hc := D.vectorImage_card_le 2 4 hdim J hcentral
        rw [he,AddSubgroup.card_top,Module.natCard_eq_pow_finrank (K := F q),
          fullEnvelope_finrank,hF] at hc
        norm_num at hc
    have hmap : J.map D.projection=⊥ := by
      ext v
      change v.toAdd ∈ W ↔ v ∈ (⊥ : Subgroup (Multiplicative (fullEnvelope q)))
      rw [hbot]
      rfl
    have hJ : J=⊥ :=
      BinaryCentralExtensionZeroLayer.eq_bot_of_projection_bot hF D J hM hmap
    have hn : Nat.card (liftedMiddle q)=512 := by
      have he := D.card_eq 4 hdim
      norm_num only [hF] at he
      exact he
    rw [hfactor,hJ,Subgroup.index_bot,hjoin,Subgroup.index_top,mul_one,hn]
    decide
  · have htwo : 2 ≤ (M ⊔ liftedMiddle q).index :=
      (M ⊔ liftedMiddle q).one_lt_index_of_ne_top hjoin
    rw [hfactor]
    exact Nat.mul_le_mul h32 htwo

end SymmetricSubgroupAsymptotics.CFSGTrialityBinaryMiddleStabilizerIndex
