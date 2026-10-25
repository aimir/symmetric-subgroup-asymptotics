import SymmetricSubgroupAsymptotics.CFSGTrialityBinaryMiddleStabilizerIndex
import SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree

/-! A surviving actual highest-root scalar moves an original simple
triality coset. The same original action restricted to the literal
generated normalizer therefore has degree at least64. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityBinaryRegularModuleIndex
open CFSGTrialityMiddleFixedTensorSpan CFSGTrialityBinaryMiddleNormalizer
open CFSGTrialityBinaryMiddleSource CFSGTrialityBinaryMiddleLayers
open CFSGTrialityBinaryMiddleStabilizerIndex CFSGTrialityGeckMiddleFixedCentralParameters
open CFSGTrialityGeckGeneratedOriginalProjection

theorem degree_of_central_motion (q : CFSG.PrimePower) (hq : q.order=2)
    {X : Type*} [Finite X] [MulAction (carrier q) X] (x : X)
    (hx : middleLift q (central q (Multiplicative.ofAdd (1 : F q))) • x≠x) :
    64 ≤ Nat.card X := by
  let M := MulAction.stabilizer (carrier q) x
  have hM : (layerData q).central (Multiplicative.ofAdd (1 : F q)) ∉
      M.comap (liftedMiddle q).subtype := by
    change ((layerData q).central (Multiplicative.ofAdd (1 : F q))).val • x≠x
    rw [layer_central]
    exact hx
  have hi : M.index ≤ Nat.card X := by
    calc
      _ = Nat.card (MulAction.orbit (carrier q) x) :=
        (Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (carrier q) x)).symm
      _ ≤ _ := Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  exact (carrier_index_lower q hq M hM).trans hi

theorem typeTriality_binary_regular_le_proper_index (q : CFSG.PrimePower) (hq : q.order=2)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)]
    (H : Subgroup (CFSG.Models.TrialityD4 q)) (hH : H≠⊤) : 64 ≤ H.index := by
  letI : Finite (CFSG.Models.TrialityD4 q) :=
    Finite.of_surjective (generatedToOriginal q) (generatedToOriginal_surjective q)
  let c : CFSGTrialityGeckMiddleFixedCommutators.fixedMiddle q :=
    central q (Multiplicative.ofAdd (1 : F q))
  have hc : c≠1 := by
    intro he
    have hz := central_injective q (he.trans (map_one (central q)).symm)
    exact one_ne_zero (congrArg (fun z : Multiplicative (F q) => z.toAdd) hz)
  let f := (originalHom q).comp (middleLift q)
  have hf : f c≠1 := by
    intro he
    exact hc (original_middle_injective q (he.trans (map_one f).symm))
  obtain ⟨x,hx⟩ := CFSGConjugateSubgroupDegree.exists_moved_coset_of_ne_one H hH (f c) hf
  letI : MulAction (carrier q) (CFSG.Models.TrialityD4 q ⧸ H) :=
    MulAction.compHom _ (originalHom q)
  have hd := degree_of_central_motion q hq x hx
  simpa only [Subgroup.index_eq_card] using hd

end SymmetricSubgroupAsymptotics.CFSGTrialityBinaryRegularModuleIndex
