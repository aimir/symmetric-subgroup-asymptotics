import SymmetricSubgroupAsymptotics.CFSGInvolutiveOppositeAlignmentRestriction
import SymmetricSubgroupAsymptotics.CFSGReeFFourModelOppositeAlignment
import SymmetricSubgroupAsymptotics.CFSGReeFFourUniqueInversionCells

/-! Actual positive fixed elements act transitively on the disjoint
conjugates of the actual fixed positive Sylow. Ambient alignment takes
place in the same original F4 Model, and its unique positive conjugator
is proved exceptional-fixed. No fixed-point lifting is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFixedOppositeAlignment
open CFSG.Models.Chevalley CFSGReeFFourFieldParameters
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourOriginalAutomorphism
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourAmbientPositiveStability
open CFSGReeFFourOriginalNegativeStability CFSGReeFFourOppositionFixedPositiveNegative
open CFSGFFourOriginalMiddleWords CFSGFFourOriginalAmbientHom CFSGFFourOriginalBruhatCells
open CFSGReeFFourRelativeOpposition CFSGReeFFourUniqueInversionCells
open CFSGReeFFourModelOppositeAlignment CFSGInvolutiveOppositeAlignmentRestriction
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private instance modelFinite (m : ℕ) : Finite (Model CartanMatrix.F₄ (Field m)) :=
  Finite.of_injective (rawHom (Field m)) (rawHom_injective (Field m))

private theorem model_positive_inf_negative_normalizer (m : ℕ) :
    modelPositive (Field m)⊓Subgroup.normalizer (modelNegative m :
      Set (Model CartanMatrix.F₄ (Field m)))=⊥ := by
  let e := MulAut.conj (relativeOpposition m)
  let Q : Sylow 2 (Model CartanMatrix.F₄ (Field m)) :=
    (modelPositiveSylow m).mapSurjective (f:=e.toMonoidHom) e.surjective
  have hQ : (Q : Subgroup (Model CartanMatrix.F₄ (Field m)))=modelNegative m := by
    change (modelPositiveSylow m : Subgroup (Model CartanMatrix.F₄ (Field m))).map
      e.toMonoidHom=_
    rw [modelPositiveSylow_coe]
    exact model_positive_image_eq_negative m
  have hP : IsPGroup 2 (modelPositive (Field m)) :=
    modelPositiveSylow_coe m ▸ (modelPositiveSylow m).isPGroup'
  have he : modelPositive (Field m)⊓Subgroup.normalizer
      ((Q : Subgroup (Model CartanMatrix.F₄ (Field m))) : Set (Model CartanMatrix.F₄ (Field m)))=
        modelPositive (Field m)⊓(Q : Subgroup (Model CartanMatrix.F₄ (Field m))) :=
    hP.inf_normalizer_sylow Q
  rw [hQ] at he
  refine he.trans ?_
  apply eq_bot_iff.mpr
  intro x hx
  apply Subgroup.mem_bot.mpr
  have hxB : x∈modelEnvelope (Field m) :=
    CFSGTwistedE6GeckNormalizerEnvelope.positive_le_envelope (Field m) hx.1
  exact Subgroup.disjoint_def.mp (modelEnvelope_negative_disjoint m) hxB hx.2

theorem fixed_opposite_conjugate_by_positive (m : ℕ) (g : originalModelFixed m)
    (hdisj : fixedPositive m⊓(fixedPositive m).map (MulAut.conj g).toMonoidHom=⊥) :
    ∃b∈fixedPositive m,(fixedPositive m).map (MulAut.conj g).toMonoidHom=
      (fixedNegative m).map (MulAut.conj b).toMonoidHom := by
  have hP : IsPGroup 2 (modelPositive (Field m)) :=
    modelPositiveSylow_coe m ▸ (modelPositiveSylow m).isPGroup'
  have hd : (modelPositive (Field m)).comap (originalModelFixed m).subtype⊓
      ((modelPositive (Field m)).comap (originalModelFixed m).subtype).map
        (MulAut.conj g).toMonoidHom=⊥ := by
    rw [←fixedPositive_eq_model_comap]
    exact hdisj
  have he := fixed_opposite_alignment (modelPositive (Field m)) (modelNegative m)
    (originalModelFixed m) hP (reeAutomorphism m) (reeAutomorphism_involutive m)
    (ree_preserves_modelPositive m) (ree_preserves_modelNegative m) (fun _=>Iff.rfl)
    (model_positive_inf_negative_normalizer m) (model_opposite_conjugate_by_positive m) g hd
  have hV : (modelNegative m).comap (originalModelFixed m).subtype=fixedNegative m := rfl
  rw [←fixedPositive_eq_model_comap,hV] at he
  exact he

end SymmetricSubgroupAsymptotics.CFSGReeFFourFixedOppositeAlignment
