import SymmetricSubgroupAsymptotics.ChiefSeriesTransport
import SymmetricSubgroupAsymptotics.RelativeAmbientTransport
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.Data.Finite.Card

/-! An explicit labelling transports an original action to its literal
permutation image on Fin n. Faithfulness supplies an actual ambient group
equivalence, preserving original normal characters and chosen chief
series. No image recognition or classification is assumed here. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {A Ω : Type} [Group A] [MulAction A Ω] {n : ℕ} (e : Ω ≃ Fin n)

def labelledActionHom : A →* Equiv.Perm (Fin n) :=
  e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom A Ω)

abbrev labelledActionImage : Subgroup (Equiv.Perm (Fin n)) :=
  (labelledActionHom (A := A) e).range

theorem labelledActionHom_apply (a : A) (ω : Ω) :
    labelledActionHom e a (e ω) = e (a • ω) := by
  change e (a • e.symm (e ω)) = e (a • ω)
  rw [e.symm_apply_apply]

include e in
theorem labelledAction_card : Nat.card Ω = n := by
  simpa only [Nat.card_fin] using Nat.card_congr e

/-- The original point labelling is equivariant for the actual range
restriction of the original action homomorphism. -/
def labelledActionPointHom :
    MulActionHom (fun a : A => (labelledActionHom e).rangeRestrict a) Ω (Fin n) where
  toFun := e
  map_smul' a ω := (labelledActionHom_apply e a ω).symm

theorem labelledAction_pretransitive_iff :
    MulAction.IsPretransitive A Ω ↔
      MulAction.IsPretransitive (labelledActionImage (A := A) e) (Fin n) :=
  MulAction.isPretransitive_congr (f := labelledActionPointHom (A := A) e)
    (labelledActionHom (A := A) e).rangeRestrict_surjective e.bijective

theorem labelledAction_preprimitive_iff :
    MulAction.IsPreprimitive A Ω ↔
      MulAction.IsPreprimitive (labelledActionImage (A := A) e) (Fin n) :=
  MulAction.isPreprimitive_congr (f := labelledActionPointHom (A := A) e)
    (labelledActionHom (A := A) e).rangeRestrict_surjective e.bijective

theorem labelledActionImage_faithful :
    FaithfulSMul (labelledActionImage (A := A) e) (Fin n) := inferInstance

theorem labelledActionImage_finite : Finite (labelledActionImage (A := A) e) :=
  inferInstance

theorem labelledActionHom_injective [FaithfulSMul A Ω] :
    Function.Injective (labelledActionHom (A := A) e) :=
  e.permCongrHom.injective.comp MulAction.toPerm_injective

include e in
theorem faithfulLabelledAction_finite [FaithfulSMul A Ω] : Finite A :=
  Finite.of_injective (labelledActionHom e) (labelledActionHom_injective e)

def faithfulLabelledActionEquiv [FaithfulSMul A Ω] :
    A ≃* labelledActionImage (A := A) e :=
  MonoidHom.ofInjective (labelledActionHom_injective e)

@[simp] theorem faithfulLabelledActionEquiv_coe [FaithfulSMul A Ω] (a : A) :
    (faithfulLabelledActionEquiv e a : Equiv.Perm (Fin n)) = labelledActionHom e a := rfl

/-- The literal image of the original normal subgroup in the actual
permutation range, with that range as its conjugating ambient group. -/
abbrev labelledActionNormal (N : Subgroup A) : Subgroup (labelledActionImage (A := A) e) :=
  originalNormalRange (labelledActionHom e) N

theorem faithfulLabelledActionEquiv_map [FaithfulSMul A Ω] (N : Subgroup A) :
    N.map (faithfulLabelledActionEquiv e).toMonoidHom = labelledActionNormal e N := rfl

def labelledActionNormalCharacters [FaithfulSMul A Ω]
    (p : ℕ) [Fact p.Prime] (N : Subgroup A) [N.Normal] :
    primeRelativeCharacters p (labelledActionNormal e N) ≃ₗ[ZMod p]
      primeRelativeCharacters p N :=
  relativeCharacterAmbientCongr p (faithfulLabelledActionEquiv e)
    N (labelledActionNormal e N) (faithfulLabelledActionEquiv_map e N)

theorem labelledActionNormal_head [FaithfulSMul A Ω]
    (p : ℕ) [Fact p.Prime] (N : Subgroup A) [N.Normal] :
    Module.finrank (ZMod p) (primeRelativeCharacters p N) =
      Module.finrank (ZMod p) (primeRelativeCharacters p (labelledActionNormal e N)) :=
  (labelledActionNormalCharacters e p N).finrank_eq.symm

/-- A chosen image chief series is pulled back to the actual ambient A. -/
def faithfulLabelledActionChiefSeries [FaithfulSMul A Ω]
    (c : ActualChiefSeries (labelledActionImage (A := A) e)) : ActualChiefSeries A :=
  actualChiefSeriesComap (faithfulLabelledActionEquiv e) c

theorem faithfulLabelledActionChiefSeries_weight [FaithfulSMul A Ω]
    (c : ActualChiefSeries (labelledActionImage (A := A) e)) :
    actualChiefSeriesTernaryWeight (faithfulLabelledActionChiefSeries e c) =
      actualChiefSeriesTernaryWeight c :=
  actualChiefSeriesComap_weight (faithfulLabelledActionEquiv e) c

end SymmetricSubgroupAsymptotics
