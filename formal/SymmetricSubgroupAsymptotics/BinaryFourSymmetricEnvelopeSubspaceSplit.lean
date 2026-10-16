import SymmetricSubgroupAsymptotics.BinaryFourSymmetricEnvelopeProjectors

/-! The C3 trace splits each actual invariant subspace of the common
S4 envelope into its two isotypic parts. This is a linear-module split,
not a splitting assertion for the original retained group quotient. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

def envelopeTrivialInclusion : (Fin 3 → Scalar) →ₗ[Scalar] SymmetricEnvelope where
  toFun a := (a, 0, 0)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def envelopeActiveInclusion : (Local × Local) →ₗ[Scalar] SymmetricEnvelope where
  toFun a := (0, a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

abbrev envelopeTrivialSection (E : Submodule Scalar SymmetricEnvelope) :=
  E.comap envelopeTrivialInclusion

abbrev envelopeActiveSection (E : Submodule Scalar SymmetricEnvelope) :=
  E.comap envelopeActiveInclusion

def envelopeSectionSum (E : Submodule Scalar SymmetricEnvelope) :
    (envelopeTrivialSection E × envelopeActiveSection E) →ₗ[Scalar] E where
  toFun x := ⟨(x.1.1, x.2.1), by
    have ht : (x.1.1, (0 : Local), (0 : Local)) ∈ E := x.1.2
    have ha : ((0 : Fin 3 → Scalar), x.2.1) ∈ E := x.2.2
    have h := E.add_mem ht ha
    simp only [Prod.mk_add_mk, add_zero] at h
    change (x.1.1, (0 : Local × Local) + x.2.1) ∈ E at h
    simpa only [zero_add] using h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem envelopeSectionSum_bijective
    (E : Submodule Scalar SymmetricEnvelope)
    (hc : ∀ x ∈ E, envelopeCycle x ∈ E) :
    Function.Bijective (envelopeSectionSum E) := by
  constructor
  · intro x y h
    have hv : (x.1.1, x.2.1) = (y.1.1, y.2.1) := congrArg Subtype.val h
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst hv)
    · exact Subtype.ext (congrArg Prod.snd hv)
  · intro x
    obtain ⟨ht, ha⟩ := envelope_projector_mem E hc x.1 x.2
    exact ⟨(⟨x.1.1, ht⟩, ⟨x.1.2, ha⟩), Subtype.ext rfl⟩

def envelopeSectionEquiv
    (E : Submodule Scalar SymmetricEnvelope)
    (hc : ∀ x ∈ E, envelopeCycle x ∈ E) :
    (envelopeTrivialSection E × envelopeActiveSection E) ≃ₗ[Scalar] E :=
  LinearEquiv.ofBijective (envelopeSectionSum E) (envelopeSectionSum_bijective E hc)

end SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

end
