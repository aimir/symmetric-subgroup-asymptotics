import SymmetricSubgroupAsymptotics.CFSGUnitaryMiddleRadicalExtension
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRadicalCenter
import SymmetricSubgroupAsymptotics.CFSGInvariantQuotientAutomorphism
import Mathlib.GroupTheory.Subgroup.Centralizer

/-! The literal radical normalizer acts on the actual radical and its
actual vector quotient. Its kernel is characteristic because it equals
the centre, not because the quotient is assumed linear. This permits
actual middle words and additional actual paired tori in one common
semidirect extension and one common stabilizer. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedAUpperUnipotent
open CFSGInvariantQuotientAutomorphism

private def invariantQuotientMulAutHom
    {A N V : Type*} [Group A] [Group N] [AddCommGroup V]
    (π : N →* Multiplicative V) (hπ : Function.Surjective π)
    (ρ : A →* MulAut N) (hker : ∀ a : A, π.ker.map (ρ a).toMonoidHom = π.ker) :
    A →* MulAut (Multiplicative V) where
  toFun := quotientMulAut π hπ ρ hker
  map_one' := by
    apply MulEquiv.ext
    intro v
    obtain ⟨g, rfl⟩ := hπ v
    rw [quotientMulAut_first, map_one]
    rfl
  map_mul' a b := by
    apply MulEquiv.ext
    intro v
    obtain ⟨g, rfl⟩ := hπ v
    change quotientMulAut π hπ ρ hker (a * b) (π g) =
      quotientMulAut π hπ ρ hker a (quotientMulAut π hπ ρ hker b (π g))
    rw [quotientMulAut_first, quotientMulAut_first, quotientMulAut_first, map_mul]
    rfl

private theorem invariantQuotientMulAutHom_parameter
    {A N V : Type*} [Group A] [Group N] [AddCommGroup V]
    (π : N →* Multiplicative V) (hπ : Function.Surjective π)
    (ρ : A →* MulAut N) (hker : ∀ a : A, π.ker.map (ρ a).toMonoidHom = π.ker)
    (a : A) (g : N) :
    π (ρ a g) = invariantQuotientMulAutHom π hπ ρ hker a (π g) :=
  (quotientMulAut_first π hπ ρ hker a g).symm

abbrev unitaryRadicalNormalizer (q : CFSG.PrimePower) (t : ℕ) :=
  Subgroup.normalizer (fixedRadical q t : Set (naturalFixed (t + 2) q))

def unitaryRadicalNormalizerAutHom (q : CFSG.PrimePower) (t : ℕ) :
    unitaryRadicalNormalizer q t →* MulAut (fixedRadical q t) :=
  (fixedRadical q t).normalizerMonoidHom

theorem unitaryRadicalNormalizer_kernel_invariant (q : CFSG.PrimePower) (t : ℕ)
    (a : unitaryRadicalNormalizer q t) :
    (fixedRadicalParameterHom q t).ker.map
        (unitaryRadicalNormalizerAutHom q t a).toMonoidHom =
      (fixedRadicalParameterHom q t).ker := by
  rw [← fixedRadical_center_eq_kernel]
  exact Subgroup.characteristic_iff_map_eq.mp inferInstance _

def unitaryRadicalNormalizerVectorAutHom (q : CFSG.PrimePower) (t : ℕ) :
    unitaryRadicalNormalizer q t →*
      MulAut (Multiplicative (Fin (t + 1) → q.Extension 2)) :=
  invariantQuotientMulAutHom (fixedRadicalParameterHom q t)
    (fixedRadicalParameterHom_surjective q t) (unitaryRadicalNormalizerAutHom q t)
    (unitaryRadicalNormalizer_kernel_invariant q t)

theorem unitaryRadicalNormalizer_parameter (q : CFSG.PrimePower) (t : ℕ)
    (a : unitaryRadicalNormalizer q t) (g : fixedRadical q t) :
    fixedRadicalParameterHom q t (unitaryRadicalNormalizerAutHom q t a g) =
      unitaryRadicalNormalizerVectorAutHom q t a (fixedRadicalParameterHom q t g) :=
  invariantQuotientMulAutHom_parameter (fixedRadicalParameterHom q t)
    (fixedRadicalParameterHom_surjective q t) (unitaryRadicalNormalizerAutHom q t)
    (unitaryRadicalNormalizer_kernel_invariant q t) a g

def unitaryRadicalNormalizerExtensionHom (q : CFSG.PrimePower) (t : ℕ) :
    fixedRadical q t ⋊[unitaryRadicalNormalizerAutHom q t] unitaryRadicalNormalizer q t →*
      naturalFixed (t + 2) q :=
  SemidirectProduct.lift (fixedRadical q t).subtype (unitaryRadicalNormalizer q t).subtype
    (fun _ => MonoidHom.ext (fun _ => rfl))

theorem unitaryRadicalNormalizerExtensionHom_inl (q : CFSG.PrimePower) (t : ℕ)
    (g : fixedRadical q t) :
    unitaryRadicalNormalizerExtensionHom q t (SemidirectProduct.inl g) = g.val := by
  simp only [unitaryRadicalNormalizerExtensionHom, SemidirectProduct.lift_inl]
  rfl

theorem naturalFixedMiddle_mem_radicalNormalizer (q : CFSG.PrimePower) (t : ℕ)
    (a : naturalFixed t q) :
    naturalFixedMiddleHom q t a ∈ unitaryRadicalNormalizer q t := by
  apply Subgroup.mem_normalizer_iff.mpr
  intro g
  constructor
  · intro hg
    exact (radicalMiddleConjugate q t a ⟨g, hg⟩).property
  · intro hg
    have hh := (radicalMiddleConjugate q t a⁻¹
      ⟨naturalFixedMiddleHom q t a * g * (naturalFixedMiddleHom q t a)⁻¹, hg⟩).property
    have he : naturalFixedMiddleHom q t a⁻¹ *
        (naturalFixedMiddleHom q t a * g * (naturalFixedMiddleHom q t a)⁻¹) *
          (naturalFixedMiddleHom q t a⁻¹)⁻¹ = g := by
      rw [map_inv]
      group
    change naturalFixedMiddleHom q t a⁻¹ *
      (naturalFixedMiddleHom q t a * g * (naturalFixedMiddleHom q t a)⁻¹) *
        (naturalFixedMiddleHom q t a⁻¹)⁻¹ ∈ fixedRadical q t at hh
    rwa [he] at hh

def middleRadicalNormalizerHom (q : CFSG.PrimePower) (t : ℕ) :
    naturalFixed t q →* unitaryRadicalNormalizer q t :=
  (naturalFixedMiddleHom q t).codRestrict (unitaryRadicalNormalizer q t)
    (naturalFixedMiddle_mem_radicalNormalizer q t)

theorem middleRadicalNormalizer_vector_action (q : CFSG.PrimePower) (t : ℕ)
    (a : naturalFixed t q) (v : Multiplicative (Fin (t + 1) → q.Extension 2)) :
    unitaryRadicalNormalizerVectorAutHom q t (middleRadicalNormalizerHom q t a) v =
      naturalVectorMulAutHom q t a v := by
  obtain ⟨g, rfl⟩ := fixedRadicalParameterHom_surjective q t v
  rw [← unitaryRadicalNormalizer_parameter, ← radicalMiddleAut_parameter]
  rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
