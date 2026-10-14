import SymmetricSubgroupAsymptotics.LinearSemidirectCoprimeQuotientSocles
import Mathlib.RepresentationTheory.Maschke
import Mathlib.Algebra.Module.ZMod

/-! A subgroup of an elementary affine group containing the full
coprime complement is a retract of that affine group. Its translation
space is an actual invariant subspace; Maschke supplies an equivariant
projection onto it. Consequently the original normal quotients inherit
the full affine model's quotient-socle bound, without listing the
translation subspace or the subgroup's normal subgroups. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics
namespace CoprimeSemidirectSubgroupRetraction

open SemidirectProduct LinearSemidirectCoprimeSocleBounds

variable {p : ℕ} [Fact p.Prime]
  {H V : Type} [Group H] [Finite H] [AddCommGroup V] [Module (ZMod p) V]
  (rho : H →* (V ≃ₗ[ZMod p] V))
  (K : Subgroup (Model rho))

def translationAddSubgroup : AddSubgroup V where
  carrier := {v | (inl (Multiplicative.ofAdd v) : Model rho) ∈ K}
  zero_mem' := by
    change (inl (1 : Multiplicative V) : Model rho) ∈ K
    simpa only [map_one] using K.one_mem
  add_mem' := by
    intro v w hv hw
    change (inl (Multiplicative.ofAdd v * Multiplicative.ofAdd w) : Model rho) ∈ K
    rw [map_mul]
    exact K.mul_mem hv hw
  neg_mem' := by
    intro v hv
    change (inl (Multiplicative.ofAdd v)⁻¹ : Model rho) ∈ K
    rw [map_inv]
    exact K.inv_mem hv

variable (hH : ∀ h : H, (inr h : Model rho) ∈ K)

def translationSubrepresentation : Subrepresentation (linearRepresentation rho) where
  toSubmodule := AddSubgroup.toZModSubmodule p (translationAddSubgroup rho K)
  apply_mem_toSubmodule := by
    intro h v hv
    change (inl (linearAction rho h (Multiplicative.ofAdd v)) : Model rho) ∈ K
    rw [inl_aut]
    exact K.mul_mem (K.mul_mem (hH h) hv) (hH h⁻¹)

include hH in
/-- The retraction fixes every element of the actual subgroup, including
its full complement. No choice of a basis for its translations is needed. -/
theorem exists_retraction [NeZero (Nat.card H : ZMod p)] :
    ∃ f : Model rho →* K, ∀ x : K, f (x : Model rho) = x := by
  let sigma := linearRepresentation rho
  let W := translationSubrepresentation rho K hH
  let inclusion : W.toRepresentation.IntertwiningMap sigma :=
    { toLinearMap := W.toSubmodule.subtype
      isIntertwining' _ := rfl }
  let I : W.toRepresentation.asModule →ₗ[(ZMod p)[H]] sigma.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule _ _ inclusion
  have hI : Function.Injective I := fun _ _ h ↦ Subtype.ext h
  obtain ⟨P, hP⟩ := MonoidAlgebra.exists_leftInverse_of_injective I
    (LinearMap.ker_eq_bot.mpr hI)
  let projection : sigma.IntertwiningMap W.toRepresentation :=
    (Representation.IntertwiningMap.equivLinearMapAsModule _ _).symm P
  have hprojection (v : W.toSubmodule) : projection v.1 = v :=
    LinearMap.congr_fun hP v
  let F : V →ₗ[ZMod p] V := W.toSubmodule.subtype.comp projection.toLinearMap
  have hF (h : H) (v : V) : F (rho h v) = rho h (F v) := by
    exact congrArg Subtype.val (LinearMap.congr_fun (projection.isIntertwining' h) v)
  let f : Model rho →* Model rho :=
    SemidirectProduct.map F.toAddMonoidHom.toMultiplicative (MonoidHom.id H) (by
      intro h
      apply MonoidHom.ext
      intro v
      apply Multiplicative.toAdd.injective
      exact hF h v.toAdd)
  have hfK (g : Model rho) : f g ∈ K := by
    rw [← inl_left_mul_inr_right (f g)]
    exact K.mul_mem (projection g.left.toAdd).property (hH g.right)
  refine ⟨f.codRestrict K hfK, ?_⟩
  intro x
  have hx : (inl (x : Model rho).left : Model rho) ∈ K := by
    have hm := K.mul_mem x.property (K.inv_mem (hH (x : Model rho).right))
    have he : (x : Model rho) * (inr (x : Model rho).right)⁻¹ =
        inl (x : Model rho).left := by
      calc
        (x : Model rho) * (inr (x : Model rho).right)⁻¹ =
            (inl (x : Model rho).left * inr (x : Model rho).right) *
              (inr (x : Model rho).right)⁻¹ :=
          congrArg (fun g : Model rho ↦ g * (inr (x : Model rho).right)⁻¹)
            (inl_left_mul_inr_right (x : Model rho)).symm
        _ = inl (x : Model rho).left := mul_inv_cancel_right _ _
    exact he ▸ hm
  have hleft := congrArg Subtype.val
    (hprojection ⟨(x : Model rho).left.toAdd, hx⟩)
  apply Subtype.ext
  apply SemidirectProduct.ext
  · exact congrArg Multiplicative.ofAdd hleft
  · rfl

include hH in
theorem exists_surjective [NeZero (Nat.card H : ZMod p)] :
    ∃ f : Model rho →* K, Function.Surjective f := by
  obtain ⟨f, hf⟩ := exists_retraction rho K hH
  exact ⟨f, fun x ↦ ⟨x, hf x⟩⟩

include hH in
/-- The same bound holds on every original quotient of the actual
subgroup, through its supplied quotient map. -/
theorem socle_of_surjective [FiniteDimensional (ZMod p) V]
    (hcop : Nat.Coprime p (Nat.card H)) (t a : ℕ)
    (hgen : RepresentationGeneratedBy (linearRepresentation rho) t)
    (hquotient : ∀ L : Subgroup H, L.Normal → MarkedC4.normalGen L ≤ a)
    {Q : Type} [Group Q] (pi : K →* Q) (hpi : Function.Surjective pi) :
    SocleNormalGeneratorBound Q (max t a) := by
  letI : NeZero (Nat.card H : ZMod p) := ⟨by
    intro hz
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp hcop
      ((ZMod.natCast_eq_zero_iff _ _).mp hz)⟩
  obtain ⟨f, hf⟩ := exists_surjective rho K hH
  exact LinearSemidirectCoprimeQuotientSocles.socle_of_surjective rho hcop t a
    hgen hquotient (pi.comp f) (hpi.comp hf)

include hH in
theorem quotient [FiniteDimensional (ZMod p) V]
    (hcop : Nat.Coprime p (Nat.card H)) (t a : ℕ)
    (hgen : RepresentationGeneratedBy (linearRepresentation rho) t)
    (hquotient : ∀ L : Subgroup H, L.Normal → MarkedC4.normalGen L ≤ a)
    (N : Subgroup K) [N.Normal] : SocleNormalGeneratorBound (K ⧸ N) (max t a) :=
  socle_of_surjective rho K hH hcop t a hgen hquotient
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

end CoprimeSemidirectSubgroupRetraction
end SymmetricSubgroupAsymptotics

end
