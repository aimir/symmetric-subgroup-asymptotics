import SymmetricSubgroupAsymptotics.CoprimeCyclicElementarySocleBounds
import Mathlib.GroupTheory.SemidirectProduct

/-!
# Positive quotient-socle bounds for a displayed linear semidirect product

The complement need not act faithfully. The translation chart uses the
actual left coordinate in `V ⋊ R`, and its quotient conjugation action
pulls back to the displayed linear representation of `R`. A positive
module-generator bound is preserved on every original quotient socle
when the complement is cyclic and its order is coprime to the prime.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics
namespace LinearSemidirectCoprimeSocleBounds

open SemidirectProduct

variable {p : ℕ} [Fact p.Prime]
  {R V : Type} [Group R] [AddCommGroup V] [Module (ZMod p) V]
  [FiniteDimensional (ZMod p) V]
  (rho : R →* (V ≃ₗ[ZMod p] V))

def linearAction : R →* MulAut (Multiplicative V) where
  toFun r := (rho r).toAddEquiv.toMultiplicative
  map_one' := by
    apply MulEquiv.ext
    intro v
    exact congrArg Multiplicative.ofAdd (LinearEquiv.congr_fun rho.map_one v.toAdd)
  map_mul' r s := by
    apply MulEquiv.ext
    intro v
    exact congrArg Multiplicative.ofAdd (LinearEquiv.congr_fun (rho.map_mul r s) v.toAdd)

abbrev Model := Multiplicative V ⋊[linearAction rho] R

instance [Finite R] : Finite (Model rho) := by
  letI : Finite V := Module.finite_of_finite (ZMod p)
  exact Finite.of_equiv _ SemidirectProduct.equivProd.symm

def linearRepresentation : Representation (ZMod p) R V where
  toFun r := (rho r).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro v
    exact LinearEquiv.congr_fun rho.map_one v
  map_mul' r s := by
    apply LinearMap.ext
    intro v
    exact LinearEquiv.congr_fun (rho.map_mul r s) v

def translationKernel : Subgroup (Model rho) := (rightHom : Model rho →* R).ker

instance : (translationKernel rho).Normal :=
  inferInstanceAs (MonoidHom.ker (rightHom : Model rho →* R)).Normal

def translationEquiv : translationKernel rho ≃* Multiplicative V where
  toFun x := (x : Model rho).left
  invFun v := ⟨inl v, rightHom_inl v⟩
  left_inv x := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · rfl
    · exact (MonoidHom.mem_ker.mp x.property).symm
  right_inv _ := rfl
  map_mul' x y := by
    change (x : Model rho).left * linearAction rho (x : Model rho).right
        (y : Model rho).left = (x : Model rho).left * (y : Model rho).left
    rw [show (x : Model rho).right = 1 from MonoidHom.mem_ker.mp x.property, map_one]
    rfl

def translationChart : ElementaryMinimalNormalChart (translationKernel rho) where
  p := p
  p_prime := Fact.out
  V := V
  equiv := translationEquiv rho

def complementEquiv : Model rho ⧸ translationKernel rho ≃* R :=
  QuotientGroup.quotientKerEquivOfSurjective
    (rightHom : Model rho →* R) rightHom_surjective

theorem conjugate_translation (g : Model rho) (v : Multiplicative V) :
    g * inl v * g⁻¹ = inl (linearAction rho g.right v) := by
  conv_lhs => rw [← inl_left_mul_inr_right g]
  have h : (inr g.right : Model rho) * inl v * (inr g.right)⁻¹ =
      inl (linearAction rho g.right v) := by
    rw [← map_inv]
    exact (inl_aut _ _).symm
  calc
    (inl g.left * inr g.right : Model rho) * inl v * (inl g.left * inr g.right)⁻¹ =
        (inl g.left : Model rho) *
          ((inr g.right : Model rho) * inl v * (inr g.right)⁻¹) * (inl g.left)⁻¹ := by
      group
    _ = (inl (g.left * linearAction rho g.right v * g.left⁻¹) : Model rho) := by
      rw [h, ← map_inv, ← map_mul, ← map_mul]
    _ = _ := by rw [mul_comm g.left, mul_inv_cancel_right]

theorem translationRepresentation_comp :
    (translationChart rho).quotientRepresentation.ρ.comp
        (QuotientGroup.mk' (translationKernel rho)) =
      (linearRepresentation rho).comp (rightHom : Model rho →* R) := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  let e : translationKernel rho :=
    ⟨inl (Multiplicative.ofAdd v), rightHom_inl _⟩
  have h := (translationChart rho).quotientRepresentation_apply g e
  change (translationChart rho).quotientRepresentation.ρ
      (QuotientGroup.mk' (translationKernel rho) g) v =
    Multiplicative.toAdd
      ((g * (inl (Multiplicative.ofAdd v) : Model rho) * g⁻¹).left) at h
  rw [conjugate_translation] at h
  exact h

theorem translationRepresentation_generated {t : ℕ}
    (hgen : RepresentationGeneratedBy (linearRepresentation rho) t) :
    RepresentationGeneratedBy (translationChart rho).quotientRepresentation.ρ t := by
  apply RepresentationGeneratedBy.of_comp
    (translationChart rho).quotientRepresentation.ρ
    (QuotientGroup.mk' (translationKernel rho))
  rw [translationRepresentation_comp]
  exact RepresentationGeneratedBy.comp_of_surjective
    (linearRepresentation rho) (rightHom : Model rho →* R) rightHom_surjective hgen

/-- The complement is the displayed group `R`; it need not be identified
with its faithful image in a general linear group. -/
theorem socle_of_surjective [Finite R] [IsCyclic R]
    (hcop : Nat.Coprime p (Nat.card R)) (t : ℕ) (ht : 1 ≤ t)
    (hgen : RepresentationGeneratedBy (linearRepresentation rho) t)
    {Q : Type} [Group Q] (pi : Model rho →* Q) (hpi : Function.Surjective pi) :
    SocleNormalGeneratorBound Q t := by
  letI : IsCyclic (Model rho ⧸ translationKernel rho) :=
    isCyclic_of_injective (complementEquiv rho).toMonoidHom (complementEquiv rho).injective
  have hcopQuotient : Nat.Coprime p (Nat.card (Model rho ⧸ translationKernel rho)) := by
    rw [Nat.card_congr (complementEquiv rho).toEquiv]
    exact hcop
  exact CoprimeCyclicElementarySocleBounds.of_surjective
    (translationKernel rho) (translationChart rho) hcopQuotient t ht
    (translationRepresentation_generated rho hgen) pi hpi

theorem quotient [Finite R] [IsCyclic R]
    (hcop : Nat.Coprime p (Nat.card R)) (t : ℕ) (ht : 1 ≤ t)
    (hgen : RepresentationGeneratedBy (linearRepresentation rho) t)
    (N : Subgroup (Model rho)) [N.Normal] :
    SocleNormalGeneratorBound (Model rho ⧸ N) t :=
  socle_of_surjective rho hcop t ht hgen
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

end LinearSemidirectCoprimeSocleBounds
end SymmetricSubgroupAsymptotics

end
