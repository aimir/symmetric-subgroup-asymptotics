import SymmetricSubgroupAsymptotics.CoprimeCyclicElementarySocles
import SymmetricSubgroupAsymptotics.Non2PreE7AffineModel

/-!
# Cyclic socles in every quotient of an actual coprime cyclic affine model

For the explicit semidirect product `V ⋊ R`, the translation chart is the
literal left coordinate. Its quotient conjugation representation pulls
back to the displayed linear action of `R`. If `R` is cyclic of order
coprime to the field characteristic and that linear module is cyclic,
every actual surjective image has a normally cyclic socle.

Irreducibility of the translation module is not required. In particular,
this covers cyclic semisimple modules with several distinct simple types;
the cyclicity hypothesis is an actual representation-generator theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics
namespace AffineModel

open SemidirectProduct

variable {p d : ℕ} [Fact p.Prime] (R : Subgroup (GLV p d))

def linearRepresentation : Representation (ZMod p) R (V p d) where
  toFun r := (r : GLV p d).toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

def translationEquiv : Vsub R ≃* Multiplicative (V p d) where
  toFun x := (x : Aff R).left
  invFun v := ⟨inl v, ⟨v, rfl⟩⟩
  left_inv x := by
    apply Subtype.ext
    change inl (x : Aff R).left = (x : Aff R)
    obtain ⟨v, hv⟩ := x.property
    rw [← hv]
    rfl
  right_inv _ := rfl
  map_mul' x y := by
    change (x : Aff R).left * linAut R (x : Aff R).right (y : Aff R).left =
      (x : Aff R).left * (y : Aff R).left
    rw [(mem_Vsub R (x : Aff R)).mp x.property, map_one]
    rfl

def translationChart : ElementaryMinimalNormalChart (Vsub R) where
  p := p
  p_prime := Fact.out
  V := V p d
  equiv := translationEquiv R

def complementEquiv : Aff R ⧸ Vsub R ≃* R :=
  (QuotientGroup.quotientMulEquivOfEq
    (show Vsub R = (rightHom : Aff R →* R).ker from range_inl_eq_ker_rightHom)).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (rightHom : Aff R →* R) rightHom_surjective)

theorem translationRepresentation_comp :
    (translationChart R).quotientRepresentation.ρ.comp (QuotientGroup.mk' (Vsub R)) =
      (linearRepresentation R).comp (rightHom : Aff R →* R) := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  let e : Vsub R := ⟨inl (Multiplicative.ofAdd v), ⟨_, rfl⟩⟩
  have h := (translationChart R).quotientRepresentation_apply g e
  change (translationChart R).quotientRepresentation.ρ
      (QuotientGroup.mk' (Vsub R) g) v =
    Multiplicative.toAdd ((g * (inl (Multiplicative.ofAdd v) : Aff R) * g⁻¹).left) at h
  rw [conj_inl] at h
  exact h

theorem translationRepresentation_generated
    (hcyclic : RepresentationGeneratedBy (linearRepresentation R) 1) :
    RepresentationGeneratedBy (translationChart R).quotientRepresentation.ρ 1 := by
  apply RepresentationGeneratedBy.of_comp
    (translationChart R).quotientRepresentation.ρ (QuotientGroup.mk' (Vsub R))
  rw [translationRepresentation_comp]
  exact RepresentationGeneratedBy.comp_of_surjective
    (linearRepresentation R) (rightHom : Aff R →* R) rightHom_surjective hcyclic

/-- Every displayed quotient of the actual semidirect model has a
one-generator socle, with no irreducibility or quotient registry input. -/
theorem socle_one_of_surjective_coprime_cyclic [IsCyclic R]
    (hcop : Nat.Coprime p (Nat.card R))
    (hcyclic : RepresentationGeneratedBy (linearRepresentation R) 1)
    {Q : Type} [Group Q] (pi : Aff R →* Q) (hpi : Function.Surjective pi) :
    SocleNormalGeneratorBound Q 1 := by
  letI : IsCyclic (Aff R ⧸ Vsub R) :=
    isCyclic_of_injective (complementEquiv R).toMonoidHom (complementEquiv R).injective
  have hcopQuotient : Nat.Coprime p (Nat.card (Aff R ⧸ Vsub R)) := by
    rw [Nat.card_congr (complementEquiv R).toEquiv]
    exact hcop
  exact CoprimeCyclicElementarySocles.of_surjective (Vsub R) (translationChart R)
    hcopQuotient (translationRepresentation_generated R hcyclic) pi hpi

/-- The denominator is any actual original normal subgroup of `V ⋊ R`. -/
theorem quotientSocle_one_of_coprime_cyclic [IsCyclic R]
    (hcop : Nat.Coprime p (Nat.card R))
    (hcyclic : RepresentationGeneratedBy (linearRepresentation R) 1)
    (N : Subgroup (Aff R)) [N.Normal] :
    SocleNormalGeneratorBound (Aff R ⧸ N) 1 :=
  socle_one_of_surjective_coprime_cyclic R hcop hcyclic
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

end AffineModel
end SymmetricSubgroupAsymptotics

end
