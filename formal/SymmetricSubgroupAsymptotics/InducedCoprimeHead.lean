import SymmetricSubgroupAsymptotics.InducedTernaryHead
import Mathlib.RepresentationTheory.Maschke

/-! Coprime restriction controls every actual induced submodule. Maschke
extends each actual submodule character; Frobenius reciprocity bounds
the whole induced head by the dimension of its original fibre. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra BigOperators
namespace SymmetricSubgroupAsymptotics

def subrepresentationInclusion {k G V : Type} [Field k] [Group G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    (S : Subrepresentation ρ) : S.toRepresentation.IntertwiningMap ρ where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' _ := rfl

theorem semisimple_subrepresentation_hom_le {k G V A : Type} [Field k]
    [Group G] [Finite G] [NeZero (Nat.card G:k)]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup A] [Module k A] [FiniteDimensional k A]
    (ρ : Representation k G V) (σ : Representation k G A)
    (S : Subrepresentation ρ) :
    Module.finrank k (S.toRepresentation.IntertwiningMap σ)≤
      Module.finrank k (ρ.IntertwiningMap σ) := by
  let f := Representation.IntertwiningMap.equivLinearMapAsModule S.toRepresentation ρ
    (subrepresentationInclusion ρ S)
  have hf : Function.Injective f := Subtype.val_injective
  let res : (ρ.asModule→ₗ[k[G]]σ.asModule)→ₗ[k]
      (S.toRepresentation.asModule→ₗ[k[G]]σ.asModule) := {
    toFun t := t.comp f
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have hsurj : Function.Surjective res := by
    intro g
    exact IsSemisimpleModule.extension_property f hf g
  rw [(Representation.IntertwiningMap.equivLinearMapAsModule S.toRepresentation σ).finrank_eq,
    (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ).finrank_eq]
  exact res.finrank_le_finrank_of_surjective hsurj

def inducedHomRestrictionEquiv {k G V A : Type} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [AddCommGroup A] [Module k A]
    (H : Subgroup G) (ρ : Representation k H V) (σ : Representation k G A) :
    (Representation.ind H.subtype ρ).IntertwiningMap σ ≃ₗ[k]
      ρ.IntertwiningMap (σ.comp H.subtype) :=
  (Rep.homLinearEquiv (Rep.ind H.subtype (Rep.of ρ)) (Rep.of σ)).symm.trans
    ((Rep.indResHomEquiv H.subtype (Rep.of ρ) (Rep.of σ)).trans
      (Rep.homLinearEquiv (Rep.of ρ) (Rep.res H.subtype (Rep.of σ))))

theorem induced_hom_trivial_le_fibre {k G V : Type} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (H : Subgroup G) (ρ : Representation k H V) :
    Module.finrank k ((Representation.ind H.subtype ρ).IntertwiningMap
      (Representation.trivial k G k))≤Module.finrank k V := by
  rw [(inducedHomRestrictionEquiv H ρ (Representation.trivial k G k)).finrank_eq]
  have h := (Representation.IntertwiningMap.toLinearMapl (ρ:=ρ)
    (σ:=(Representation.trivial k G k).comp H.subtype)).finrank_le_finrank_of_injective
      (Representation.IntertwiningMap.toLinearMap_injective _ _)
  simpa only [Module.finrank_linearMap,Module.finrank_self,mul_one] using h

theorem induced_coprime_submodule_head_le_fibre (p : ℕ) [Fact p.Prime]
    {G V : Type} [Group G] [Finite G] [NeZero (Nat.card G:ZMod p)]
    [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (H : Subgroup G) (ρ : Representation (ZMod p) H V)
    (S : Subrepresentation (Representation.ind H.subtype ρ)) :
    Module.finrank (ZMod p)
      (primeActionCharacters p (representationGroupAction S.toRepresentation))≤
        Module.finrank (ZMod p) V := by
  letI := induced_finiteDimensional H ρ
  rw [(representationCharacterHeadEquiv S.toRepresentation).finrank_eq]
  exact (semisimple_subrepresentation_hom_le (Representation.ind H.subtype ρ)
    (Representation.trivial (ZMod p) G (ZMod p)) S).trans
      (induced_hom_trivial_le_fibre H ρ)

end SymmetricSubgroupAsymptotics
