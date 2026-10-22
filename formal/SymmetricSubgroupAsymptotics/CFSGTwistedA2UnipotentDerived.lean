import SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentLangParameters
import SymmetricSubgroupAsymptotics.CFSGTwistedA2PrimitiveWeights
import SymmetricSubgroupAsymptotics.CFSGTwistedA2OriginalUnipotent

/-! Actual original rank-two unipotents lie in the original fixed group's
DERIVED subgroup. An explicit torus commutator inverse on the norm fibres
proves this, rather than assuming a full SU realization or perfectness. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
open CFSG.Models.Chevalley CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists
open CFSGTwistedA2OriginalRelations CFSGTwistedA2DiagonalTorus CFSGSerreFixedRootElements
variable (K : Type) [Field K] (σ : K ≃+* K)

theorem torus_commutator_upper (hσ : Function.Involutive σ) (z : K) (hz : z ≠ 0) (a b : K) :
    ⁅torusNatural K σ z, upperNatural K σ a b⁆ =
      upperNatural K σ ((firstWeight K σ z - 1) * a)
        ((centralWeight K σ z - 1) * b + (1 - firstWeight K σ z) * a * σ a) := by
  rw [commutatorElement_def, torus_conjugate_upper K σ hσ z hz,
    upperNatural_inv, upperNatural_mul]
  apply congrArg₂ (upperNatural K σ)
  · ring
  · simp only [map_neg]
    ring

theorem fixedToModel_injective (q : CFSG.PrimePower) :
    Function.Injective (fixedToModel A (q.Extension 2) CFSG.Models.reverseNode (fun _ => q.order)) := by
  intro g h he
  apply Subtype.ext
  exact congrArg (fun u : Model A (q.Extension 2) => u.val) he

theorem originalUpper_toModel (q : CFSG.PrimePower) (a b : q.Extension 2)
    (hab : NormCondition (definingFieldAutomorphism q 2) a b) :
    fixedToModel A (q.Extension 2) CFSG.Models.reverseNode (fun _ => q.order)
      (originalUpper q a b hab) = elementaryToModel (q.Extension 2)
        (upperNatural (q.Extension 2) (definingFieldAutomorphism q 2) a b) := rfl

theorem originalTorus_toModel (q : CFSG.PrimePower) (z : q.Extension 2) (hz : z ≠ 0) :
    fixedToModel A (q.Extension 2) CFSG.Models.reverseNode (fun _ => q.order)
      (originalTorus q z hz) = elementaryToModel (q.Extension 2)
        (torusNatural (q.Extension 2) (definingFieldAutomorphism q 2) z) := rfl

theorem originalUpper_mem_commutator (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    (A0 B0 : q.Extension 2) (hAB : NormCondition (definingFieldAutomorphism q 2) A0 B0) :
    originalUpper q A0 B0 hAB ∈ commutator (OriginalFixedA 2 q) := by
  let σ := definingFieldAutomorphism q 2
  obtain ⟨z, hz, hk, hn⟩ := exists_nontrivial_layer_weights q hq
  have hσ : Function.Involutive σ := fun x => extension_two_pow_twice q x
  obtain ⟨a, b, hab, ha, hb⟩ := commutatorParameters_surjective σ hσ
    (firstWeight (q.Extension 2) σ z) (centralWeight (q.Extension 2) σ z)
    (firstWeight_norm (q.Extension 2) σ hσ z hz)
    (centralWeight_fixed (q.Extension 2) σ hσ z) hk hn A0 B0 hAB
  have he : ⁅originalTorus q z hz, originalUpper q a b hab⁆ = originalUpper q A0 B0 hAB := by
    apply fixedToModel_injective q
    rw [map_commutatorElement, originalTorus_toModel, originalUpper_toModel, originalUpper_toModel]
    rw [← map_commutatorElement]
    apply congrArg (elementaryToModel (q.Extension 2))
    rw [torus_commutator_upper (q.Extension 2) σ hσ z hz, ha, hb]
  rw [← he, commutator_eq_closure]
  exact Subgroup.subset_closure (commutator_mem_commutatorSet _ _)

theorem originalUnipotent_le_commutator (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    originalUnipotent q ≤ commutator (OriginalFixedA 2 q) := by
  rintro g ⟨u, rfl⟩
  obtain ⟨a, b, hab, hu⟩ := u.property
  have he : unipotentToOriginalFixed q u = originalUpper q a b hab := by
    apply Subtype.ext
    change (elementaryToModel (q.Extension 2) u.val).val =
      (elementaryToModel (q.Extension 2)
        (upperNatural (q.Extension 2) (definingFieldAutomorphism q 2) a b)).val
    rw [hu]
  rw [he]
  exact originalUpper_mem_commutator q hq a b hab

end SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
