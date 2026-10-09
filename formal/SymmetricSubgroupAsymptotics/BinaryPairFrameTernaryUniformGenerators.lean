import SymmetricSubgroupAsymptotics.BinaryPairFrameTernaryUniformCyclic

/-!
# Uniform generators from uniform literal sign fibres

The cyclic sign-fibre assembly works without changing the generator count:
one `H`-tuple on a chosen fibre is transported across the transitive set of
sign labels, and the diagonal character projectors recover every component.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics
namespace BinaryPairFrame

variable {X I : Type*} {G : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame G I)

/-- A common `H`-generator bound on every literal sign fibre gives the same
bound on the complete signed coordinate representation. -/
theorem ternarySignedRepresentation_uniformSubrepresentationGeneratorBound
    [Finite X] [Finite I] [Nonempty I]
    (H : ℕ)
    (htrans : MulAction.IsPretransitive G X)
    (hfiber : ∀ chi : CoordinateSign F,
      UniformSubrepresentationGeneratorBound
        (signFiberRepresentation F chi) H) :
    UniformSubrepresentationGeneratorBound
      (ternarySignedRepresentation F) H := by
  letI : MulAction.IsPretransitive G (CoordinateSign F) :=
    coordinateSign_pretransitive F htrans
  intro M
  let chi : CoordinateSign F :=
    coordinateSign F (Classical.choice (inferInstance : Nonempty I))
  obtain ⟨a, ha⟩ := hfiber chi (signFiberSubrepresentation F M chi)
  let inclusion := signFiberSubrepresentationInclusion F M chi
  let generator : Fin H → M.toRepresentation.asModule := fun i ↦
    M.toRepresentation.asModuleEquiv.symm
      (inclusion (a i)).1
  let W : Submodule (ZMod 3)[G] M.toRepresentation.asModule :=
    Submodule.span (ZMod 3)[G] (Set.range generator)
  let N : Subrepresentation M.toRepresentation :=
    Subrepresentation.ofSubmodule' W
  have hfiber_le : ∀ y : signFiberSubrepresentation F M chi,
      inclusion y ∈ N.toSubmodule := by
    let Q : Subrepresentation
        (signFiberSubrepresentation F M chi).toRepresentation :=
      { toSubmodule := N.toSubmodule.comap inclusion.toLinearMap
        apply_mem_toSubmodule := by
          intro u y hy
          change inclusion
              ((signFiberSubrepresentation F M chi).toRepresentation u y) ∈ N
          rw [Representation.IntertwiningMap.isIntertwining]
          exact N.apply_mem_toSubmodule u.1 hy }
    have haQ : ∀ i, a i ∈ Q.asSubmodule := by
      intro i
      change generator i ∈ W
      exact Submodule.subset_span (Set.mem_range_self i)
    have hspan : Submodule.span (ZMod 3)[MulAction.stabilizer G chi]
        (Set.range a) ≤ Q.asSubmodule :=
      Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact haQ i)
    rw [ha] at hspan
    intro y
    exact hspan Submodule.mem_top
  refine ⟨generator, top_unique ?_⟩
  intro x _hx
  change x ∈ W
  have hcomponent : ∀ psi : CoordinateSign F,
      ⟨coordinateSignProjection F psi x.1,
        coordinateSignProjection_mem F M psi x.1 x.2⟩ ∈ N.toSubmodule := by
    intro psi
    obtain ⟨u, hu⟩ := MulAction.exists_smul_eq G chi psi
    let z : M.toSubmodule :=
      ⟨coordinateSignProjection F psi x.1,
        coordinateSignProjection_mem F M psi x.1 x.2⟩
    let y : M.toSubmodule := M.toRepresentation u⁻¹ z
    have hysupport : ∀ i, coordinateSign F i ≠ chi → y.1 i = 0 := by
      intro i hi
      have hnotpsi : coordinateSign F (F.top u i) ≠ psi := by
        intro heq
        apply hi
        apply (coordinateSignTopPerm F u).injective
        simpa only [coordinateSignTopPerm_apply,
          coordinateSignTopMap_apply_coordinate, hu] using heq
      simp [y, z, ternarySignedRepresentation_apply,
        coordinateSignProjection_apply, hnotpsi]
    have hyext : signFiberExtension F chi
        (signFiberRestriction F chi y.1) = y.1 :=
      signFiberExtension_restriction_of_supported F chi y.1 hysupport
    let yF : signFiberSubrepresentation F M chi :=
      ⟨signFiberRestriction F chi y.1, by
        change signFiberExtension F chi
          (signFiberRestriction F chi y.1) ∈ M
        rw [hyext]
        exact y.2⟩
    have hyN : y ∈ N.toSubmodule := by
      have := hfiber_le yF
      simpa only [inclusion, signFiberSubrepresentationInclusion, yF,
        hyext] using this
    have huz : M.toRepresentation u y = z := by
      simp [y]
    rw [← huz]
    exact N.apply_mem_toSubmodule u hyN
  have hsum : (∑ psi : CoordinateSign F,
      (⟨coordinateSignProjection F psi x.1,
        coordinateSignProjection_mem F M psi x.1 x.2⟩ : M.toSubmodule)) ∈
      N.toSubmodule :=
    N.toSubmodule.sum_mem (fun psi _ ↦ hcomponent psi)
  have heq : (∑ psi : CoordinateSign F,
      (⟨coordinateSignProjection F psi x.1,
        coordinateSignProjection_mem F M psi x.1 x.2⟩ : M.toSubmodule)) = x := by
    apply Subtype.ext
    exact sum_coordinateSignProjection F x.1
  rw [heq] at hsum
  exact hsum

/-- The same uniform bound holds for the contragredient. -/
theorem ternarySignedRepresentation_dual_uniformSubrepresentationGeneratorBound
    [Finite X] [Finite I] [Nonempty I]
    (H : ℕ)
    (htrans : MulAction.IsPretransitive G X)
    (hfiber : ∀ chi : CoordinateSign F,
      UniformSubrepresentationGeneratorBound
        (signFiberRepresentation F chi) H) :
    UniformSubrepresentationGeneratorBound
      (ternarySignedRepresentation F).dual H :=
  ternarySignedRepresentation_dual_uniform_of_primal F
    (ternarySignedRepresentation_uniformSubrepresentationGeneratorBound
      F H htrans hfiber)

end BinaryPairFrame
end SymmetricSubgroupAsymptotics

end
