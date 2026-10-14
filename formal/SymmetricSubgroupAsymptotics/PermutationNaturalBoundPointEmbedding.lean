import SymmetricSubgroupAsymptotics.PermutationOrbitCoverGenerators

/-! A uniform natural-module bound transfers along an actual equivariant
point bijection and an acting-group homomorphism. A short literal
generator certificate constructs such a map into a larger permutation
top without identifying that top by its order or enumerating its elements. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

theorem permutationFunctionRepresentation_uniform_of_pointEquiv
    {k G H X Y : Type} [Field k] [Group G] [Group H]
    [MulAction G X] [MulAction H Y]
    (f : G →* H) (e : X ≃ Y)
    (he : ∀ g x, e (g • x) = f g • e x) {n : ℕ}
    (h : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation k G X) n) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation k H Y) n := by
  let rho := permutationFunctionRepresentation k G X
  let sigma := permutationFunctionRepresentation k H Y
  let F : rho.IntertwiningMap (sigma.comp f) :=
    { toLinearMap :=
        { toFun := fun v y ↦ v (e.symm y)
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro v
        funext y
        change v (g⁻¹ • e.symm y) = v (e.symm ((f g)⁻¹ • y))
        congr 1
        apply e.injective
        simpa only [e.apply_symm_apply, map_inv] using he g⁻¹ (e.symm y) }
  have hF : Function.Surjective F := by
    intro v
    refine ⟨fun x ↦ v (e x), ?_⟩
    funext y
    exact congrArg v (e.apply_symm_apply y)
  exact UniformSubrepresentationGeneratorBound.of_comp sigma f (h.of_surjective F hF)

/-- A point chart and target words for the original generators give an
actual conjugate inclusion of the generated source top. -/
structure LiteralPermutationGeneratorEmbedding {ι X : Type}
    (source : ι → Equiv.Perm X) (T : Subgroup (Equiv.Perm X)) where
  pointEquiv : X ≃ X
  images : ι → T
  point_eq : ∀ i x, pointEquiv (source i x) =
    (images i : Equiv.Perm X) (pointEquiv x)

namespace LiteralPermutationGeneratorEmbedding

variable {ι X : Type} {source : ι → Equiv.Perm X}
  {T : Subgroup (Equiv.Perm X)} (C : LiteralPermutationGeneratorEmbedding source T)

theorem conjugates_mem : Subgroup.closure (Set.range source) ≤
    T.comap C.pointEquiv.permCongrHom.toMonoidHom := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  have heq : C.pointEquiv.permCongrHom (source i) = (C.images i : Equiv.Perm X) := by
    apply Equiv.ext
    intro x
    change C.pointEquiv (source i (C.pointEquiv.symm x)) =
      (C.images i : Equiv.Perm X) x
    simpa only [C.pointEquiv.apply_symm_apply] using
      C.point_eq i (C.pointEquiv.symm x)
  change C.pointEquiv.permCongrHom (source i) ∈ T
  rw [heq]
  exact (C.images i).property

def topMap : Subgroup.closure (Set.range source) →* T :=
  (C.pointEquiv.permCongrHom.toMonoidHom.comp
    (Subgroup.closure (Set.range source)).subtype).codRestrict T
      (fun g ↦ C.conjugates_mem g.property)

theorem equivariant (g : Subgroup.closure (Set.range source)) (x : X) :
    C.pointEquiv (g • x) = C.topMap g • C.pointEquiv x := by
  change C.pointEquiv ((g : Equiv.Perm X) x) =
    C.pointEquiv ((g : Equiv.Perm X) (C.pointEquiv.symm (C.pointEquiv x)))
  rw [C.pointEquiv.symm_apply_apply]

include C in
theorem uniform {k : Type} [Field k] {n : ℕ}
    (h : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation k (Subgroup.closure (Set.range source)) X) n) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation k T X) n :=
  permutationFunctionRepresentation_uniform_of_pointEquiv
    C.topMap C.pointEquiv C.equivariant h

end LiteralPermutationGeneratorEmbedding
end SymmetricSubgroupAsymptotics

end
