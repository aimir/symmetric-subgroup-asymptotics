import SymmetricSubgroupAsymptotics.RepresentationCoordinateChangeCoinvariants

/-! Exact original coinvariant denominators, including their ambient
coordinate images, are retained by an intertwining linear equivalence. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {k G V Z : Type*} [Field k] [Monoid G]
  [AddCommGroup V] [Module k V] [AddCommGroup Z] [Module k Z]

theorem representationEquiv_coinvariantsKer_map
    {rho : Representation k G V} {sigma : Representation k G Z}
    (e : rho.Equiv sigma) :
    (Representation.Coinvariants.ker rho).map e.toLinearMap =
      Representation.Coinvariants.ker sigma := by
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,v⟩,rfl⟩
    change e.toIntertwiningMap (rho g v-v) ∈ Representation.Coinvariants.ker sigma
    rw [map_sub,Representation.IntertwiningMap.isIntertwining]
    exact Representation.Coinvariants.sub_mem_ker g (e.toIntertwiningMap v)
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,z⟩,rfl⟩
    refine ⟨rho g (e.toLinearEquiv.symm z)-e.toLinearEquiv.symm z,
      Representation.Coinvariants.sub_mem_ker g (e.toLinearEquiv.symm z),?_⟩
    change e.toIntertwiningMap (rho g (e.toLinearEquiv.symm z)-e.toLinearEquiv.symm z) = _
    rw [map_sub,Representation.IntertwiningMap.isIntertwining]
    change sigma g (e.toLinearEquiv (e.toLinearEquiv.symm z)) -
      e.toLinearEquiv (e.toLinearEquiv.symm z) = _
    rw [e.toLinearEquiv.apply_symm_apply]

namespace RepresentationCoordinateChange
variable (rho : Representation k G V) (e : V ≃ₗ[k] Z)

/-- The ambient image of the original radical is precisely the ambient
radical of the coordinate image of the same original invariant subspace. -/
theorem subrepresentation_radical (B : Subrepresentation rho) :
    ((Representation.Coinvariants.ker B.toRepresentation).map B.toSubmodule.subtype).map e.toLinearMap =
      (Representation.Coinvariants.ker (subrepresentation rho e B).toRepresentation).map
        (subrepresentation rho e B).toSubmodule.subtype := by
  let f := subrepresentationEquiv rho e B
  have h := representationEquiv_coinvariantsKer_map f
  have hm := congrArg
    (fun P => P.map (subrepresentation rho e B).toSubmodule.subtype) h
  dsimp only at hm
  rw [← Submodule.map_comp] at hm
  rw [← Submodule.map_comp]
  rw [← hm]
  congr 1

end RepresentationCoordinateChange
end SymmetricSubgroupAsymptotics
