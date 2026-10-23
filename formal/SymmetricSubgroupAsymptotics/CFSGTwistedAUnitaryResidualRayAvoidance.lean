import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryThreeSingularRays

/-! A literal singular residue vector avoids any two one-dimensional
subspaces, uniformly over all fields including q=2. Three displayed
singular rays and dimension one suffice; no residue census is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices

theorem exists_unitary_singular_vector_outside_two_lines (q : CFSG.PrimePower) (r : ℕ)
    (hr : 1 ≤ r)
    (A B : Submodule (q.Extension 2) (Fin (r + 1) → q.Extension 2))
    (hA : Module.finrank (q.Extension 2) A = 1) (hB : Module.finrank (q.Extension 2) B = 1) :
    ∃ v : Fin (r + 1) → q.Extension 2,
      v ≠ 0 ∧ unitaryNaturalPair q r v v = 0 ∧ v ∉ A ∧ v ∉ B := by
  classical
  have ray_eq (x : Fin (r + 1) → q.Extension 2) (hx : x ≠ 0)
      (C : Submodule (q.Extension 2) (Fin (r + 1) → q.Extension 2))
      (hC : Module.finrank (q.Extension 2) C = 1) (hmem : x ∈ C) :
      (q.Extension 2) ∙ x = C :=
    Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hmem)
      (by rw [hC, finrank_span_singleton hx])
  obtain ⟨u, v, w, hu, hv, hw, hU, hV, hW, huv, huw, hvw⟩ :=
    exists_three_unitary_singular_rays q r hr
  by_contra hnone
  have hcover (x : Fin (r + 1) → q.Extension 2) (hx : x ≠ 0)
      (hiso : unitaryNaturalPair q r x x = 0) : x ∈ A ∨ x ∈ B := by
    by_contra hnot
    exact hnone ⟨x, hx, hiso, (fun ha => hnot (Or.inl ha)), (fun hb => hnot (Or.inr hb))⟩
  rcases hcover u hu hU with hUm | hUm <;>
    rcases hcover v hv hV with hVm | hVm <;>
    rcases hcover w hw hW with hWm | hWm
  all_goals first
    | exact huv ((ray_eq u hu A hA hUm).trans (ray_eq v hv A hA hVm).symm)
    | exact huw ((ray_eq u hu A hA hUm).trans (ray_eq w hw A hA hWm).symm)
    | exact hvw ((ray_eq v hv A hA hVm).trans (ray_eq w hw A hA hWm).symm)
    | exact huv ((ray_eq u hu B hB hUm).trans (ray_eq v hv B hB hVm).symm)
    | exact huw ((ray_eq u hu B hB hUm).trans (ray_eq w hw B hB hWm).symm)
    | exact hvw ((ray_eq v hv B hB hVm).trans (ray_eq w hw B hB hWm).symm)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
