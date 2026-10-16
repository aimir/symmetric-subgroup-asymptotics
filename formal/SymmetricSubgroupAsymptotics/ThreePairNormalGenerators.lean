import SymmetricSubgroupAsymptotics.NestedBinaryPairSocles
import SymmetricSubgroupAsymptotics.SymmetricThreeSubgroupNormalGenerators
import SymmetricSubgroupAsymptotics.BinaryPairDiagonalUniform

/-! An actual six-point group with three physical pairs and an element
cycling those pairs has all-normal generator bound two. The correlated
binary block kernel is uniformly cyclic, and every actual subgroup of S3
is normally cyclic. Applying this structure to the actual pair image of
an original action gives quotient-socle bound three from original natural
capacity one, even when the six-pair image has no six-cycle. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.ThreePairNormalGenerators

variable {P : Subgroup (Equiv.Perm (Fin 6))} (E : BinaryPairFrame P (Fin 3))

theorem normalGen_le (r : P) (hr : E.top r = NestedBinaryPairSocles.rotation)
    (L : Subgroup P) [L.Normal] : MarkedC4.normalGen L ≤ 2 := by
  apply E.normalGen_le_of_uniform_pair_action 1 1
    (NestedBinaryPairSocles.inner_uniform E r hr) ?_ L
  intro M hM
  letI := hM
  exact SymmetricThreeSubgroupNormalGenerators.normalGen_le E.top.range M

theorem normal_generating_pairs (r : P)
    (hr : E.top r = NestedBinaryPairSocles.rotation)
    (L : Subgroup P) (hL : L.Normal) :
    ∃ x : Fin 2 → P, Subgroup.normalClosure (Set.range x) = L := by
  letI := hL
  exact exists_normal_generating_tuple_of_normalGen_le L (normalGen_le E r hr L)

/-- Two elements moving the first label to the other labels contain a
three-cycle among these six fixed words. Only permutations of three labels
are checked; no subgroups or invariant subspaces are enumerated. -/
private theorem rotation_word : ∀ a b : Equiv.Perm (Fin 3), a 0 = 1 → b 0 = 2 →
    a = NestedBinaryPairSocles.rotation ∨ a⁻¹ = NestedBinaryPairSocles.rotation ∨
    b = NestedBinaryPairSocles.rotation ∨ b⁻¹ = NestedBinaryPairSocles.rotation ∨
    a * b = NestedBinaryPairSocles.rotation ∨ b * a = NestedBinaryPairSocles.rotation := by
  decide +kernel

theorem exists_rotation_of_transitive [MulAction.IsPretransitive P (Fin 6)] :
    ∃ r : P, E.top r = NestedBinaryPairSocles.rotation := by
  have ht (i j : Fin 3) : ∃ g : P, E.top g i = j := by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P (E.frame (i, 0)) (E.frame (j, 0))
    refine ⟨g, ?_⟩
    have h := E.intertwine g (i, 0)
    change (E.frame.symm ((g : Equiv.Perm (Fin 6)) (E.frame (i, 0)))).1 = E.top g i at h
    change (g : Equiv.Perm (Fin 6)) (E.frame (i, 0)) = E.frame (j, 0) at hg
    rw [hg, E.frame.symm_apply_apply] at h
    exact h.symm
  obtain ⟨a, ha⟩ := ht 0 1
  obtain ⟨b, hb⟩ := ht 0 2
  rcases rotation_word (E.top a) (E.top b) ha hb with h | h | h | h | h | h
  · exact ⟨a, h⟩
  · exact ⟨a⁻¹, (map_inv E.top a).trans h⟩
  · exact ⟨b, h⟩
  · exact ⟨b⁻¹, (map_inv E.top b).trans h⟩
  · exact ⟨a * b, (map_mul E.top a b).trans h⟩
  · exact ⟨b * a, (map_mul E.top b a).trans h⟩

include E in
/-- Every transitive actual six-point group preserving three physical pairs
has the uniform all-normal bound two, with arbitrary binary correlations. -/
theorem normalGen_le_of_transitive [MulAction.IsPretransitive P (Fin 6)]
    (L : Subgroup P) [L.Normal] : MarkedC4.normalGen L ≤ 2 := by
  obtain ⟨r, hr⟩ := exists_rotation_of_transitive E
  exact normalGen_le E r hr L

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 6))

theorem quotientSocle_of_original_natural
    (himage : F.top.range = P)
    (r : P) (hr : E.top r = NestedBinaryPairSocles.rotation)
    (huniform : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U X) 1)
    (N : Subgroup U) [N.Normal] : SocleNormalGeneratorBound (U ⧸ N) 3 := by
  apply F.quotientSocle_of_uniform_pair_action 1 2
    (F.uniform_pair_action_of_original 1 huniform) ?_ N
  intro L hL
  letI := hL
  let e : F.top.range ≃* P := MulEquiv.subgroupCongr himage
  exact CoprimeKernelQuotientSocles.normalGen_image_bound
    e.symm.toMonoidHom e.symm.surjective 2
    (fun J hJ => by letI := hJ; exact normalGen_le E r hr J) L

include E in
/-- The transitive structural form needs only the inner physical pairing,
not a selected word or an abstract group identification. -/
theorem quotientSocle_of_transitive_original_natural
    [MulAction.IsPretransitive P (Fin 6)]
    (himage : F.top.range = P)
    (huniform : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U X) 1)
    (N : Subgroup U) [N.Normal] : SocleNormalGeneratorBound (U ⧸ N) 3 := by
  obtain ⟨r, hr⟩ := exists_rotation_of_transitive E
  exact quotientSocle_of_original_natural E F himage r hr huniform N

end SymmetricSubgroupAsymptotics.ThreePairNormalGenerators

end
