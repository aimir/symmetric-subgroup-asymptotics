import SymmetricSubgroupAsymptotics.FusionPhysicalFilters

/-! An arbitrary actual orbit/complement chart enters the canonical physical
family. The original subgroup is reconstructed literally; changing the chart
does not add a new combinatorial weight or a coverage hypothesis.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- Any complete physical chart of an already counted labelled family
can be placed in the fixed canonical chart. -/
theorem fusionRelabelledFamily_of_chart {X Y : Type*}
    (P : Subgroup (Equiv.Perm X) → Prop) (e f : X ≃ Y)
    (K : Subgroup (Equiv.Perm X)) (hK : K ∈ FusionLabelledFamily P) :
    relabelSubgroup e K ∈ FusionRelabelledFamily f (FusionLabelledFamily P) := by
  let c : Equiv.Perm X := e.trans f.symm
  refine ⟨⟨relabelSubgroup c K, fusionLabelledFamily_relabel P c hK⟩, ?_⟩
  change relabelSubgroup f (relabelSubgroup c K) = relabelSubgroup e K
  rw [relabelSubgroup_trans]
  have he : c.trans f = e := by
    ext x
    simp only [c, Equiv.trans_apply, Equiv.apply_symm_apply]
  rw [he]

/-- The restriction image and preservation of the actual original block
suffice. Survival is evaluated on the complete deleted subgroup, retaining
all correlations with the complement. -/
theorem fusionCanonicalFamily_of_chart {h n : ℕ}
    (U : Subgroup (Equiv.Perm (Fin (2*h)))) (hn : 2*h ≤ n)
    (H : Subgroup (Equiv.Perm (Fin n)))
    (e : Fin (2*h) ⊕ Fin (n-2*h) ≃ Fin n)
    (hblock : ∀ k ∈ relabelSubgroup e.symm H,
      Set.MapsTo k (Set.range (Sum.inl : Fin (2*h) → Fin (2*h) ⊕ Fin (n-2*h)))
        (Set.range (Sum.inl : Fin (2*h) → Fin (2*h) ⊕ Fin (n-2*h))))
    (hprojection : (fusionPhysicalBlockPullback (relabelSubgroup e.symm H)).map
      (MonoidHom.fst (Equiv.Perm (Fin (2*h))) (Equiv.Perm (Fin (n-2*h)))) = U)
    (P : Subgroup (U × Equiv.Perm (Fin (n-2*h))) → Prop)
    (hP : P (fusionDeletedModel U (relabelSubgroup e.symm H))) :
    H ∈ FusionCanonicalFamily U hn P := by
  have hm := fusionDeletedModel_mem_family U (relabelSubgroup e.symm H)
    hblock hprojection P hP
  have hr := fusionRelabelledFamily_of_chart
    (FusionOrbitModel U (FusionAcceptedOrbitPredicate U P))
    e (fusionMenuPointEquiv h n hn) (relabelSubgroup e.symm H) hm
  simpa only [relabelSubgroup_trans, Equiv.symm_trans_self, relabelSubgroup_refl] using hr

end SymmetricSubgroupAsymptotics
