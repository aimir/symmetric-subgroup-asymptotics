import SymmetricSubgroupAsymptotics.BinaryCoordinateSpaces
import SymmetricSubgroupAsymptotics.RepresentationCoinvariantFiniteCertificate

/-!
# Basis tests for displacement containment

A fixed upper-layer certificate only needs an upper bound on the
displacement space. Testing the retained group generators on a coordinate
basis proves that bound for every group element and every vector. No exact
displacement basis, normal-subgroup census, or coupled-head table is needed.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- Membership in a coordinate-space annihilator is a basis test. -/
theorem BinaryCoordinateSpace.mem_dualAnnihilator_iff_basis {w d : ℕ}
    (C : BinaryCoordinateSpace w d)
    (f : Module.Dual (ZMod 2) (Fin w → ZMod 2)) :
    f ∈ C.space.dualAnnihilator ↔
      ∀ j, f (C.inclusion (Pi.single j 1)) = 0 := by
  rw [Submodule.mem_dualAnnihilator]
  constructor
  · intro h j
    exact h _ ⟨Pi.single j 1, rfl⟩
  · intro h v hv
    have hle : C.space ≤ LinearMap.ker f :=
      C.le_of_basis_mem _ (fun j ↦ h j)
    exact hle hv

/-- Generator displacements of the displayed basis control all
displacements of the invariant state. -/
theorem binaryCoordinate_displacements_mem_of_generator_basis
    {G I : Type} [Group G] {w d : ℕ}
    (rho : Representation (ZMod 2) G (Fin w → ZMod 2))
    (generators : I → G)
    (hgen : Subgroup.closure (Set.range generators) = ⊤)
    (B : Subrepresentation rho) (C : Submodule (ZMod 2) (Fin w → ZMod 2))
    (S : BinaryCoordinateSpace w d) (hstate : B.toSubmodule = S.space)
    (hbasis : ∀ q j, rho (generators q) (S.inclusion (Pi.single j 1)) -
      S.inclusion (Pi.single j 1) ∈ C)
    (g : G) (v : Fin w → ZMod 2) (hv : v ∈ B) :
    rho g v - v ∈ C := by
  have hspan : representationGeneratorDisplacementSpan rho generators B ≤
      C.comap B.toSubmodule.subtype := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨q, x⟩, rfl⟩
    let delta : (Fin w → ZMod 2) →ₗ[ZMod 2] (Fin w → ZMod 2) :=
      rho (generators q) - LinearMap.id
    have hle : B.toSubmodule ≤ C.comap delta := by
      rw [hstate]
      apply S.le_of_basis_mem
      intro j
      exact hbasis q j
    exact hle x.2
  have hmem := Representation.Coinvariants.sub_mem_ker
    (ρ := B.toRepresentation) g (⟨v, hv⟩ : B.toSubmodule)
  rw [← representationGeneratorDisplacementSpan_eq_coinvariantsKer
    rho generators hgen B] at hmem
  exact hspan hmem

end SymmetricSubgroupAsymptotics

end
