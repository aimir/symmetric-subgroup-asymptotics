import SymmetricSubgroupAsymptotics.InducedElementOrbitHead
import SymmetricSubgroupAsymptotics.InducedDoubleCosetIndices

/-! Restate the actual-element bound as the number of actual cyclic orbits
on the original subgroup cosets. The existing double-coset/orbit equivalence
uses inversion and retains the original subgroup; no classification input
or existence of a special cyclic subgroup is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem induced_subrepresentationCharacterHead_le_cyclicOrbitCount
    {p : ℕ} [Fact p.Prime] {G V : Type} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (H : Subgroup G) (ρ : Representation (ZMod p) H V) (g : G)
    (M : Subrepresentation (Representation.ind H.subtype ρ)) :
    Module.finrank (ZMod p)
      (primeActionCharacters p (representationGroupAction M.toRepresentation)) ≤
        Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ H)) *
          Module.finrank (ZMod p) V := by
  have h := induced_subrepresentationCharacterHead_le_cyclicDoubleCosets H ρ g M
  rw [Nat.card_congr (inducedDoubleCosetOrbitEquiv H (Subgroup.zpowers g))] at h
  exact h

end SymmetricSubgroupAsymptotics
