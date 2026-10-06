import SymmetricSubgroupAsymptotics.FiniteLinearOrbitStabilizerCover

/-!
# Sparse orbit separation by canonical minima

The selected eight-frame exporter chooses the least encoded vector in each
orbit.  Checking that canonical-minimum property is linear in the number of
displayed orbit rows and group elements, whereas checking every pair of
rows is quadratic.  This adapter converts the minimum checks into the
pairwise separation required by `FiniteLinearOrbitStabilizerCover`.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

universe uV

variable {k G : Type*} {V : Type uV} [Field k] [Group G] [Finite G]
  [AddCommGroup V] [Module k V] [Finite V] {c : ℕ}

/-- Canonically ordered vector-orbit representatives with checked literal
stabilizer orders and the exact orbit-size sum. -/
structure FiniteLinearOrbitMinimalStabilizerCover
    (rho : Representation k G V) (representative : Fin c → V) :
    Type (max 1 uV) where
  code : V → ℕ
  representativeCode_injective :
    Function.Injective (fun i ↦ code (representative i))
  minimal : ∀ i g, code (representative i) ≤ code (rho g (representative i))
  stabilizerCard : Fin c → ℕ
  stabilizer_card : ∀ i,
    Nat.card (representationVectorStabilizer rho (representative i)) =
      stabilizerCard i
  orbit_card_sum :
    (∑ i : Fin c, Nat.card G / stabilizerCard i) = Nat.card V

namespace FiniteLinearOrbitMinimalStabilizerCover

variable {rho : Representation k G V} {representative : Fin c → V}
  (C : FiniteLinearOrbitMinimalStabilizerCover rho representative)

include C

omit [Finite G] [Finite V] in
/-- Distinct canonical minima cannot lie in the same orbit. -/
theorem separated (i j : Fin c)
    (h : ∃ g : G, rho g (representative i) = representative j) : i = j := by
  obtain ⟨g, hg⟩ := h
  apply C.representativeCode_injective
  apply le_antisymm
  · simpa only [hg] using C.minimal i g
  · have hginv : rho g⁻¹ (representative j) = representative i := by
      rw [← hg]
      change (rho g⁻¹ * rho g) (representative i) = representative i
      rw [← map_mul, inv_mul_cancel, map_one]
      rfl
    simpa only [hginv] using C.minimal j g⁻¹

/-- Forget the chosen code after deriving pairwise orbit separation. -/
def toStabilizerCover :
    FiniteLinearOrbitStabilizerCover rho representative where
  separated := C.separated
  stabilizerCard := C.stabilizerCard
  stabilizer_card := C.stabilizer_card
  orbit_card_sum := C.orbit_card_sum

end FiniteLinearOrbitMinimalStabilizerCover
end SymmetricSubgroupAsymptotics

end
