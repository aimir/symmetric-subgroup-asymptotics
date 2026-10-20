import SymmetricSubgroupAsymptotics.CoinducedOrbitGeneratorBound
import SymmetricSubgroupAsymptotics.CoinducedScalarGeneratorBound
import SymmetricSubgroupAsymptotics.FiniteModulePaddedGenerators
import SymmetricSubgroupAsymptotics.FiniteRepresentationOrbitDuality

/-! The exact minimum of local dimension and dual-orbit coefficients,
with one padded tuple length for every original coinduced submodule. The
remaining numerical input is a proved width of the actual row poset. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra
namespace SymmetricSubgroupAsymptotics

variable {k G V : Type} [Field k] [Finite k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] [Finite V] [Nontrivial V]
    [FiniteDimensional k V] {n d : ℕ}

theorem coinduced_uniform_capacity_of_width
    (H : Subgroup G) (rho : Representation k H V) (T : Fin n → G)
    (basis : Module.Basis (Fin d) k V) (a0 : Fin n) (i0 : Fin d)
    (hfactor : ∀ x : G, ∃ h : G, h∈H ∧ ∃ a : Fin n, x=h*T a)
    (rel : Fin n → Fin n → Prop) (hrefl : ∀ a, rel a a)
    (hunique : ∀ a b, T a*(T b)⁻¹∈H → a=b)
    (htri : CosetTriangular H T (· < ·) rel)
    (L : Subgroup H) (hL : L.map H.subtype≤H.normalCore)
    (w : ℕ) (hwidth : ∀ s : Finset (Fin n), IsAntichain rel (s : Set (Fin n)) → s.card≤w)
    [FiniteDimensional k (Representation.coindV H.subtype rho)] :
    UniformSubrepresentationGeneratorBound (Representation.coind H.subtype rho)
      (min d (Nat.card (Quotient (representationNonzeroOrbitRel
        (Representation.dual (rho.comp L.subtype)))))*w) := by
  intro M
  letI : AddCommGroup M.toSubmodule := Module.addCommMonoidToAddCommGroup k
  let c := Nat.card (Quotient (representationNonzeroOrbitRel (Representation.dual (rho.comp L.subtype))))
  have hc : c=Nat.card (Quotient (representationNonzeroOrbitRel (rho.comp L.subtype))) :=
    FiniteRepresentationOrbitDuality.nonzero_orbit_card_dual (rho.comp L.subtype)
  by_cases hdc : d≤c
  · obtain ⟨S,hS,hcard⟩ := CoinducedLeadingCoordinates.exists_generating_finset_le_dimension_mul_width
      H rho T basis a0 i0 hfactor rel hrefl hunique htri w hwidth M
    apply ModuleGeneratedBy.of_finset_card_le S hS
    change S.card ≤ min d c * w
    rw [Nat.min_eq_left hdc]
    exact hcard
  · obtain ⟨S,hS,hcard⟩ := CoinducedLeadingRows.exists_generating_finset_le_local_orbits_mul_width
      H rho T a0 hfactor rel hrefl hunique htri L hL w hwidth M
    apply ModuleGeneratedBy.of_finset_card_le S hS
    rw [←hc] at hcard
    change S.card ≤ min d c * w
    rw [Nat.min_eq_right (Nat.le_of_lt (lt_of_not_ge hdc))]
    exact hcard

end SymmetricSubgroupAsymptotics
