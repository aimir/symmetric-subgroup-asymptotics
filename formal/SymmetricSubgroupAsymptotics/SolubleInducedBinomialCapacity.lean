import SymmetricSubgroupAsymptotics.SolubleCoinducedUniformCapacity
import SymmetricSubgroupAsymptotics.SolubleGridPrimeFactorRank
import SymmetricSubgroupAsymptotics.InducedElementHead
import SymmetricSubgroupAsymptotics.RepresentationDualSubquotientGenerators

/-! The exact binomial capacity for actual induced subrepresentations of
an original finite soluble group. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

variable {k G V : Type} [Field k] [Finite k] [Group G] [Finite G] [IsSolvable G]
    [AddCommGroup V] [Module k V] [Finite V] [Nontrivial V] [FiniteDimensional k V]

theorem soluble_induced_binomial_capacity (H : Subgroup G) (rho : Representation k H V) :
    ∃ w : ℕ,2^traceyBinaryK H.index*w≤H.index*(traceyBinaryK H.index).choose
        (traceyBinaryK H.index/2) ∧
      UniformSubrepresentationGeneratorBound (Representation.ind H.subtype rho)
        (Module.finrank k V*w) := by
  letI : Fintype G := Fintype.ofFinite _
  letI : FiniteDimensional k (Representation.coindV H.subtype rho) := inferInstance
  obtain ⟨D,hD,hwidth⟩ := soluble_coinduced_uniform_capacity H rho (⊥ : Subgroup H) (by simp)
  refine ⟨SolubleCosetShape.middleWidth D.shape,?_,?_⟩
  · simpa only [D.shape.maxRank_eq_K D.primes,D.degree_eq_index] using hwidth
  · have hDC := hD.mono (Nat.mul_le_mul_right _ (min_le_left _ _))
    let e := inducedElementCoinducedEquiv H rho
    exact hDC.of_injective e.toIntertwiningMap e.toLinearEquiv.injective

end SymmetricSubgroupAsymptotics
