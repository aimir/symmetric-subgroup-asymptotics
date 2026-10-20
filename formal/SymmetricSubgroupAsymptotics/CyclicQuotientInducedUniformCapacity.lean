import SymmetricSubgroupAsymptotics.CyclicQuotientOrderedTransversal
import SymmetricSubgroupAsymptotics.CoinducedUniformWidthCapacity
import SymmetricSubgroupAsymptotics.InducedElementHead
import SymmetricSubgroupAsymptotics.RepresentationDualSubquotientGenerators

/-! A cyclic actual coset quotient has width one; the local coefficient
orbit count therefore bounds every original induced subrepresentation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra
namespace SymmetricSubgroupAsymptotics

variable {k G V : Type} [Field k] [Finite k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] [Finite V] [Nontrivial V] [FiniteDimensional k V]

theorem cyclicQuotient_induced_uniform_capacity
    (H : Subgroup G) [H.Normal] [IsCyclic (G⧸H)]
    (rho : Representation k H V) (L : Subgroup H) (hL : L.map H.subtype≤H.normalCore) :
    UniformSubrepresentationGeneratorBound (Representation.ind H.subtype rho)
      (min (Module.finrank k V)
        (Nat.card (Quotient (representationNonzeroOrbitRel
          (Representation.dual (rho.comp L.subtype)))))) := by
  obtain ⟨D⟩ := cyclicQuotient_orderedTransversal H
  let e := inducedElementCoinducedEquiv H rho
  letI : FiniteDimensional k (Representation.coindV H.subtype rho) :=
    FiniteDimensional.of_injective (CoinducedLeadingCoordinates.coordinates H rho D.repr
      (Module.finBasis k V))
      (CoinducedLeadingCoordinates.coordinates_injective H rho D.repr (Module.finBasis k V)
        (fun x => D.factor x (Subgroup.mem_top x)))
  have hc : UniformSubrepresentationGeneratorBound (Representation.coind H.subtype rho)
      (min (Module.finrank k V)
        (Nat.card (Quotient (representationNonzeroOrbitRel
          (Representation.dual (rho.comp L.subtype)))))*1) := by
    apply coinduced_uniform_capacity_of_width H rho D.repr (Module.finBasis k V)
      ⟨0,Nat.pos_of_ne_zero H.index_ne_zero_of_finite⟩ ⟨0,Module.finrank_pos⟩
      (fun x => D.factor x (Subgroup.mem_top x)) (· ≤ ·) (fun _ => le_refl _)
      D.unique D.triangular L hL 1
    intro s hs
    apply Finset.card_le_one.mpr
    intro a ha b hb
    rcases le_total a b with h|h
    · exact hs.eq ha hb h
    · exact hs.eq' ha hb h
  have h := hc.of_injective e.toIntertwiningMap e.toLinearEquiv.injective
  simpa only [Nat.mul_one] using h

end SymmetricSubgroupAsymptotics
