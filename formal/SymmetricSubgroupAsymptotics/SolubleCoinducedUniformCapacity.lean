import SymmetricSubgroupAsymptotics.CoinducedUniformWidthCapacity
import SymmetricSubgroupAsymptotics.SolubleGridMiddleBound

/-! The full leading-coefficient/width engine on one actual finite soluble
group.  Its chart is constructed from that group, and its width is proved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra
namespace SymmetricSubgroupAsymptotics

variable {k G V : Type} [Field k] [Finite k] [Group G] [Finite G] [IsSolvable G]
    [AddCommGroup V] [Module k V] [Finite V] [Nontrivial V] [FiniteDimensional k V]

/-- The same actual soluble coset chart supplies both a uniform generating
capacity and its exact central-binomial width. -/
theorem soluble_coinduced_uniform_capacity
    (H : Subgroup G) (rho : Representation k H V)
    (L : Subgroup H) (hL : L.map H.subtype≤H.normalCore)
    [FiniteDimensional k (Representation.coindV H.subtype rho)] :
    ∃ D : SolubleOrderedCosetChart H,
      UniformSubrepresentationGeneratorBound (Representation.coind H.subtype rho)
        (min (Module.finrank k V)
          (Nat.card (Quotient (representationNonzeroOrbitRel
            (Representation.dual (rho.comp L.subtype)))))*
          SolubleCosetShape.middleWidth D.shape) ∧
      2^D.shape.maxRank*SolubleCosetShape.middleWidth D.shape≤
        D.shape.degree*D.shape.maxRank.choose (D.shape.maxRank/2) := by
  obtain ⟨D⟩ := soluble_ordered_coset_chart G H
  obtain ⟨h,hh,a0,_⟩ := D.finRows.factor 1 (Subgroup.mem_top 1)
  let i0 : Fin (Module.finrank k V) := ⟨0,Module.finrank_pos⟩
  refine ⟨D,?_,D.shape.middleWidth_binomial D.primes⟩
  apply coinduced_uniform_capacity_of_width H rho D.finRows.repr
    (Module.finBasis k V) a0 i0
    (fun x => D.finRows.factor x (Subgroup.mem_top x)) D.shape.finComparable
    (fun a => D.shape.comparable_refl _) D.finRows.unique D.finRows.triangular
    L hL (SolubleCosetShape.middleWidth D.shape)
  exact D.shape.fin_antichain_card_le_middle D.primes

end SymmetricSubgroupAsymptotics
