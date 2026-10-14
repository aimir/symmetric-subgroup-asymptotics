import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFourTernaryCatalogueMap

/-!
# Generated finite input for the eight four-ternary tops

This file contains only the literal core-generator data and one shared
certificate interface.  The emitter proves the fields of
`DegreeTwoFourTernaryFiniteChecks`; the generic assembler then produces all
eight `DegreeTwoFourTernaryLiteralWitness` values.  No original degree-24
pair lift or original normal subgroup is enumerated here.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- One variable-length row of literal ternary-core generators. -/
structure DegreeTwoFourTernaryCoreGeneratorRow where
  count : ℕ
  image : Fin count → Fin 12 → Fin 12

/-- Literal zero-based images copied from the pinned selected witness map.
Every listed permutation has exponent dividing three. -/
def degreeTwoFourTernaryCoreGeneratorRow :
    Fin 8 → DegreeTwoFourTernaryCoreGeneratorRow :=
  ![
    { count := 2
      image := ![
        (fun x => (#[0, 9, 2, 11, 4, 1, 6, 3, 8, 5, 10, 7] : Array (Fin 12))[x.val]!),
        (fun x => (#[4, 9, 6, 11, 8, 1, 10, 3, 0, 5, 2, 7] : Array (Fin 12))[x.val]!)
      ] },
    { count := 2
      image := ![
        (fun x => (#[0, 5, 2, 7, 4, 9, 6, 11, 8, 1, 10, 3] : Array (Fin 12))[x.val]!),
        (fun x => (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!)
      ] },
    { count := 3
      image := ![
        (fun x => (#[0, 1, 10, 7, 4, 5, 2, 11, 8, 9, 6, 3] : Array (Fin 12))[x.val]!),
        (fun x => (#[0, 5, 10, 3, 4, 9, 2, 7, 8, 1, 6, 11] : Array (Fin 12))[x.val]!),
        (fun x => (#[4, 5, 10, 11, 8, 9, 2, 3, 0, 1, 6, 7] : Array (Fin 12))[x.val]!)
      ] },
    { count := 4
      image := ![
        (fun x => (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!),
        (fun x => (#[0, 1, 10, 11, 4, 5, 2, 3, 8, 9, 6, 7] : Array (Fin 12))[x.val]!),
        (fun x => (#[0, 5, 10, 11, 4, 9, 2, 3, 8, 1, 6, 7] : Array (Fin 12))[x.val]!),
        (fun x => (#[4, 1, 10, 11, 8, 5, 2, 3, 0, 9, 6, 7] : Array (Fin 12))[x.val]!)
      ] },
    { count := 4
      image := ![
        (fun x => (#[0, 1, 6, 3, 4, 5, 10, 7, 8, 9, 2, 11] : Array (Fin 12))[x.val]!),
        (fun x => (#[0, 9, 6, 3, 4, 1, 10, 7, 8, 5, 2, 11] : Array (Fin 12))[x.val]!),
        (fun x => (#[0, 9, 6, 7, 4, 1, 10, 11, 8, 5, 2, 3] : Array (Fin 12))[x.val]!),
        (fun x => (#[4, 9, 6, 3, 8, 1, 10, 7, 0, 5, 2, 11] : Array (Fin 12))[x.val]!)
      ] },
    { count := 9
      image := ![
        (fun x => (#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : Array (Fin 12))[x.val]!),
        (fun x => (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!),
        (fun x => (#[0, 9, 2, 7, 4, 1, 6, 11, 8, 5, 10, 3] : Array (Fin 12))[x.val]!),
        (fun x => (#[0, 1, 10, 7, 4, 5, 2, 11, 8, 9, 6, 3] : Array (Fin 12))[x.val]!),
        (fun x => (#[0, 9, 10, 3, 4, 1, 2, 7, 8, 5, 6, 11] : Array (Fin 12))[x.val]!),
        (fun x => (#[0, 9, 10, 7, 4, 1, 2, 11, 8, 5, 6, 3] : Array (Fin 12))[x.val]!),
        (fun x => (#[0, 9, 10, 11, 4, 1, 2, 3, 8, 5, 6, 7] : Array (Fin 12))[x.val]!),
        (fun x => (#[4, 9, 10, 7, 8, 1, 2, 11, 0, 5, 6, 3] : Array (Fin 12))[x.val]!),
        (fun x => (#[4, 9, 10, 11, 8, 1, 2, 3, 0, 5, 6, 7] : Array (Fin 12))[x.val]!)
      ] },
    { count := 8
      image := ![
        (fun x => (#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : Array (Fin 12))[x.val]!),
        (fun x => (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!),
        (fun x => (#[0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 2, 3] : Array (Fin 12))[x.val]!),
        (fun x => (#[0, 5, 2, 7, 4, 9, 6, 11, 8, 1, 10, 3] : Array (Fin 12))[x.val]!),
        (fun x => (#[0, 5, 6, 3, 4, 9, 10, 7, 8, 1, 2, 11] : Array (Fin 12))[x.val]!),
        (fun x => (#[0, 5, 6, 7, 4, 9, 10, 11, 8, 1, 2, 3] : Array (Fin 12))[x.val]!),
        (fun x => (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!),
        (fun x => (#[4, 5, 6, 11, 8, 9, 10, 3, 0, 1, 2, 7] : Array (Fin 12))[x.val]!)
      ] },
    { count := 7
      image := ![
        (fun x => (#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : Array (Fin 12))[x.val]!),
        (fun x => (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!),
        (fun x => (#[0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 2, 3] : Array (Fin 12))[x.val]!),
        (fun x => (#[0, 5, 2, 7, 4, 9, 6, 11, 8, 1, 10, 3] : Array (Fin 12))[x.val]!),
        (fun x => (#[0, 5, 6, 3, 4, 9, 10, 7, 8, 1, 2, 11] : Array (Fin 12))[x.val]!),
        (fun x => (#[0, 5, 6, 7, 4, 9, 10, 11, 8, 1, 2, 3] : Array (Fin 12))[x.val]!),
        (fun x => (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!)
      ] }
  ]

/-- The checked literal permutations.  Since every source array has cube
one, its square is the inverse; only closed finite array equalities enter. -/
def degreeTwoFourTernaryCoreGeneratorPerm
    (r : Fin 8)
    (j : Fin (degreeTwoFourTernaryCoreGeneratorRow r).count) :
    Equiv.Perm (Fin 12) where
  toFun := (degreeTwoFourTernaryCoreGeneratorRow r).image j
  invFun := fun x =>
    (degreeTwoFourTernaryCoreGeneratorRow r).image j
      ((degreeTwoFourTernaryCoreGeneratorRow r).image j x)
  left_inv := by
    fin_cases r <;> fin_cases j <;> decide +kernel
  right_inv := by
    fin_cases r <;> fin_cases j <;> decide +kernel

/-- The only word-membership payload: the generated core elements lie in
their displayed literal catalogue tops.  This is separated because the
top groups are closures of the published row generators. -/
structure DegreeTwoFourTernaryGeneratorMembership : Prop where
  mem : ∀ (r : Fin 8)
    (j : Fin (degreeTwoFourTernaryCoreGeneratorRow r).count),
      degreeTwoFourTernaryCoreGeneratorPerm r j ∈
        (degreeTwoFourTernaryInterface r).top

/-- The core generated inside the literal top from the shared data table. -/
def degreeTwoFourTernaryCore
    (M : DegreeTwoFourTernaryGeneratorMembership) (r : Fin 8) :
    Subgroup (degreeTwoFourTernaryInterface r).top :=
  Subgroup.closure (Set.range (fun j =>
    (⟨degreeTwoFourTernaryCoreGeneratorPerm r j, M.mem r j⟩ :
      (degreeTwoFourTernaryInterface r).top)))

/-- One proof-carrying finite payload for all eight rows.  Each field is a
closed top/core computation, while the original-lift theorem remains
entirely in the generic block-parity file.  The centralizer quotient field
replaces a universal enumeration of normal binary subgroups. -/
structure DegreeTwoFourTernaryFiniteChecks : Type 1 where
  membership : DegreeTwoFourTernaryGeneratorMembership
  core_normal : ∀ r : Fin 8,
    (degreeTwoFourTernaryCore membership r).Normal
  core_commutative : ∀ r : Fin 8,
    IsMulCommutative (degreeTwoFourTernaryCore membership r)
  core_exponent_three : ∀ (r : Fin 8)
    (c : degreeTwoFourTernaryCore membership r), c ^ (3 : ℕ) = 1
  top_card : ∀ r : Fin 8,
    Nat.card (degreeTwoFourTernaryInterface r).top =
      degreeTwoFourTernaryTopOrder r
  core_card : ∀ r : Fin 8,
    Nat.card (degreeTwoFourTernaryCore membership r) =
      degreeTwoFourTernaryCoreOrder r
  top_transitive : ∀ r : Fin 8,
    MulAction.IsPretransitive
      (degreeTwoFourTernaryInterface r).top (Fin 12)
  exact_orbits : ∀ (r : Fin 8) (x y : Fin 12),
    degreeTwoFourTernaryBlock x = degreeTwoFourTernaryBlock y ↔
      ∃ c : degreeTwoFourTernaryCore membership r, c.1.1 x = y
  quotient_binary : ∀ r : Fin 8,
    letI : (degreeTwoFourTernaryCore membership r).Normal :=
      core_normal r
    IsPGroup 2 ((degreeTwoFourTernaryInterface r).top ⧸
      degreeTwoFourTernaryCore membership r)
  centralizer_quotient_card : ∀ r : Fin 8,
    letI : (degreeTwoFourTernaryCore membership r).Normal :=
      core_normal r
    Nat.card ((Subgroup.centralizer
      (degreeTwoFourTernaryCore membership r :
        Set (degreeTwoFourTernaryInterface r).top)).map
      (QuotientGroup.mk' (degreeTwoFourTernaryCore membership r))) =
        degreeTwoFourTernaryDisjointBinaryBound r

namespace DegreeTwoFourTernaryFiniteChecks

variable (F : DegreeTwoFourTernaryFiniteChecks)

/-- Assemble the exact common structural input for one generated row. -/
noncomputable def topStructure (r : Fin 8) :
    DegreeTwoFourTernaryTopStructure
      (degreeTwoFourTernaryInterface r) where
  core := degreeTwoFourTernaryCore F.membership r
  core_normal := F.core_normal r
  core_commutative := F.core_commutative r
  core_exponent_three := F.core_exponent_three r
  core_card_lower := by
    rw [F.core_card r]
    exact degreeTwoFourTernary_coreOrder_lower r
  top_transitive := F.top_transitive r
  same_block_iff_core_orbit := F.exact_orbits r
  quotient_binary := F.quotient_binary r
  core_centralizer_quotient_card_le_two := by
    rw [F.centralizer_quotient_card r]
    exact degreeTwoFourTernary_disjointBinaryBound_le_two r

/-- All eight finite witnesses follow from the single generated payload. -/
noncomputable def catalogueWitnesses :
    DegreeTwoFourTernaryCatalogueWitnesses where
  witness r :=
    { topStructure := F.topStructure r
      top_card_eq := F.top_card r
      core_card_eq := F.core_card r }

end DegreeTwoFourTernaryFiniteChecks

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
