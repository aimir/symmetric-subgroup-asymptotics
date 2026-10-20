import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFourTernaryCompressionSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogue
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFourTernaryStructure

/-!
# Exact map for the eight four-ternary-orbit pair tops

This file records the small finite input to the common pair-compression
theorem.  The theorem itself is uniform in the literal top.  Consequently
the row certificates stop at the top subgroup `C`; they do not enumerate
normal subgroups of an original degree-twenty-four pair lift.

The selected-normal locators are zero based positions in the pinned
`pair_top_groups.jsonl.gz` rows.  They are emitter locators only.  A Lean
row witness reconstructs the corresponding literal subgroup and proves the
structural fields below.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

open DegreeTwoTwelvePairFiniteCatalogue

/-- The eight rows, in increasing literal catalogue order. -/
def degreeTwoFourTernaryCatalogueIndex : Fin 8 → Fin 301 :=
  ![36, 76, 116, 167, 209, 213, 241, 260]

/-- External one-based row labels. -/
def degreeTwoFourTernaryRowNumber : Fin 8 → ℕ :=
  ![37, 77, 117, 168, 210, 214, 242, 261]

/-- Exact literal interfaces named by the eight rows. -/
noncomputable def degreeTwoFourTernaryInterface :
    Fin 8 → DegreeTwoPairTopFiniteInterface 12 :=
  ![row37Interface, row77Interface, row117Interface, row168Interface,
    row210Interface, row214Interface, row242Interface, row261Interface]

/-- Zero-based positions of the distinguished ternary core in the pinned
normal-state arrays. -/
def degreeTwoFourTernaryNormalStateLocator : Fin 8 → ℕ :=
  ![27, 15, 37, 52, 18, 8, 16, 14]

/-- Exact top orders. -/
def degreeTwoFourTernaryTopOrder : Fin 8 → ℕ :=
  ![72, 144, 216, 648, 1296, 1296, 2592, 5184]

/-- Exact orders of the distinguished elementary ternary cores. -/
def degreeTwoFourTernaryCoreOrder : Fin 8 → ℕ :=
  ![9, 9, 27, 81, 81, 81, 81, 81]

/-- Exact orders of the binary quotients of the tops by those cores. -/
def degreeTwoFourTernaryBinaryQuotientOrder : Fin 8 → ℕ :=
  ![8, 16, 8, 8, 16, 16, 32, 64]

/-- Exact bound needed for normal binary subgroups disjoint from the
ternary core.  The first two rows attain two; it is one in the other rows. -/
def degreeTwoFourTernaryDisjointBinaryBound : Fin 8 → ℕ :=
  ![2, 2, 1, 1, 1, 1, 1, 1]

/-- The internal catalogue indices and the external one-based labels agree.
This tiny lemma is useful to keep generated witness modules free of manual
casts between the two conventions. -/
theorem degreeTwoFourTernaryRowNumber_eq
    (r : Fin 8) :
    degreeTwoFourTernaryRowNumber r =
      (degreeTwoFourTernaryCatalogueIndex r).val + 1 := by
  fin_cases r <;> rfl

/-- The displayed interface really is the row selected from the complete
301-row literal catalogue. -/
theorem degreeTwoFourTernaryInterface_eq_catalogue
    (r : Fin 8) :
    degreeTwoFourTernaryInterface r =
      (catalogue.row (degreeTwoFourTernaryCatalogueIndex r)).finite := by
  fin_cases r <;> rfl

/-- Every selected row is in the ternary branch of the literal catalogue. -/
theorem degreeTwoFourTernaryCatalogueIndex_branch
    (r : Fin 8) :
    branch (degreeTwoFourTernaryCatalogueIndex r) = .ternary := by
  fin_cases r <;> rfl

/-- The eight displayed ternary indices are distinct.  Keeping this as a
small structural certificate avoids asking `native_decide` to recompile the
complete 301-row catalogue when proving exhaustion below. -/
theorem degreeTwoFourTernaryCatalogueIndex_injective :
    Function.Injective degreeTwoFourTernaryCatalogueIndex := by
  intro r s hrs
  fin_cases r <;> fin_cases s <;>
    simp_all [degreeTwoFourTernaryCatalogueIndex]

/-- The displayed eight indices exhaust the ternary branch of the literal
301-row catalogue. -/
theorem degreeTwoFourTernaryCatalogueIndex_complete
    (j : Fin 301) (h : branch j = .ternary) :
    ∃ r : Fin 8, degreeTwoFourTernaryCatalogueIndex r = j := by
  let selected : Finset (Fin 301) :=
    Finset.univ.image degreeTwoFourTernaryCatalogueIndex
  have hselected_card : selected.card = 8 := by
    dsimp [selected]
    rw [Finset.card_image_of_injective _
      degreeTwoFourTernaryCatalogueIndex_injective]
    simp
  have hselected_subset :
      selected ⊆ Finset.univ.filter (fun k => branch k = .ternary) := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨r, -, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact degreeTwoFourTernaryCatalogueIndex_branch r
  have hselected_eq :
      selected = Finset.univ.filter (fun k => branch k = .ternary) := by
    apply Finset.eq_of_subset_of_card_le hselected_subset
    rw [ternary_count_certified, hselected_card]
  have hj : j ∈ selected := by
    rw [hselected_eq]
    simpa using h
  rcases Finset.mem_image.mp hj with ⟨r, -, hr⟩
  exact ⟨r, hr⟩

/-- The exact top/core orders have the advertised binary quotient. -/
theorem degreeTwoFourTernary_order_factorization
    (r : Fin 8) :
    degreeTwoFourTernaryTopOrder r =
      degreeTwoFourTernaryCoreOrder r *
        degreeTwoFourTernaryBinaryQuotientOrder r := by
  fin_cases r <;> norm_num [degreeTwoFourTernaryTopOrder,
    degreeTwoFourTernaryCoreOrder,
    degreeTwoFourTernaryBinaryQuotientOrder]

theorem degreeTwoFourTernary_coreOrder_lower
    (r : Fin 8) : 9 ≤ degreeTwoFourTernaryCoreOrder r := by
  fin_cases r <;> norm_num [degreeTwoFourTernaryCoreOrder]

theorem degreeTwoFourTernary_coreOrder_is_three_power
    (r : Fin 8) : ∃ a : ℕ,
      degreeTwoFourTernaryCoreOrder r = 3 ^ a := by
  fin_cases r
  · exact ⟨2, by norm_num [degreeTwoFourTernaryCoreOrder]⟩
  · exact ⟨2, by norm_num [degreeTwoFourTernaryCoreOrder]⟩
  · exact ⟨3, by norm_num [degreeTwoFourTernaryCoreOrder]⟩
  · exact ⟨4, by norm_num [degreeTwoFourTernaryCoreOrder]⟩
  · exact ⟨4, by norm_num [degreeTwoFourTernaryCoreOrder]⟩
  · exact ⟨4, by norm_num [degreeTwoFourTernaryCoreOrder]⟩
  · exact ⟨4, by norm_num [degreeTwoFourTernaryCoreOrder]⟩
  · exact ⟨4, by norm_num [degreeTwoFourTernaryCoreOrder]⟩

theorem degreeTwoFourTernary_quotientOrder_is_two_power
    (r : Fin 8) : ∃ a : ℕ,
      degreeTwoFourTernaryBinaryQuotientOrder r = 2 ^ a := by
  fin_cases r
  · exact ⟨3, by norm_num [degreeTwoFourTernaryBinaryQuotientOrder]⟩
  · exact ⟨4, by norm_num [degreeTwoFourTernaryBinaryQuotientOrder]⟩
  · exact ⟨3, by norm_num [degreeTwoFourTernaryBinaryQuotientOrder]⟩
  · exact ⟨3, by norm_num [degreeTwoFourTernaryBinaryQuotientOrder]⟩
  · exact ⟨4, by norm_num [degreeTwoFourTernaryBinaryQuotientOrder]⟩
  · exact ⟨4, by norm_num [degreeTwoFourTernaryBinaryQuotientOrder]⟩
  · exact ⟨5, by norm_num [degreeTwoFourTernaryBinaryQuotientOrder]⟩
  · exact ⟨6, by norm_num [degreeTwoFourTernaryBinaryQuotientOrder]⟩

theorem degreeTwoFourTernary_disjointBinaryBound_le_two
    (r : Fin 8) :
    degreeTwoFourTernaryDisjointBinaryBound r ≤ 2 := by
  fin_cases r <;> norm_num [degreeTwoFourTernaryDisjointBinaryBound]

/-- One literal row witness adds only its checked exact orders to the
uniform structural hypotheses. -/
structure DegreeTwoFourTernaryLiteralWitness (r : Fin 8) : Type 1 where
  topStructure : DegreeTwoFourTernaryTopStructure
    (degreeTwoFourTernaryInterface r)
  top_card_eq :
    Nat.card (degreeTwoFourTernaryInterface r).top =
      degreeTwoFourTernaryTopOrder r
  core_card_eq :
    Nat.card topStructure.core = degreeTwoFourTernaryCoreOrder r

/-- The complete finite obligation: eight small top witnesses, with no
original-lift or original-normal census. -/
structure DegreeTwoFourTernaryCatalogueWitnesses : Type 1 where
  witness : ∀ r : Fin 8, DegreeTwoFourTernaryLiteralWitness r

/-- The generic theorem target.  Once proved, each literal top witness
produces the already-defined complete QCHAR compression for every actual
pair realization of that top. -/
def DegreeTwoFourTernaryTopStructure.CompressionTheorem
    {D : DegreeTwoPairTopFiniteInterface 12}
    (S : DegreeTwoFourTernaryTopStructure D) : Prop :=
  ∀ (p : PreE7PairActionClass 12),
    DegreeTwoPairTopRealization D p →
      Nonempty (DegreeTwoFourTernaryCompressionData p)

/-- Kernel-facing statement of the same uniform theorem.  This is the
actual target for the block-parity proof: it constructs a degree-twenty
action of the original group, proves its exact kernel, and proves the
three-slot whole-socle bound on every retained original normal subgroup. -/
def DegreeTwoFourTernaryTopStructure.CertificateTheorem
    {D : DegreeTwoPairTopFiniteInterface 12}
    (S : DegreeTwoFourTernaryTopStructure D) : Prop :=
  ∀ (p : PreE7PairActionClass 12),
    DegreeTwoPairTopRealization D p →
      Nonempty (DegreeTwoFourTernaryCompressionCertificate p)

/-- The exact-kernel form implies the counting-facing quotient form without
any row-specific quotient construction. -/
theorem DegreeTwoFourTernaryTopStructure.compressionTheorem_of_certificate
    {D : DegreeTwoPairTopFiniteInterface 12}
    (S : DegreeTwoFourTernaryTopStructure D)
    (h : S.CertificateTheorem) :
    S.CompressionTheorem := by
  intro p R
  obtain ⟨C⟩ := h p R
  exact ⟨C.toCompressionData⟩

/-- Uniformly turn eight checked top witnesses and the single structural
theorem into all eight per-row packages. -/
noncomputable def DegreeTwoFourTernaryCatalogueWitnesses.packages
    (W : DegreeTwoFourTernaryCatalogueWitnesses)
    (compression : ∀ r : Fin 8,
      (W.witness r).topStructure.CertificateTheorem) :
    ∀ r : Fin 8,
      DegreeTwoTwelveFourTernaryCompressionPackage
        (degreeTwoFourTernaryInterface r) := by
  intro r
  refine { compression := ?_ }
  intro p R
  exact Classical.choice
    (((W.witness r).topStructure.compressionTheorem_of_certificate
      (compression r)) p R)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
