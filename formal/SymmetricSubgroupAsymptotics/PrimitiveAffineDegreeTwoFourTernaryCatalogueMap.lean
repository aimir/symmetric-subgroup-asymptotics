import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFourTernaryCompressionSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogue

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

/-- The exact top/core orders have the advertised binary quotient. -/
theorem degreeTwoFourTernary_order_factorization
    (r : Fin 8) :
    degreeTwoFourTernaryTopOrder r =
      degreeTwoFourTernaryCoreOrder r *
        degreeTwoFourTernaryBinaryQuotientOrder r := by
  fin_cases r <;> norm_num

theorem degreeTwoFourTernary_coreOrder_lower
    (r : Fin 8) : 9 ≤ degreeTwoFourTernaryCoreOrder r := by
  fin_cases r <;> norm_num

theorem degreeTwoFourTernary_coreOrder_is_three_power
    (r : Fin 8) : ∃ a : ℕ,
      degreeTwoFourTernaryCoreOrder r = 3 ^ a := by
  fin_cases r
  all_goals first | exact ⟨2, by norm_num⟩ | exact ⟨3, by norm_num⟩ |
    exact ⟨4, by norm_num⟩

theorem degreeTwoFourTernary_quotientOrder_is_two_power
    (r : Fin 8) : ∃ a : ℕ,
      degreeTwoFourTernaryBinaryQuotientOrder r = 2 ^ a := by
  fin_cases r
  all_goals first | exact ⟨3, by norm_num⟩ | exact ⟨4, by norm_num⟩ |
    exact ⟨5, by norm_num⟩ | exact ⟨6, by norm_num⟩

theorem degreeTwoFourTernary_disjointBinaryBound_le_two
    (r : Fin 8) :
    degreeTwoFourTernaryDisjointBinaryBound r ≤ 2 := by
  fin_cases r <;> norm_num

/-- Common block label on the original twelve points.  Its fibres are the
zero-based versions of `{1,5,9}`, `{2,6,10}`, `{3,7,11}`, `{4,8,12}`. -/
def degreeTwoFourTernaryBlock (x : Fin 12) : Fin 4 :=
  ⟨x.val % 4, Nat.mod_lt _ (by norm_num)⟩

/-- Minimal structural input used by the common compression proof.

`same_block_iff_core_orbit` says exactly that the displayed triples are the
`C`-orbits.  Normality then makes the four-block system top invariant; no
separate block-action table is needed.  The last field is the one finite
centralizer check shared by the normal-binary argument.  It is strictly
smaller than enumerating every normal binary subgroup of the top. -/
structure DegreeTwoFourTernaryTopStructure
    (D : DegreeTwoPairTopFiniteInterface 12) : Type 1 where
  core : Subgroup D.top
  core_normal : core.Normal
  core_commutative : IsMulCommutative core
  core_exponent_three : ∀ c : core, c ^ (3 : ℕ) = 1
  core_card_lower : 9 ≤ Nat.card core
  top_transitive : MulAction.IsPretransitive D.top (Fin 12)
  same_block_iff_core_orbit : ∀ x y : Fin 12,
    degreeTwoFourTernaryBlock x = degreeTwoFourTernaryBlock y ↔
      ∃ c : core, c.1.1 x = y
  quotient_binary :
    letI : core.Normal := core_normal
    IsPGroup 2 (D.top ⧸ core)
  core_centralizer_quotient_card_le_two :
    letI : core.Normal := core_normal
    Nat.card ((Subgroup.centralizer (core : Set D.top)).map
      (QuotientGroup.mk' core)) ≤ 2

namespace DegreeTwoFourTernaryTopStructure

variable {D : DegreeTwoPairTopFiniteInterface 12}
  (S : DegreeTwoFourTernaryTopStructure D)

/-- A normal subgroup disjoint from the ternary core centralizes the core:
its commutator lies in both normal subgroups.  Its quotient map is then an
embedding into the checked centralizer quotient.  This derives the former
row-wise universal binary-subgroup field from one concrete finite check. -/
theorem normal_disjoint_core_card_le_two
    (L : Subgroup D.top) [L.Normal]
    (hdisjoint : L ⊓ S.core = ⊥) :
    Nat.card L ≤ 2 := by
  letI : S.core.Normal := S.core_normal
  have hcomm : ⁅L, S.core⁆ = ⊥ := by
    apply le_antisymm
    · exact (Subgroup.commutator_le_inf (H₁ := L) (H₂ := S.core)).trans_eq
        hdisjoint
    · exact bot_le
  have hcentral : L ≤ Subgroup.centralizer (S.core : Set D.top) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  let q := QuotientGroup.mk' S.core
  let f : L →* D.top ⧸ S.core := q.comp L.subtype
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    apply Subtype.ext
    change QuotientGroup.mk' S.core (x : D.top) = 1 at hx
    have hxcore : (x : D.top) ∈ S.core :=
      (QuotientGroup.eq_one_iff (x : D.top)).mp hx
    have hxbot : (x : D.top) ∈ (⊥ : Subgroup D.top) := by
      rw [← hdisjoint]
      exact ⟨x.property, hxcore⟩
    exact Subgroup.mem_bot.mp hxbot
  let intoCentralizerQuotient : L →
      (Subgroup.centralizer (S.core : Set D.top)).map q := fun x =>
    ⟨f x, ⟨⟨x, hcentral x.property⟩, rfl⟩⟩
  have hinjective : Function.Injective intoCentralizerQuotient := by
    intro x y hxy
    apply hf
    exact congrArg Subtype.val hxy
  exact (Nat.card_le_card_of_injective intoCentralizerQuotient hinjective).trans
    S.core_centralizer_quotient_card_le_two

/-- The exact form used later in the socle proof.  The p-group hypothesis is
retained at the call site, although normality and disjointness already force
the stronger cardinal bound above. -/
theorem normal_binary_disjoint_card_le_two
    (L : Subgroup D.top) [L.Normal]
    (_ : IsPGroup 2 L) (hdisjoint : L ⊓ S.core = ⊥) :
    Nat.card L ≤ 2 :=
  S.normal_disjoint_core_card_le_two L hdisjoint

end DegreeTwoFourTernaryTopStructure

/-- One literal row witness adds only its checked exact orders to the
uniform structural hypotheses. -/
structure DegreeTwoFourTernaryLiteralWitness (r : Fin 8) : Type 1 where
  structure : DegreeTwoFourTernaryTopStructure
    (degreeTwoFourTernaryInterface r)
  top_card_eq :
    Nat.card (degreeTwoFourTernaryInterface r).top =
      degreeTwoFourTernaryTopOrder r
  core_card_eq :
    Nat.card structure.core = degreeTwoFourTernaryCoreOrder r

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
      (W.witness r).structure.CertificateTheorem) :
    ∀ r : Fin 8,
      DegreeTwoTwelveFourTernaryCompressionPackage
        (degreeTwoFourTernaryInterface r) := by
  intro r
  refine { compression := ?_ }
  intro p R
  exact ((W.witness r).structure.compressionTheorem_of_certificate
    (compression r)) p R

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
