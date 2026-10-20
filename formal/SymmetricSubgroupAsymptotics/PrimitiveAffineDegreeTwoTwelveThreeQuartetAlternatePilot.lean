import SymmetricSubgroupAsymptotics.BinaryThreeQuartetLiteralSocles
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows251To301
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow94NaturalFamily

/-! The first three-quartet alternate profile uses the exact original
row292 action. Its local four-cycle and transposition give a local binary
Singer map; two explicit conjugates give the other two blocks. The actual
linear image has normal bound three, and its irreducible binary kernel
preserves that bound. The historical capacity-one label is unchanged. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveThreeQuartetAlternatePilot

open SemidirectProduct BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open Non2UnipotentPrefixFiniteMenu Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue BinaryThreeQuartetLiteralSocles

abbrev Blocks := Subgroup.zpowers (finRotate 3)
def rotation : Blocks := ⟨finRotate 3,Subgroup.mem_zpowers _⟩

def localPerm (g : Equiv.Perm (Fin 4)) : Equiv.Perm Plane := planeLabel.symm.permCongr g

def row292WreathLifts : Fin 3 → BinaryPlanePermutationWreathCoordinates.W
    (R := Blocks) (I := Fin 3) :=
  ![⟨Pi.mulSingle 2 (localPerm (finRotate 4)),1⟩,
    ⟨Pi.mulSingle 2 (localPerm (Equiv.swap 1 2)),1⟩,
    ⟨![localPerm ((finRotate 4)^2),localPerm (finRotate 4),localPerm (finRotate 4)],rotation⟩]

def row292Lifts : Fin 3 → BinaryThreeQuartetLiteralSocles.Model (R := Blocks) :=
  fun i => BinaryPlanePermutationWreathCoordinates.coordinates (row292WreathLifts i)

theorem row292_bindings (i : Fin 3) :
    BinaryThreeQuartetLiteralSocles.action (row292Lifts i) = row292Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

theorem row292_blocks :
    Subgroup.closure (Set.range (fun i => (row292Lifts i).right.right)) = ⊤ := by
  let B := Subgroup.closure (Set.range (fun i => (row292Lifts i).right.right))
  have hr : rotation ∈ B := Subgroup.subset_closure (Set.mem_range_self (2 : Fin 3))
  apply top_unique
  intro r _
  obtain ⟨z,hz⟩ := Subgroup.mem_zpowers_iff.mp r.property
  have he : rotation^z = r := Subtype.ext hz
  rw [← he]
  exact B.zpow_mem hr z

def singerWords : Fin 3 → W (R := Blocks) (I := Fin 3) :=
  let z := (row292Lifts 0).right * (row292Lifts 1).right
  let g := (row292Lifts 2).right
  ![g*z*g⁻¹,g^2*z⁻¹*(g^2)⁻¹,z]

theorem singerWords_eq (i : Fin 3) : singerWords i = localEmbedding i singer := by
  apply PermutationalWreathProduct.ext
  · funext j
    apply LinearEquiv.ext
    intro v
    revert i j v
    decide +kernel
  · apply Subtype.ext
    apply Equiv.ext
    intro j
    revert i j
    decide +kernel

theorem row292_local : ∀ j : Fin 3, localEmbedding j singer ∈
    Subgroup.closure (Set.range (fun i => (row292Lifts i).right)) := by
  let C := Subgroup.closure (Set.range (fun i => (row292Lifts i).right))
  have hg (i : Fin 3) : (row292Lifts i).right ∈ C :=
    Subgroup.subset_closure (Set.mem_range_self i)
  have hz := C.mul_mem (hg 0) (hg 1)
  intro j
  rw [← singerWords_eq j]
  fin_cases j
  · exact C.mul_mem (C.mul_mem (hg 2) hz) (C.inv_mem (hg 2))
  · exact C.mul_mem (C.mul_mem (C.pow_mem (hg 2) 2) (C.inv_mem hz))
      (C.inv_mem (C.pow_mem (hg 2) 2))
  · exact hz

theorem blocks_transitive (i j : Fin 3) : ∃ r : Blocks, r • i = j := by
  have h : ∀ i j : Fin 3, ∃ n : Fin 3, ((finRotate 3)^n.val) i = j := by
    decide +kernel
  obtain ⟨n,hn⟩ := h i j
  exact ⟨rotation^n.val,hn⟩

theorem blocks_cycle (j : Fin 3) : ∃ n : ℕ, rotation^n • (0 : Fin 3) = j :=
  ⟨j.val,(by decide +kernel : ∀ j : Fin 3, ((finRotate 3)^j.val) 0 = j) j⟩

theorem blocks_normalGen (N : Subgroup Blocks) (hN : N.Normal) : MarkedC4.normalGen N ≤ 1 := by
  letI := hN
  exact CoprimeCyclicQuotientSocles.normalGen_le_one_of_isCyclic N

theorem row292AtThree_quotientSocle (N : Subgroup Row292Top) [N.Normal] :
    SocleNormalGeneratorBound (Row292Top ⧸ N) 3 :=
  BinaryThreeQuartetLiteralSocles.quotientSocle row292Lifts row292Generators row292_bindings
    row292_blocks row292_local blocks_transitive rotation 0 blocks_cycle 1 blocks_normalGen N

def row292AtThree_family : row292Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row292Interface.normalRegistry (fun N => by letI := N.2; exact row292AtThree_quotientSocle N.1)

def row292AtThree : DegreeTwoTwelveFlexibleProfiles.Data row292Interface where
  kappa := 3
  sectionCap := 1
  parameters := by decide +kernel
  finite := { topSocle := row292AtThree_family
              natural := DegreeTwoTwelveRow94NaturalFamily.row292Natural }

def row292AtThreeResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (291 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (291 : Fin 301)).finite
      (catalogue.row (291 : Fin 301)).expectedProfiles p :=
  row292AtThree.resolvedRow hZmud lit _ R

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveThreeQuartetAlternatePilot

end
