import SymmetricSubgroupAsymptotics.PrimitiveAffinePublishedSmallStructuralInput

/-! A binary-only small affine package. It contains no degree27 coverage.
The existing full package restricts to it, while the final constructor needs
only the already-retained primitive16 correspondence. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu

structure BinaryAffineRepresentativeCertificate
    (R : SmallAffineCatalogueRow → SmallAffineCatalogueRepresentative)
    (r : SmallAffineCatalogueRow) where
  card_eq : Nat.card (R r).Carrier=r.complementOrder
  solvable_iff : IsSolvable (R r).Carrier ↔ r.nonsoluble=false
  nonsolubleCore : r.nonsoluble=true → SmallAffineChiefOrderSavingCertificate
    (R r).Carrier r.nonsolubleAbelianCap

structure BinaryAffineSmallCatalogueData where
  representative : SmallAffineCatalogueRow → SmallAffineCatalogueRepresentative
  representativeFacts : ∀ r,BinaryAffineRepresentativeCertificate representative r
  locate : ∀ {G X : Type} [Group G] [Finite G] [Fintype X]
    [MulAction G X] [FaithfulSMul G X],
    MulAction.IsPreprimitive G X → (P : PrimitiveAffineProfile G X) → (x : X) →
    (Nat.card X=8 ∨ Nat.card X=16) →
    ∃ r : SmallAffineCatalogueRow,r.degree=Nat.card X ∧
      Nonempty (P.complement x ≃* (representative r).Carrier)

namespace BinaryAffineSmallCatalogueData

def ofFull (D : PublishedPrimitiveAffineSmallCatalogueData) : BinaryAffineSmallCatalogueData where
  representative := D.locator.representative
  representativeFacts r := {
    card_eq := (D.representativeFacts r).card_eq
    solvable_iff := (D.representativeFacts r).solvable_iff
    nonsolubleCore := (D.representativeFacts r).nonsolubleCore }
  locate hp P x h := D.locator.locate hp P x (h.elim Or.inl (fun h16 => Or.inr (Or.inl h16)))

instance : Coe PublishedPrimitiveAffineSmallCatalogueData BinaryAffineSmallCatalogueData := ⟨ofFull⟩


end BinaryAffineSmallCatalogueData
end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
