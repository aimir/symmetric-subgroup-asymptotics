import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeSignedQuotientNonbinary
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeSignedQuotientPairPackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoB6RawEnvelope
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairCatalogueDispatcher

/-!
# The exact six-block signed quotient as a six-pair B6 row

This file records the literal adapter between the degree-three six-block
signed quotient and the existing degree-two six-pair B6 source.  It does
not add an owner assumption: the only finite input is the already declared
182-row owner table together with its published locator.

The result is deliberately a raw summed package.  Its exceptional B6 row
still has to be combined with the ternary layer's numerical margin before it
can discharge the degree-three residual endpoint.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

namespace PreE7B6ActionCertificate

variable {w : ℕ} {U : PreE7NonPairActionClass w}

/-- The raw B6 comparator is trivial, but the final numerical transfer
requires a positive faithful permutation degree.  Realize the same trivial
comparator on one point.  The envelope and every coefficient are unchanged. -/
noncomputable def quotientSummedPositivePackage
    (S : PreE7B6SourceData w U)
    (lit : PreE7CharacterLiterature) :
    PreE7DegreeTwoPairQuotientSummedPackage
      (preE7NonPairAction w U) := by
  let E := S.quotientSummedEnvelope lit
  letI : Subsingleton E.R := by
    change Subsingleton PUnit
    infer_instance
  exact
    { envelope := E
      v := 1
      action := 1
      action_injective := fun _ _ _ => Subsingleton.elim _ _ }

end PreE7B6ActionCertificate

/-- A literal nonbinary six-pair action transported to its pre-`E7`
transitive-action representative. -/
structure SixPairRepresentativeChart
    (A : Subgroup (Equiv.Perm (Fin 12))) : Type 1 where
  representative : PreE7PairActionClass 6
  sourceEquiv : A ≃* preE7PairAction 6 representative

/-- Construct the representative chart without changing the physical pair
system.  The pair frame is relabelled by the same point conjugation as the
group. -/
noncomputable def sixPairRepresentativeChart
    (A : Subgroup (Equiv.Perm (Fin 12)))
    (hA : ¬ IsPGroup 2 A)
    (htrans : MulAction.IsPretransitive A (Fin 12))
    (F : BinaryPairFrame A (Fin 6)) :
    SixPairRepresentativeChart A := by
  let hcover :=
    Non2TransitiveActionClass.representative_cover A hA htrans
  let i : Non2TransitiveActionClass (Fin 12) := Classical.choose hcover
  let hi : ∃ c : Equiv.Perm (Fin 12),
      MulAut.conj c • A = i.representative :=
    Classical.choose_spec hcover
  let c : Equiv.Perm (Fin 12) := Classical.choose hi
  have hc : MulAut.conj c • A = i.representative :=
    Classical.choose_spec hi
  have hc' : relabelSubgroup c A = i.representative := by
    calc
      relabelSubgroup c A = MulAut.conj c • A := by
        change A.map c.permCongrHom.toMonoidHom = _
        rw [Subgroup.pointwise_smul_def]
        congr 1
      _ = i.representative := hc
  let F' : BinaryPairFrame i.representative (Fin 6) :=
    hc' ▸ F.relabelPoints c
  let p : PreE7PairActionClass 6 :=
    ⟨⟨i, fun d hd => by
        cases d <;> norm_num [PairCountLabel.sourceDegree,
          PairCountLabel.pairCount] at hd⟩, ⟨F'⟩⟩
  exact
    { representative := p
      sourceEquiv := (BinaryPairFrame.sourceRelabelEquiv (U := A) c).trans
        (MulEquiv.subgroupCongr hc') }

/-- Pull the checked B6 summed package from the selected catalogue
representative back to the literal six-pair action. -/
noncomputable def degreeTwoSixPairLiteralSummedPackage
    (table : PrimitiveAffineDegreeTwoSixPairOwnerTable)
    (published : PublishedDegreeTwoSixPairCatalogueLocator table)
    (lit : PreE7CharacterLiterature)
    (A : Subgroup (Equiv.Perm (Fin 12)))
    (hA : ¬ IsPGroup 2 A)
    (htrans : MulAction.IsPretransitive A (Fin 12))
    (F : BinaryPairFrame A (Fin 6)) :
    PreE7DegreeTwoPairQuotientSummedPackage A := by
  let C := sixPairRepresentativeChart A hA htrans F
  let S := degreeTwoSixPairSource table published C.representative
  have hsource : PreE7B6SourceData 12
      (preE7SixPairNonPairAction C.representative) := S
  let Q : PreE7DegreeTwoPairQuotientSummedPackage
      (preE7PairAction 6 C.representative) := by
    simpa only [preE7SixPairNonPairAction_literal] using
      hsource.quotientSummedPositivePackage lit
  exact Q.comapEquiv C.sourceEquiv

namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- The exact local-`S3` six-block signed quotient receives the raw B6
package on its literal action and is then pulled back along the retained
source equivalence to `U / E`. -/
noncomputable def degreeThreeSixBlockSignedQuotientSummedPackage
    (table : PrimitiveAffineDegreeTwoSixPairOwnerTable)
    (published : PublishedDegreeTwoSixPairCatalogueLocator table)
    (lit : PreE7CharacterLiterature)
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 6)
    (hcomponent : Nat.card block.Component = 6) :
    PreE7DegreeTwoPairQuotientSummedPackage
      (preE7NonPairAction w U ⧸ E block P) := by
  let C := degreeThreeSignedQuotientPairChart
    block P hr hs hcomponent
  have hnonbinary : ¬ IsPGroup 2 C.action :=
    C.not_isPGroup_of_residual_count block P (Or.inr (Or.inl rfl))
  let G := degreeTwoSixPairLiteralSummedPackage table published lit
    C.action hnonbinary C.pretransitive C.frame
  exact C.pullbackSummedPackage block P G

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
