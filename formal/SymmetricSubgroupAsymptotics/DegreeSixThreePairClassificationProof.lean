import SymmetricSubgroupAsymptotics.DegreeSixThreePairCentralSubgroups
import SymmetricSubgroupAsymptotics.DegreeSixThreePairFourPointSubgroups
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoThreePairsRawPackage

/-!
# The three-pair degree-six classification from literal coordinates

The full three-pair wreath group is `S4 × C2`. The projection of an actual
transitive six-point subgroup has order divisible by three. Its four
possible abstract models in `S4` are `C3`, `S3`, `A4`, and `S4`; the prime
central binary factor either adds a direct factor or has trivial kernel.
The order-three case cannot act transitively on six points. These facts
give exactly the seven abstract models required by the existing sources.

No published finite classification is a premise of this proof.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace DegreeSixThreePairClassificationProof

private abbrev C2 := Multiplicative (ZMod 2)

private theorem cyclicThree_card : Nat.card CyclicThree = 3 :=
  (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod 3)

/-- Every literal transitive six-point action with three physical pairs
has one of the required abstract group models. -/
theorem model_of_pairFrame
    (U : PreE7NonPairActionClass 6)
    (F : BinaryPairFrame (preE7NonPairAction 6 U) (Fin 3)) :
    Nonempty (PublishedDegreeTwoThreePairModel U) := by
  let A := preE7NonPairAction 6 U
  let f := DegreeSixThreePairWreathChart.productEmbedding F
  let H := f.range
  let E : A ≃* H := MonoidHom.ofInjective
    (DegreeSixThreePairWreathChart.productEmbedding_injective F)
  have hsix : 6 ∣ Nat.card A := by
    have hidx := MulAction.index_stabilizer_of_transitive A (0 : Fin 6)
    rw [Nat.card_fin] at hidx
    have hd := Subgroup.index_dvd_card (MulAction.stabilizer A (0 : Fin 6))
    exact Eq.mp (congrArg (fun m : ℕ => m ∣ Nat.card A) hidx) hd
  have hthree : 3 ∣ Nat.card H := by
    rw [← Nat.card_congr E.toEquiv]
    exact (by decide : 3 ∣ 6).trans hsix
  rcases DegreeSixThreePairCentralSubgroups.subgroupChart H with ⟨J, e | e⟩
  · have hJ : 3 ∣ Nat.card J := by
      rw [← Nat.card_congr e.toEquiv]
      exact hthree
    cases DegreeSixThreePairFourPointSubgroups.subgroupModel J hJ with
    | cyclicThree eJ =>
      have hcard : Nat.card A = 3 :=
        (Nat.card_congr ((E.trans e).trans eJ).toEquiv).trans cyclicThree_card
      rw [hcard] at hsix
      norm_num at hsix
    | symmetricThree eJ =>
      exact ⟨.easy (.symmetricThree ((E.trans e).trans eJ))⟩
    | alternatingFour eJ =>
      exact ⟨.easy (.alternatingFour ((E.trans e).trans eJ))⟩
    | symmetricFour eJ =>
      exact ⟨.easy (.abstractSymmetricFour ((E.trans e).trans eJ))⟩
  · have hJ : 3 ∣ Nat.card J := by
      have hprod : 3 ∣ Nat.card J * 2 := by
        have h := (Nat.card_congr e.toEquiv) ▸ hthree
        simpa only [Nat.card_prod, DegreeSixThreePairCentralSubgroups.card_two] using h
      exact (Nat.prime_three.dvd_mul.mp hprod).resolve_right (by decide)
    cases DegreeSixThreePairFourPointSubgroups.subgroupModel J hJ with
    | cyclicThree eJ =>
      exact ⟨.easy (.cyclicSix ((E.trans e).trans
        (MulEquiv.prodCongr eJ (MulEquiv.refl C2))))⟩
    | symmetricThree eJ =>
      exact ⟨.easy (.symmetricThreeTimesTwo ((E.trans e).trans
        (MulEquiv.prodCongr eJ (MulEquiv.refl C2))))⟩
    | alternatingFour eJ =>
      exact ⟨.central (.alternatingFourTimesTwo ((E.trans e).trans
        (MulEquiv.prodCongr eJ (MulEquiv.refl C2))))⟩
    | symmetricFour eJ =>
      exact ⟨.central (.symmetricFourTimesTwo ((E.trans e).trans
        (MulEquiv.prodCongr eJ (MulEquiv.refl C2))))⟩

/-- The former published representative correspondence is an elementary
consequence of the actual pair frame and transitivity. -/
theorem representativeClassification :
    PublishedDegreeTwoThreePairRepresentativeClassification := by
  intro p
  exact model_of_pairFrame (preE7ThreePairNonPairAction p) (preE7PairFrame 3 p)

/-- The same unconditional recognition applies directly to the actual
minimal-block interface. -/
theorem blockClassification : PublishedDegreeTwoThreePairClassification := by
  intro U basePoint block hFibre hPoints
  let F : BinaryPairFrame (preE7NonPairAction 6 U) (Fin 3) :=
    (OriginalMinimalBlock.pairFrameOfFibreCardTwo
      (A := preE7NonPairAction 6 U) block hFibre).reindex
        (Finite.equivFinOfCardEq hPoints)
  exact model_of_pairFrame U F

end DegreeSixThreePairClassificationProof
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
