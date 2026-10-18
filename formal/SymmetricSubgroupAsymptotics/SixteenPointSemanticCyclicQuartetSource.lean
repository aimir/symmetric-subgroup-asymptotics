import SymmetricSubgroupAsymptotics.BinaryPlaneCyclicWreathQuotientSocles
import SymmetricSubgroupAsymptotics.PreE7FiniteMixedPermutationStructural

/-! A complete original-weight source for the cyclic-quartet family.
The supplied homomorphism is onto the original action, rather than onto a
split substitute for its normal quotients. Independent local Singers and
cyclic block motion are structural hypotheses; coefficient and slope bounds
are discharged by the checked permutation menu. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SixteenPointSemanticCyclicQuartetSource
open BinaryPlaneWreathIrreducible BinaryPlaneWreathNormalGenerators
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {R : Type} [Group R] [Finite R] [IsCyclic R]
  [MulAction R (Fin 4)] [FaithfulSMul R (Fin 4)]
  (K : Subgroup (BinaryPlaneWreathNormalGenerators.Model (R := R) (I := Fin 4)))
  (hloc : ∀ i : Fin 4, localEmbedding i singer ∈ actualImage K)
  (htrans : ∀ i j : Fin 4, ∃ g : actualImage K,
    (g : W (R := R) (I := Fin 4)).right • i = j)
  (hsurj : Function.Surjective
    ((PermutationalWreathProduct.rightHom : W (R := R) (I := Fin 4) →* R).comp
      (actualImage K).subtype))
  (c : R) (hcycle : ∀ j : Fin 4, ∃ n : ℕ, c^n • (0 : Fin 4) = j)
  (hR : Nat.Coprime 3 (Nat.card R))
  (i : PreE7NonPairActionClass 16)
  (pi : K →* preE7NonPairAction 16 i) (hpi : Function.Surjective pi)

include K hloc htrans hsurj c hcycle hR pi hpi in
/-- Every denominator is the original supplied normal subgroup. -/
theorem quotientSocle (N : Subgroup (preE7NonPairAction 16 i)) [N.Normal] :
    SocleNormalGeneratorBound (preE7NonPairAction 16 i ⧸ N) 2 :=
  BinaryPlaneCyclicWreathQuotientSocles.socle_of_surjective K hloc htrans hsurj
    c 0 hcycle hR ((QuotientGroup.mk' N).comp pi)
    ((QuotientGroup.mk'_surjective N).comp hpi)

/-- No order certificate, finite normal census, or final numerical premise. -/
def importedRow (hMN : McIverNeumannPermutationGeneratorBound)
    (hZmud : ZmudFaithfulCharacterTupleInput) : DegreeTwoDegreeSixteenImportedRow i :=
  PreE7FiniteMixedPermutationMenu.censusFreeImportedRow hMN i (by decide : 2 ≤ 2)
    (fun N => by
      letI := N.2
      exact quotientSocle K hloc htrans hsurj c hcycle hR i pi hpi N.1)
    hZmud

/-- The complete source retains the original marking and all normal-axis weights. -/
def source (hMN : McIverNeumannPermutationGeneratorBound)
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    PreE7RankTailSourceOrYonedaTopData 16 i :=
  (importedRow K hloc htrans hsurj c hcycle hR i pi hpi hMN hZmud).source

end SymmetricSubgroupAsymptotics.SixteenPointSemanticCyclicQuartetSource
end
