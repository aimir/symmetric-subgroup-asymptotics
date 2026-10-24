import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedCellWordAction
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalNegativeStability
import SymmetricSubgroupAsymptotics.CFSGE6GeckOrbitParameterWordMembership
import SymmetricSubgroupAsymptotics.CFSGSerreModelRootGeneration

/-! Negative descents of a genuinely exceptional-fixed original cell
occur in reversed relative-node pairs. The proof transports an actual
root parameter at one through T and the whole negative preimage. It
does not posit an exceptional automorphism on the E6 root lattice. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFixedWordPairedSigns
open CFSG.Models.Chevalley CFSGReeFFourFieldParameters
open CFSGReeFFourOriginalAutomorphism CFSGReeFFourOriginalWeylWords
open CFSGReeFFourOriginalNegativeStability CFSGReeFFourFixedCellWordAction
open CFSGFFourOriginalMiddleWords CFSGFFourOriginalBruhatCells
open CFSGFFourE6FixedGeneratedGroup CFSGTwistedE6GeckRelativeRootGenerated
open CFSGE6GeckOrbitParameterWordMembership
open CFSGE6GeckOrbitOneSignDetection CFSGTwistedE6WeylChamber
open CFSGTwistedE6FixedWordClassification CFSGNormTwoGeckWeylWordDegree
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
local notation "A" => CartanMatrix.E₆
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite

private theorem raw_model_root_one (m : ℕ) (a : Fin 4) :
    rawHom (Field m) (CFSGSerreModelRootGeneration.modelRoot CartanMatrix.F₄ (Field m) false a 1)=
      orbitParameter (Field m) false a 1 := by
  rw [rawHom_root,folded_root_eq_orbitParameter]

private theorem raw_conjugate_one (m : ℕ) (r : List (Fin 4)) (a : Fin 4) :
    rawHom (Field m) (modelWeylWord (Field m) r*CFSGSerreModelRootGeneration.modelRoot CartanMatrix.F₄ (Field m) false a 1*
      (modelWeylWord (Field m) r)⁻¹)=
    wordUnit A hs hp E6Base E6Index (Field m) (expandRelative r)*orbitParameter (Field m) false a 1*
      (wordUnit A hs hp E6Base E6Index (Field m) (expandRelative r))⁻¹ := by
  simp only [map_mul,map_inv,rawHom_modelWeylWord_relative,raw_model_root_one]

private theorem twist_conjugate_one (m : ℕ) (r : List (Fin 4)) (a : Fin 4) :
    reeAutomorphism m (modelWeylWord (Field m) r*CFSGSerreModelRootGeneration.modelRoot CartanMatrix.F₄ (Field m) false a 1*
      (modelWeylWord (Field m) r)⁻¹)=
    modelWeylWord (Field m) (r.map CFSG.Models.reverseNode)*
      CFSGSerreModelRootGeneration.modelRoot CartanMatrix.F₄ (Field m) false (CFSG.Models.reverseNode a) 1*
      (modelWeylWord (Field m) (r.map CFSG.Models.reverseNode))⁻¹ := by
  simp only [map_mul,map_inv,ree_modelWeylWord,reeAutomorphism_root,one_pow]

theorem negative_partner_of_reversed_word_action (m : ℕ) (r : List (Fin 4)) (a : Fin 4)
    (hword : ∀k,rootAction (expandRelative (r.map CFSG.Models.reverseNode)) k=
      rootAction (expandRelative r) k)
    (hall : ∀i∈CFSGTwistedE6RelativeWeylOrbits.orbitWord a,
      ∀j,(rootAction (expandRelative r) (E6Index i)).val j≤0) :
    ∀i∈CFSGTwistedE6RelativeWeylOrbits.orbitWord (CFSG.Models.reverseNode a),
      ∀j,(rootAction (expandRelative r) (E6Index i)).val j≤0 := by
  let x := modelWeylWord (Field m) r*CFSGSerreModelRootGeneration.modelRoot CartanMatrix.F₄ (Field m) false a 1*
    (modelWeylWord (Field m) r)⁻¹
  have hx : x∈modelNegative m := by
    change rawHom (Field m) x∈CFSGTwistedE6GeckPositiveTwist.Negative (Field m)
    rw [raw_conjugate_one]
    exact negative_conjugate_orbit_one (Field m) r a hall
  have htx : reeAutomorphism m x∈modelNegative m := by
    have ht : reeAutomorphism m x∈(modelNegative m).map (reeAutomorphism m).toMonoidHom :=
      ⟨x,hx,rfl⟩
    rw [ree_preserves_modelNegative] at ht
    exact ht
  have hraw : rawHom (Field m) (reeAutomorphism m x)∈CFSGTwistedE6GeckPositiveTwist.Negative (Field m) := htx
  have heT : reeAutomorphism m x=
      modelWeylWord (Field m) (r.map CFSG.Models.reverseNode)*
        CFSGSerreModelRootGeneration.modelRoot CartanMatrix.F₄ (Field m) false (CFSG.Models.reverseNode a) 1*
        (modelWeylWord (Field m) (r.map CFSG.Models.reverseNode))⁻¹ :=
    twist_conjugate_one m r a
  rw [heT,raw_conjugate_one] at hraw
  have hsign := nonpositive_of_orbit_one_negative (Field m)
    (r.map CFSG.Models.reverseNode) (CFSG.Models.reverseNode a) hraw
  intro i hi j
  have h := hsign i hi j
  rw [hword] at h
  exact h

theorem fixed_cell_negative_partner (m : ℕ) (r : List (Fin 4))
    (b c : Model CartanMatrix.F₄ (Field m))
    (hb : b∈modelEnvelope (Field m)) (hc : c∈modelEnvelope (Field m))
    (hfix : reeAutomorphism m (b*modelWeylWord (Field m) r*c)=b*modelWeylWord (Field m) r*c)
    (a : Fin 4)
    (hall : ∀i∈CFSGTwistedE6RelativeWeylOrbits.orbitWord a,
      ∀j,(rootAction (expandRelative r) (E6Index i)).val j≤0) :
    ∀i∈CFSGTwistedE6RelativeWeylOrbits.orbitWord (CFSG.Models.reverseNode a),
      ∀j,(rootAction (expandRelative r) (E6Index i)).val j≤0 :=
  negative_partner_of_reversed_word_action m r a
    (fixed_cell_root_action m r b c hb hc hfix) hall

end SymmetricSubgroupAsymptotics.CFSGReeFFourFixedWordPairedSigns
