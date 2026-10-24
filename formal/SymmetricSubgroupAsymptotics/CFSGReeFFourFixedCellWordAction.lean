import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalPositiveNormalizer

/-! A genuinely exceptional-fixed original cell has the same Weyl
action as its letter-reversed cell. This follows from actual T-stability
of the enlarged envelope and proved original cell uniqueness, without
assuming a root-duality map or any fixed-Weyl classification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFixedCellWordAction
open CFSG.Models.Chevalley CFSGReeFFourFieldParameters
open CFSGReeFFourOriginalAutomorphism CFSGReeFFourOriginalWeylWords
open CFSGFFourOriginalBruhatCells CFSGReeFFourOriginalPositiveNormalizer
open CFSGNormTwoCoordinateWeylBlocks CFSGTwistedE6WeylChamber
open CFSGTwistedE6FixedWordClassification CFSGExceptionalCartanPositiveDefinite
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

private theorem fixed_cell_comparison {G : Type*} [Group G] (f : G→*G)
    (b c w wt : G) (hw : f w=wt) (hfix : f (b*w*c)=b*w*c) :
    (b⁻¹*f b)*wt*(f c*c⁻¹)=w := by
  have he : f b*wt*f c=b*w*c := by simpa only [map_mul,hw] using hfix
  calc
    _=b⁻¹*(f b*wt*f c)*c⁻¹ := by group
    _=b⁻¹*(b*w*c)*c⁻¹ := by rw [he]
    _=w := by group

theorem fixed_cell_word_blocks (m : ℕ) (r : List (Fin 4))
    (b c : Model CartanMatrix.F₄ (Field m))
    (hb : b∈modelEnvelope (Field m)) (hc : c∈modelEnvelope (Field m))
    (hfix : reeAutomorphism m (b*modelWeylWord (Field m) r*c)=b*modelWeylWord (Field m) r*c) :
    wordBlockPermutation A hd hs hp ho (expandRelative (r.map CFSG.Models.reverseNode))=
      wordBlockPermutation A hd hs hp ho (expandRelative r) := by
  have hbt : reeAutomorphism m b∈modelEnvelope (Field m) := by
    have ht : reeAutomorphism m b∈(modelEnvelope (Field m)).map (reeAutomorphism m).toMonoidHom :=
      ⟨b,hb,rfl⟩
    rw [ree_preserves_modelEnvelope] at ht
    exact ht
  have hct : reeAutomorphism m c∈modelEnvelope (Field m) := by
    have ht : reeAutomorphism m c∈(modelEnvelope (Field m)).map (reeAutomorphism m).toMonoidHom :=
      ⟨c,hc,rfl⟩
    rw [ree_preserves_modelEnvelope] at ht
    exact ht
  have he := fixed_cell_comparison (reeAutomorphism m).toMonoidHom b c
    (modelWeylWord (Field m) r) (modelWeylWord (Field m) (r.map CFSG.Models.reverseNode))
    (ree_modelWeylWord m r) hfix
  exact model_cell_word_block_unique (Field m) (r.map CFSG.Models.reverseNode) r
    (b⁻¹*reeAutomorphism m b) (reeAutomorphism m c*c⁻¹)
    ((modelEnvelope (Field m)).mul_mem ((modelEnvelope (Field m)).inv_mem hb) hbt)
    ((modelEnvelope (Field m)).mul_mem hct ((modelEnvelope (Field m)).inv_mem hc)) he

theorem fixed_cell_root_action (m : ℕ) (r : List (Fin 4))
    (b c : Model CartanMatrix.F₄ (Field m))
    (hb : b∈modelEnvelope (Field m)) (hc : c∈modelEnvelope (Field m))
    (hfix : reeAutomorphism m (b*modelWeylWord (Field m) r*c)=b*modelWeylWord (Field m) r*c)
    (k : CFSGNormTwoRootPairing.Roots A) :
    rootAction (expandRelative (r.map CFSG.Models.reverseNode)) k=rootAction (expandRelative r) k := by
  have hk := congrArg (fun p : Equiv.Perm (CFSGNormTwoRootSeparatingWeight.WeightBlock A)=>p (some k))
    (fixed_cell_word_blocks m r b c hb hc hfix)
  change some (rootWordPermutation A hd hs hp ho (expandRelative (r.map CFSG.Models.reverseNode)) k)=
    some (rootWordPermutation A hd hs hp ho (expandRelative r) k) at hk
  simpa only [rootWordPermutation_apply] using Option.some.inj hk

end SymmetricSubgroupAsymptotics.CFSGReeFFourFixedCellWordAction
