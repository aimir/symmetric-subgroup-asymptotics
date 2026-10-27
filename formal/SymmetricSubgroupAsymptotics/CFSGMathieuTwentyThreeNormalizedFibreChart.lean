import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeStabilizerTransversalCover
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeNormalizedFixedPointFibre

/-! A fixed original word takes22 to0. Conjugating the checked original
point-stabilizer chart by this word covers the actual represented images
in the SAME pinned-M23 normalized automorphism fibre. No original-model
recovery or surjectivity of the pinned representation is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeNormalizedFibreChart
open CFSG.Certificates.Mathieu23 M23Certificates M23Certificates.StabilizerChain
open CFSGMathieuTwentyThreeStabilizerTransversalCover

private theorem mul_val_apply (g h : M23) (p : Fin 23) :
    (g*h).val p = g.val (h.val p) := rfl

private theorem smul_val_apply (g : M23) (p : Fin 23) :
    g • p = g.val p := rfl

def conjugator : M23 := Word.toM23 (levelOneWord 0)

theorem conjugator_last : conjugator.val 22 = 0 := levelOneWord_maps_last_all 0

theorem conjugator_inv_zero : (conjugator⁻¹).val 0 = 22 := by
  change conjugator.val.symm 0 = 22
  apply conjugator.val.injective
  rw [conjugator.val.apply_symm_apply,conjugator_last]

def decodeAtZero (c : Code) : M23 := conjugator * wordDecode c * conjugator⁻¹

theorem decodeAtZero_zero (c : Code) : (decodeAtZero c).val 0 = 0 := by
  simp only [decodeAtZero,mul_val_apply,conjugator_inv_zero,wordDecode_last,conjugator_last]

theorem decodeAtZero_injective : Function.Injective decodeAtZero := by
  intro c d he
  apply wordDecode_injective
  have hh := congrArg (fun g : M23 => conjugator⁻¹ * g * conjugator) he
  simpa [decodeAtZero,mul_assoc] using hh

theorem decodeAtZero_surjective (g : M23) (hg : g.val 0 = 0) :
    ∃ c : Code, decodeAtZero c = g := by
  let k : Stabilizer := ⟨conjugator⁻¹ * g * conjugator,by
    rw [MulAction.mem_stabilizer_iff]
    simp only [mul_smul,smul_val_apply,conjugator_last,hg,conjugator_inv_zero]⟩
  obtain ⟨c,hc⟩ := decode_surjective k
  have he : wordDecode c = conjugator⁻¹ * g * conjugator := congrArg Subtype.val hc
  refine ⟨c,?_⟩
  change conjugator * wordDecode c * conjugator⁻¹ = g
  rw [he]
  simp [mul_assoc]

theorem pointFibre_image_has_code
    (f : CFSGMathieuTwentyThreeNormalizedFixedPointFibre.pointFibre 0) :
    ∃ c : Code, (decodeAtZero c).val =
      CFSGMathieuTwentyThreeActualRepresentation.permutationRepresentation
        (f.val.val CFSGMathieuTwentyThreeGoodSylowTwentyThree.pinnedX) := by
  let g : M23 := CFSGMathieuTwentyThreeActualRepresentation.representation
    (f.val.val CFSGMathieuTwentyThreeGoodSylowTwentyThree.pinnedX)
  have hg : g.val 0 = 0 := f.property
  obtain ⟨c,hc⟩ := decodeAtZero_surjective g hg
  exact ⟨c,congrArg Subtype.val hc⟩

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeNormalizedFibreChart
