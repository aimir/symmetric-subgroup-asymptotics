import SymmetricSubgroupAsymptotics.Selected1542QuotientStructureEightRows00
import SymmetricSubgroupAsymptotics.Selected1542QuotientStructureEightRows01
import SymmetricSubgroupAsymptotics.Selected1542QuotientStructureEightRows02
import SymmetricSubgroupAsymptotics.Selected1542QuotientStructureEightRows03
import SymmetricSubgroupAsymptotics.Selected1542QuotientStructureEightRows04
import SymmetricSubgroupAsymptotics.Selected1542QuotientStructureEightRows05
import SymmetricSubgroupAsymptotics.Selected1542QuotientStructureEightRows06
import SymmetricSubgroupAsymptotics.Selected1542QuotientStructureEightRows07

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1542QuotientStructure

private theorem kernel_assemble (P : Fin 64 → Prop)
    (h0 : ∀ r : Fin 8, P (finProdFinEquiv ((0 : Fin 8),r)))
    (h1 : ∀ r : Fin 8, P (finProdFinEquiv ((1 : Fin 8),r)))
    (h2 : ∀ r : Fin 8, P (finProdFinEquiv ((2 : Fin 8),r)))
    (h3 : ∀ r : Fin 8, P (finProdFinEquiv ((3 : Fin 8),r)))
    (h4 : ∀ r : Fin 8, P (finProdFinEquiv ((4 : Fin 8),r)))
    (h5 : ∀ r : Fin 8, P (finProdFinEquiv ((5 : Fin 8),r)))
    (h6 : ∀ r : Fin 8, P (finProdFinEquiv ((6 : Fin 8),r)))
    (h7 : ∀ r : Fin 8, P (finProdFinEquiv ((7 : Fin 8),r)))
    (i : Fin 64) : P i := by
  obtain ⟨⟨k,r⟩,rfl⟩ := (finProdFinEquiv : Fin 8 × Fin 8 ≃ Fin 64).surjective i
  fin_cases k
  · exact h0 r
  · exact h1 r
  · exact h2 r
  · exact h3 r
  · exact h4 r
  · exact h5 r
  · exact h6 r
  · exact h7 r

private theorem state_assemble (P : Fin 48 → Prop)
    (h0 : ∀ r : Fin 8, P (finProdFinEquiv ((0 : Fin 6),r)))
    (h1 : ∀ r : Fin 8, P (finProdFinEquiv ((1 : Fin 6),r)))
    (h2 : ∀ r : Fin 8, P (finProdFinEquiv ((2 : Fin 6),r)))
    (h3 : ∀ r : Fin 8, P (finProdFinEquiv ((3 : Fin 6),r)))
    (h4 : ∀ r : Fin 8, P (finProdFinEquiv ((4 : Fin 6),r)))
    (h5 : ∀ r : Fin 8, P (finProdFinEquiv ((5 : Fin 6),r)))
    (i : Fin 48) : P i := by
  obtain ⟨⟨k,r⟩,rfl⟩ := (finProdFinEquiv : Fin 6 × Fin 8 ≃ Fin 48).surjective i
  fin_cases k
  · exact h0 r
  · exact h1 r
  · exact h2 r
  · exact h3 r
  · exact h4 r
  · exact h5 r

theorem all_preimage_word : ∀ i : Fin 64, ∀ x : Fin 16, preimageWordElement i x=preimageElements i x :=
  kernel_assemble (fun i => ∀ x : Fin 16, preimageWordElement i x=preimageElements i x)
    eightRows00_preimage_word eightRows01_preimage_word eightRows02_preimage_word eightRows03_preimage_word eightRows04_preimage_word eightRows05_preimage_word eightRows06_preimage_word eightRows07_preimage_word

theorem all_preimage_mul : ∀ i : Fin 64, ∀ (j : Fin 64) (x : Fin 16), (preimageElements i*preimageElements j) x=preimageElements (preimageMul i j) x :=
  kernel_assemble (fun i => ∀ (j : Fin 64) (x : Fin 16), (preimageElements i*preimageElements j) x=preimageElements (preimageMul i j) x)
    eightRows00_preimage_mul eightRows01_preimage_mul eightRows02_preimage_mul eightRows03_preimage_mul eightRows04_preimage_mul eightRows05_preimage_mul eightRows06_preimage_mul eightRows07_preimage_mul

theorem all_preimage_inverse : ∀ i : Fin 64, ∀ x : Fin 16, (preimageElements i)⁻¹ x=preimageElements (preimageInv i) x :=
  kernel_assemble (fun i => ∀ x : Fin 16, (preimageElements i)⁻¹ x=preimageElements (preimageInv i) x)
    eightRows00_preimage_inverse eightRows01_preimage_inverse eightRows02_preimage_inverse eightRows03_preimage_inverse eightRows04_preimage_inverse eightRows05_preimage_inverse eightRows06_preimage_inverse eightRows07_preimage_inverse

theorem all_preimage_conjugation : ∀ i : Fin 64, ∀ (j : Fin 3) (x : Fin 16), (sourceGenerators j*preimageElements i*(sourceGenerators j)⁻¹) x=preimageElements (preimageConj j i) x :=
  kernel_assemble (fun i => ∀ (j : Fin 3) (x : Fin 16), (sourceGenerators j*preimageElements i*(sourceGenerators j)⁻¹) x=preimageElements (preimageConj j i) x)
    eightRows00_preimage_conjugation eightRows01_preimage_conjugation eightRows02_preimage_conjugation eightRows03_preimage_conjugation eightRows04_preimage_conjugation eightRows05_preimage_conjugation eightRows06_preimage_conjugation eightRows07_preimage_conjugation

theorem all_preimage_conj_inverse : ∀ i : Fin 64, ∀ j : Fin 3, preimageConj j (preimageInvConj j i)=i ∧ preimageInvConj j (preimageConj j i)=i :=
  kernel_assemble (fun i => ∀ j : Fin 3, preimageConj j (preimageInvConj j i)=i ∧ preimageInvConj j (preimageConj j i)=i)
    eightRows00_preimage_conj_inverse eightRows01_preimage_conj_inverse eightRows02_preimage_conj_inverse eightRows03_preimage_conj_inverse eightRows04_preimage_conj_inverse eightRows05_preimage_conj_inverse eightRows06_preimage_conj_inverse eightRows07_preimage_conj_inverse

theorem all_preimage_code : ∀ i : Fin 64, pointCode (preimageElements i)=preimageCode i :=
  kernel_assemble (fun i => pointCode (preimageElements i)=preimageCode i)
    eightRows00_preimage_code eightRows01_preimage_code eightRows02_preimage_code eightRows03_preimage_code eightRows04_preimage_code eightRows05_preimage_code eightRows06_preimage_code eightRows07_preimage_code

theorem all_preimage_code_injective : ∀ i : Fin 64, ∀ j : Fin 64, preimageCode i=preimageCode j → i=j :=
  kernel_assemble (fun i => ∀ j : Fin 64, preimageCode i=preimageCode j → i=j)
    eightRows00_preimage_code_injective eightRows01_preimage_code_injective eightRows02_preimage_code_injective eightRows03_preimage_code_injective eightRows04_preimage_code_injective eightRows05_preimage_code_injective eightRows06_preimage_code_injective eightRows07_preimage_code_injective

theorem all_central_mod_N : ∀ i : Fin 64, ∀ (j : Fin 3) (x : Fin 16), (sourceGenerators j*preimageElements i*(sourceGenerators j)⁻¹*(preimageElements i)⁻¹) x=normalElements (centralResidue j i) x :=
  kernel_assemble (fun i => ∀ (j : Fin 3) (x : Fin 16), (sourceGenerators j*preimageElements i*(sourceGenerators j)⁻¹*(preimageElements i)⁻¹) x=normalElements (centralResidue j i) x)
    eightRows00_central_mod_N eightRows01_central_mod_N eightRows02_central_mod_N eightRows03_central_mod_N eightRows04_central_mod_N eightRows05_central_mod_N eightRows06_central_mod_N eightRows07_central_mod_N

theorem all_target_code : ∀ i : Fin 48, pointCode (targetState i)=targetCode i :=
  state_assemble (fun i => pointCode (targetState i)=targetCode i)
    eightRows00_target_code eightRows01_target_code eightRows02_target_code eightRows03_target_code eightRows04_target_code eightRows05_target_code

theorem all_target_code_injective : ∀ i : Fin 48, ∀ j : Fin 48, targetCode i=targetCode j → i=j :=
  state_assemble (fun i => ∀ j : Fin 48, targetCode i=targetCode j → i=j)
    eightRows00_target_code_injective eightRows01_target_code_injective eightRows02_target_code_injective eightRows03_target_code_injective eightRows04_target_code_injective eightRows05_target_code_injective

theorem all_signature : ∀ i : Fin 48, cosetSignature i=signatureCode i :=
  state_assemble (fun i => cosetSignature i=signatureCode i)
    eightRows00_signature eightRows01_signature eightRows02_signature eightRows03_signature eightRows04_signature eightRows05_signature

theorem all_signature_injective : ∀ i : Fin 48, ∀ j : Fin 48, signatureCode i=signatureCode j → i=j :=
  state_assemble (fun i => ∀ j : Fin 48, signatureCode i=signatureCode j → i=j)
    eightRows00_signature_injective eightRows01_signature_injective eightRows02_signature_injective eightRows03_signature_injective eightRows04_signature_injective eightRows05_signature_injective

theorem all_step_source : ∀ i : Fin 48, ∀ (j : Fin 3) (x : Fin 16), (sourceState (step i j)*preimageElements (stepResidue i j)) x=(sourceState i*sourceGenerators j) x :=
  state_assemble (fun i => ∀ (j : Fin 3) (x : Fin 16), (sourceState (step i j)*preimageElements (stepResidue i j)) x=(sourceState i*sourceGenerators j) x)
    eightRows00_step_source eightRows01_step_source eightRows02_step_source eightRows03_step_source eightRows04_step_source eightRows05_step_source

theorem all_step_target : ∀ i : Fin 48, ∀ (j : Fin 3) (x : Fin 8), targetState (step i j) x=(targetState i*targetGenerators j) x :=
  state_assemble (fun i => ∀ (j : Fin 3) (x : Fin 8), targetState (step i j) x=(targetState i*targetGenerators j) x)
    eightRows00_step_target eightRows01_step_target eightRows02_step_target eightRows03_step_target eightRows04_step_target eightRows05_step_target

theorem all_inverse_source : ∀ i : Fin 48, ∀ x : Fin 16, (sourceState (inverse i)*preimageElements (inverseResidue i)) x=(sourceState i)⁻¹ x :=
  state_assemble (fun i => ∀ x : Fin 16, (sourceState (inverse i)*preimageElements (inverseResidue i)) x=(sourceState i)⁻¹ x)
    eightRows00_inverse_source eightRows01_inverse_source eightRows02_inverse_source eightRows03_inverse_source eightRows04_inverse_source eightRows05_inverse_source

theorem all_inverse_target : ∀ i : Fin 48, ∀ x : Fin 8, targetState (inverse i) x=(targetState i)⁻¹ x :=
  state_assemble (fun i => ∀ x : Fin 8, targetState (inverse i) x=(targetState i)⁻¹ x)
    eightRows00_inverse_target eightRows01_inverse_target eightRows02_inverse_target eightRows03_inverse_target eightRows04_inverse_target eightRows05_inverse_target

abbrev all_normal_word := eightRows00_normal_word

abbrev all_normal_mul := eightRows00_normal_mul

abbrev all_normal_inverse := eightRows00_normal_inverse

abbrev all_normal_conjugation := eightRows00_normal_conjugation

abbrev all_normal_conj_inverse := eightRows00_normal_conj_inverse

abbrev all_normal_code := eightRows00_normal_code

abbrev all_normal_code_injective := eightRows00_normal_code_injective

abbrev all_normal_in_preimage := eightRows00_normal_in_preimage
end SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
