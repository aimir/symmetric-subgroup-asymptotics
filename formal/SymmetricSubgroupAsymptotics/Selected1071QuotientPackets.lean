import SymmetricSubgroupAsymptotics.Selected1071QuotientGraphPacket00
import SymmetricSubgroupAsymptotics.Selected1071QuotientGraphPacket01
import SymmetricSubgroupAsymptotics.Selected1071QuotientGraphPacket02
import SymmetricSubgroupAsymptotics.Selected1071QuotientGraphPacket03
import SymmetricSubgroupAsymptotics.Selected1071QuotientGraphPacket04
import SymmetricSubgroupAsymptotics.Selected1071QuotientGraphPacket05
import SymmetricSubgroupAsymptotics.Selected1071QuotientGraphPacket06
import SymmetricSubgroupAsymptotics.Selected1071QuotientGraphPacket07
import SymmetricSubgroupAsymptotics.Selected1071QuotientGraphPacket08
import SymmetricSubgroupAsymptotics.Selected1071QuotientGraphPacket09
import SymmetricSubgroupAsymptotics.Selected1071QuotientGraphPacket10
import SymmetricSubgroupAsymptotics.Selected1071QuotientGraphPacket11

/-! Assembly of the bounded target graph receipts. No original group closure
or normal-subgroup census is used. -/
set_option autoImplicit false
set_option maxRecDepth 8192
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1071QuotientGraph

private theorem packet_assemble (P : Fin 192 → Prop)
    (h0 : ∀ r : Fin 16, P (finProdFinEquiv ((0 : Fin 12),r)))
    (h1 : ∀ r : Fin 16, P (finProdFinEquiv ((1 : Fin 12),r)))
    (h2 : ∀ r : Fin 16, P (finProdFinEquiv ((2 : Fin 12),r)))
    (h3 : ∀ r : Fin 16, P (finProdFinEquiv ((3 : Fin 12),r)))
    (h4 : ∀ r : Fin 16, P (finProdFinEquiv ((4 : Fin 12),r)))
    (h5 : ∀ r : Fin 16, P (finProdFinEquiv ((5 : Fin 12),r)))
    (h6 : ∀ r : Fin 16, P (finProdFinEquiv ((6 : Fin 12),r)))
    (h7 : ∀ r : Fin 16, P (finProdFinEquiv ((7 : Fin 12),r)))
    (h8 : ∀ r : Fin 16, P (finProdFinEquiv ((8 : Fin 12),r)))
    (h9 : ∀ r : Fin 16, P (finProdFinEquiv ((9 : Fin 12),r)))
    (h10 : ∀ r : Fin 16, P (finProdFinEquiv ((10 : Fin 12),r)))
    (h11 : ∀ r : Fin 16, P (finProdFinEquiv ((11 : Fin 12),r)))
    (i : Fin 192) : P i := by
  obtain ⟨⟨k,r⟩,rfl⟩ := (finProdFinEquiv : Fin 12 × Fin 16 ≃ Fin 192).surjective i
  fin_cases k
  · exact h0 r
  · exact h1 r
  · exact h2 r
  · exact h3 r
  · exact h4 r
  · exact h5 r
  · exact h6 r
  · exact h7 r
  · exact h8 r
  · exact h9 r
  · exact h10 r
  · exact h11 r

theorem all_source_code : ∀ i : Fin 192, pointCode (targetState i)=sourceCode i :=
  packet_assemble (fun i => pointCode (targetState i)=sourceCode i)
    packet00_source_code packet01_source_code packet02_source_code packet03_source_code packet04_source_code packet05_source_code packet06_source_code packet07_source_code packet08_source_code packet09_source_code packet10_source_code packet11_source_code

theorem all_source_code_injective : ∀ i : Fin 192, ∀ j : Fin 192, sourceCode i=sourceCode j → i=j :=
  packet_assemble (fun i => ∀ j : Fin 192, sourceCode i=sourceCode j → i=j)
    packet00_source_code_injective packet01_source_code_injective packet02_source_code_injective packet03_source_code_injective packet04_source_code_injective packet05_source_code_injective packet06_source_code_injective packet07_source_code_injective packet08_source_code_injective packet09_source_code_injective packet10_source_code_injective packet11_source_code_injective

theorem all_signature : ∀ i : Fin 192, cosetSignature i=signatureCode i :=
  packet_assemble (fun i => cosetSignature i=signatureCode i)
    packet00_signature packet01_signature packet02_signature packet03_signature packet04_signature packet05_signature packet06_signature packet07_signature packet08_signature packet09_signature packet10_signature packet11_signature

theorem all_signature_injective : ∀ i : Fin 192, ∀ j : Fin 192, signatureCode i=signatureCode j → i=j :=
  packet_assemble (fun i => ∀ j : Fin 192, signatureCode i=signatureCode j → i=j)
    packet00_signature_injective packet01_signature_injective packet02_signature_injective packet03_signature_injective packet04_signature_injective packet05_signature_injective packet06_signature_injective packet07_signature_injective packet08_signature_injective packet09_signature_injective packet10_signature_injective packet11_signature_injective

theorem all_step_source : ∀ i : Fin 192, ∀ (j : Fin 4) (x : Fin 16), (sourceState (step i j)*kernelElements (stepResidue i j)) x=(sourceState i*sourceGenerators j) x :=
  packet_assemble (fun i => ∀ (j : Fin 4) (x : Fin 16), (sourceState (step i j)*kernelElements (stepResidue i j)) x=(sourceState i*sourceGenerators j) x)
    packet00_step_source packet01_step_source packet02_step_source packet03_step_source packet04_step_source packet05_step_source packet06_step_source packet07_step_source packet08_step_source packet09_step_source packet10_step_source packet11_step_source

theorem all_step_target : ∀ i : Fin 192, ∀ (j : Fin 4) (x : Fin 12), targetState (step i j) x=(targetState i*targetGenerators j) x :=
  packet_assemble (fun i => ∀ (j : Fin 4) (x : Fin 12), targetState (step i j) x=(targetState i*targetGenerators j) x)
    packet00_step_target packet01_step_target packet02_step_target packet03_step_target packet04_step_target packet05_step_target packet06_step_target packet07_step_target packet08_step_target packet09_step_target packet10_step_target packet11_step_target

theorem all_inverse_source : ∀ i : Fin 192, ∀ x : Fin 16, (sourceState (inverse i)*kernelElements (inverseResidue i)) x=(sourceState i)⁻¹ x :=
  packet_assemble (fun i => ∀ x : Fin 16, (sourceState (inverse i)*kernelElements (inverseResidue i)) x=(sourceState i)⁻¹ x)
    packet00_inverse_source packet01_inverse_source packet02_inverse_source packet03_inverse_source packet04_inverse_source packet05_inverse_source packet06_inverse_source packet07_inverse_source packet08_inverse_source packet09_inverse_source packet10_inverse_source packet11_inverse_source

theorem all_inverse_target : ∀ i : Fin 192, ∀ x : Fin 12, targetState (inverse i) x=(targetState i)⁻¹ x :=
  packet_assemble (fun i => ∀ x : Fin 12, targetState (inverse i) x=(targetState i)⁻¹ x)
    packet00_inverse_target packet01_inverse_target packet02_inverse_target packet03_inverse_target packet04_inverse_target packet05_inverse_target packet06_inverse_target packet07_inverse_target packet08_inverse_target packet09_inverse_target packet10_inverse_target packet11_inverse_target

theorem targetState_injective : Function.Injective targetState := by
  intro i j h
  apply all_source_code_injective i j
  rw [← all_source_code i,← all_source_code j,h]

theorem cosetSignature_injective : Function.Injective cosetSignature := by
  intro i j h
  apply all_signature_injective i j
  rw [← all_signature i,← all_signature j,h]

end SymmetricSubgroupAsymptotics.Selected1071QuotientGraph
