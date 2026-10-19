import SymmetricSubgroupAsymptotics.Row182QuotientWordGraphPacket00
import SymmetricSubgroupAsymptotics.Row182QuotientWordGraphPacket01
import SymmetricSubgroupAsymptotics.Row182QuotientWordGraphPacket02
import SymmetricSubgroupAsymptotics.Row182QuotientWordGraphPacket03
import SymmetricSubgroupAsymptotics.Row182QuotientWordGraphPacket04
import SymmetricSubgroupAsymptotics.Row182QuotientWordGraphPacket05
import SymmetricSubgroupAsymptotics.Row182QuotientWordGraphPacket06
import SymmetricSubgroupAsymptotics.Row182QuotientWordGraphPacket07
import SymmetricSubgroupAsymptotics.Row182QuotientWordGraphPacket08
import SymmetricSubgroupAsymptotics.Row182QuotientWordGraphPacket09
import SymmetricSubgroupAsymptotics.Row182QuotientWordGraphPacket10
import SymmetricSubgroupAsymptotics.Row182QuotientWordGraphPacket11
set_option autoImplicit false
set_option maxRecDepth 8192
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.Row182QuotientWordGraph
/- Assemble the finite packets with an abstract predicate. This keeps
case-splitting from unfolding the word-state arrays in each branch. -/
private theorem packet_assemble (P : Fin 360 → Prop)
    (h0 : ∀ r : Fin 30, P (finProdFinEquiv ((0 : Fin 12), r)))
    (h1 : ∀ r : Fin 30, P (finProdFinEquiv ((1 : Fin 12), r)))
    (h2 : ∀ r : Fin 30, P (finProdFinEquiv ((2 : Fin 12), r)))
    (h3 : ∀ r : Fin 30, P (finProdFinEquiv ((3 : Fin 12), r)))
    (h4 : ∀ r : Fin 30, P (finProdFinEquiv ((4 : Fin 12), r)))
    (h5 : ∀ r : Fin 30, P (finProdFinEquiv ((5 : Fin 12), r)))
    (h6 : ∀ r : Fin 30, P (finProdFinEquiv ((6 : Fin 12), r)))
    (h7 : ∀ r : Fin 30, P (finProdFinEquiv ((7 : Fin 12), r)))
    (h8 : ∀ r : Fin 30, P (finProdFinEquiv ((8 : Fin 12), r)))
    (h9 : ∀ r : Fin 30, P (finProdFinEquiv ((9 : Fin 12), r)))
    (h10 : ∀ r : Fin 30, P (finProdFinEquiv ((10 : Fin 12), r)))
    (h11 : ∀ r : Fin 30, P (finProdFinEquiv ((11 : Fin 12), r)))
    (i : Fin 360) : P i := by
  obtain ⟨⟨q,r⟩, rfl⟩ := (finProdFinEquiv : Fin 12 × Fin 30 ≃ Fin 360).surjective i
  fin_cases q
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

private theorem code_checked (i : Fin 360) :
    permutationCode (sourceState i) = sourceCode i :=
  packet_assemble (fun k => permutationCode (sourceState k) = sourceCode k)
    packet00_code packet01_code packet02_code packet03_code
    packet04_code packet05_code packet06_code packet07_code
    packet08_code packet09_code packet10_code packet11_code i
private theorem code_strict : StrictMono sourceCode := by
  apply Fin.strictMono_iff_lt_succ.mpr
  decide +kernel
private theorem step_source (i : Fin 360) (j : Fin 9) (x : Fin 6) :
    sourceState (step i j) x = (sourceState i * sourceGenerators j) x :=
  packet_assemble (fun k => ∀ (j : Fin 9) (x : Fin 6),
      sourceState (step k j) x = (sourceState k * sourceGenerators j) x)
    packet00_step_source packet01_step_source packet02_step_source packet03_step_source
    packet04_step_source packet05_step_source packet06_step_source packet07_step_source
    packet08_step_source packet09_step_source packet10_step_source packet11_step_source i j x
private theorem step_target (i : Fin 360) (j : Fin 9) (x : Fin 6) :
    targetState (step i j) x = (targetState i * targetGenerators j) x :=
  packet_assemble (fun k => ∀ (j : Fin 9) (x : Fin 6),
      targetState (step k j) x = (targetState k * targetGenerators j) x)
    packet00_step_target packet01_step_target packet02_step_target packet03_step_target
    packet04_step_target packet05_step_target packet06_step_target packet07_step_target
    packet08_step_target packet09_step_target packet10_step_target packet11_step_target i j x
private theorem inverse_source (i : Fin 360) (x : Fin 6) :
    sourceState (inverse i) x = (sourceState i)⁻¹ x :=
  packet_assemble (fun k => ∀ x : Fin 6,
      sourceState (inverse k) x = (sourceState k)⁻¹ x)
    packet00_inverse_source packet01_inverse_source packet02_inverse_source packet03_inverse_source
    packet04_inverse_source packet05_inverse_source packet06_inverse_source packet07_inverse_source
    packet08_inverse_source packet09_inverse_source packet10_inverse_source packet11_inverse_source i x
private theorem inverse_target (i : Fin 360) (x : Fin 6) :
    targetState (inverse i) x = (targetState i)⁻¹ x :=
  packet_assemble (fun k => ∀ x : Fin 6,
      targetState (inverse k) x = (targetState k)⁻¹ x)
    packet00_inverse_target packet01_inverse_target packet02_inverse_target packet03_inverse_target
    packet04_inverse_target packet05_inverse_target packet06_inverse_target packet07_inverse_target
    packet08_inverse_target packet09_inverse_target packet10_inverse_target packet11_inverse_target i x
private theorem identity_source : ∀ x : Fin 6, sourceState 359 x = x := by decide +kernel
private theorem identity_target : ∀ x : Fin 6, targetState 359 x = x := by decide +kernel
def certificate : FiniteGeneratorGraphCertificate (I := Fin 360) sourceGenerators targetGenerators where
  state := state
  word := word
  word_eq _ := rfl
  identity := 359
  identity_eq := Prod.ext (Equiv.ext identity_source) (Equiv.ext identity_target)
  step := step
  step_eq i j := Prod.ext (Equiv.ext (step_source i j)) (Equiv.ext (step_target i j))
  inverse := inverse
  inverse_eq i := Prod.ext (Equiv.ext (inverse_source i)) (Equiv.ext (inverse_target i))
  source_injective := by
    intro i j hij
    apply code_strict.injective
    rw [← code_checked i, ← code_checked j]
    exact congrArg permutationCode hij
end SymmetricSubgroupAsymptotics.Row182QuotientWordGraph
