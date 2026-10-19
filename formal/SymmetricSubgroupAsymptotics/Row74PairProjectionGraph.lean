import SymmetricSubgroupAsymptotics.Row74PairProjectionGraphPacket00
import SymmetricSubgroupAsymptotics.Row74PairProjectionGraphPacket01
import SymmetricSubgroupAsymptotics.Row74PairProjectionGraphPacket02
import SymmetricSubgroupAsymptotics.Row74PairProjectionGraphPacket03
import Mathlib.Order.Fin.Basic
set_option autoImplicit false
set_option maxRecDepth 8192
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row74PairProjectionGraph
set_option maxHeartbeats 2000000
private theorem assemble (P : Check → Prop)
    (h00 : ∀ r : Fin 30,P (finProdFinEquiv ((0 : Fin 4),r)))
    (h01 : ∀ r : Fin 30,P (finProdFinEquiv ((1 : Fin 4),r)))
    (h02 : ∀ r : Fin 30,P (finProdFinEquiv ((2 : Fin 4),r)))
    (h03 : ∀ r : Fin 30,P (finProdFinEquiv ((3 : Fin 4),r)))
    (i : Check) : P i := by
  obtain ⟨⟨k,r⟩,rfl⟩ := (finProdFinEquiv : Fin 4 × Fin 30 ≃ Check).surjective i
  fin_cases k
  · exact h00 r
  · exact h01 r
  · exact h02 r
  · exact h03 r
private theorem code_checked (i : Check) : permutationCode (sourceState i)=rawCode i :=
  assemble (fun t => permutationCode (sourceState t)=rawCode t) packet00_code packet01_code packet02_code packet03_code i
private theorem code_strict : StrictMono sourceCode := by
  apply Fin.strictMono_iff_lt_succ.mpr
  decide +kernel
private theorem step_source (i : Check) (j : Fin 4) (x : Fin 6) : sourceState (embed (step i j)) x=(sourceState i*sourceGenerators j) x :=
  assemble (fun t => sourceState (embed (step t j)) x=(sourceState t*sourceGenerators j) x) (fun r => packet00_step_source r j x) (fun r => packet01_step_source r j x) (fun r => packet02_step_source r j x) (fun r => packet03_step_source r j x) i
private theorem inverse_source (i : Check) (x : Fin 6) : sourceState (embed (inverse i)) x=(sourceState i)⁻¹ x :=
  assemble (fun t => sourceState (embed (inverse t)) x=(sourceState t)⁻¹ x) (fun r => packet00_inverse_source r x) (fun r => packet01_inverse_source r x) (fun r => packet02_inverse_source r x) (fun r => packet03_inverse_source r x) i
private theorem identity_source : ∀ x : Fin 6,sourceState (embed 119) x=x := by decide +kernel
private theorem step_target (i : Check) (j : Fin 4) (x : Fin 12) : targetState (embed (step i j)) x=(targetState i*targetGenerators j) x :=
  assemble (fun t => targetState (embed (step t j)) x=(targetState t*targetGenerators j) x) (fun r => packet00_step_target r j x) (fun r => packet01_step_target r j x) (fun r => packet02_step_target r j x) (fun r => packet03_step_target r j x) i
private theorem inverse_target (i : Check) (x : Fin 12) : targetState (embed (inverse i)) x=(targetState i)⁻¹ x :=
  assemble (fun t => targetState (embed (inverse t)) x=(targetState t)⁻¹ x) (fun r => packet00_inverse_target r x) (fun r => packet01_inverse_target r x) (fun r => packet02_inverse_target r x) (fun r => packet03_inverse_target r x) i
private theorem identity_target : ∀ x : Fin 12,targetState (embed 119) x=x := by decide +kernel
def certificate : FiniteGeneratorGraphCertificate (I := Count) sourceGenerators targetGenerators where
  state i := state (embed i)
  word i := word (embed i)
  word_eq _ := rfl
  identity := 119
  identity_eq := Prod.ext (Equiv.ext identity_source) (Equiv.ext identity_target)
  step i j := step (embed i) j
  step_eq i j := Prod.ext (Equiv.ext (step_source (embed i) j)) (Equiv.ext (step_target (embed i) j))
  inverse i := inverse (embed i)
  inverse_eq i := Prod.ext (Equiv.ext (inverse_source (embed i))) (Equiv.ext (inverse_target (embed i)))
  source_injective := by
    intro i j h
    apply code_strict.injective
    change rawCode (embed i)=rawCode (embed j)
    rw [← code_checked,← code_checked]
    exact congrArg permutationCode h
end SymmetricSubgroupAsymptotics.Row74PairProjectionGraph
