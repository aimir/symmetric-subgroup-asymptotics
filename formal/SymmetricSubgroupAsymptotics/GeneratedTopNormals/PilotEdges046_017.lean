import SymmetricSubgroupAsymptotics.GeneratedTopNormals.PilotStates046

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryTopRegistry046
local instance pilotEdge017Group : Group Source := BinaryTopSource046.group

def child17 (x : Source) : Fin 19 :=
  (if x.index.val < 8 then (if x.index.val < 4 then (if x.index.val < 2 then (if x.index.val < 1 then 18 else 0) else (if x.index.val < 3 then 0 else 18)) else (if x.index.val < 6 then (if x.index.val < 5 then 18 else 0) else (if x.index.val < 7 then 0 else 18))) else (if x.index.val < 12 then (if x.index.val < 10 then (if x.index.val < 9 then 18 else 0) else (if x.index.val < 11 then 0 else 18)) else (if x.index.val < 14 then (if x.index.val < 13 then 0 else 18) else (if x.index.val < 15 then 18 else 0))))

theorem edges17 : ∀ x : Source,
    N17.state.liftTests generators x →
    (∀ y, N17.mask y=true → (states (child17 x)).mask y=true) ∧
    (states (child17 x)).mask x=true ∧
    (states (child17 x)).size=N17.state.size*2 := by
  have checked : ∀ x : Fin 16,
      (N17.values x≠(1 : Equiv.Perm (Fin 2)) ∧
        N17.values x*N17.values x=1 ∧
        ∀ j : Fin 3, N17.values x*N17.values (generators j).index=
          N17.values (generators j).index*N17.values x) →
      (∀ y : Fin 16, N17.mask ⟨y⟩=true → (states (child17 ⟨x⟩)).mask ⟨y⟩=true) ∧
      (states (child17 ⟨x⟩)).mask ⟨x⟩=true ∧
      (states (child17 ⟨x⟩)).size=N17.state.size*2 := by
    simp only [states_size,N17.size_checked]
    decide +kernel
  intro x hx
  have ht := (N17.state.liftTests_iff_hom generators x).mp hx
  simp only [N17.state_hom_apply] at ht
  have hc := checked x.index ht
  exact ⟨fun y hy => hc.1 y.index hy,hc.2⟩

end SymmetricSubgroupAsymptotics.BinaryTopRegistry046
