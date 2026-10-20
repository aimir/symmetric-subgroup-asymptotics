import SymmetricSubgroupAsymptotics.GeneratedTopNormals.PilotStates056

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryTopRegistry056
local instance pilotEdge000Group : Group Source := BinaryTopSource056.group

def child0 (x : Source) : Fin 11 :=
  (if x.index.val < 8 then (if x.index.val < 4 then (if x.index.val < 2 then (if x.index.val < 1 then 0 else 0) else (if x.index.val < 3 then 0 else 0)) else (if x.index.val < 6 then (if x.index.val < 5 then 0 else 0) else (if x.index.val < 7 then 0 else 0))) else (if x.index.val < 12 then (if x.index.val < 10 then (if x.index.val < 9 then 0 else 1) else (if x.index.val < 11 then 2 else 0)) else (if x.index.val < 14 then (if x.index.val < 13 then 3 else 0) else (if x.index.val < 15 then 0 else 0))))

theorem edges0 : ∀ x : Source,
    N0.state.liftTests generators x →
    (∀ y, N0.mask y=true → (states (child0 x)).mask y=true) ∧
    (states (child0 x)).mask x=true ∧
    (states (child0 x)).size=N0.state.size*2 := by
  have checked : ∀ x : Fin 16,
      (N0.values x≠(1 : Equiv.Perm (Fin 8)) ∧
        N0.values x*N0.values x=1 ∧
        ∀ j : Fin 2, N0.values x*N0.values (generators j).index=
          N0.values (generators j).index*N0.values x) →
      (∀ y : Fin 16, N0.mask ⟨y⟩=true → (states (child0 ⟨x⟩)).mask ⟨y⟩=true) ∧
      (states (child0 ⟨x⟩)).mask ⟨x⟩=true ∧
      (states (child0 ⟨x⟩)).size=N0.state.size*2 := by
    simp only [states_size,N0.size_checked]
    decide +kernel
  intro x hx
  have ht := (N0.state.liftTests_iff_hom generators x).mp hx
  simp only [N0.state_hom_apply] at ht
  have hc := checked x.index ht
  exact ⟨fun y hy => hc.1 y.index hy,hc.2⟩

end SymmetricSubgroupAsymptotics.BinaryTopRegistry056
