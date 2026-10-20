import SymmetricSubgroupAsymptotics.GeneratedTopNormals.PilotStates056

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryTopRegistry056
local instance pilotEdge009Group : Group Source := BinaryTopSource056.group

def child9 (x : Source) : Fin 11 :=
  (if x.index.val < 8 then (if x.index.val < 4 then (if x.index.val < 2 then (if x.index.val < 1 then 10 else 0) else (if x.index.val < 3 then 0 else 10)) else (if x.index.val < 6 then (if x.index.val < 5 then 0 else 10) else (if x.index.val < 7 then 10 else 0))) else (if x.index.val < 12 then (if x.index.val < 10 then (if x.index.val < 9 then 10 else 0) else (if x.index.val < 11 then 0 else 10)) else (if x.index.val < 14 then (if x.index.val < 13 then 0 else 10) else (if x.index.val < 15 then 10 else 0))))

theorem edges9 : ∀ x : Source,
    N9.state.liftTests generators x →
    (∀ y, N9.mask y=true → (states (child9 x)).mask y=true) ∧
    (states (child9 x)).mask x=true ∧
    (states (child9 x)).size=N9.state.size*2 := by
  have checked : ∀ x : Fin 16,
      (N9.values x≠(1 : Equiv.Perm (Fin 2)) ∧
        N9.values x*N9.values x=1 ∧
        ∀ j : Fin 2, N9.values x*N9.values (generators j).index=
          N9.values (generators j).index*N9.values x) →
      (∀ y : Fin 16, N9.mask ⟨y⟩=true → (states (child9 ⟨x⟩)).mask ⟨y⟩=true) ∧
      (states (child9 ⟨x⟩)).mask ⟨x⟩=true ∧
      (states (child9 ⟨x⟩)).size=N9.state.size*2 := by
    simp only [states_size,N9.size_checked]
    decide +kernel
  intro x hx
  have ht := (N9.state.liftTests_iff_hom generators x).mp hx
  simp only [N9.state_hom_apply] at ht
  have hc := checked x.index ht
  exact ⟨fun y hy => hc.1 y.index hy,hc.2⟩

end SymmetricSubgroupAsymptotics.BinaryTopRegistry056
