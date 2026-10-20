import SymmetricSubgroupAsymptotics.GeneratedTopNormals.PilotStates056

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryTopRegistry056
local instance pilotEdge001Group : Group Source := BinaryTopSource056.group

def child1 (x : Source) : Fin 11 :=
  (if x.index.val < 8 then (if x.index.val < 4 then (if x.index.val < 2 then (if x.index.val < 1 then 0 else 0) else (if x.index.val < 3 then 0 else 0)) else (if x.index.val < 6 then (if x.index.val < 5 then 0 else 0) else (if x.index.val < 7 then 0 else 0))) else (if x.index.val < 12 then (if x.index.val < 10 then (if x.index.val < 9 then 0 else 0) else (if x.index.val < 11 then 6 else 0)) else (if x.index.val < 14 then (if x.index.val < 13 then 6 else 0) else (if x.index.val < 15 then 0 else 0))))

theorem edges1 : ∀ x : Source,
    N1.state.liftTests generators x →
    (∀ y, N1.mask y=true → (states (child1 x)).mask y=true) ∧
    (states (child1 x)).mask x=true ∧
    (states (child1 x)).size=N1.state.size*2 := by
  have checked : ∀ x : Fin 16,
      (N1.values x≠(1 : Equiv.Perm (Fin 4)) ∧
        N1.values x*N1.values x=1 ∧
        ∀ j : Fin 2, N1.values x*N1.values (generators j).index=
          N1.values (generators j).index*N1.values x) →
      (∀ y : Fin 16, N1.mask ⟨y⟩=true → (states (child1 ⟨x⟩)).mask ⟨y⟩=true) ∧
      (states (child1 ⟨x⟩)).mask ⟨x⟩=true ∧
      (states (child1 ⟨x⟩)).size=N1.state.size*2 := by
    simp only [states_size,N1.size_checked]
    decide +kernel
  intro x hx
  have ht := (N1.state.liftTests_iff_hom generators x).mp hx
  simp only [N1.state_hom_apply] at ht
  have hc := checked x.index ht
  exact ⟨fun y hy => hc.1 y.index hy,hc.2⟩

end SymmetricSubgroupAsymptotics.BinaryTopRegistry056
