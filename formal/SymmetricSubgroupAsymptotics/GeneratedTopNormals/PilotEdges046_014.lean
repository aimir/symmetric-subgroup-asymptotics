import SymmetricSubgroupAsymptotics.GeneratedTopNormals.PilotStates046

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryTopRegistry046
local instance pilotEdge014Group : Group Source := BinaryTopSource046.group

def child14 (x : Source) : Fin 19 :=
  (if x.index.val < 8 then (if x.index.val < 4 then (if x.index.val < 2 then (if x.index.val < 1 then 18 else 0) else (if x.index.val < 3 then 18 else 0)) else (if x.index.val < 6 then (if x.index.val < 5 then 0 else 18) else (if x.index.val < 7 then 0 else 18))) else (if x.index.val < 12 then (if x.index.val < 10 then (if x.index.val < 9 then 0 else 18) else (if x.index.val < 11 then 18 else 0)) else (if x.index.val < 14 then (if x.index.val < 13 then 0 else 18) else (if x.index.val < 15 then 18 else 0))))

theorem edges14 : ∀ x : Source,
    N14.state.liftTests generators x →
    (∀ y, N14.mask y=true → (states (child14 x)).mask y=true) ∧
    (states (child14 x)).mask x=true ∧
    (states (child14 x)).size=N14.state.size*2 := by
  have checked : ∀ x : Fin 16,
      (N14.values x≠(1 : Equiv.Perm (Fin 2)) ∧
        N14.values x*N14.values x=1 ∧
        ∀ j : Fin 3, N14.values x*N14.values (generators j).index=
          N14.values (generators j).index*N14.values x) →
      (∀ y : Fin 16, N14.mask ⟨y⟩=true → (states (child14 ⟨x⟩)).mask ⟨y⟩=true) ∧
      (states (child14 ⟨x⟩)).mask ⟨x⟩=true ∧
      (states (child14 ⟨x⟩)).size=N14.state.size*2 := by
    simp only [states_size,N14.size_checked]
    decide +kernel
  intro x hx
  have ht := (N14.state.liftTests_iff_hom generators x).mp hx
  simp only [N14.state_hom_apply] at ht
  have hc := checked x.index ht
  exact ⟨fun y hy => hc.1 y.index hy,hc.2⟩

end SymmetricSubgroupAsymptotics.BinaryTopRegistry046
