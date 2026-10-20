import SymmetricSubgroupAsymptotics.GeneratedTopNormals.PilotStates046

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryTopRegistry046
local instance pilotEdge003Group : Group Source := BinaryTopSource046.group

def child3 (x : Source) : Fin 19 :=
  (if x.index.val < 8 then (if x.index.val < 4 then (if x.index.val < 2 then (if x.index.val < 1 then 10 else 9) else (if x.index.val < 3 then 8 else 7)) else (if x.index.val < 6 then (if x.index.val < 5 then 7 else 8) else (if x.index.val < 7 then 9 else 10))) else (if x.index.val < 12 then (if x.index.val < 10 then (if x.index.val < 9 then 5 else 6) else (if x.index.val < 11 then 6 else 5)) else (if x.index.val < 14 then (if x.index.val < 13 then 0 else 4) else (if x.index.val < 15 then 4 else 0))))

theorem edges3 : ∀ x : Source,
    N3.state.liftTests generators x →
    (∀ y, N3.mask y=true → (states (child3 x)).mask y=true) ∧
    (states (child3 x)).mask x=true ∧
    (states (child3 x)).size=N3.state.size*2 := by
  have checked : ∀ x : Fin 16,
      (N3.values x≠(1 : Equiv.Perm (Fin 6)) ∧
        N3.values x*N3.values x=1 ∧
        ∀ j : Fin 3, N3.values x*N3.values (generators j).index=
          N3.values (generators j).index*N3.values x) →
      (∀ y : Fin 16, N3.mask ⟨y⟩=true → (states (child3 ⟨x⟩)).mask ⟨y⟩=true) ∧
      (states (child3 ⟨x⟩)).mask ⟨x⟩=true ∧
      (states (child3 ⟨x⟩)).size=N3.state.size*2 := by
    simp only [states_size,N3.size_checked]
    decide +kernel
  intro x hx
  have ht := (N3.state.liftTests_iff_hom generators x).mp hx
  simp only [N3.state_hom_apply] at ht
  have hc := checked x.index ht
  exact ⟨fun y hy => hc.1 y.index hy,hc.2⟩

end SymmetricSubgroupAsymptotics.BinaryTopRegistry046
