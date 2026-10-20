import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.Pilot077
import SymmetricSubgroupAsymptotics.BinaryCoordinateCuts
import SymmetricSubgroupAsymptotics.BinaryCoordinateFixedFactor

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
noncomputable section


namespace SymmetricSubgroupAsymptotics.BinaryKernelCuts077
open BinaryKernelAxes077
local instance : Group Source := BinaryTopSource046.group

def cutIndex (i : Fin 19) : Fin 19 := (if i.val < 9 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 3) else (if i.val < 3 then 2 else 3)) else (if i.val < 6 then (if i.val < 5 then 4 else 10) else (if i.val < 7 then 9 else (if i.val < 8 then 8 else 8)))) else (if i.val < 14 then (if i.val < 11 then (if i.val < 10 then 9 else 10) else (if i.val < 12 then 11 else (if i.val < 13 then 12 else 13))) else (if i.val < 16 then (if i.val < 15 then 18 else 18) else (if i.val < 17 then 18 else (if i.val < 18 then 18 else 18)))))
def fixedIndex (i : Fin 19) : Fin 19 := (if i.val < 9 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 5) else (if i.val < 3 then 14 else 5)) else (if i.val < 6 then (if i.val < 5 then 5 else 17) else (if i.val < 7 then 16 else (if i.val < 8 then 15 else 15)))) else (if i.val < 14 then (if i.val < 11 then (if i.val < 10 then 16 else 17) else (if i.val < 12 then 16 else (if i.val < 13 then 15 else 17))) else (if i.val < 16 then (if i.val < 15 then 18 else 18) else (if i.val < 17 then 18 else (if i.val < 18 then 18 else 18)))))

private theorem axis_le_cut_basis : ∀ i j,
    (charts i).2.inclusion (Pi.single j 1)∈(charts (cutIndex i)).2.space := by decide +kernel
private theorem cut_le_kernel_basis : ∀ i j,
    (charts (cutIndex i)).2.inclusion (Pi.single j 1)∈kernelChart.space := by decide +kernel
private theorem central_basis : ∀ i j l,
    action (generators j) ((charts (cutIndex i)).2.inclusion (Pi.single l 1))-
      (charts (cutIndex i)).2.inclusion (Pi.single l 1)∈(charts i).2.space := by
  simp only [action_numeric]
  decide +kernel
private def factorEntries (i : Fin 19) (l : Fin 8) : List (Fin 3 × Fin 8) :=
  (if i.val*8+l.val < 76 then (if i.val*8+l.val < 38 then (if i.val*8+l.val < 19 then (if i.val*8+l.val < 9 then (if i.val*8+l.val < 4 then (if i.val*8+l.val < 2 then (if i.val*8+l.val < 1 then [(2,0)] else [(1,0),(2,0)]) else (if i.val*8+l.val < 3 then [(1,4),(2,2)] else [(1,0),(1,4),(2,2)])) else (if i.val*8+l.val < 6 then (if i.val*8+l.val < 5 then [(0,4),(1,4)] else [(1,4)]) else (if i.val*8+l.val < 7 then [(0,4)] else (if i.val*8+l.val < 8 then [] else [(2,0)])))) else (if i.val*8+l.val < 14 then (if i.val*8+l.val < 11 then (if i.val*8+l.val < 10 then [(1,0),(2,0)] else [(1,0)]) else (if i.val*8+l.val < 12 then [] else (if i.val*8+l.val < 13 then [(0,0)] else []))) else (if i.val*8+l.val < 16 then (if i.val*8+l.val < 15 then [(0,0)] else []) else (if i.val*8+l.val < 17 then [(2,0)] else (if i.val*8+l.val < 18 then [(2,1)] else [(2,0),(2,1)]))))) else (if i.val*8+l.val < 28 then (if i.val*8+l.val < 23 then (if i.val*8+l.val < 21 then (if i.val*8+l.val < 20 then [] else []) else (if i.val*8+l.val < 22 then [] else [])) else (if i.val*8+l.val < 25 then (if i.val*8+l.val < 24 then [] else [(2,0)]) else (if i.val*8+l.val < 26 then [(1,0),(2,0)] else (if i.val*8+l.val < 27 then [(1,0)] else [])))) else (if i.val*8+l.val < 33 then (if i.val*8+l.val < 30 then (if i.val*8+l.val < 29 then [(0,0)] else []) else (if i.val*8+l.val < 31 then [(0,0)] else (if i.val*8+l.val < 32 then [] else [(0,0),(1,0),(2,1)]))) else (if i.val*8+l.val < 35 then (if i.val*8+l.val < 34 then [(0,0),(2,1)] else [(1,0)]) else (if i.val*8+l.val < 36 then [] else (if i.val*8+l.val < 37 then [(0,0)] else [])))))) else (if i.val*8+l.val < 57 then (if i.val*8+l.val < 47 then (if i.val*8+l.val < 42 then (if i.val*8+l.val < 40 then (if i.val*8+l.val < 39 then [(0,0)] else []) else (if i.val*8+l.val < 41 then [(2,0)] else [(2,0)])) else (if i.val*8+l.val < 44 then (if i.val*8+l.val < 43 then [] else []) else (if i.val*8+l.val < 45 then [] else (if i.val*8+l.val < 46 then [] else [])))) else (if i.val*8+l.val < 52 then (if i.val*8+l.val < 49 then (if i.val*8+l.val < 48 then [] else [(2,0)]) else (if i.val*8+l.val < 50 then [(2,0)] else (if i.val*8+l.val < 51 then [] else []))) else (if i.val*8+l.val < 54 then (if i.val*8+l.val < 53 then [] else []) else (if i.val*8+l.val < 55 then [] else (if i.val*8+l.val < 56 then [] else [(2,0)]))))) else (if i.val*8+l.val < 66 then (if i.val*8+l.val < 61 then (if i.val*8+l.val < 59 then (if i.val*8+l.val < 58 then [] else [(2,0)]) else (if i.val*8+l.val < 60 then [] else [])) else (if i.val*8+l.val < 63 then (if i.val*8+l.val < 62 then [] else []) else (if i.val*8+l.val < 64 then [] else (if i.val*8+l.val < 65 then [(2,0)] else [])))) else (if i.val*8+l.val < 71 then (if i.val*8+l.val < 68 then (if i.val*8+l.val < 67 then [(2,0)] else []) else (if i.val*8+l.val < 69 then [] else (if i.val*8+l.val < 70 then [] else []))) else (if i.val*8+l.val < 73 then (if i.val*8+l.val < 72 then [] else [(2,0)]) else (if i.val*8+l.val < 74 then [(2,0)] else (if i.val*8+l.val < 75 then [] else []))))))) else (if i.val*8+l.val < 114 then (if i.val*8+l.val < 95 then (if i.val*8+l.val < 85 then (if i.val*8+l.val < 80 then (if i.val*8+l.val < 78 then (if i.val*8+l.val < 77 then [] else []) else (if i.val*8+l.val < 79 then [] else [])) else (if i.val*8+l.val < 82 then (if i.val*8+l.val < 81 then [(2,0)] else [(2,0)]) else (if i.val*8+l.val < 83 then [] else (if i.val*8+l.val < 84 then [] else [])))) else (if i.val*8+l.val < 90 then (if i.val*8+l.val < 87 then (if i.val*8+l.val < 86 then [] else []) else (if i.val*8+l.val < 88 then [] else (if i.val*8+l.val < 89 then [(2,0)] else [(2,0)]))) else (if i.val*8+l.val < 92 then (if i.val*8+l.val < 91 then [] else []) else (if i.val*8+l.val < 93 then [] else (if i.val*8+l.val < 94 then [] else []))))) else (if i.val*8+l.val < 104 then (if i.val*8+l.val < 99 then (if i.val*8+l.val < 97 then (if i.val*8+l.val < 96 then [] else [(2,0)]) else (if i.val*8+l.val < 98 then [] else [(2,0)])) else (if i.val*8+l.val < 101 then (if i.val*8+l.val < 100 then [] else []) else (if i.val*8+l.val < 102 then [] else (if i.val*8+l.val < 103 then [] else [])))) else (if i.val*8+l.val < 109 then (if i.val*8+l.val < 106 then (if i.val*8+l.val < 105 then [(2,1)] else [(2,1)]) else (if i.val*8+l.val < 107 then [] else (if i.val*8+l.val < 108 then [] else []))) else (if i.val*8+l.val < 111 then (if i.val*8+l.val < 110 then [] else []) else (if i.val*8+l.val < 112 then [] else (if i.val*8+l.val < 113 then [] else [])))))) else (if i.val*8+l.val < 133 then (if i.val*8+l.val < 123 then (if i.val*8+l.val < 118 then (if i.val*8+l.val < 116 then (if i.val*8+l.val < 115 then [] else []) else (if i.val*8+l.val < 117 then [] else [])) else (if i.val*8+l.val < 120 then (if i.val*8+l.val < 119 then [] else []) else (if i.val*8+l.val < 121 then [] else (if i.val*8+l.val < 122 then [] else [])))) else (if i.val*8+l.val < 128 then (if i.val*8+l.val < 125 then (if i.val*8+l.val < 124 then [] else []) else (if i.val*8+l.val < 126 then [] else (if i.val*8+l.val < 127 then [] else []))) else (if i.val*8+l.val < 130 then (if i.val*8+l.val < 129 then [] else []) else (if i.val*8+l.val < 131 then [] else (if i.val*8+l.val < 132 then [] else []))))) else (if i.val*8+l.val < 142 then (if i.val*8+l.val < 137 then (if i.val*8+l.val < 135 then (if i.val*8+l.val < 134 then [] else []) else (if i.val*8+l.val < 136 then [] else [])) else (if i.val*8+l.val < 139 then (if i.val*8+l.val < 138 then [] else []) else (if i.val*8+l.val < 140 then [] else (if i.val*8+l.val < 141 then [] else [])))) else (if i.val*8+l.val < 147 then (if i.val*8+l.val < 144 then (if i.val*8+l.val < 143 then [] else []) else (if i.val*8+l.val < 145 then [] else (if i.val*8+l.val < 146 then [] else []))) else (if i.val*8+l.val < 149 then (if i.val*8+l.val < 148 then [] else []) else (if i.val*8+l.val < 150 then [] else (if i.val*8+l.val < 151 then [] else []))))))))
private def factor (i : Fin 19) :
    (Fin 3 → Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2) :=
  LinearMap.pi (fun l => ((factorEntries i l).map
    (fun p => (LinearMap.proj p.2 : (Fin 8 → ZMod 2) →ₗ[ZMod 2] ZMod 2).comp
      (LinearMap.proj p.1 : (Fin 3 → Fin 8 → ZMod 2) →ₗ[ZMod 2]
        (Fin 8 → ZMod 2)))).sum)
private theorem fixed_le_kernel_basis : ∀ i j,
    (charts (fixedIndex i)).2.inclusion (Pi.single j 1)∈kernelChart.space := by decide +kernel
private theorem fixed_basis : ∀ i j l,
    action (generators l) ((charts (fixedIndex i)).2.inclusion (Pi.single j 1))-
      (charts (fixedIndex i)).2.inclusion (Pi.single j 1)∈
        (charts (cutIndex i)).2.space := by
  simp only [action_numeric]
  decide +kernel
private theorem factor_basis : ∀ i j,
    (charts (fixedIndex i)).2.defect (kernelChart.inclusion (Pi.single j 1))=
      factor i (binaryCoordinate_generatorDefects action generators (charts (cutIndex i)).2
        (kernelChart.inclusion (Pi.single j 1))) := by
  simp only [binaryCoordinate_generatorDefects_apply,action_numeric]
  decide +kernel
private theorem full_fixed_predicate (i : Fin 19) : ∀ v : Fin 8 → ZMod 2,
    v∈(charts (fixedIndex i)).2.space ↔ v∈kernelChart.space ∧
      ∀ j, action (generators j) v-v∈(charts (cutIndex i)).2.space :=
  binaryCoordinate_fixed_of_factor kernelChart (charts (cutIndex i)).2
    (charts (fixedIndex i)).2 action generators (factor i)
    (fixed_le_kernel_basis i) (fixed_basis i) (factor_basis i)

/-- The complete fixed preimage and central cut are certified actual spaces. -/
theorem certificate (i : Fin 19) : BinaryCoordinateCutData action kernel
    (states i) (states (cutIndex i)) (states (fixedIndex i)) :=
  binaryCoordinate_cut_of_checks kernelChart (charts i).2 (charts (cutIndex i)).2
    (charts (fixedIndex i)).2 action kernel (states i) (states (cutIndex i))
    (states (fixedIndex i)) rfl (states_space i) (states_space (cutIndex i))
    (states_space (fixedIndex i)) generators generators_full (axis_le_cut_basis i)
    (cut_le_kernel_basis i) (central_basis i) (full_fixed_predicate i)

def cost (i : Fin 19) : ℕ :=
  2*((charts (cutIndex i)).1-(charts i).1)+
    4*((charts (fixedIndex i)).1-(charts (cutIndex i)).1)

theorem cost_eq_actual_finranks (i : Fin 19) : cost i=
    2*(Module.finrank (ZMod 2) (states (cutIndex i)).toSubmodule-
      Module.finrank (ZMod 2) (states i).toSubmodule)+
    4*(Module.finrank (ZMod 2) (states (fixedIndex i)).toSubmodule-
      Module.finrank (ZMod 2) (states (cutIndex i)).toSubmodule) := by
  rw [states_space (cutIndex i),states_space i,states_space (fixedIndex i),
    (charts (cutIndex i)).2.finrank,(charts i).2.finrank,(charts (fixedIndex i)).2.finrank]
  rfl
end SymmetricSubgroupAsymptotics.BinaryKernelCuts077

