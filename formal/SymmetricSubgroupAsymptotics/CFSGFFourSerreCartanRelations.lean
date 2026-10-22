import SymmetricSubgroupAsymptotics.CFSGFFourSerreMatrices
import Mathlib.Tactic.Module
import Mathlib.Tactic.Abel

/-! Four literal folded E6 relations in the pinned F4 node order.
Closed scalar entries are evaluated separately from matrix Lie algebra. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourSerreMatrices
local instance fFourCartanRelationsDecEq : DecidableEq
    (CFSGNormTwoRootPairing.Roots CartanMatrix.E₆) := Classical.decEq _

theorem HH (i j : Fin 4) : ⁅cartan i,cartan j⁆=0 := by
  fin_cases i <;> fin_cases j
  · change ⁅(e6H 0+e6H 5),(e6H 0+e6H 5)⁆=0
    simp [add_lie,lie_add,e6HH]
  · change ⁅(e6H 0+e6H 5),(e6H 2+e6H 4)⁆=0
    simp [add_lie,lie_add,e6HH]
  · change ⁅(e6H 0+e6H 5),(e6H 3)⁆=0
    simp [add_lie,lie_add,e6HH]
  · change ⁅(e6H 0+e6H 5),(e6H 1)⁆=0
    simp [add_lie,lie_add,e6HH]
  · change ⁅(e6H 2+e6H 4),(e6H 0+e6H 5)⁆=0
    simp [add_lie,lie_add,e6HH]
  · change ⁅(e6H 2+e6H 4),(e6H 2+e6H 4)⁆=0
    simp [add_lie,lie_add,e6HH]
  · change ⁅(e6H 2+e6H 4),(e6H 3)⁆=0
    simp [add_lie,lie_add,e6HH]
  · change ⁅(e6H 2+e6H 4),(e6H 1)⁆=0
    simp [add_lie,lie_add,e6HH]
  · change ⁅(e6H 3),(e6H 0+e6H 5)⁆=0
    simp [add_lie,lie_add,e6HH]
  · change ⁅(e6H 3),(e6H 2+e6H 4)⁆=0
    simp [add_lie,lie_add,e6HH]
  · change ⁅(e6H 3),(e6H 3)⁆=0
    simp [add_lie,lie_add,e6HH]
  · change ⁅(e6H 3),(e6H 1)⁆=0
    simp [add_lie,lie_add,e6HH]
  · change ⁅(e6H 1),(e6H 0+e6H 5)⁆=0
    simp [add_lie,lie_add,e6HH]
  · change ⁅(e6H 1),(e6H 2+e6H 4)⁆=0
    simp [add_lie,lie_add,e6HH]
  · change ⁅(e6H 1),(e6H 3)⁆=0
    simp [add_lie,lie_add,e6HH]
  · change ⁅(e6H 1),(e6H 1)⁆=0
    simp [add_lie,lie_add,e6HH]

theorem EF (i j : Fin 4) : ⁅positive i,negative j⁆=if i=j then cartan i else 0 := by
  fin_cases i <;> fin_cases j
  · change ⁅(e6E 0+e6E 5),(e6F 0+e6F 5)⁆=(e6H 0+e6H 5)
    simp [add_lie,lie_add,e6EF]
  · change ⁅(e6E 0+e6E 5),(e6F 2+e6F 4)⁆=0
    simp [add_lie,lie_add,e6EF]
  · change ⁅(e6E 0+e6E 5),(e6F 3)⁆=0
    simp [add_lie,lie_add,e6EF]
  · change ⁅(e6E 0+e6E 5),(e6F 1)⁆=0
    simp [add_lie,lie_add,e6EF]
  · change ⁅(e6E 2+e6E 4),(e6F 0+e6F 5)⁆=0
    simp [add_lie,lie_add,e6EF]
  · change ⁅(e6E 2+e6E 4),(e6F 2+e6F 4)⁆=(e6H 2+e6H 4)
    simp [add_lie,lie_add,e6EF]
  · change ⁅(e6E 2+e6E 4),(e6F 3)⁆=0
    simp [add_lie,lie_add,e6EF]
  · change ⁅(e6E 2+e6E 4),(e6F 1)⁆=0
    simp [add_lie,lie_add,e6EF]
  · change ⁅(e6E 3),(e6F 0+e6F 5)⁆=0
    simp [add_lie,lie_add,e6EF]
  · change ⁅(e6E 3),(e6F 2+e6F 4)⁆=0
    simp [add_lie,lie_add,e6EF]
  · change ⁅(e6E 3),(e6F 3)⁆=(e6H 3)
    simp [add_lie,lie_add,e6EF]
  · change ⁅(e6E 3),(e6F 1)⁆=0
    simp [add_lie,lie_add,e6EF]
  · change ⁅(e6E 1),(e6F 0+e6F 5)⁆=0
    simp [add_lie,lie_add,e6EF]
  · change ⁅(e6E 1),(e6F 2+e6F 4)⁆=0
    simp [add_lie,lie_add,e6EF]
  · change ⁅(e6E 1),(e6F 3)⁆=0
    simp [add_lie,lie_add,e6EF]
  · change ⁅(e6E 1),(e6F 1)⁆=(e6H 1)
    simp [add_lie,lie_add,e6EF]

theorem HE (i j : Fin 4) : ⁅cartan i,positive j⁆=CartanMatrix.F₄ i j • positive j := by
  fin_cases i <;> fin_cases j
  · change ⁅(e6H 0+e6H 5),(e6E 0+e6E 5)⁆=(2:ℤ) • (e6E 0+e6E 5)
    simp only [add_lie,lie_add,e6HE]
    simp only [show CartanMatrix.E₆ (0:Fin 6) (0:Fin 6)=(2:ℤ) by decide,
      show CartanMatrix.E₆ (0:Fin 6) (5:Fin 6)=(0:ℤ) by decide,
      show CartanMatrix.E₆ (5:Fin 6) (0:Fin 6)=(0:ℤ) by decide,
      show CartanMatrix.E₆ (5:Fin 6) (5:Fin 6)=(2:ℤ) by decide]
    module
  · change ⁅(e6H 0+e6H 5),(e6E 2+e6E 4)⁆=(-1:ℤ) • (e6E 2+e6E 4)
    simp only [add_lie,lie_add,e6HE]
    simp only [show CartanMatrix.E₆ (0:Fin 6) (2:Fin 6)=(-1:ℤ) by decide,
      show CartanMatrix.E₆ (0:Fin 6) (4:Fin 6)=(0:ℤ) by decide,
      show CartanMatrix.E₆ (5:Fin 6) (2:Fin 6)=(0:ℤ) by decide,
      show CartanMatrix.E₆ (5:Fin 6) (4:Fin 6)=(-1:ℤ) by decide]
    module
  · change ⁅(e6H 0+e6H 5),(e6E 3)⁆=(0:ℤ) • (e6E 3)
    simp only [add_lie,lie_add,e6HE]
    simp only [show CartanMatrix.E₆ (0:Fin 6) (3:Fin 6)=(0:ℤ) by decide,
      show CartanMatrix.E₆ (5:Fin 6) (3:Fin 6)=(0:ℤ) by decide]
    module
  · change ⁅(e6H 0+e6H 5),(e6E 1)⁆=(0:ℤ) • (e6E 1)
    simp only [add_lie,lie_add,e6HE]
    simp only [show CartanMatrix.E₆ (0:Fin 6) (1:Fin 6)=(0:ℤ) by decide,
      show CartanMatrix.E₆ (5:Fin 6) (1:Fin 6)=(0:ℤ) by decide]
    module
  · change ⁅(e6H 2+e6H 4),(e6E 0+e6E 5)⁆=(-1:ℤ) • (e6E 0+e6E 5)
    simp only [add_lie,lie_add,e6HE]
    simp only [show CartanMatrix.E₆ (2:Fin 6) (0:Fin 6)=(-1:ℤ) by decide,
      show CartanMatrix.E₆ (2:Fin 6) (5:Fin 6)=(0:ℤ) by decide,
      show CartanMatrix.E₆ (4:Fin 6) (0:Fin 6)=(0:ℤ) by decide,
      show CartanMatrix.E₆ (4:Fin 6) (5:Fin 6)=(-1:ℤ) by decide]
    module
  · change ⁅(e6H 2+e6H 4),(e6E 2+e6E 4)⁆=(2:ℤ) • (e6E 2+e6E 4)
    simp only [add_lie,lie_add,e6HE]
    simp only [show CartanMatrix.E₆ (2:Fin 6) (2:Fin 6)=(2:ℤ) by decide,
      show CartanMatrix.E₆ (2:Fin 6) (4:Fin 6)=(0:ℤ) by decide,
      show CartanMatrix.E₆ (4:Fin 6) (2:Fin 6)=(0:ℤ) by decide,
      show CartanMatrix.E₆ (4:Fin 6) (4:Fin 6)=(2:ℤ) by decide]
    module
  · change ⁅(e6H 2+e6H 4),(e6E 3)⁆=(-2:ℤ) • (e6E 3)
    simp only [add_lie,lie_add,e6HE]
    simp only [show CartanMatrix.E₆ (2:Fin 6) (3:Fin 6)=(-1:ℤ) by decide,
      show CartanMatrix.E₆ (4:Fin 6) (3:Fin 6)=(-1:ℤ) by decide]
    module
  · change ⁅(e6H 2+e6H 4),(e6E 1)⁆=(0:ℤ) • (e6E 1)
    simp only [add_lie,lie_add,e6HE]
    simp only [show CartanMatrix.E₆ (2:Fin 6) (1:Fin 6)=(0:ℤ) by decide,
      show CartanMatrix.E₆ (4:Fin 6) (1:Fin 6)=(0:ℤ) by decide]
    module
  · change ⁅(e6H 3),(e6E 0+e6E 5)⁆=(0:ℤ) • (e6E 0+e6E 5)
    simp only [add_lie,lie_add,e6HE]
    simp only [show CartanMatrix.E₆ (3:Fin 6) (0:Fin 6)=(0:ℤ) by decide,
      show CartanMatrix.E₆ (3:Fin 6) (5:Fin 6)=(0:ℤ) by decide]
    module
  · change ⁅(e6H 3),(e6E 2+e6E 4)⁆=(-1:ℤ) • (e6E 2+e6E 4)
    simp only [add_lie,lie_add,e6HE]
    simp only [show CartanMatrix.E₆ (3:Fin 6) (2:Fin 6)=(-1:ℤ) by decide,
      show CartanMatrix.E₆ (3:Fin 6) (4:Fin 6)=(-1:ℤ) by decide]
    module
  · change ⁅(e6H 3),(e6E 3)⁆=(2:ℤ) • (e6E 3)
    simp only [add_lie,lie_add,e6HE]
    simp only [show CartanMatrix.E₆ (3:Fin 6) (3:Fin 6)=(2:ℤ) by decide]
  · change ⁅(e6H 3),(e6E 1)⁆=(-1:ℤ) • (e6E 1)
    simp only [add_lie,lie_add,e6HE]
    simp only [show CartanMatrix.E₆ (3:Fin 6) (1:Fin 6)=(-1:ℤ) by decide]
  · change ⁅(e6H 1),(e6E 0+e6E 5)⁆=(0:ℤ) • (e6E 0+e6E 5)
    simp only [add_lie,lie_add,e6HE]
    simp only [show CartanMatrix.E₆ (1:Fin 6) (0:Fin 6)=(0:ℤ) by decide,
      show CartanMatrix.E₆ (1:Fin 6) (5:Fin 6)=(0:ℤ) by decide]
    module
  · change ⁅(e6H 1),(e6E 2+e6E 4)⁆=(0:ℤ) • (e6E 2+e6E 4)
    simp only [add_lie,lie_add,e6HE]
    simp only [show CartanMatrix.E₆ (1:Fin 6) (2:Fin 6)=(0:ℤ) by decide,
      show CartanMatrix.E₆ (1:Fin 6) (4:Fin 6)=(0:ℤ) by decide]
    module
  · change ⁅(e6H 1),(e6E 3)⁆=(-1:ℤ) • (e6E 3)
    simp only [add_lie,lie_add,e6HE]
    simp only [show CartanMatrix.E₆ (1:Fin 6) (3:Fin 6)=(-1:ℤ) by decide]
  · change ⁅(e6H 1),(e6E 1)⁆=(2:ℤ) • (e6E 1)
    simp only [add_lie,lie_add,e6HE]
    simp only [show CartanMatrix.E₆ (1:Fin 6) (1:Fin 6)=(2:ℤ) by decide]

theorem HF (i j : Fin 4) : ⁅cartan i,negative j⁆= -(CartanMatrix.F₄ i j • negative j) := by
  fin_cases i <;> fin_cases j
  · change ⁅(e6H 0+e6H 5),(e6F 0+e6F 5)⁆=-((2:ℤ) • (e6F 0+e6F 5))
    simp only [add_lie,lie_add,e6HF]
    simp only [show CartanMatrix.E₆ (0:Fin 6) (0:Fin 6)=(2:ℤ) by decide,
      show CartanMatrix.E₆ (0:Fin 6) (5:Fin 6)=(0:ℤ) by decide,
      show CartanMatrix.E₆ (5:Fin 6) (0:Fin 6)=(0:ℤ) by decide,
      show CartanMatrix.E₆ (5:Fin 6) (5:Fin 6)=(2:ℤ) by decide]
    module
  · change ⁅(e6H 0+e6H 5),(e6F 2+e6F 4)⁆=-((-1:ℤ) • (e6F 2+e6F 4))
    simp only [add_lie,lie_add,e6HF]
    simp only [show CartanMatrix.E₆ (0:Fin 6) (2:Fin 6)=(-1:ℤ) by decide,
      show CartanMatrix.E₆ (0:Fin 6) (4:Fin 6)=(0:ℤ) by decide,
      show CartanMatrix.E₆ (5:Fin 6) (2:Fin 6)=(0:ℤ) by decide,
      show CartanMatrix.E₆ (5:Fin 6) (4:Fin 6)=(-1:ℤ) by decide]
    module
  · change ⁅(e6H 0+e6H 5),(e6F 3)⁆=-((0:ℤ) • (e6F 3))
    simp only [add_lie,lie_add,e6HF]
    simp only [show CartanMatrix.E₆ (0:Fin 6) (3:Fin 6)=(0:ℤ) by decide,
      show CartanMatrix.E₆ (5:Fin 6) (3:Fin 6)=(0:ℤ) by decide]
    module
  · change ⁅(e6H 0+e6H 5),(e6F 1)⁆=-((0:ℤ) • (e6F 1))
    simp only [add_lie,lie_add,e6HF]
    simp only [show CartanMatrix.E₆ (0:Fin 6) (1:Fin 6)=(0:ℤ) by decide,
      show CartanMatrix.E₆ (5:Fin 6) (1:Fin 6)=(0:ℤ) by decide]
    module
  · change ⁅(e6H 2+e6H 4),(e6F 0+e6F 5)⁆=-((-1:ℤ) • (e6F 0+e6F 5))
    simp only [add_lie,lie_add,e6HF]
    simp only [show CartanMatrix.E₆ (2:Fin 6) (0:Fin 6)=(-1:ℤ) by decide,
      show CartanMatrix.E₆ (2:Fin 6) (5:Fin 6)=(0:ℤ) by decide,
      show CartanMatrix.E₆ (4:Fin 6) (0:Fin 6)=(0:ℤ) by decide,
      show CartanMatrix.E₆ (4:Fin 6) (5:Fin 6)=(-1:ℤ) by decide]
    module
  · change ⁅(e6H 2+e6H 4),(e6F 2+e6F 4)⁆=-((2:ℤ) • (e6F 2+e6F 4))
    simp only [add_lie,lie_add,e6HF]
    simp only [show CartanMatrix.E₆ (2:Fin 6) (2:Fin 6)=(2:ℤ) by decide,
      show CartanMatrix.E₆ (2:Fin 6) (4:Fin 6)=(0:ℤ) by decide,
      show CartanMatrix.E₆ (4:Fin 6) (2:Fin 6)=(0:ℤ) by decide,
      show CartanMatrix.E₆ (4:Fin 6) (4:Fin 6)=(2:ℤ) by decide]
    module
  · change ⁅(e6H 2+e6H 4),(e6F 3)⁆=-((-2:ℤ) • (e6F 3))
    simp only [add_lie,lie_add,e6HF]
    simp only [show CartanMatrix.E₆ (2:Fin 6) (3:Fin 6)=(-1:ℤ) by decide,
      show CartanMatrix.E₆ (4:Fin 6) (3:Fin 6)=(-1:ℤ) by decide]
    module
  · change ⁅(e6H 2+e6H 4),(e6F 1)⁆=-((0:ℤ) • (e6F 1))
    simp only [add_lie,lie_add,e6HF]
    simp only [show CartanMatrix.E₆ (2:Fin 6) (1:Fin 6)=(0:ℤ) by decide,
      show CartanMatrix.E₆ (4:Fin 6) (1:Fin 6)=(0:ℤ) by decide]
    module
  · change ⁅(e6H 3),(e6F 0+e6F 5)⁆=-((0:ℤ) • (e6F 0+e6F 5))
    simp only [add_lie,lie_add,e6HF]
    simp only [show CartanMatrix.E₆ (3:Fin 6) (0:Fin 6)=(0:ℤ) by decide,
      show CartanMatrix.E₆ (3:Fin 6) (5:Fin 6)=(0:ℤ) by decide]
    module
  · change ⁅(e6H 3),(e6F 2+e6F 4)⁆=-((-1:ℤ) • (e6F 2+e6F 4))
    simp only [add_lie,lie_add,e6HF]
    simp only [show CartanMatrix.E₆ (3:Fin 6) (2:Fin 6)=(-1:ℤ) by decide,
      show CartanMatrix.E₆ (3:Fin 6) (4:Fin 6)=(-1:ℤ) by decide]
    module
  · change ⁅(e6H 3),(e6F 3)⁆=-((2:ℤ) • (e6F 3))
    simp only [add_lie,lie_add,e6HF]
    simp only [show CartanMatrix.E₆ (3:Fin 6) (3:Fin 6)=(2:ℤ) by decide]
  · change ⁅(e6H 3),(e6F 1)⁆=-((-1:ℤ) • (e6F 1))
    simp only [add_lie,lie_add,e6HF]
    simp only [show CartanMatrix.E₆ (3:Fin 6) (1:Fin 6)=(-1:ℤ) by decide]
  · change ⁅(e6H 1),(e6F 0+e6F 5)⁆=-((0:ℤ) • (e6F 0+e6F 5))
    simp only [add_lie,lie_add,e6HF]
    simp only [show CartanMatrix.E₆ (1:Fin 6) (0:Fin 6)=(0:ℤ) by decide,
      show CartanMatrix.E₆ (1:Fin 6) (5:Fin 6)=(0:ℤ) by decide]
    module
  · change ⁅(e6H 1),(e6F 2+e6F 4)⁆=-((0:ℤ) • (e6F 2+e6F 4))
    simp only [add_lie,lie_add,e6HF]
    simp only [show CartanMatrix.E₆ (1:Fin 6) (2:Fin 6)=(0:ℤ) by decide,
      show CartanMatrix.E₆ (1:Fin 6) (4:Fin 6)=(0:ℤ) by decide]
    module
  · change ⁅(e6H 1),(e6F 3)⁆=-((-1:ℤ) • (e6F 3))
    simp only [add_lie,lie_add,e6HF]
    simp only [show CartanMatrix.E₆ (1:Fin 6) (3:Fin 6)=(-1:ℤ) by decide]
  · change ⁅(e6H 1),(e6F 1)⁆=-((2:ℤ) • (e6F 1))
    simp only [add_lie,lie_add,e6HF]
    simp only [show CartanMatrix.E₆ (1:Fin 6) (1:Fin 6)=(2:ℤ) by decide]

end SymmetricSubgroupAsymptotics.CFSGFFourSerreMatrices
