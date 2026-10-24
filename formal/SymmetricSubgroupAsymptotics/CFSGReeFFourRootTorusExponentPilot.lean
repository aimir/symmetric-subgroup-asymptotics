import SymmetricSubgroupAsymptotics.CFSGE6FiniteRootMenu

/-! A bounded integer pilot for the two fixed-torus exponents on the
ambient E6 root lattice. The first pair belongs to the first torus unit,
the second to the second unit; each pair consists of its untwisted and
alpha-power coefficients. This is arithmetic only, not yet a theorem
about conjugation or full-positive derived membership. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourRootTorusExponentPilot
open CFSGNormTwoRootPairing CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoCoordinateFiniteRootMenu CFSGE6FiniteRootMenu

def firstBase (x : Fin 6→ℤ) : ℤ := 2*(x 0+x 5)-(x 2+x 4)
def firstAlpha (x : Fin 6→ℤ) : ℤ := 2*x 1-x 3
def secondBase (x : Fin 6→ℤ) : ℤ := -(x 0+x 5)+2*(x 2+x 4)-2*x 3
def secondAlpha (x : Fin 6→ℤ) : ℤ := -(x 2+x 4)+2*x 3-x 1

private theorem menu_bounds : ∀x∈menu,
    (-2≤firstBase x ∧ firstBase x≤2) ∧
    (-2≤firstAlpha x ∧ firstAlpha x≤2) ∧
    (-2≤secondBase x ∧ secondBase x≤2) ∧
    (-2≤secondAlpha x ∧ secondAlpha x≤2) := by decide +kernel

private theorem menu_nonzero : ∀x∈menu,
    ¬(firstBase x=0 ∧ firstAlpha x=0 ∧ secondBase x=0 ∧ secondAlpha x=0) := by decide +kernel

private theorem menu_eight : ∀x∈menu,
    ¬((7 : ℤ)∣firstBase x+4*firstAlpha x) ∨
      ¬((7 : ℤ)∣secondBase x+4*secondAlpha x) := by decide +kernel

noncomputable section
local instance : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _

private theorem mem_menu (k : Roots CartanMatrix.E₆) : k.val∈menu :=
  root_mem_menu CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos menu negative_simple_mem reflection_closed k

theorem root_exponent_bounds (k : Roots CartanMatrix.E₆) :
    (-2≤firstBase k.val ∧ firstBase k.val≤2) ∧
    (-2≤firstAlpha k.val ∧ firstAlpha k.val≤2) ∧
    (-2≤secondBase k.val ∧ secondBase k.val≤2) ∧
    (-2≤secondAlpha k.val ∧ secondAlpha k.val≤2) :=
  menu_bounds k.val (mem_menu k)

theorem root_exponents_nonzero (k : Roots CartanMatrix.E₆) :
    ¬(firstBase k.val=0 ∧ firstAlpha k.val=0 ∧ secondBase k.val=0 ∧ secondAlpha k.val=0) :=
  menu_nonzero k.val (mem_menu k)

theorem root_eight_exponents_nondivisible (k : Roots CartanMatrix.E₆) :
    ¬((7 : ℤ)∣firstBase k.val+4*firstAlpha k.val) ∨
      ¬((7 : ℤ)∣secondBase k.val+4*secondAlpha k.val) :=
  menu_eight k.val (mem_menu k)

end
end SymmetricSubgroupAsymptotics.CFSGReeFFourRootTorusExponentPilot
