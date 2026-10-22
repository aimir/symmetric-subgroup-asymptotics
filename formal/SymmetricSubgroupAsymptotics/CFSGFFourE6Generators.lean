import SymmetricSubgroupAsymptotics.CFSGExceptionalNormTwoBases

/-! The literal six rational E6 Geck generators used for the F4 folding.
Their relations use the already proved original E6 Cartan equality. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourSerreMatrices
open CFSGNormTwoRootPairing CFSGExceptionalNormTwoBases

local instance fFourE6GeneratorsDecEq : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _
abbrev Index := E6Base.support⊕Roots CartanMatrix.E₆
abbrev Mat := Matrix Index Index ℚ

def e6H (i : Fin 6) : Mat := CFSGGeckSerreRepresentation.H E6Base E6Index i
def e6E (i : Fin 6) : Mat := CFSGGeckSerreRepresentation.E E6Base E6Index i
def e6F (i : Fin 6) : Mat := CFSGGeckSerreRepresentation.F E6Base E6Index i

theorem e6HH (i j : Fin 6) : ⁅e6H i,e6H j⁆=0 :=
  CFSGGeckSerreRepresentation.HH E6Base E6Index i j
theorem e6EF (i j : Fin 6) : ⁅e6E i,e6F j⁆=if i=j then e6H i else 0 :=
  CFSGGeckSerreRepresentation.EF E6Base E6Index i j
theorem e6HE (i j : Fin 6) : ⁅e6H i,e6E j⁆=CartanMatrix.E₆ i j • e6E j := by
  have h := CFSGGeckSerreRepresentation.HE E6Base E6Index i j
  rw [E6_cartan] at h
  exact h
theorem e6HF (i j : Fin 6) : ⁅e6H i,e6F j⁆= -(CartanMatrix.E₆ i j • e6F j) := by
  have h := CFSGGeckSerreRepresentation.HF E6Base E6Index i j
  rw [E6_cartan] at h
  exact h

end SymmetricSubgroupAsymptotics.CFSGFFourSerreMatrices
