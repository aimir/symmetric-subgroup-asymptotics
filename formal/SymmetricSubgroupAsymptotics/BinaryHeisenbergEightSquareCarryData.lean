import SymmetricSubgroupAsymptotics.DerivedSignedPairOffsetWords
import SymmetricSubgroupAsymptotics.BinaryRegularEightSquareCarry
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T22

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators Classical commutatorElement
namespace SymmetricSubgroupAsymptotics.BinaryHeisenbergEightSquareCarry

abbrev V := Fin 8 → ZMod 2
abbrev Offsets := Fin 32 → ZMod 2
def originalSelected (i : Fin 4) : Equiv.Perm (Fin 8) := BinaryMenuCayley8T22.generators ⟨i.val + 1, by omega⟩
def central : DerivedGeneratorWord (Fin 4) := .comm 0 2
private theorem omitted_pointwise : ∀ x, BinaryMenuCayley8T22.generators 0 x = central.eval originalSelected x := by decide +kernel
theorem omitted_eq_central : BinaryMenuCayley8T22.generators 0 = central.eval originalSelected := Equiv.ext omitted_pointwise
theorem selected_closure_eq_original : Subgroup.closure (Set.range originalSelected) =
    Subgroup.closure (Set.range BinaryMenuCayley8T22.generators) := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact Subgroup.subset_closure ⟨⟨i.val + 1, by omega⟩, rfl⟩
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · change BinaryMenuCayley8T22.generators 0 ∈ Subgroup.closure (Set.range originalSelected)
      rw [omitted_eq_central]
      let H := Subgroup.closure (Set.range originalSelected)
      have h0 : originalSelected 0 ∈ H := Subgroup.subset_closure ⟨0, rfl⟩
      have h2 : originalSelected 2 ∈ H := Subgroup.subset_closure ⟨2, rfl⟩
      change originalSelected 0 * originalSelected 2 * (originalSelected 0)⁻¹ *
        (originalSelected 2)⁻¹ ∈ H
      exact H.mul_mem (H.mul_mem (H.mul_mem h0 h2) (H.inv_mem h0)) (H.inv_mem h2)
    · exact Subgroup.subset_closure ⟨(0 : Fin 4), rfl⟩
    · exact Subgroup.subset_closure ⟨(1 : Fin 4), rfl⟩
    · exact Subgroup.subset_closure ⟨(2 : Fin 4), rfl⟩
    · exact Subgroup.subset_closure ⟨(3 : Fin 4), rfl⟩
def relators : Fin 11 → DerivedGeneratorWord (Fin 4) := ![.comm 0 1,.mul (.comm 0 2) (.inv central),.mul (.comm 0 3) (.inv central),.mul (.comm 1 2) (.inv central),.comm 1 3,.comm 2 3,.mul central central,.mul central (.conj 0 (.inv central)),.mul central (.conj 1 (.inv central)),.mul central (.conj 2 (.inv central)),.mul central (.conj 3 (.inv central))]
private theorem relators_pointwise : ∀ r x, (relators r).eval originalSelected x = x := by decide +kernel
theorem relators_top (r : Fin 11) : (relators r).eval originalSelected = 1 := Equiv.ext (relators_pointwise r)
theorem originalSelected_involution : ∀ i x, originalSelected i (originalSelected i x) = x := by decide +kernel
def unflatten : Offsets →ₗ[ZMod 2] (Fin 4 → V) where
  toFun x i j := x (finProdFinEquiv (i, j))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def squareMap (i : Fin 4) : Offsets →ₗ[ZMod 2] V :=
  (BinarySignedOffsetWord.offset originalSelected [(i, true), (i, true)]).comp unflatten
def relatorMap (r : Fin 11) : Offsets →ₗ[ZMod 2] V :=
  (BinarySignedOffsetWord.offset originalSelected (BinarySignedOffsetWord.ofDerived (relators r))).comp unflatten
def squareFunctional (i : Fin 4) (chi : V) : Offsets →ₗ[ZMod 2] ZMod 2 := (binaryRowFunctional chi).comp (squareMap i)
def relatorFunctional (r : Fin 11) (chi : V) : Offsets →ₗ[ZMod 2] ZMod 2 := (binaryRowFunctional chi).comp (relatorMap r)
def annihilatorK12 : Fin 1 → ℕ := ![255]
def annihilatorR12 : Fin 3 → ℕ := ![135,102,30]
abbrev K12 := BinaryRegularEightSquareCarry.annihilatorSpace annihilatorK12
abbrev R12 := BinaryRegularEightSquareCarry.annihilatorSpace annihilatorR12
def annihilatorK13 : Fin 3 → ℕ := ![135,102,30]
def annihilatorR13 : Fin 5 → ℕ := ![129,75,43,24,6]
abbrev K13 := BinaryRegularEightSquareCarry.annihilatorSpace annihilatorK13
abbrev R13 := BinaryRegularEightSquareCarry.annihilatorSpace annihilatorR13
def annihilatorK14 : Fin 5 → ℕ := ![129,75,43,24,6]
def annihilatorR14 : Fin 7 → ℕ := ![129,65,33,17,9,5,3]
abbrev K14 := BinaryRegularEightSquareCarry.annihilatorSpace annihilatorK14
abbrev R14 := BinaryRegularEightSquareCarry.annihilatorSpace annihilatorR14

end SymmetricSubgroupAsymptotics.BinaryHeisenbergEightSquareCarry
