import SymmetricSubgroupAsymptotics.BinaryCarrierDerivedRadical16T1082
import Mathlib.Algebra.CharP.Two

/-! Three literal original derived generators give coordinates on the
whole-original-group invariant character space. The fourth generator has
the same character value as the first because their product is an actual
mixed commutator. Surjectivity follows from the checked exact relative
radical dimension, not from an assumption that characters extend. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics.BinaryCarrierDerivedCharacters16T1082

abbrev Original := BinaryCarrierDerivedOrder16T1082.Original
abbrev D := commutator Original
abbrev Characters := primeRelativeCharacters 2 D
private abbrev g := BinaryActionData16.node1082Generators
private abbrev words := BinaryCarrierDerivedOrder16T1082.basisWords
private abbrev basis := derivedWordGenerators g words

def originalBasis (j : Fin 4) : D :=
  ⟨basis j, (words j).eval_mem_commutator (closureGenerators g)⟩

theorem originalBasis_full : Subgroup.closure (Set.range originalBasis) = ⊤ := by
  apply Subgroup.map_injective D.subtype_injective
  rw [MonoidHom.map_closure]
  have himage : D.subtype '' Set.range originalBasis = Set.range basis := by
    ext x
    constructor
    · rintro ⟨b, ⟨j, rfl⟩, rfl⟩
      exact Set.mem_range_self j
    · rintro ⟨j, rfl⟩
      exact ⟨originalBasis j, Set.mem_range_self j, rfl⟩
  rw [himage, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact BinaryCarrierDerivedOrder16T1082.certificate.subgroup_eq_commutator

private theorem relation_pointwise : ∀ x : Fin 16,
    ((words 0).eval g * (words 3).eval g) x = ⁅(words 0).eval g, g 4⁆ x := by
  decide +kernel

theorem basis_relation :
    ((originalBasis 0 * originalBasis 3 : D) : Original) =
      ⁅basis 0, closureGenerators g 4⁆ := by
  apply Subtype.ext
  change (basis 0 : Equiv.Perm (Fin 16)) * (basis 3 : Equiv.Perm (Fin 16)) =
    ⁅(basis 0 : Equiv.Perm (Fin 16)), g 4⁆
  have hcoe (j : Fin 4) : (basis j : Equiv.Perm (Fin 16)) = (words j).eval g :=
    closureGenerators_eval_coe g (words j)
  rw [hcoe, hcoe]
  exact Equiv.ext relation_pointwise

theorem fourth_value_eq_first (χ : Characters) :
    χ.1 (Additive.ofMul (originalBasis 3)) = χ.1 (Additive.ofMul (originalBasis 0)) := by
  have hmem : ((originalBasis 0 * originalBasis 3 : D) : Original) ∈
      primeRelativeRadical 2 D := by
    rw [basis_relation]
    exact commutator_mem_primeRelativeRadical 2 D (originalBasis 0) (closureGenerators g 4)
  have hk := (coe_mem_primeRelativeRadical_iff 2 D
    (originalBasis 0 * originalBasis 3)).mp hmem
  have hz := (mem_primeRelativeRadicalKernel_iff 2 D _).mp hk χ
  change χ.1 (Additive.ofMul (originalBasis 0) + Additive.ofMul (originalBasis 3)) = 0 at hz
  rw [map_add] at hz
  have he := eq_neg_of_add_eq_zero_right hz
  simpa only [CharTwo.neg_eq] using he

/-- Literal evaluation on the first three original derived generators. -/
def coordinates : Characters →ₗ[ZMod 2] (Fin 3 → ZMod 2) where
  toFun χ i := χ.1 (Additive.ofMul (originalBasis i.castSucc))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coordinates_injective : Function.Injective coordinates := by
  intro χ ψ h
  have hfirst : ∀ i : Fin 3,
      χ.1 (Additive.ofMul (originalBasis i.castSucc)) =
        ψ.1 (Additive.ofMul (originalBasis i.castSucc)) := congrFun h
  have hall : ∀ j : Fin 4, χ.1 (Additive.ofMul (originalBasis j)) =
      ψ.1 (Additive.ofMul (originalBasis j)) := by
    intro j
    fin_cases j
    · exact hfirst 0
    · exact hfirst 1
    · exact hfirst 2
    · change χ.1 (Additive.ofMul (originalBasis 3)) = ψ.1 (Additive.ofMul (originalBasis 3))
      rw [fourth_value_eq_first, fourth_value_eq_first]
      exact hfirst 0
  apply Subtype.ext
  apply AddMonoidHom.toMultiplicativeRight.injective
  apply MonoidHom.eq_of_eqOn_dense originalBasis_full
  rintro _ ⟨j, rfl⟩
  exact congrArg Multiplicative.ofAdd (hall j)

/-- This is a full coordinate equivalence for invariant derived
characters; it does not assert that these characters extend to Original. -/
def coordinateEquiv : Characters ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
  LinearEquiv.ofBijective coordinates ⟨coordinates_injective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [BinaryCarrierDerivedRadical16T1082.relative_character_rank]
      simp)).mp coordinates_injective⟩

end SymmetricSubgroupAsymptotics.BinaryCarrierDerivedCharacters16T1082
