import SymmetricSubgroupAsymptotics.PrimeRelativeCharacterCoordinates
import SymmetricSubgroupAsymptotics.BinaryCarrierDerivedRadical16T1332

/-! Complete coordinates on the actual whole-original-group invariant
derived characters. Every relation is certified modulo the original
relative radical on the original sixteen points. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierDerivedCharacters16T1332

abbrev Original := BinaryCarrierDerivedOrder16T1332.Original
abbrev D := commutator Original
abbrev Characters := primeRelativeCharacters 2 D
private abbrev g := BinaryActionData16.node1332Generators
private abbrev words := BinaryCarrierDerivedOrder16T1332.basisWords
private abbrev basis := derivedWordGenerators g words

def originalBasis (j : Fin 6) : D :=
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
  exact BinaryCarrierDerivedOrder16T1332.certificate.subgroup_eq_commutator

def selected : Fin 4 → Fin 6 := ![1,3,4,5]
def quotientWords : Fin 6 → List (Fin 4) := ![[],[0],[],[1],[2],[3]]
private def residueRow : Fin 6 → Fin 4 := ![3,0,2,0,0,0]

private theorem relation_pointwise : ∀ (j : Fin 6) (x : Fin 16),
    BinaryCarrierDerivedRadical16T1332.ambientRows (residueRow j) x =
      (BinaryCarrierDerivedRadical16T1332.ambientBasis j *
        (((quotientWords j).map
          (BinaryCarrierDerivedRadical16T1332.ambientBasis ∘ selected)).prod)⁻¹) x := by
  decide +kernel

theorem quotientWords_mem_radical (j : Fin 6) :
    ((originalBasis j * (((quotientWords j).map (originalBasis ∘ selected)).prod)⁻¹ : D) : Original) ∈
      primeRelativeRadical 2 D := by
  have he :
      ((originalBasis j * (((quotientWords j).map (originalBasis ∘ selected)).prod)⁻¹ : D) : Original) =
        BinaryCarrierDerivedRadical16T1332.elements (residueRow j) := by
    apply Subtype.ext
    let projection : D →* Equiv.Perm (Fin 16) := Original.subtype.comp D.subtype
    change projection (originalBasis j * (((quotientWords j).map (originalBasis ∘ selected)).prod)⁻¹) =
      (BinaryCarrierDerivedRadical16T1332.elements (residueRow j) : Equiv.Perm (Fin 16))
    have hf : projection ∘ (originalBasis ∘ selected) =
        BinaryCarrierDerivedRadical16T1332.ambientBasis ∘ selected := by
      funext i
      exact BinaryCarrierDerivedRadical16T1332.basis_coe (selected i)
    have hb : projection (originalBasis j) = BinaryCarrierDerivedRadical16T1332.ambientBasis j :=
      BinaryCarrierDerivedRadical16T1332.basis_coe j
    rw [map_mul, map_inv, map_list_prod, List.map_map, hf, hb,
      BinaryCarrierDerivedRadical16T1332.elements_coe]
    exact (Equiv.ext (relation_pointwise j)).symm
  rw [he]
  exact BinaryCarrierDerivedRadical16T1332.elements_mem_radical _

def coordinates : Characters →ₗ[ZMod 2] (Fin 4 → ZMod 2) :=
  primeRelativeCharacterCoordinates 2 D originalBasis selected

@[simp] theorem coordinates_apply (χ : Characters) (i : Fin 4) :
    coordinates χ i = χ.1 (Additive.ofMul (originalBasis (selected i))) := rfl

theorem originalBasis_value (χ : Characters) (j : Fin 6) :
    χ.1 (Additive.ofMul (originalBasis j)) = ((quotientWords j).map (coordinates χ)).sum :=
  primeRelativeCharacter_generator_values 2 D originalBasis selected quotientWords
    quotientWords_mem_radical χ j

theorem coordinates_injective : Function.Injective coordinates :=
  primeRelativeCharacterCoordinates_injective 2 D originalBasis originalBasis_full selected quotientWords
    quotientWords_mem_radical

def coordinateEquiv : Characters ≃ₗ[ZMod 2] (Fin 4 → ZMod 2) :=
  primeRelativeCharacterCoordinateEquiv 2 D originalBasis originalBasis_full selected quotientWords
    quotientWords_mem_radical BinaryCarrierDerivedRadical16T1332.relative_character_rank

end SymmetricSubgroupAsymptotics.BinaryCarrierDerivedCharacters16T1332
