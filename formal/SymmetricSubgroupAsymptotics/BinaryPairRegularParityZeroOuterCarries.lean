import SymmetricSubgroupAsymptotics.BinaryRegular46ParityZeroOuterCarries
import SymmetricSubgroupAsymptotics.BinaryPairLiftCarryExponent

/-! The selected outer carry certificate applies to arbitrary original
lifts of the literal six top generators. Its balanced derived words are
bound to the same actual commutator subgroup. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame.RegularParityZeroOuterCarries

open BinaryRegular46ParityZeroOuterCarries
variable {X : Type} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16)) (u : Fin 6 → U)
    (hp : ∀ i, F.top (u i) = generators i)

def actualOffsets : Offsets := fun j =>
  F.affineTranslation (u ((finProdFinEquiv (m := 6) (n := 16)).symm j).1)
    ((finProdFinEquiv (m := 6) (n := 16)).symm j).2

include hp

theorem sourceOffsets_actualOffsets :
    sourceOffsets (actualOffsets F u) = fun i => F.offset (u i) := by
  ext i j
  change F.affineTranslation
      (u ((finProdFinEquiv (m := 6) (n := 16)).symm
        (finProdFinEquiv (i, generatorImages i j))).1)
      ((finProdFinEquiv (m := 6) (n := 16)).symm
        (finProdFinEquiv (i, generatorImages i j))).2 = _
  rw [Equiv.symm_apply_apply]
  change F.offset (u i) ((F.top (u i))⁻¹ (generatorImages i j)) = _
  rw [hp]
  change F.offset (u i) (generatorImages i (generatorImages i j)) = _
  rw [generator_involution]

theorem lift_top_square (i : Fin 6) : F.top (u i) ^ 2 = 1 := by
  rw [hp]
  apply Equiv.ext
  exact generator_involution i

def actualRelator (r : Fin 21) : F.top.ker :=
  ⟨(relators r).eval u, by
    change F.top ((relators r).eval u) = 1
    rw [DerivedGeneratorWord.map_eval]
    rw [show (fun i => F.top (u i)) = generators from funext hp]
    exact relators_top r⟩

theorem actualRelator_mem_commutator (r : Fin 21) :
    (actualRelator F u hp r : U) ∈ commutator U :=
  (relators r).eval_mem_commutator u

theorem squareMap_actualOffsets (i : Fin 6) :
    squareMap i (actualOffsets F u) =
      layerChange (F.bits (F.carrySquare (u i) (lift_top_square F u hp i))) := by
  change layerChange (BinarySignedOffsetWord.offset generators [(i,true),(i,true)]
    (sourceOffsets (actualOffsets F u))) = _
  rw [sourceOffsets_actualOffsets F u hp,
    BinarySignedOffsetWord.offset_original F u generators hp]
  change layerChange (F.offset (BinarySignedOffsetWord.eval u [(i,true),(i,true)])) =
    layerChange (F.offset (u i ^ 2))
  apply congrArg layerChange
  congr 1

theorem relatorMap_actualOffsets (r : Fin 21) :
    relatorMap r (actualOffsets F u) = layerChange (F.bits (actualRelator F u hp r)) := by
  change layerChange (BinarySignedOffsetWord.offset generators (rawWords r)
    (sourceOffsets (actualOffsets F u))) = _
  rw [← relators_words r, sourceOffsets_actualOffsets F u hp,
    BinarySignedOffsetWord.offset_original F u generators hp,
    BinarySignedOffsetWord.eval_ofDerived]
  rfl

/-- These are the actual original squares, not squares of independently
chosen involutory lifts or of a split replacement. -/
theorem square_carries (hK : F.kernelSpace = pointState)
    (hderived : ∀ k : F.top.ker, (k : U) ∈ commutator U → F.bits k ∈ pointRadical) :
    ∀ i, F.bits (F.carrySquare (u i) (lift_top_square F u hp i)) ∈ pointRadical := by
  have hsquare (i : Fin 6) : squareMap i (actualOffsets F u) ∈ wideState := by
    rw [squareMap_actualOffsets F u hp]
    have hm : F.bits (F.carrySquare (u i) (lift_top_square F u hp i)) ∈ F.kernelSpace :=
      ⟨Additive.ofMul _, rfl⟩
    rw [hK] at hm
    exact hm
  have hrelator (r : Fin 21) : relatorMap r (actualOffsets F u) ∈ lowerRadical := by
    rw [relatorMap_actualOffsets F u hp]
    exact hderived _ (actualRelator_mem_commutator F u hp r)
  intro i
  change layerChange (F.bits (F.carrySquare (u i) (lift_top_square F u hp i))) ∈ lowerRadical
  rw [← squareMap_actualOffsets F u hp]
  exact BinaryRegular46ParityZeroOuterCarries.square_carry _ hsquare hrelator i

/-- Once the exact original kernel radical is identified, the sparse
certificate forces exponent two in the full original abelianization. -/
theorem abelianization_pow_two
    (hgen : Subgroup.closure (Set.range fun i => F.top (u i)) = F.top.range)
    (hK : F.kernelSpace = pointState)
    (hrad : primeRelativeRadical 2 F.top.ker = F.top.ker ⊓ commutator U)
    (hR : ∀ k : F.top.ker, F.bits k ∈ pointRadical ↔
      (k : U) ∈ primeRelativeRadical 2 F.top.ker) :
    ∀ a : Abelianization U, a ^ 2 = 1 :=
  F.abelianization_pow_two_of_radical_square_carries u hgen
    (lift_top_square F u hp) hrad pointRadical hR
    (square_carries F u hp hK (F.bits_mem_radical_of_derived hrad pointRadical hR))

end SymmetricSubgroupAsymptotics.BinaryPairFrame.RegularParityZeroOuterCarries
