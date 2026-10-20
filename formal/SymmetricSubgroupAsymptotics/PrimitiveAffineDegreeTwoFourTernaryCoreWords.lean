import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFourTernaryCoordinates

/-!
# Literal ternary-core coordinates and words

Four prescribed conjugates of the first original generator span the core
translation coordinates. The displayed coefficients come from matrices of
at most four rows over F3. Kernel checks evaluate the resulting explicit
words on twelve points; no membership test in a noncomputable closure is
asked to decide itself.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoFourTernaryCoreWords

open TernarySignedBlockCoordinates
open PrimitiveAffineDegreeTwoFourTernaryCoordinates
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

/-- Translation coordinates of every retained original core generator. -/
def coreVector (r : Fin 8) :
    Fin (degreeTwoFourTernaryCoreGeneratorRow r).count → Vector := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
      (fun i => Fin.elim0 i)))))))) r
  · exact ![![0, 2, 0, 2], ![1, 2, 1, 2]]
  · exact ![![0, 1, 0, 1], ![1, 1, 1, 1]]
  · exact ![![0, 0, 2, 1], ![0, 1, 2, 0], ![1, 1, 2, 2]]
  · exact ![![0, 0, 0, 2], ![0, 0, 2, 2], ![0, 1, 2, 2], ![1, 0, 2, 2]]
  · exact ![![0, 0, 1, 0], ![0, 2, 1, 0], ![0, 2, 1, 1], ![1, 2, 1, 0]]
  · exact ![![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 2, 0, 1],
      ![0, 0, 2, 1], ![0, 2, 2, 0], ![0, 2, 2, 1],
      ![0, 2, 2, 2], ![1, 2, 2, 1], ![1, 2, 2, 2]]
  · exact ![![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 1, 1],
      ![0, 1, 0, 1], ![0, 1, 1, 0], ![0, 1, 1, 1],
      ![1, 1, 1, 1], ![1, 1, 1, 2]]
  · exact ![![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 1, 1],
      ![0, 1, 0, 1], ![0, 1, 1, 0], ![0, 1, 1, 1], ![1, 1, 1, 1]]

theorem core_generator_binding (r : Fin 8)
    (j : Fin (degreeTwoFourTernaryCoreGeneratorRow r).count) :
    literalAction (phase r) (translate (coreVector r j)) =
      degreeTwoFourTernaryCoreGeneratorPerm r j := by
  fin_cases r <;> fin_cases j <;>
    apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel

def firstBlockLetter : Fin 8 → Fin 5 := ![2, 2, 2, 2, 2, 2, 3, 2]
def secondBlockLetter : Fin 8 → Fin 5 := ![3, 3, 3, 3, 3, 3, 4, 3]

def conjugator (r : Fin 8) : Fin 4 → Equiv.Perm (Fin 12) :=
  ![1, literalGenerators r (firstBlockLetter r),
    literalGenerators r (secondBlockLetter r),
    literalGenerators r (firstBlockLetter r) *
      literalGenerators r (secondBlockLetter r)]

def basisWord (r : Fin 8) (i : Fin 4) : Equiv.Perm (Fin 12) :=
  conjugator r i * literalGenerators r 0 * (conjugator r i)⁻¹

/-- Explicit coefficients in the four fixed conjugate-translation words. -/
def coefficient (r : Fin 8) :
    Fin (degreeTwoFourTernaryCoreGeneratorRow r).count → Fin 4 → Fin 3 := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
      (fun i => Fin.elim0 i)))))))) r
  · exact ![![2, 0, 0, 0], ![2, 1, 0, 0]]
  · exact ![![1, 0, 0, 0], ![1, 1, 0, 0]]
  · exact ![![1, 1, 2, 0], ![0, 2, 1, 0], ![1, 1, 0, 0]]
  · exact ![![2, 0, 0, 0], ![2, 2, 0, 0], ![2, 2, 1, 0], ![2, 2, 0, 1]]
  · exact ![![0, 1, 0, 0], ![0, 1, 2, 0], ![1, 1, 2, 0], ![0, 1, 2, 1]]
  · exact ![![0, 0, 0, 0], ![1, 0, 0, 0], ![1, 1, 0, 0],
      ![1, 0, 0, 1], ![0, 1, 0, 1], ![1, 1, 0, 1],
      ![2, 1, 0, 1], ![1, 1, 1, 1], ![2, 1, 1, 1]]
  · exact ![![0, 0, 0, 0], ![1, 0, 0, 0], ![1, 1, 0, 0],
      ![1, 0, 1, 0], ![0, 1, 1, 0], ![1, 1, 1, 0],
      ![1, 1, 1, 1], ![2, 1, 1, 1]]
  · exact ![![0, 0, 0, 0], ![1, 0, 0, 0], ![1, 1, 0, 0],
      ![1, 0, 1, 0], ![0, 1, 1, 0], ![1, 1, 1, 0], ![1, 1, 1, 1]]

def coreWord (r : Fin 8)
    (j : Fin (degreeTwoFourTernaryCoreGeneratorRow r).count) : Equiv.Perm (Fin 12) :=
  basisWord r 0 ^ (coefficient r j 0).val *
    basisWord r 1 ^ (coefficient r j 1).val *
    basisWord r 2 ^ (coefficient r j 2).val *
    basisWord r 3 ^ (coefficient r j 3).val

theorem coreWord_eq (r : Fin 8)
    (j : Fin (degreeTwoFourTernaryCoreGeneratorRow r).count) :
    coreWord r j = degreeTwoFourTernaryCoreGeneratorPerm r j := by
  fin_cases r <;> fin_cases j <;>
    apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel

theorem conjugator_mem (r : Fin 8) (i : Fin 4) :
    conjugator r i ∈ (degreeTwoFourTernaryInterface r).top := by
  fin_cases i
  · exact Subgroup.one_mem _
  · exact literalGenerator_mem r (firstBlockLetter r)
  · exact literalGenerator_mem r (secondBlockLetter r)
  · exact Subgroup.mul_mem _ (literalGenerator_mem r (firstBlockLetter r))
      (literalGenerator_mem r (secondBlockLetter r))

theorem basisWord_mem (r : Fin 8) (i : Fin 4) :
    basisWord r i ∈ (degreeTwoFourTernaryInterface r).top :=
  Subgroup.mul_mem _
    (Subgroup.mul_mem _ (conjugator_mem r i) (literalGenerator_mem r 0))
    (Subgroup.inv_mem _ (conjugator_mem r i))

theorem coreWord_mem (r : Fin 8)
    (j : Fin (degreeTwoFourTernaryCoreGeneratorRow r).count) :
    coreWord r j ∈ (degreeTwoFourTernaryInterface r).top :=
  Subgroup.mul_mem _
    (Subgroup.mul_mem _
      (Subgroup.mul_mem _
        (Subgroup.pow_mem _ (basisWord_mem r 0) _)
        (Subgroup.pow_mem _ (basisWord_mem r 1) _))
      (Subgroup.pow_mem _ (basisWord_mem r 2) _))
    (Subgroup.pow_mem _ (basisWord_mem r 3) _)

/-- The original membership payload is proved by literal words in its generators. -/
def membership : DegreeTwoFourTernaryGeneratorMembership where
  mem r j := by
    rw [← coreWord_eq]
    exact coreWord_mem r j

theorem translate_coreVector_mem (r : Fin 8)
    (j : Fin (degreeTwoFourTernaryCoreGeneratorRow r).count) :
    TernarySignedBlockCoordinates.translate (coreVector r j) ∈ CoordinateTop r := by
  have hm : literalAction (phase r)
      (TernarySignedBlockCoordinates.translate (coreVector r j)) ∈
      (CoordinateTop r).map (literalAction (phase r)) := by
    rw [map_closure_eq (phase r) (generators r) (literalGenerators r)
      (generators_binding r), literal_closure_eq, core_generator_binding]
    exact membership.mem r j
  obtain ⟨g, hg, he⟩ := hm
  have heq := literalAction_injective (phase r) he
  simpa only [heq] using hg

end PrimitiveAffineDegreeTwoFourTernaryCoreWords
end SymmetricSubgroupAsymptotics

end
