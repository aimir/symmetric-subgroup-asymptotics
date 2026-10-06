import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction023OneGeneralIndices
import SymmetricSubgroupAsymptotics.FiniteGroupCertificates

/-!
# Action 023 one-general pilot: four-row middle certificate

The only finite subgroup enumeration used by the final pilot is isolated in
this module.  All native checks concern the executable twelve-row source;
the noncomputable equivalence is applied only after those equalities have
been checked.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoSixPairAction023OneGeneralSplit

open Non2UnipotentPrefixFiniteMenu

private def middleSourceElement :
    Fin 4 → PrimitiveAffineDegreeTwoSixPairAction023ClassPilot.Source :=
  Fin.cases
    (⟨11⟩ : PrimitiveAffineDegreeTwoSixPairAction023ClassPilot.Source)
    (Fin.cases
      (⟨4⟩ : PrimitiveAffineDegreeTwoSixPairAction023ClassPilot.Source)
      (Fin.cases
        (⟨10⟩ : PrimitiveAffineDegreeTwoSixPairAction023ClassPilot.Source)
        (Fin.cases
          (⟨5⟩ : PrimitiveAffineDegreeTwoSixPairAction023ClassPilot.Source)
          Fin.elim0)))

private def middleSourceGenerator :
    Fin 3 → PrimitiveAffineDegreeTwoSixPairAction023ClassPilot.Source :=
  Fin.cases
    (⟨4⟩ : PrimitiveAffineDegreeTwoSixPairAction023ClassPilot.Source)
    (Fin.cases
      (⟨10⟩ : PrimitiveAffineDegreeTwoSixPairAction023ClassPilot.Source)
      (Fin.cases
        (⟨11⟩ : PrimitiveAffineDegreeTwoSixPairAction023ClassPilot.Source)
        Fin.elim0))

private def middleNext : Fin 4 → Fin 3 → Fin 4 :=
  Fin.cases
    (Fin.cases 1 (Fin.cases 2 (Fin.cases 0 Fin.elim0)))
    (Fin.cases
      (Fin.cases 0 (Fin.cases 3 (Fin.cases 1 Fin.elim0)))
      (Fin.cases
        (Fin.cases 3 (Fin.cases 0 (Fin.cases 2 Fin.elim0)))
        (Fin.cases
          (Fin.cases 2 (Fin.cases 1 (Fin.cases 3 Fin.elim0)))
          Fin.elim0)))

private def middleWords : Fin 4 → List (Fin 3) :=
  Fin.cases []
    (Fin.cases [0]
      (Fin.cases [1]
        (Fin.cases [0, 1] Fin.elim0)))

private theorem middleGenerator_source (j : Fin 3) :
    degreeTwoSixPairAction023CheckedLiteral.stateGenerators stateMiddle j =
      PrimitiveAffineDegreeTwoSixPairAction023ClassPilot.originalEquiv (middleSourceGenerator j) := by
  fin_cases j
  · change PrimitiveAffineDegreeTwoSixPairAction023CatalogueRow.stateGenerators 1 0 =
      PrimitiveAffineDegreeTwoSixPairAction023ClassPilot.originalEquiv (middleSourceGenerator 0)
    exact congrArg PrimitiveAffineDegreeTwoSixPairAction023ClassPilot.originalEquiv (by native_decide)
  · change PrimitiveAffineDegreeTwoSixPairAction023CatalogueRow.stateGenerators 1 1 =
      PrimitiveAffineDegreeTwoSixPairAction023ClassPilot.originalEquiv (middleSourceGenerator 1)
    exact congrArg PrimitiveAffineDegreeTwoSixPairAction023ClassPilot.originalEquiv (by native_decide)
  · change PrimitiveAffineDegreeTwoSixPairAction023CatalogueRow.stateGenerators 1 2 =
      PrimitiveAffineDegreeTwoSixPairAction023ClassPilot.originalEquiv (middleSourceGenerator 2)
    exact congrArg PrimitiveAffineDegreeTwoSixPairAction023ClassPilot.originalEquiv (by native_decide)

private theorem middleSource_identity : middleSourceElement 0 = 1 := by
  native_decide

private theorem middleSource_next (i : Fin 4) (j : Fin 3) :
    middleSourceElement (middleNext i j) =
      middleSourceElement i * middleSourceGenerator j := by
  fin_cases i <;> fin_cases j <;> native_decide

private theorem middleSource_words (i : Fin 4) :
    middleSourceElement i =
      ((middleWords i).map middleSourceGenerator).prod := by
  fin_cases i <;> native_decide

private theorem middleSource_injective :
    Function.Injective middleSourceElement := by
  native_decide

private noncomputable def middleElements (i : Fin 4) : Original :=
  PrimitiveAffineDegreeTwoSixPairAction023ClassPilot.originalEquiv (middleSourceElement i)

private theorem middleWord_map (w : List (Fin 3)) :
    PrimitiveAffineDegreeTwoSixPairAction023ClassPilot.originalEquiv
        ((w.map middleSourceGenerator).prod) =
      (w.map
        (degreeTwoSixPairAction023CheckedLiteral.stateGenerators
          stateMiddle)).prod := by
  induction w with
  | nil =>
      simpa only [List.map_nil, List.prod_nil] using
        map_one
          PrimitiveAffineDegreeTwoSixPairAction023ClassPilot.originalEquiv
  | cons j w ih =>
      change
        PrimitiveAffineDegreeTwoSixPairAction023ClassPilot.originalEquiv
            (middleSourceGenerator j *
              ((w.map middleSourceGenerator).prod)) =
          degreeTwoSixPairAction023CheckedLiteral.stateGenerators
              stateMiddle j *
            ((w.map
              (degreeTwoSixPairAction023CheckedLiteral.stateGenerators
                stateMiddle)).prod)
      rw [PrimitiveAffineDegreeTwoSixPairAction023ClassPilot.originalEquiv.map_mul, ← middleGenerator_source j, ih]
      rfl

private noncomputable def middleCertificate :
    FiniteCayleyCertificate
      (degreeTwoSixPairAction023CheckedLiteral.stateGenerators stateMiddle) 4
    where
  elements := middleElements
  identity := 0
  identity_eq := by
    calc
      middleElements 0 = PrimitiveAffineDegreeTwoSixPairAction023ClassPilot.originalEquiv 1 :=
        congrArg PrimitiveAffineDegreeTwoSixPairAction023ClassPilot.originalEquiv middleSource_identity
      _ = 1 := map_one PrimitiveAffineDegreeTwoSixPairAction023ClassPilot.originalEquiv
  next := middleNext
  next_eq := by
    intro i j
    rw [middleGenerator_source]
    change
      PrimitiveAffineDegreeTwoSixPairAction023ClassPilot.originalEquiv
          (middleSourceElement (middleNext i j)) =
        PrimitiveAffineDegreeTwoSixPairAction023ClassPilot.originalEquiv
            (middleSourceElement i) *
          PrimitiveAffineDegreeTwoSixPairAction023ClassPilot.originalEquiv
            (middleSourceGenerator j)
    rw [← PrimitiveAffineDegreeTwoSixPairAction023ClassPilot.originalEquiv.map_mul]
    exact congrArg PrimitiveAffineDegreeTwoSixPairAction023ClassPilot.originalEquiv (middleSource_next i j)
  words := middleWords
  words_eq := by
    intro i
    calc
      middleElements i =
          PrimitiveAffineDegreeTwoSixPairAction023ClassPilot.originalEquiv
            (((middleWords i).map middleSourceGenerator).prod) :=
        congrArg PrimitiveAffineDegreeTwoSixPairAction023ClassPilot.originalEquiv (middleSource_words i)
      _ = ((middleWords i).map
            (degreeTwoSixPairAction023CheckedLiteral.stateGenerators
              stateMiddle)).prod := middleWord_map (middleWords i)

private theorem middleElements_injective :
    Function.Injective middleElements :=
  PrimitiveAffineDegreeTwoSixPairAction023ClassPilot.originalEquiv.injective.comp middleSource_injective

theorem middleCard :
    Nat.card
      ((degreeTwoSixPairAction023CheckedLiteral.normalStateIndex
        stateMiddle).1) = 4 := by
  change Nat.card
    (Subgroup.closure
      (Set.range
        (degreeTwoSixPairAction023CheckedLiteral.stateGenerators
          stateMiddle))) = 4
  exact middleCertificate.card_closure middleElements_injective

theorem middleGenerator_ne_one :
    degreeTwoSixPairAction023CheckedLiteral.stateGenerators
      stateMiddle genZero ≠ 1 := by
  rw [middleGenerator_source]
  intro h
  have hsource : middleSourceGenerator genZero = 1 := by
    apply PrimitiveAffineDegreeTwoSixPairAction023ClassPilot.originalEquiv.injective
    simpa only [map_one] using h
  exact (by native_decide : middleSourceGenerator genZero ≠ 1) hsource

theorem middleGenerator_mem :
    degreeTwoSixPairAction023CheckedLiteral.stateGenerators
        stateMiddle genZero ∈
      (degreeTwoSixPairAction023CheckedLiteral.normalStateIndex
        stateMiddle).1 := by
  exact Subgroup.subset_closure (Set.mem_range_self genZero)

theorem middle_ne_bot :
    (degreeTwoSixPairAction023CheckedLiteral.normalStateIndex stateMiddle).1 ≠
      ⊥ := by
  intro h
  apply middleGenerator_ne_one
  apply Subgroup.mem_bot.mp
  rw [← h]
  exact middleGenerator_mem

end PrimitiveAffineDegreeTwoSixPairAction023OneGeneralSplit
end SymmetricSubgroupAsymptotics

end
