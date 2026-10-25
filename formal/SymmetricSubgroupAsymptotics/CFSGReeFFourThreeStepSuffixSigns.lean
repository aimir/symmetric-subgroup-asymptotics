import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWeylPositivePartMonotonicity
import SymmetricSubgroupAsymptotics.CFSGReeFFourInversionPeelingWords
import SymmetricSubgroupAsymptotics.CFSGE6FiniteRootMenu

/-! A selected three-step reduced-word sign check, in both relative
orientations. The existing complete integral E6 root menu supplies
coverage. Only integer root vectors are evaluated; no group elements
or coefficient-field actions are enumerated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourThreeStepSuffixSigns
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoCoordinatePositiveRootGenerators CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoCoordinateWeylIntersectionFactor CFSGNormTwoCoordinateFiniteRootMenu
open CFSGNormTwoCoordinateWeylPositivePartMonotonicity
open CFSGReeFFourInversionPeelingWords
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local instance : DecidableEq (Roots A) := Classical.decEq _

private def vectorWord : List (Fin 6) → (Fin 6 → ℤ) → (Fin 6 → ℤ)
  | [], x => x
  | i :: w, x => vectorWord w x -
      integerPairing A (vectorWord w x) (Pi.single i 1) • Pi.single i 1

private theorem wordRoot_val_eq (w : List (Fin 6)) (k : Roots A) :
    (wordRoot A hs hp b₀ s₀ w k).val = vectorWord w k.val := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change ((rootPairing A hs hp).reflectionPerm (s₀ i)
      (wordRoot A hs hp b₀ s₀ w k)).val = _
    rw [CFSGNormTwoGeckSignedRootColumns.reflection_val, ih]
    rfl

private theorem selected_suffix_certificate :
    ∀ head : Bool, ∀ x ∈ CFSGE6FiniteRootMenu.menu,
      (∀ j, 0 ≤ x j) →
      (∀ j, 0 ≤ vectorWord (suffixWord head 3 3) x j) →
      ∀ k : Fin 4, ∀ j, 0 ≤ vectorWord (suffixWord head 3 k.val) x j := by
  decide +kernel

theorem three_step_suffix_positive (head : Bool) (k : Fin 4) (a : PositiveRoot A)
    (ha : ∀ j, 0 ≤ (wordRoot A hs hp b₀ s₀ (suffixWord head 3 3) a.val).val j) :
    ∀ j, 0 ≤ (wordRoot A hs hp b₀ s₀ (suffixWord head 3 k.val) a.val).val j := by
  have hm : a.val.val ∈ CFSGE6FiniteRootMenu.menu :=
    root_mem_menu A hd hs hp ho CFSGE6FiniteRootMenu.menu
      CFSGE6FiniteRootMenu.negative_simple_mem CFSGE6FiniteRootMenu.reflection_closed a.val
  rw [wordRoot_val_eq] at ha ⊢
  exact selected_suffix_certificate head a.val.val hm a.property ha k

theorem three_step_positive_part_le (K : Type) [Field K] [Finite K]
    (head : Bool) (k : Fin 4) :
    wordSignPart A hd hs hp ho K (suffixWord head 3 3) false ≤
      wordSignPart A hd hs hp ho K (suffixWord head 3 k.val) false :=
  positive_part_le_of_root_implication A hd hs hp ho K
    (suffixWord head 3 3) (suffixWord head 3 k.val)
    (three_step_suffix_positive head k)

end SymmetricSubgroupAsymptotics.CFSGReeFFourThreeStepSuffixSigns
