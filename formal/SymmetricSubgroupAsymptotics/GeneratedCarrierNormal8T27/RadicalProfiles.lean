import SymmetricSubgroupAsymptotics.GeneratedCarrierNormal8T27.Registry
import SymmetricSubgroupAsymptotics.GeneratedCarrierNormal8T27.Radicals
import SymmetricSubgroupAsymptotics.RelativeAmbientTransport

/-! Actual J head, order, and second-radical-head bindings for every original normal.
Generated only by export_lean_carrier_j_radicals.py. All finite equations
are kernel checked; no stored numerical carrier profile is a premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.BinaryCarrierNormal8T27
local instance radicalProfilesSourceGroup : Group Source := BinaryMenuCayley8T27.group

def radicalIndex (i : Fin 13) : Fin 13 :=
  ((if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 0 else (if i.val < 2 then 0 else 1)) else (if i.val < 4 then 2 else (if i.val < 5 then 2 else 4))) else (if i.val < 9 then (if i.val < 7 then 4 else (if i.val < 8 then 2 else 2)) else (if i.val < 11 then (if i.val < 10 then 8 else 4) else (if i.val < 12 then 8 else 8)))) : Fin 13)

def headRank (i : Fin 13) : ℕ := (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 0 else (if i.val < 2 then 1 else 1)) else (if i.val < 4 then 1 else (if i.val < 5 then 1 else 1))) else (if i.val < 9 then (if i.val < 7 then 1 else (if i.val < 8 then 1 else 2)) else (if i.val < 11 then (if i.val < 10 then 1 else 2) else (if i.val < 12 then 1 else 2))))
def orderLog (i : Fin 13) : ℕ := (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 0 else (if i.val < 2 then 1 else 2)) else (if i.val < 4 then 3 else (if i.val < 5 then 3 else 4))) else (if i.val < 9 then (if i.val < 7 then 4 else (if i.val < 8 then 3 else 4)) else (if i.val < 11 then (if i.val < 10 then 5 else 5) else (if i.val < 12 then 5 else 6))))

theorem state_radical_eq (i : Fin 13) :
    primeRelativeRadical 2 (states i).kernel = (states (radicalIndex i)).kernel := by
  fin_cases i
  · exact RadicalN0.radical_eq
  · exact RadicalN1.radical_eq
  · exact RadicalN2.radical_eq
  · exact RadicalN3.radical_eq
  · exact RadicalN4.radical_eq
  · exact RadicalN5.radical_eq
  · exact RadicalN6.radical_eq
  · exact RadicalN7.radical_eq
  · exact RadicalN8.radical_eq
  · exact RadicalN9.radical_eq
  · exact RadicalN10.radical_eq
  · exact RadicalN11.radical_eq
  · exact RadicalN12.radical_eq

theorem state_head_eq (i : Fin 13) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 (states i).kernel) = headRank i := by
  fin_cases i
  · exact RadicalN0.head_eq
  · exact RadicalN1.head_eq
  · exact RadicalN2.head_eq
  · exact RadicalN3.head_eq
  · exact RadicalN4.head_eq
  · exact RadicalN5.head_eq
  · exact RadicalN6.head_eq
  · exact RadicalN7.head_eq
  · exact RadicalN8.head_eq
  · exact RadicalN9.head_eq
  · exact RadicalN10.head_eq
  · exact RadicalN11.head_eq
  · exact RadicalN12.head_eq

theorem state_card (i : Fin 13) : Nat.card (states i).kernel = 2 ^ orderLog i := by
  fin_cases i
  · exact N0.kernel_card
  · exact N1.kernel_card
  · exact N2.kernel_card
  · exact N3.kernel_card
  · exact N4.kernel_card
  · exact N5.kernel_card
  · exact N6.kernel_card
  · exact N7.kernel_card
  · exact N8.kernel_card
  · exact N9.kernel_card
  · exact N10.kernel_card
  · exact N11.kernel_card
  · exact N12.kernel_card

/-- The second head uses the radical as a normal of the SAME original Source. -/
theorem state_radical_head_eq (i : Fin 13) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2
      (primeRelativeRadical 2 (states i).kernel)) = headRank (radicalIndex i) :=
  (primeRelativeHead_eq_of_subgroup_eq 2 _ _ (state_radical_eq i)).trans
    (state_head_eq (radicalIndex i))

abbrev Original := Subgroup.closure (Set.range BinaryMenuCayley8T27.generators)

def originalKernel (i : Fin 13) : Subgroup Original :=
  (states i).kernel.map BinaryMenuCayley8T27.originalEquiv.toMonoidHom

instance originalKernel_normal (i : Fin 13) : (originalKernel i).Normal :=
  Subgroup.Normal.map inferInstance _ BinaryMenuCayley8T27.originalEquiv.surjective

theorem original_radical_eq (i : Fin 13) :
    primeRelativeRadical 2 (originalKernel i) = originalKernel (radicalIndex i) := by
  letI : ((states i).kernel.map BinaryMenuCayley8T27.originalEquiv.toMonoidHom).Normal :=
    originalKernel_normal i
  exact (primeRelativeRadical_map_equiv 2 BinaryMenuCayley8T27.originalEquiv
    (states i).kernel).symm.trans
      (congrArg (fun K : Subgroup Source =>
        K.map BinaryMenuCayley8T27.originalEquiv.toMonoidHom) (state_radical_eq i))

theorem original_head_eq (i : Fin 13) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 (originalKernel i)) = headRank i :=
  (relativeCharacterAmbientCongr 2 BinaryMenuCayley8T27.originalEquiv
    (states i).kernel (originalKernel i) rfl).finrank_eq.trans (state_head_eq i)

theorem original_card (i : Fin 13) : Nat.card (originalKernel i) = 2 ^ orderLog i :=
  (Nat.card_congr (normalAmbientEquiv BinaryMenuCayley8T27.originalEquiv
    (states i).kernel (originalKernel i) rfl).toEquiv).symm.trans (state_card i)

theorem original_radical_head_eq (i : Fin 13) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2
      (primeRelativeRadical 2 (originalKernel i))) = headRank (radicalIndex i) :=
  (primeRelativeHead_eq_of_subgroup_eq 2 _ _ (original_radical_eq i)).trans
    (original_head_eq (radicalIndex i))

private theorem radical_congr (N R : Subgroup Original) [N.Normal] [R.Normal] (h : N = R) :
    primeRelativeRadical 2 N = primeRelativeRadical 2 R := by
  subst R
  rfl

theorem original_second_radical_eq (i : Fin 13) :
    primeRelativeRadical 2 (primeRelativeRadical 2 (originalKernel i)) =
      originalKernel (radicalIndex (radicalIndex i)) :=
  (radical_congr _ _ (original_radical_eq i)).trans (original_radical_eq (radicalIndex i))

/-- Exhaustive binding uses the accepted original-normal registry, not
the stored profile fields. The maximum head m and quotient fields c,g
remain separate obligations. In particular no inequality a2 ≤ m is used. -/
theorem complete_original_radical_profiles (N : Subgroup Original) [N.Normal] :
    ∃ i : Fin 13, originalKernel i = N ∧
      primeRelativeRadical 2 N = originalKernel (radicalIndex i) ∧
      primeRelativeRadical 2 (primeRelativeRadical 2 N) =
        originalKernel (radicalIndex (radicalIndex i)) ∧
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) = headRank i ∧
      Nat.card N = 2 ^ orderLog i ∧
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 (primeRelativeRadical 2 N)) =
        headRank (radicalIndex i) := by
  obtain ⟨i, hi⟩ := complete_original N
  change originalKernel i = N at hi
  subst N
  exact ⟨i, rfl, original_radical_eq i, original_second_radical_eq i,
    original_head_eq i, original_card i, original_radical_head_eq i⟩

end SymmetricSubgroupAsymptotics.BinaryCarrierNormal8T27
