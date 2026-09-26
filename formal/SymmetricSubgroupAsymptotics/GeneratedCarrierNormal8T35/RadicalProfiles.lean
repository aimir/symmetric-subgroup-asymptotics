import SymmetricSubgroupAsymptotics.GeneratedCarrierNormal8T35.Registry
import SymmetricSubgroupAsymptotics.GeneratedCarrierNormal8T35.Radicals
import SymmetricSubgroupAsymptotics.RelativeAmbientTransport

/-! Actual 8T35 head, order, and second-radical-head bindings for every original normal.
Generated only by export_lean_carrier_profiles_selected.py --stage radicals. All finite equations
are kernel checked; no stored numerical carrier profile is a premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.BinaryCarrierNormal8T35
local instance radicalProfilesSourceGroup : Group Source := BinaryMenuCayley8T35.group

def radicalIndex (i : Fin 28) : Fin 28 :=
  ((if i.val < 14 then (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then 0 else (if i.val < 2 then 0 else 1)) else (if i.val < 5 then (if i.val < 4 then 2 else 2) else (if i.val < 6 then 3 else 3))) else (if i.val < 10 then (if i.val < 8 then 4 else (if i.val < 9 then 4 else 2)) else (if i.val < 12 then (if i.val < 11 then 9 else 9) else (if i.val < 13 then 2 else 12)))) else (if i.val < 21 then (if i.val < 17 then (if i.val < 15 then 3 else (if i.val < 16 then 12 else 9)) else (if i.val < 19 then (if i.val < 18 then 12 else 4) else (if i.val < 20 then 12 else 12))) else (if i.val < 24 then (if i.val < 22 then 12 else (if i.val < 23 then 12 else 12)) else (if i.val < 26 then (if i.val < 25 then 12 else 12) else (if i.val < 27 then 12 else 12))))) : Fin 28)

def headRank (i : Fin 28) : ℕ := (if i.val < 14 then (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then 0 else (if i.val < 2 then 1 else 1)) else (if i.val < 5 then (if i.val < 4 then 1 else 1) else (if i.val < 6 then 1 else 1))) else (if i.val < 10 then (if i.val < 8 then 1 else (if i.val < 9 then 1 else 1)) else (if i.val < 12 then (if i.val < 11 then 1 else 1) else (if i.val < 13 then 2 else 1)))) else (if i.val < 21 then (if i.val < 17 then (if i.val < 15 then 2 else (if i.val < 16 then 1 else 2)) else (if i.val < 19 then (if i.val < 18 then 1 else 2) else (if i.val < 20 then 2 else 2))) else (if i.val < 24 then (if i.val < 22 then 2 else (if i.val < 23 then 2 else 1)) else (if i.val < 26 then (if i.val < 25 then 2 else 2) else (if i.val < 27 then 2 else 3)))))
def orderLog (i : Fin 28) : ℕ := (if i.val < 14 then (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then 0 else (if i.val < 2 then 1 else 2)) else (if i.val < 5 then (if i.val < 4 then 3 else 3) else (if i.val < 6 then 4 else 4))) else (if i.val < 10 then (if i.val < 8 then 4 else (if i.val < 9 then 4 else 3)) else (if i.val < 12 then (if i.val < 11 then 4 else 4) else (if i.val < 13 then 4 else 5)))) else (if i.val < 21 then (if i.val < 17 then (if i.val < 15 then 5 else (if i.val < 16 then 5 else 5)) else (if i.val < 19 then (if i.val < 18 then 5 else 5) else (if i.val < 20 then 6 else 6))) else (if i.val < 24 then (if i.val < 22 then 6 else (if i.val < 23 then 6 else 5)) else (if i.val < 26 then (if i.val < 25 then 6 else 6) else (if i.val < 27 then 6 else 7)))))

theorem state_radical_eq (i : Fin 28) :
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
  · exact RadicalN13.radical_eq
  · exact RadicalN14.radical_eq
  · exact RadicalN15.radical_eq
  · exact RadicalN16.radical_eq
  · exact RadicalN17.radical_eq
  · exact RadicalN18.radical_eq
  · exact RadicalN19.radical_eq
  · exact RadicalN20.radical_eq
  · exact RadicalN21.radical_eq
  · exact RadicalN22.radical_eq
  · exact RadicalN23.radical_eq
  · exact RadicalN24.radical_eq
  · exact RadicalN25.radical_eq
  · exact RadicalN26.radical_eq
  · exact RadicalN27.radical_eq

theorem state_head_eq (i : Fin 28) :
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
  · exact RadicalN13.head_eq
  · exact RadicalN14.head_eq
  · exact RadicalN15.head_eq
  · exact RadicalN16.head_eq
  · exact RadicalN17.head_eq
  · exact RadicalN18.head_eq
  · exact RadicalN19.head_eq
  · exact RadicalN20.head_eq
  · exact RadicalN21.head_eq
  · exact RadicalN22.head_eq
  · exact RadicalN23.head_eq
  · exact RadicalN24.head_eq
  · exact RadicalN25.head_eq
  · exact RadicalN26.head_eq
  · exact RadicalN27.head_eq

theorem state_card (i : Fin 28) : Nat.card (states i).kernel = 2 ^ orderLog i := by
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
  · exact N13.kernel_card
  · exact N14.kernel_card
  · exact N15.kernel_card
  · exact N16.kernel_card
  · exact N17.kernel_card
  · exact N18.kernel_card
  · exact N19.kernel_card
  · exact N20.kernel_card
  · exact N21.kernel_card
  · exact N22.kernel_card
  · exact N23.kernel_card
  · exact N24.kernel_card
  · exact N25.kernel_card
  · exact N26.kernel_card
  · exact N27.kernel_card

/-- The second head uses the radical as a normal of the SAME original Source. -/
theorem state_radical_head_eq (i : Fin 28) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2
      (primeRelativeRadical 2 (states i).kernel)) = headRank (radicalIndex i) :=
  (primeRelativeHead_eq_of_subgroup_eq 2 _ _ (state_radical_eq i)).trans
    (state_head_eq (radicalIndex i))

abbrev Original := Subgroup.closure (Set.range BinaryMenuCayley8T35.generators)

def originalKernel (i : Fin 28) : Subgroup Original :=
  (states i).kernel.map BinaryMenuCayley8T35.originalEquiv.toMonoidHom

instance originalKernel_normal (i : Fin 28) : (originalKernel i).Normal :=
  Subgroup.Normal.map inferInstance _ BinaryMenuCayley8T35.originalEquiv.surjective

theorem original_radical_eq (i : Fin 28) :
    primeRelativeRadical 2 (originalKernel i) = originalKernel (radicalIndex i) := by
  letI : ((states i).kernel.map BinaryMenuCayley8T35.originalEquiv.toMonoidHom).Normal :=
    originalKernel_normal i
  exact (primeRelativeRadical_map_equiv 2 BinaryMenuCayley8T35.originalEquiv
    (states i).kernel).symm.trans
      (congrArg (fun K : Subgroup Source =>
        K.map BinaryMenuCayley8T35.originalEquiv.toMonoidHom) (state_radical_eq i))

theorem original_head_eq (i : Fin 28) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 (originalKernel i)) = headRank i :=
  (relativeCharacterAmbientCongr 2 BinaryMenuCayley8T35.originalEquiv
    (states i).kernel (originalKernel i) rfl).finrank_eq.trans (state_head_eq i)

theorem original_card (i : Fin 28) : Nat.card (originalKernel i) = 2 ^ orderLog i :=
  (Nat.card_congr (normalAmbientEquiv BinaryMenuCayley8T35.originalEquiv
    (states i).kernel (originalKernel i) rfl).toEquiv).symm.trans (state_card i)

theorem original_radical_head_eq (i : Fin 28) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2
      (primeRelativeRadical 2 (originalKernel i))) = headRank (radicalIndex i) :=
  (primeRelativeHead_eq_of_subgroup_eq 2 _ _ (original_radical_eq i)).trans
    (original_head_eq (radicalIndex i))

private theorem radical_congr (N R : Subgroup Original) [N.Normal] [R.Normal] (h : N = R) :
    primeRelativeRadical 2 N = primeRelativeRadical 2 R := by
  subst R
  rfl

theorem original_second_radical_eq (i : Fin 28) :
    primeRelativeRadical 2 (primeRelativeRadical 2 (originalKernel i)) =
      originalKernel (radicalIndex (radicalIndex i)) :=
  (radical_congr _ _ (original_radical_eq i)).trans (original_radical_eq (radicalIndex i))

/-- Exhaustive binding uses the accepted original-normal registry, not
the stored profile fields. The maximum head m and quotient fields c,g
remain separate obligations. In particular no inequality a2 ≤ m is used. -/
theorem complete_original_radical_profiles (N : Subgroup Original) [N.Normal] :
    ∃ i : Fin 28, originalKernel i = N ∧
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

end SymmetricSubgroupAsymptotics.BinaryCarrierNormal8T35
