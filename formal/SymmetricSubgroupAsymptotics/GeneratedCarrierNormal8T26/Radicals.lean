import SymmetricSubgroupAsymptotics.PrimeRelativeRadicalWords
import SymmetricSubgroupAsymptotics.GeneratedCarrierNormal8T26.States

/-! Exact whole-original-group relative radicals of the 27 accepted 8T26 states.
Generated only by export_lean_carrier_profiles_selected.py --stage radicals. All finite equations
are kernel checked; no stored numerical carrier profile is a premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.BinaryCarrierNormal8T26
local instance radicalCertificateSourceGroup : Group Source := BinaryMenuCayley8T26.group

namespace RadicalN0

private def word0 : PrimeRelativeRadicalWord (Fin 3) (Fin 0) :=
  .one

private def radicalWords (j : Fin 0) : PrimeRelativeRadicalWord (Fin 3) (Fin 0) :=
  Fin.elim0 j

private theorem radicalWords_checked : ∀ j : Fin 0,
    (radicalWords j).eval 2 generators N0.normalGenerators = N0.normalGenerators j := by
  intro j
  exact Fin.elim0 j

private def powerRow (j : Fin 0) : Fin 1 := Fin.elim0 j
private def mixedRow (j : Fin 0) (i : Fin 3) : Fin 1 := Fin.elim0 j

private theorem power_checked : ∀ j : Fin 0, N0.normalGenerators j ^ 2 =
    (⟨N0.normalCertificate.rows (powerRow j)⟩ : Source) := by
  intro j
  exact Fin.elim0 j

private theorem mixed_checked : ∀ (j : Fin 0) (i : Fin 3),
    ⁅N0.normalGenerators j, generators i⁆ =
      (⟨N0.normalCertificate.rows (mixedRow j i)⟩ : Source) := by
  intro j
  exact Fin.elim0 j

theorem radical_eq : primeRelativeRadical 2 N0.kernel = N0.kernel := by
  apply primeRelativeRadical_eq_of_generator_words 2 N0.kernel N0.kernel
    generators generators_full N0.normalGenerators rfl N0.normalGenerators rfl
    radicalWords radicalWords_checked
  · intro j
    rw [power_checked]
    exact binaryNormalRow_mem N0.normalCertificate _
  · intro j k
    rw [mixed_checked]
    exact binaryNormalRow_mem N0.normalCertificate _

theorem head_eq : Module.finrank (ZMod 2) (primeRelativeCharacters 2 N0.kernel) = 0 := by
  apply primeRelativeHead_eq_of_radical_card 2 N0.kernel N0.kernel 0 radical_eq
  norm_num [N0.kernel_card, N0.kernel_card]

end RadicalN0

namespace RadicalN1

private def word0 : PrimeRelativeRadicalWord (Fin 3) (Fin 1) :=
  .one

private def radicalWords (j : Fin 0) : PrimeRelativeRadicalWord (Fin 3) (Fin 1) :=
  Fin.elim0 j

private theorem radicalWords_checked : ∀ j : Fin 0,
    (radicalWords j).eval 2 generators N1.normalGenerators = N0.normalGenerators j := by
  intro j
  exact Fin.elim0 j

private def powerRow (j : Fin 1) : Fin 1 := (0 : Fin 1)
private def mixedRow (j : Fin 1) (i : Fin 3) : Fin 1 := (#[0,0,0] : Array (Fin 1))[i.val]!

private theorem power_checked : ∀ j : Fin 1, N1.normalGenerators j ^ 2 =
    (⟨N0.normalCertificate.rows (powerRow j)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

private theorem mixed_checked : ∀ (j : Fin 1) (i : Fin 3),
    ⁅N1.normalGenerators j, generators i⁆ =
      (⟨N0.normalCertificate.rows (mixedRow j i)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

theorem radical_eq : primeRelativeRadical 2 N1.kernel = N0.kernel := by
  apply primeRelativeRadical_eq_of_generator_words 2 N1.kernel N0.kernel
    generators generators_full N1.normalGenerators rfl N0.normalGenerators rfl
    radicalWords radicalWords_checked
  · intro j
    rw [power_checked]
    exact binaryNormalRow_mem N0.normalCertificate _
  · intro j k
    rw [mixed_checked]
    exact binaryNormalRow_mem N0.normalCertificate _

theorem head_eq : Module.finrank (ZMod 2) (primeRelativeCharacters 2 N1.kernel) = 1 := by
  apply primeRelativeHead_eq_of_radical_card 2 N1.kernel N0.kernel 1 radical_eq
  norm_num [N1.kernel_card, N0.kernel_card]

end RadicalN1

namespace RadicalN2

private def word0 : PrimeRelativeRadicalWord (Fin 3) (Fin 1) :=
  .one
private def word1 : PrimeRelativeRadicalWord (Fin 3) (Fin 1) :=
  .power 0

private def radicalWords (j : Fin 1) : PrimeRelativeRadicalWord (Fin 3) (Fin 1) :=
  word1

private theorem radicalWords_checked : ∀ j : Fin 1,
    (radicalWords j).eval 2 generators N2.normalGenerators = N1.normalGenerators j := by
  intro j
  fin_cases j <;> decide +kernel

private def powerRow (j : Fin 1) : Fin 2 := (0 : Fin 2)
private def mixedRow (j : Fin 1) (i : Fin 3) : Fin 2 := (#[0,0,0] : Array (Fin 2))[i.val]!

private theorem power_checked : ∀ j : Fin 1, N2.normalGenerators j ^ 2 =
    (⟨N1.normalCertificate.rows (powerRow j)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

private theorem mixed_checked : ∀ (j : Fin 1) (i : Fin 3),
    ⁅N2.normalGenerators j, generators i⁆ =
      (⟨N1.normalCertificate.rows (mixedRow j i)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

theorem radical_eq : primeRelativeRadical 2 N2.kernel = N1.kernel := by
  apply primeRelativeRadical_eq_of_generator_words 2 N2.kernel N1.kernel
    generators generators_full N2.normalGenerators rfl N1.normalGenerators rfl
    radicalWords radicalWords_checked
  · intro j
    rw [power_checked]
    exact binaryNormalRow_mem N1.normalCertificate _
  · intro j k
    rw [mixed_checked]
    exact binaryNormalRow_mem N1.normalCertificate _

theorem head_eq : Module.finrank (ZMod 2) (primeRelativeCharacters 2 N2.kernel) = 1 := by
  apply primeRelativeHead_eq_of_radical_card 2 N2.kernel N1.kernel 1 radical_eq
  norm_num [N2.kernel_card, N1.kernel_card]

end RadicalN2

namespace RadicalN3

private def word0 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .one
private def word1 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .mixed 0 0

private def radicalWords (j : Fin 1) : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  word1

private theorem radicalWords_checked : ∀ j : Fin 1,
    (radicalWords j).eval 2 generators N3.normalGenerators = N1.normalGenerators j := by
  intro j
  fin_cases j <;> decide +kernel

private def powerRow (j : Fin 2) : Fin 2 := ((if j.val < 1 then 1 else 1) : Fin 2)
private def mixedRow (j : Fin 2) (i : Fin 3) : Fin 2 := ((if j.val < 1 then #[0,1,1] else #[1,1,1]) : Array (Fin 2))[i.val]!

private theorem power_checked : ∀ j : Fin 2, N3.normalGenerators j ^ 2 =
    (⟨N1.normalCertificate.rows (powerRow j)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

private theorem mixed_checked : ∀ (j : Fin 2) (i : Fin 3),
    ⁅N3.normalGenerators j, generators i⁆ =
      (⟨N1.normalCertificate.rows (mixedRow j i)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

theorem radical_eq : primeRelativeRadical 2 N3.kernel = N1.kernel := by
  apply primeRelativeRadical_eq_of_generator_words 2 N3.kernel N1.kernel
    generators generators_full N3.normalGenerators rfl N1.normalGenerators rfl
    radicalWords radicalWords_checked
  · intro j
    rw [power_checked]
    exact binaryNormalRow_mem N1.normalCertificate _
  · intro j k
    rw [mixed_checked]
    exact binaryNormalRow_mem N1.normalCertificate _

theorem head_eq : Module.finrank (ZMod 2) (primeRelativeCharacters 2 N3.kernel) = 1 := by
  apply primeRelativeHead_eq_of_radical_card 2 N3.kernel N1.kernel 1 radical_eq
  norm_num [N3.kernel_card, N1.kernel_card]

end RadicalN3

namespace RadicalN4

private def word0 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .one
private def word1 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .power 0
private def word2 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .mixed 1 0
private def word3 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .mul word1 word2

private def radicalWords (j : Fin 1) : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  word3

private theorem radicalWords_checked : ∀ j : Fin 1,
    (radicalWords j).eval 2 generators N4.normalGenerators = N2.normalGenerators j := by
  intro j
  fin_cases j <;> decide +kernel

private def powerRow (j : Fin 2) : Fin 4 := ((if j.val < 1 then 1 else 1) : Fin 4)
private def mixedRow (j : Fin 2) (i : Fin 3) : Fin 4 := ((if j.val < 1 then #[1,1,1] else #[0,3,0]) : Array (Fin 4))[i.val]!

private theorem power_checked : ∀ j : Fin 2, N4.normalGenerators j ^ 2 =
    (⟨N2.normalCertificate.rows (powerRow j)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

private theorem mixed_checked : ∀ (j : Fin 2) (i : Fin 3),
    ⁅N4.normalGenerators j, generators i⁆ =
      (⟨N2.normalCertificate.rows (mixedRow j i)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

theorem radical_eq : primeRelativeRadical 2 N4.kernel = N2.kernel := by
  apply primeRelativeRadical_eq_of_generator_words 2 N4.kernel N2.kernel
    generators generators_full N4.normalGenerators rfl N2.normalGenerators rfl
    radicalWords radicalWords_checked
  · intro j
    rw [power_checked]
    exact binaryNormalRow_mem N2.normalCertificate _
  · intro j k
    rw [mixed_checked]
    exact binaryNormalRow_mem N2.normalCertificate _

theorem head_eq : Module.finrank (ZMod 2) (primeRelativeCharacters 2 N4.kernel) = 1 := by
  apply primeRelativeHead_eq_of_radical_card 2 N4.kernel N2.kernel 1 radical_eq
  norm_num [N4.kernel_card, N2.kernel_card]

end RadicalN4

namespace RadicalN5

private def word0 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .one
private def word1 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .power 0
private def word2 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .mixed 1 0
private def word3 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .mixed 1 2

private def radicalWords (j : Fin 1) : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  word3

private theorem radicalWords_checked : ∀ j : Fin 1,
    (radicalWords j).eval 2 generators N5.normalGenerators = N2.normalGenerators j := by
  intro j
  fin_cases j <;> decide +kernel

private def powerRow (j : Fin 2) : Fin 4 := ((if j.val < 1 then 1 else 3) : Fin 4)
private def mixedRow (j : Fin 2) (i : Fin 3) : Fin 4 := ((if j.val < 1 then #[1,1,1] else #[0,1,2]) : Array (Fin 4))[i.val]!

private theorem power_checked : ∀ j : Fin 2, N5.normalGenerators j ^ 2 =
    (⟨N2.normalCertificate.rows (powerRow j)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

private theorem mixed_checked : ∀ (j : Fin 2) (i : Fin 3),
    ⁅N5.normalGenerators j, generators i⁆ =
      (⟨N2.normalCertificate.rows (mixedRow j i)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

theorem radical_eq : primeRelativeRadical 2 N5.kernel = N2.kernel := by
  apply primeRelativeRadical_eq_of_generator_words 2 N5.kernel N2.kernel
    generators generators_full N5.normalGenerators rfl N2.normalGenerators rfl
    radicalWords radicalWords_checked
  · intro j
    rw [power_checked]
    exact binaryNormalRow_mem N2.normalCertificate _
  · intro j k
    rw [mixed_checked]
    exact binaryNormalRow_mem N2.normalCertificate _

theorem head_eq : Module.finrank (ZMod 2) (primeRelativeCharacters 2 N5.kernel) = 1 := by
  apply primeRelativeHead_eq_of_radical_card 2 N5.kernel N2.kernel 1 radical_eq
  norm_num [N5.kernel_card, N2.kernel_card]

end RadicalN5

namespace RadicalN6

private def word0 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .one
private def word1 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mixed 0 0
private def word2 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mixed 1 0
private def word3 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mixed 1 2

private def radicalWords (j : Fin 2) : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  (if j.val < 1 then word3 else word1)

private theorem radicalWords_checked : ∀ j : Fin 2,
    (radicalWords j).eval 2 generators N6.normalGenerators = N3.normalGenerators j := by
  intro j
  fin_cases j <;> decide +kernel

private def powerRow (j : Fin 3) : Fin 4 := ((if j.val < 1 then 3 else (if j.val < 2 then 3 else 3)) : Fin 4)
private def mixedRow (j : Fin 3) (i : Fin 3) : Fin 4 := ((if j.val < 1 then #[0,3,3] else (if j.val < 2 then #[2,0,1] else #[3,3,3])) : Array (Fin 4))[i.val]!

private theorem power_checked : ∀ j : Fin 3, N6.normalGenerators j ^ 2 =
    (⟨N3.normalCertificate.rows (powerRow j)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

private theorem mixed_checked : ∀ (j : Fin 3) (i : Fin 3),
    ⁅N6.normalGenerators j, generators i⁆ =
      (⟨N3.normalCertificate.rows (mixedRow j i)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

theorem radical_eq : primeRelativeRadical 2 N6.kernel = N3.kernel := by
  apply primeRelativeRadical_eq_of_generator_words 2 N6.kernel N3.kernel
    generators generators_full N6.normalGenerators rfl N3.normalGenerators rfl
    radicalWords radicalWords_checked
  · intro j
    rw [power_checked]
    exact binaryNormalRow_mem N3.normalCertificate _
  · intro j k
    rw [mixed_checked]
    exact binaryNormalRow_mem N3.normalCertificate _

theorem head_eq : Module.finrank (ZMod 2) (primeRelativeCharacters 2 N6.kernel) = 1 := by
  apply primeRelativeHead_eq_of_radical_card 2 N6.kernel N3.kernel 1 radical_eq
  norm_num [N6.kernel_card, N3.kernel_card]

end RadicalN6

namespace RadicalN7

private def word0 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .one
private def word1 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mixed 0 0
private def word2 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mixed 1 0
private def word3 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mul word1 word2

private def radicalWords (j : Fin 2) : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  (if j.val < 1 then word3 else word2)

private theorem radicalWords_checked : ∀ j : Fin 2,
    (radicalWords j).eval 2 generators N7.normalGenerators = N3.normalGenerators j := by
  intro j
  fin_cases j <;> decide +kernel

private def powerRow (j : Fin 3) : Fin 4 := ((if j.val < 1 then 3 else (if j.val < 2 then 3 else 3)) : Fin 4)
private def mixedRow (j : Fin 3) (i : Fin 3) : Fin 4 := ((if j.val < 1 then #[2,3,2] else (if j.val < 2 then #[0,3,3] else #[3,3,3])) : Array (Fin 4))[i.val]!

private theorem power_checked : ∀ j : Fin 3, N7.normalGenerators j ^ 2 =
    (⟨N3.normalCertificate.rows (powerRow j)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

private theorem mixed_checked : ∀ (j : Fin 3) (i : Fin 3),
    ⁅N7.normalGenerators j, generators i⁆ =
      (⟨N3.normalCertificate.rows (mixedRow j i)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

theorem radical_eq : primeRelativeRadical 2 N7.kernel = N3.kernel := by
  apply primeRelativeRadical_eq_of_generator_words 2 N7.kernel N3.kernel
    generators generators_full N7.normalGenerators rfl N3.normalGenerators rfl
    radicalWords radicalWords_checked
  · intro j
    rw [power_checked]
    exact binaryNormalRow_mem N3.normalCertificate _
  · intro j k
    rw [mixed_checked]
    exact binaryNormalRow_mem N3.normalCertificate _

theorem head_eq : Module.finrank (ZMod 2) (primeRelativeCharacters 2 N7.kernel) = 1 := by
  apply primeRelativeHead_eq_of_radical_card 2 N7.kernel N3.kernel 1 radical_eq
  norm_num [N7.kernel_card, N3.kernel_card]

end RadicalN7

namespace RadicalN8

private def word0 : PrimeRelativeRadicalWord (Fin 3) (Fin 1) :=
  .one
private def word1 : PrimeRelativeRadicalWord (Fin 3) (Fin 1) :=
  .power 0

private def radicalWords (j : Fin 1) : PrimeRelativeRadicalWord (Fin 3) (Fin 1) :=
  word1

private theorem radicalWords_checked : ∀ j : Fin 1,
    (radicalWords j).eval 2 generators N8.normalGenerators = N1.normalGenerators j := by
  intro j
  fin_cases j <;> decide +kernel

private def powerRow (j : Fin 1) : Fin 2 := (0 : Fin 2)
private def mixedRow (j : Fin 1) (i : Fin 3) : Fin 2 := (#[1,0,0] : Array (Fin 2))[i.val]!

private theorem power_checked : ∀ j : Fin 1, N8.normalGenerators j ^ 2 =
    (⟨N1.normalCertificate.rows (powerRow j)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

private theorem mixed_checked : ∀ (j : Fin 1) (i : Fin 3),
    ⁅N8.normalGenerators j, generators i⁆ =
      (⟨N1.normalCertificate.rows (mixedRow j i)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

theorem radical_eq : primeRelativeRadical 2 N8.kernel = N1.kernel := by
  apply primeRelativeRadical_eq_of_generator_words 2 N8.kernel N1.kernel
    generators generators_full N8.normalGenerators rfl N1.normalGenerators rfl
    radicalWords radicalWords_checked
  · intro j
    rw [power_checked]
    exact binaryNormalRow_mem N1.normalCertificate _
  · intro j k
    rw [mixed_checked]
    exact binaryNormalRow_mem N1.normalCertificate _

theorem head_eq : Module.finrank (ZMod 2) (primeRelativeCharacters 2 N8.kernel) = 1 := by
  apply primeRelativeHead_eq_of_radical_card 2 N8.kernel N1.kernel 1 radical_eq
  norm_num [N8.kernel_card, N1.kernel_card]

end RadicalN8

namespace RadicalN9

private def word0 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .one
private def word1 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .power 0
private def word2 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .mixed 1 0
private def word3 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .mixed 1 2

private def radicalWords (j : Fin 1) : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  word3

private theorem radicalWords_checked : ∀ j : Fin 1,
    (radicalWords j).eval 2 generators N9.normalGenerators = N8.normalGenerators j := by
  intro j
  fin_cases j <;> decide +kernel

private def powerRow (j : Fin 2) : Fin 4 := ((if j.val < 1 then 1 else 3) : Fin 4)
private def mixedRow (j : Fin 2) (i : Fin 3) : Fin 4 := ((if j.val < 1 then #[3,1,1] else #[2,1,0]) : Array (Fin 4))[i.val]!

private theorem power_checked : ∀ j : Fin 2, N9.normalGenerators j ^ 2 =
    (⟨N8.normalCertificate.rows (powerRow j)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

private theorem mixed_checked : ∀ (j : Fin 2) (i : Fin 3),
    ⁅N9.normalGenerators j, generators i⁆ =
      (⟨N8.normalCertificate.rows (mixedRow j i)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

theorem radical_eq : primeRelativeRadical 2 N9.kernel = N8.kernel := by
  apply primeRelativeRadical_eq_of_generator_words 2 N9.kernel N8.kernel
    generators generators_full N9.normalGenerators rfl N8.normalGenerators rfl
    radicalWords radicalWords_checked
  · intro j
    rw [power_checked]
    exact binaryNormalRow_mem N8.normalCertificate _
  · intro j k
    rw [mixed_checked]
    exact binaryNormalRow_mem N8.normalCertificate _

theorem head_eq : Module.finrank (ZMod 2) (primeRelativeCharacters 2 N9.kernel) = 1 := by
  apply primeRelativeHead_eq_of_radical_card 2 N9.kernel N8.kernel 1 radical_eq
  norm_num [N9.kernel_card, N8.kernel_card]

end RadicalN9

namespace RadicalN10

private def word0 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .one
private def word1 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .power 0
private def word2 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .mixed 0 0
private def word3 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .mul word1 word2

private def radicalWords (j : Fin 1) : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  word2

private theorem radicalWords_checked : ∀ j : Fin 1,
    (radicalWords j).eval 2 generators N10.normalGenerators = N8.normalGenerators j := by
  intro j
  fin_cases j <;> decide +kernel

private def powerRow (j : Fin 2) : Fin 4 := ((if j.val < 1 then 1 else 1) : Fin 4)
private def mixedRow (j : Fin 2) (i : Fin 3) : Fin 4 := ((if j.val < 1 then #[0,1,0] else #[3,1,1]) : Array (Fin 4))[i.val]!

private theorem power_checked : ∀ j : Fin 2, N10.normalGenerators j ^ 2 =
    (⟨N8.normalCertificate.rows (powerRow j)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

private theorem mixed_checked : ∀ (j : Fin 2) (i : Fin 3),
    ⁅N10.normalGenerators j, generators i⁆ =
      (⟨N8.normalCertificate.rows (mixedRow j i)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

theorem radical_eq : primeRelativeRadical 2 N10.kernel = N8.kernel := by
  apply primeRelativeRadical_eq_of_generator_words 2 N10.kernel N8.kernel
    generators generators_full N10.normalGenerators rfl N8.normalGenerators rfl
    radicalWords radicalWords_checked
  · intro j
    rw [power_checked]
    exact binaryNormalRow_mem N8.normalCertificate _
  · intro j k
    rw [mixed_checked]
    exact binaryNormalRow_mem N8.normalCertificate _

theorem head_eq : Module.finrank (ZMod 2) (primeRelativeCharacters 2 N10.kernel) = 1 := by
  apply primeRelativeHead_eq_of_radical_card 2 N10.kernel N8.kernel 1 radical_eq
  norm_num [N10.kernel_card, N8.kernel_card]

end RadicalN10

namespace RadicalN11

private def word0 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .one
private def word1 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .power 0

private def radicalWords (j : Fin 1) : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  word1

private theorem radicalWords_checked : ∀ j : Fin 1,
    (radicalWords j).eval 2 generators N11.normalGenerators = N1.normalGenerators j := by
  intro j
  fin_cases j <;> decide +kernel

private def powerRow (j : Fin 2) : Fin 2 := ((if j.val < 1 then 0 else 0) : Fin 2)
private def mixedRow (j : Fin 2) (i : Fin 3) : Fin 2 := ((if j.val < 1 then #[1,0,0] else #[0,0,0]) : Array (Fin 2))[i.val]!

private theorem power_checked : ∀ j : Fin 2, N11.normalGenerators j ^ 2 =
    (⟨N1.normalCertificate.rows (powerRow j)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

private theorem mixed_checked : ∀ (j : Fin 2) (i : Fin 3),
    ⁅N11.normalGenerators j, generators i⁆ =
      (⟨N1.normalCertificate.rows (mixedRow j i)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

theorem radical_eq : primeRelativeRadical 2 N11.kernel = N1.kernel := by
  apply primeRelativeRadical_eq_of_generator_words 2 N11.kernel N1.kernel
    generators generators_full N11.normalGenerators rfl N1.normalGenerators rfl
    radicalWords radicalWords_checked
  · intro j
    rw [power_checked]
    exact binaryNormalRow_mem N1.normalCertificate _
  · intro j k
    rw [mixed_checked]
    exact binaryNormalRow_mem N1.normalCertificate _

theorem head_eq : Module.finrank (ZMod 2) (primeRelativeCharacters 2 N11.kernel) = 2 := by
  apply primeRelativeHead_eq_of_radical_card 2 N11.kernel N1.kernel 2 radical_eq
  norm_num [N11.kernel_card, N1.kernel_card]

end RadicalN11

namespace RadicalN12

private def word0 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .one
private def word1 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .power 0
private def word2 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mixed 2 0
private def word3 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mixed 2 2

private def radicalWords (j : Fin 1) : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  word3

private theorem radicalWords_checked : ∀ j : Fin 1,
    (radicalWords j).eval 2 generators N12.normalGenerators = N2.normalGenerators j := by
  intro j
  fin_cases j <;> decide +kernel

private def powerRow (j : Fin 3) : Fin 4 := ((if j.val < 1 then 1 else (if j.val < 2 then 1 else 3)) : Fin 4)
private def mixedRow (j : Fin 3) (i : Fin 3) : Fin 4 := ((if j.val < 1 then #[3,1,1] else (if j.val < 2 then #[1,1,1] else #[0,1,2])) : Array (Fin 4))[i.val]!

private theorem power_checked : ∀ j : Fin 3, N12.normalGenerators j ^ 2 =
    (⟨N2.normalCertificate.rows (powerRow j)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

private theorem mixed_checked : ∀ (j : Fin 3) (i : Fin 3),
    ⁅N12.normalGenerators j, generators i⁆ =
      (⟨N2.normalCertificate.rows (mixedRow j i)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

theorem radical_eq : primeRelativeRadical 2 N12.kernel = N2.kernel := by
  apply primeRelativeRadical_eq_of_generator_words 2 N12.kernel N2.kernel
    generators generators_full N12.normalGenerators rfl N2.normalGenerators rfl
    radicalWords radicalWords_checked
  · intro j
    rw [power_checked]
    exact binaryNormalRow_mem N2.normalCertificate _
  · intro j k
    rw [mixed_checked]
    exact binaryNormalRow_mem N2.normalCertificate _

theorem head_eq : Module.finrank (ZMod 2) (primeRelativeCharacters 2 N12.kernel) = 2 := by
  apply primeRelativeHead_eq_of_radical_card 2 N12.kernel N2.kernel 2 radical_eq
  norm_num [N12.kernel_card, N2.kernel_card]

end RadicalN12

namespace RadicalN13

private def word0 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .one
private def word1 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .power 0
private def word2 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mixed 0 0
private def word3 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .power 1
private def word4 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mul word1 word2
private def word5 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mul word1 word3
private def word6 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mul word2 word3
private def word7 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mul word4 word3

private def radicalWords (j : Fin 2) : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  (if j.val < 1 then word4 else word6)

private theorem radicalWords_checked : ∀ j : Fin 2,
    (radicalWords j).eval 2 generators N13.normalGenerators = N11.normalGenerators j := by
  intro j
  fin_cases j <;> decide +kernel

private def powerRow (j : Fin 3) : Fin 8 := ((if j.val < 1 then 3 else (if j.val < 2 then 2 else 2)) : Fin 8)
private def mixedRow (j : Fin 3) (i : Fin 3) : Fin 8 := ((if j.val < 1 then #[4,3,3] else (if j.val < 2 then #[7,2,2] else #[2,2,2])) : Array (Fin 8))[i.val]!

private theorem power_checked : ∀ j : Fin 3, N13.normalGenerators j ^ 2 =
    (⟨N11.normalCertificate.rows (powerRow j)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

private theorem mixed_checked : ∀ (j : Fin 3) (i : Fin 3),
    ⁅N13.normalGenerators j, generators i⁆ =
      (⟨N11.normalCertificate.rows (mixedRow j i)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

theorem radical_eq : primeRelativeRadical 2 N13.kernel = N11.kernel := by
  apply primeRelativeRadical_eq_of_generator_words 2 N13.kernel N11.kernel
    generators generators_full N13.normalGenerators rfl N11.normalGenerators rfl
    radicalWords radicalWords_checked
  · intro j
    rw [power_checked]
    exact binaryNormalRow_mem N11.normalCertificate _
  · intro j k
    rw [mixed_checked]
    exact binaryNormalRow_mem N11.normalCertificate _

theorem head_eq : Module.finrank (ZMod 2) (primeRelativeCharacters 2 N13.kernel) = 1 := by
  apply primeRelativeHead_eq_of_radical_card 2 N13.kernel N11.kernel 1 radical_eq
  norm_num [N13.kernel_card, N11.kernel_card]

end RadicalN13

namespace RadicalN14

private def word0 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .one
private def word1 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .power 0
private def word2 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mixed 0 0
private def word3 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mul word1 word2

private def radicalWords (j : Fin 1) : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  word2

private theorem radicalWords_checked : ∀ j : Fin 1,
    (radicalWords j).eval 2 generators N14.normalGenerators = N8.normalGenerators j := by
  intro j
  fin_cases j <;> decide +kernel

private def powerRow (j : Fin 3) : Fin 4 := ((if j.val < 1 then 1 else (if j.val < 2 then 1 else 1)) : Fin 4)
private def mixedRow (j : Fin 3) (i : Fin 3) : Fin 4 := ((if j.val < 1 then #[0,1,0] else (if j.val < 2 then #[3,1,1] else #[1,1,1])) : Array (Fin 4))[i.val]!

private theorem power_checked : ∀ j : Fin 3, N14.normalGenerators j ^ 2 =
    (⟨N8.normalCertificate.rows (powerRow j)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

private theorem mixed_checked : ∀ (j : Fin 3) (i : Fin 3),
    ⁅N14.normalGenerators j, generators i⁆ =
      (⟨N8.normalCertificate.rows (mixedRow j i)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

theorem radical_eq : primeRelativeRadical 2 N14.kernel = N8.kernel := by
  apply primeRelativeRadical_eq_of_generator_words 2 N14.kernel N8.kernel
    generators generators_full N14.normalGenerators rfl N8.normalGenerators rfl
    radicalWords radicalWords_checked
  · intro j
    rw [power_checked]
    exact binaryNormalRow_mem N8.normalCertificate _
  · intro j k
    rw [mixed_checked]
    exact binaryNormalRow_mem N8.normalCertificate _

theorem head_eq : Module.finrank (ZMod 2) (primeRelativeCharacters 2 N14.kernel) = 2 := by
  apply primeRelativeHead_eq_of_radical_card 2 N14.kernel N8.kernel 2 radical_eq
  norm_num [N14.kernel_card, N8.kernel_card]

end RadicalN14

namespace RadicalN15

private def word0 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .one
private def word1 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .power 0
private def word2 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mixed 2 0
private def word3 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mixed 2 1
private def word4 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mul word1 word2
private def word5 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mul word1 word3
private def word6 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mul word2 word3
private def word7 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mul word4 word3

private def radicalWords (j : Fin 2) : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  (if j.val < 1 then word2 else word7)

private theorem radicalWords_checked : ∀ j : Fin 2,
    (radicalWords j).eval 2 generators N15.normalGenerators = N11.normalGenerators j := by
  intro j
  fin_cases j <;> decide +kernel

private def powerRow (j : Fin 3) : Fin 8 := ((if j.val < 1 then 2 else (if j.val < 2 then 2 else 7)) : Fin 8)
private def mixedRow (j : Fin 3) (i : Fin 3) : Fin 8 := ((if j.val < 1 then #[7,2,2] else (if j.val < 2 then #[2,2,2] else #[0,3,2])) : Array (Fin 8))[i.val]!

private theorem power_checked : ∀ j : Fin 3, N15.normalGenerators j ^ 2 =
    (⟨N11.normalCertificate.rows (powerRow j)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

private theorem mixed_checked : ∀ (j : Fin 3) (i : Fin 3),
    ⁅N15.normalGenerators j, generators i⁆ =
      (⟨N11.normalCertificate.rows (mixedRow j i)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

theorem radical_eq : primeRelativeRadical 2 N15.kernel = N11.kernel := by
  apply primeRelativeRadical_eq_of_generator_words 2 N15.kernel N11.kernel
    generators generators_full N15.normalGenerators rfl N11.normalGenerators rfl
    radicalWords radicalWords_checked
  · intro j
    rw [power_checked]
    exact binaryNormalRow_mem N11.normalCertificate _
  · intro j k
    rw [mixed_checked]
    exact binaryNormalRow_mem N11.normalCertificate _

theorem head_eq : Module.finrank (ZMod 2) (primeRelativeCharacters 2 N15.kernel) = 1 := by
  apply primeRelativeHead_eq_of_radical_card 2 N15.kernel N11.kernel 1 radical_eq
  norm_num [N15.kernel_card, N11.kernel_card]

end RadicalN15

namespace RadicalN16

private def word0 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .one
private def word1 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .power 0
private def word2 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .mixed 0 0
private def word3 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .mixed 0 2
private def word4 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .power 1
private def word5 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .mul word1 word2
private def word6 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .mul word2 word3
private def word7 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .mul word2 word4

private def radicalWords (j : Fin 2) : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  (if j.val < 1 then word5 else word3)

private theorem radicalWords_checked : ∀ j : Fin 2,
    (radicalWords j).eval 2 generators N16.normalGenerators = N11.normalGenerators j := by
  intro j
  fin_cases j <;> decide +kernel

private def powerRow (j : Fin 2) : Fin 8 := ((if j.val < 1 then 4 else 2) : Fin 8)
private def mixedRow (j : Fin 2) (i : Fin 3) : Fin 8 := ((if j.val < 1 then #[3,3,1] else #[7,2,2]) : Array (Fin 8))[i.val]!

private theorem power_checked : ∀ j : Fin 2, N16.normalGenerators j ^ 2 =
    (⟨N11.normalCertificate.rows (powerRow j)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

private theorem mixed_checked : ∀ (j : Fin 2) (i : Fin 3),
    ⁅N16.normalGenerators j, generators i⁆ =
      (⟨N11.normalCertificate.rows (mixedRow j i)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

theorem radical_eq : primeRelativeRadical 2 N16.kernel = N11.kernel := by
  apply primeRelativeRadical_eq_of_generator_words 2 N16.kernel N11.kernel
    generators generators_full N16.normalGenerators rfl N11.normalGenerators rfl
    radicalWords radicalWords_checked
  · intro j
    rw [power_checked]
    exact binaryNormalRow_mem N11.normalCertificate _
  · intro j k
    rw [mixed_checked]
    exact binaryNormalRow_mem N11.normalCertificate _

theorem head_eq : Module.finrank (ZMod 2) (primeRelativeCharacters 2 N16.kernel) = 1 := by
  apply primeRelativeHead_eq_of_radical_card 2 N16.kernel N11.kernel 1 radical_eq
  norm_num [N16.kernel_card, N11.kernel_card]

end RadicalN16

namespace RadicalN17

private def word0 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .one
private def word1 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .power 0
private def word2 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mixed 2 0
private def word3 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mul word1 word2

private def radicalWords (j : Fin 2) : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  (if j.val < 1 then word3 else word1)

private theorem radicalWords_checked : ∀ j : Fin 2,
    (radicalWords j).eval 2 generators N17.normalGenerators = N3.normalGenerators j := by
  intro j
  fin_cases j <;> decide +kernel

private def powerRow (j : Fin 3) : Fin 4 := ((if j.val < 1 then 0 else (if j.val < 2 then 0 else 3)) : Fin 4)
private def mixedRow (j : Fin 3) (i : Fin 3) : Fin 4 := ((if j.val < 1 then #[3,0,0] else (if j.val < 2 then #[0,0,0] else #[2,3,2])) : Array (Fin 4))[i.val]!

private theorem power_checked : ∀ j : Fin 3, N17.normalGenerators j ^ 2 =
    (⟨N3.normalCertificate.rows (powerRow j)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

private theorem mixed_checked : ∀ (j : Fin 3) (i : Fin 3),
    ⁅N17.normalGenerators j, generators i⁆ =
      (⟨N3.normalCertificate.rows (mixedRow j i)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

theorem radical_eq : primeRelativeRadical 2 N17.kernel = N3.kernel := by
  apply primeRelativeRadical_eq_of_generator_words 2 N17.kernel N3.kernel
    generators generators_full N17.normalGenerators rfl N3.normalGenerators rfl
    radicalWords radicalWords_checked
  · intro j
    rw [power_checked]
    exact binaryNormalRow_mem N3.normalCertificate _
  · intro j k
    rw [mixed_checked]
    exact binaryNormalRow_mem N3.normalCertificate _

theorem head_eq : Module.finrank (ZMod 2) (primeRelativeCharacters 2 N17.kernel) = 2 := by
  apply primeRelativeHead_eq_of_radical_card 2 N17.kernel N3.kernel 2 radical_eq
  norm_num [N17.kernel_card, N3.kernel_card]

end RadicalN17

namespace RadicalN18

private def word0 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .one
private def word1 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .power 0
private def word2 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mixed 0 0
private def word3 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mixed 0 2
private def word4 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .power 1
private def word5 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mixed 1 0
private def word6 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mul word1 word5
private def word7 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mul word2 word3

private def radicalWords (j : Fin 2) : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  (if j.val < 1 then word5 else word3)

private theorem radicalWords_checked : ∀ j : Fin 2,
    (radicalWords j).eval 2 generators N18.normalGenerators = N11.normalGenerators j := by
  intro j
  fin_cases j <;> decide +kernel

private def powerRow (j : Fin 3) : Fin 8 := ((if j.val < 1 then 4 else (if j.val < 2 then 2 else 2)) : Fin 8)
private def mixedRow (j : Fin 3) (i : Fin 3) : Fin 8 := ((if j.val < 1 then #[3,3,1] else (if j.val < 2 then #[0,2,0] else #[7,2,2])) : Array (Fin 8))[i.val]!

private theorem power_checked : ∀ j : Fin 3, N18.normalGenerators j ^ 2 =
    (⟨N11.normalCertificate.rows (powerRow j)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

private theorem mixed_checked : ∀ (j : Fin 3) (i : Fin 3),
    ⁅N18.normalGenerators j, generators i⁆ =
      (⟨N11.normalCertificate.rows (mixedRow j i)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

theorem radical_eq : primeRelativeRadical 2 N18.kernel = N11.kernel := by
  apply primeRelativeRadical_eq_of_generator_words 2 N18.kernel N11.kernel
    generators generators_full N18.normalGenerators rfl N11.normalGenerators rfl
    radicalWords radicalWords_checked
  · intro j
    rw [power_checked]
    exact binaryNormalRow_mem N11.normalCertificate _
  · intro j k
    rw [mixed_checked]
    exact binaryNormalRow_mem N11.normalCertificate _

theorem head_eq : Module.finrank (ZMod 2) (primeRelativeCharacters 2 N18.kernel) = 2 := by
  apply primeRelativeHead_eq_of_radical_card 2 N18.kernel N11.kernel 2 radical_eq
  norm_num [N18.kernel_card, N11.kernel_card]

end RadicalN18

namespace RadicalN19

private def word0 : PrimeRelativeRadicalWord (Fin 3) (Fin 4) :=
  .one
private def word1 : PrimeRelativeRadicalWord (Fin 3) (Fin 4) :=
  .power 0
private def word2 : PrimeRelativeRadicalWord (Fin 3) (Fin 4) :=
  .mixed 0 0
private def word3 : PrimeRelativeRadicalWord (Fin 3) (Fin 4) :=
  .mixed 3 0
private def word4 : PrimeRelativeRadicalWord (Fin 3) (Fin 4) :=
  .mul word1 word2
private def word5 : PrimeRelativeRadicalWord (Fin 3) (Fin 4) :=
  .mul word1 word3
private def word6 : PrimeRelativeRadicalWord (Fin 3) (Fin 4) :=
  .mul word2 word3
private def word7 : PrimeRelativeRadicalWord (Fin 3) (Fin 4) :=
  .mul word4 word3

private def radicalWords (j : Fin 2) : PrimeRelativeRadicalWord (Fin 3) (Fin 4) :=
  (if j.val < 1 then word2 else word6)

private theorem radicalWords_checked : ∀ j : Fin 2,
    (radicalWords j).eval 2 generators N19.normalGenerators = N11.normalGenerators j := by
  intro j
  fin_cases j <;> decide +kernel

private def powerRow (j : Fin 4) : Fin 8 := ((if j.val < 2 then (if j.val < 1 then 2 else 2) else (if j.val < 3 then 2 else 7)) : Fin 8)
private def mixedRow (j : Fin 4) (i : Fin 3) : Fin 8 := ((if j.val < 2 then (if j.val < 1 then #[0,2,0] else #[7,2,2]) else (if j.val < 3 then #[2,2,2] else #[6,7,6])) : Array (Fin 8))[i.val]!

private theorem power_checked : ∀ j : Fin 4, N19.normalGenerators j ^ 2 =
    (⟨N11.normalCertificate.rows (powerRow j)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

private theorem mixed_checked : ∀ (j : Fin 4) (i : Fin 3),
    ⁅N19.normalGenerators j, generators i⁆ =
      (⟨N11.normalCertificate.rows (mixedRow j i)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

theorem radical_eq : primeRelativeRadical 2 N19.kernel = N11.kernel := by
  apply primeRelativeRadical_eq_of_generator_words 2 N19.kernel N11.kernel
    generators generators_full N19.normalGenerators rfl N11.normalGenerators rfl
    radicalWords radicalWords_checked
  · intro j
    rw [power_checked]
    exact binaryNormalRow_mem N11.normalCertificate _
  · intro j k
    rw [mixed_checked]
    exact binaryNormalRow_mem N11.normalCertificate _

theorem head_eq : Module.finrank (ZMod 2) (primeRelativeCharacters 2 N19.kernel) = 2 := by
  apply primeRelativeHead_eq_of_radical_card 2 N19.kernel N11.kernel 2 radical_eq
  norm_num [N19.kernel_card, N11.kernel_card]

end RadicalN19

namespace RadicalN20

private def word0 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .one
private def word1 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .power 0
private def word2 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mixed 0 0
private def word3 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mixed 0 2
private def word4 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .power 1
private def word5 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mixed 2 0
private def word6 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mul word1 word5
private def word7 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mul word2 word3

private def radicalWords (j : Fin 2) : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  (if j.val < 1 then word5 else word3)

private theorem radicalWords_checked : ∀ j : Fin 2,
    (radicalWords j).eval 2 generators N20.normalGenerators = N11.normalGenerators j := by
  intro j
  fin_cases j <;> decide +kernel

private def powerRow (j : Fin 3) : Fin 8 := ((if j.val < 1 then 4 else (if j.val < 2 then 2 else 7)) : Fin 8)
private def mixedRow (j : Fin 3) (i : Fin 3) : Fin 8 := ((if j.val < 1 then #[3,3,1] else (if j.val < 2 then #[7,2,2] else #[0,3,2])) : Array (Fin 8))[i.val]!

private theorem power_checked : ∀ j : Fin 3, N20.normalGenerators j ^ 2 =
    (⟨N11.normalCertificate.rows (powerRow j)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

private theorem mixed_checked : ∀ (j : Fin 3) (i : Fin 3),
    ⁅N20.normalGenerators j, generators i⁆ =
      (⟨N11.normalCertificate.rows (mixedRow j i)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

theorem radical_eq : primeRelativeRadical 2 N20.kernel = N11.kernel := by
  apply primeRelativeRadical_eq_of_generator_words 2 N20.kernel N11.kernel
    generators generators_full N20.normalGenerators rfl N11.normalGenerators rfl
    radicalWords radicalWords_checked
  · intro j
    rw [power_checked]
    exact binaryNormalRow_mem N11.normalCertificate _
  · intro j k
    rw [mixed_checked]
    exact binaryNormalRow_mem N11.normalCertificate _

theorem head_eq : Module.finrank (ZMod 2) (primeRelativeCharacters 2 N20.kernel) = 2 := by
  apply primeRelativeHead_eq_of_radical_card 2 N20.kernel N11.kernel 2 radical_eq
  norm_num [N20.kernel_card, N11.kernel_card]

end RadicalN20

namespace RadicalN21

private def word0 : PrimeRelativeRadicalWord (Fin 3) (Fin 4) :=
  .one
private def word1 : PrimeRelativeRadicalWord (Fin 3) (Fin 4) :=
  .power 0
private def word2 : PrimeRelativeRadicalWord (Fin 3) (Fin 4) :=
  .mixed 2 0
private def word3 : PrimeRelativeRadicalWord (Fin 3) (Fin 4) :=
  .mixed 3 0
private def word4 : PrimeRelativeRadicalWord (Fin 3) (Fin 4) :=
  .mixed 3 1
private def word5 : PrimeRelativeRadicalWord (Fin 3) (Fin 4) :=
  .mul word1 word3
private def word6 : PrimeRelativeRadicalWord (Fin 3) (Fin 4) :=
  .mul word2 word3
private def word7 : PrimeRelativeRadicalWord (Fin 3) (Fin 4) :=
  .mul word3 word4

private def radicalWords (j : Fin 2) : PrimeRelativeRadicalWord (Fin 3) (Fin 4) :=
  (if j.val < 1 then word3 else word6)

private theorem radicalWords_checked : ∀ j : Fin 2,
    (radicalWords j).eval 2 generators N21.normalGenerators = N11.normalGenerators j := by
  intro j
  fin_cases j <;> decide +kernel

private def powerRow (j : Fin 4) : Fin 8 := ((if j.val < 2 then (if j.val < 1 then 2 else 2) else (if j.val < 3 then 7 else 7)) : Fin 8)
private def mixedRow (j : Fin 4) (i : Fin 3) : Fin 8 := ((if j.val < 2 then (if j.val < 1 then #[7,2,2] else #[2,2,2]) else (if j.val < 3 then #[6,7,6] else #[0,3,2])) : Array (Fin 8))[i.val]!

private theorem power_checked : ∀ j : Fin 4, N21.normalGenerators j ^ 2 =
    (⟨N11.normalCertificate.rows (powerRow j)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

private theorem mixed_checked : ∀ (j : Fin 4) (i : Fin 3),
    ⁅N21.normalGenerators j, generators i⁆ =
      (⟨N11.normalCertificate.rows (mixedRow j i)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

theorem radical_eq : primeRelativeRadical 2 N21.kernel = N11.kernel := by
  apply primeRelativeRadical_eq_of_generator_words 2 N21.kernel N11.kernel
    generators generators_full N21.normalGenerators rfl N11.normalGenerators rfl
    radicalWords radicalWords_checked
  · intro j
    rw [power_checked]
    exact binaryNormalRow_mem N11.normalCertificate _
  · intro j k
    rw [mixed_checked]
    exact binaryNormalRow_mem N11.normalCertificate _

theorem head_eq : Module.finrank (ZMod 2) (primeRelativeCharacters 2 N21.kernel) = 2 := by
  apply primeRelativeHead_eq_of_radical_card 2 N21.kernel N11.kernel 2 radical_eq
  norm_num [N21.kernel_card, N11.kernel_card]

end RadicalN21

namespace RadicalN22

private def word0 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .one
private def word1 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .power 0
private def word2 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .mixed 0 1
private def word3 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .mixed 0 2
private def word4 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .mixed 1 0
private def word5 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .mul word1 word2
private def word6 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .mul word2 word3
private def word7 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .mul word2 word4

private def radicalWords (j : Fin 2) : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  (if j.val < 1 then word1 else word6)

private theorem radicalWords_checked : ∀ j : Fin 2,
    (radicalWords j).eval 2 generators N22.normalGenerators = N11.normalGenerators j := by
  intro j
  fin_cases j <;> decide +kernel

private def powerRow (j : Fin 2) : Fin 8 := ((if j.val < 1 then 0 else 7) : Fin 8)
private def mixedRow (j : Fin 2) (i : Fin 3) : Fin 8 := ((if j.val < 1 then #[7,3,5] else #[2,7,7]) : Array (Fin 8))[i.val]!

private theorem power_checked : ∀ j : Fin 2, N22.normalGenerators j ^ 2 =
    (⟨N11.normalCertificate.rows (powerRow j)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

private theorem mixed_checked : ∀ (j : Fin 2) (i : Fin 3),
    ⁅N22.normalGenerators j, generators i⁆ =
      (⟨N11.normalCertificate.rows (mixedRow j i)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

theorem radical_eq : primeRelativeRadical 2 N22.kernel = N11.kernel := by
  apply primeRelativeRadical_eq_of_generator_words 2 N22.kernel N11.kernel
    generators generators_full N22.normalGenerators rfl N11.normalGenerators rfl
    radicalWords radicalWords_checked
  · intro j
    rw [power_checked]
    exact binaryNormalRow_mem N11.normalCertificate _
  · intro j k
    rw [mixed_checked]
    exact binaryNormalRow_mem N11.normalCertificate _

theorem head_eq : Module.finrank (ZMod 2) (primeRelativeCharacters 2 N22.kernel) = 1 := by
  apply primeRelativeHead_eq_of_radical_card 2 N22.kernel N11.kernel 1 radical_eq
  norm_num [N22.kernel_card, N11.kernel_card]

end RadicalN22

namespace RadicalN23

private def word0 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .one
private def word1 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .power 0
private def word2 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .mixed 0 1
private def word3 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .mixed 0 2
private def word4 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .mixed 1 0
private def word5 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .mul word1 word1
private def word6 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .mul word1 word4
private def word7 : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  .mul word2 word3

private def radicalWords (j : Fin 2) : PrimeRelativeRadicalWord (Fin 3) (Fin 2) :=
  (if j.val < 1 then word1 else word7)

private theorem radicalWords_checked : ∀ j : Fin 2,
    (radicalWords j).eval 2 generators N23.normalGenerators = N11.normalGenerators j := by
  intro j
  fin_cases j <;> decide +kernel

private def powerRow (j : Fin 2) : Fin 8 := ((if j.val < 1 then 0 else 3) : Fin 8)
private def mixedRow (j : Fin 2) (i : Fin 3) : Fin 8 := ((if j.val < 1 then #[7,3,5] else #[4,3,3]) : Array (Fin 8))[i.val]!

private theorem power_checked : ∀ j : Fin 2, N23.normalGenerators j ^ 2 =
    (⟨N11.normalCertificate.rows (powerRow j)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

private theorem mixed_checked : ∀ (j : Fin 2) (i : Fin 3),
    ⁅N23.normalGenerators j, generators i⁆ =
      (⟨N11.normalCertificate.rows (mixedRow j i)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

theorem radical_eq : primeRelativeRadical 2 N23.kernel = N11.kernel := by
  apply primeRelativeRadical_eq_of_generator_words 2 N23.kernel N11.kernel
    generators generators_full N23.normalGenerators rfl N11.normalGenerators rfl
    radicalWords radicalWords_checked
  · intro j
    rw [power_checked]
    exact binaryNormalRow_mem N11.normalCertificate _
  · intro j k
    rw [mixed_checked]
    exact binaryNormalRow_mem N11.normalCertificate _

theorem head_eq : Module.finrank (ZMod 2) (primeRelativeCharacters 2 N23.kernel) = 2 := by
  apply primeRelativeHead_eq_of_radical_card 2 N23.kernel N11.kernel 2 radical_eq
  norm_num [N23.kernel_card, N11.kernel_card]

end RadicalN23

namespace RadicalN24

private def word0 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .one
private def word1 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .power 0
private def word2 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mixed 0 1
private def word3 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mixed 0 2
private def word4 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mixed 1 2
private def word5 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mul word1 word2
private def word6 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mul word2 word3
private def word7 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mul word2 word4

private def radicalWords (j : Fin 2) : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  (if j.val < 1 then word1 else word6)

private theorem radicalWords_checked : ∀ j : Fin 2,
    (radicalWords j).eval 2 generators N24.normalGenerators = N11.normalGenerators j := by
  intro j
  fin_cases j <;> decide +kernel

private def powerRow (j : Fin 3) : Fin 8 := ((if j.val < 1 then 0 else (if j.val < 2 then 7 else 7)) : Fin 8)
private def mixedRow (j : Fin 3) (i : Fin 3) : Fin 8 := ((if j.val < 1 then #[7,3,5] else (if j.val < 2 then #[0,3,2] else #[2,7,7])) : Array (Fin 8))[i.val]!

private theorem power_checked : ∀ j : Fin 3, N24.normalGenerators j ^ 2 =
    (⟨N11.normalCertificate.rows (powerRow j)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

private theorem mixed_checked : ∀ (j : Fin 3) (i : Fin 3),
    ⁅N24.normalGenerators j, generators i⁆ =
      (⟨N11.normalCertificate.rows (mixedRow j i)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

theorem radical_eq : primeRelativeRadical 2 N24.kernel = N11.kernel := by
  apply primeRelativeRadical_eq_of_generator_words 2 N24.kernel N11.kernel
    generators generators_full N24.normalGenerators rfl N11.normalGenerators rfl
    radicalWords radicalWords_checked
  · intro j
    rw [power_checked]
    exact binaryNormalRow_mem N11.normalCertificate _
  · intro j k
    rw [mixed_checked]
    exact binaryNormalRow_mem N11.normalCertificate _

theorem head_eq : Module.finrank (ZMod 2) (primeRelativeCharacters 2 N24.kernel) = 2 := by
  apply primeRelativeHead_eq_of_radical_card 2 N24.kernel N11.kernel 2 radical_eq
  norm_num [N24.kernel_card, N11.kernel_card]

end RadicalN24

namespace RadicalN25

private def word0 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .one
private def word1 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .power 0
private def word2 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mixed 0 1
private def word3 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mixed 0 2
private def word4 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mixed 1 0
private def word5 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mixed 2 0
private def word6 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mul word1 word2
private def word7 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mul word1 word4

private def radicalWords (j : Fin 2) : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  (if j.val < 1 then word1 else word7)

private theorem radicalWords_checked : ∀ j : Fin 2,
    (radicalWords j).eval 2 generators N25.normalGenerators = N11.normalGenerators j := by
  intro j
  fin_cases j <;> decide +kernel

private def powerRow (j : Fin 3) : Fin 8 := ((if j.val < 1 then 0 else (if j.val < 2 then 7 else 7)) : Fin 8)
private def mixedRow (j : Fin 3) (i : Fin 3) : Fin 8 := ((if j.val < 1 then #[7,3,5] else (if j.val < 2 then #[6,7,6] else #[2,7,7])) : Array (Fin 8))[i.val]!

private theorem power_checked : ∀ j : Fin 3, N25.normalGenerators j ^ 2 =
    (⟨N11.normalCertificate.rows (powerRow j)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

private theorem mixed_checked : ∀ (j : Fin 3) (i : Fin 3),
    ⁅N25.normalGenerators j, generators i⁆ =
      (⟨N11.normalCertificate.rows (mixedRow j i)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

theorem radical_eq : primeRelativeRadical 2 N25.kernel = N11.kernel := by
  apply primeRelativeRadical_eq_of_generator_words 2 N25.kernel N11.kernel
    generators generators_full N25.normalGenerators rfl N11.normalGenerators rfl
    radicalWords radicalWords_checked
  · intro j
    rw [power_checked]
    exact binaryNormalRow_mem N11.normalCertificate _
  · intro j k
    rw [mixed_checked]
    exact binaryNormalRow_mem N11.normalCertificate _

theorem head_eq : Module.finrank (ZMod 2) (primeRelativeCharacters 2 N25.kernel) = 2 := by
  apply primeRelativeHead_eq_of_radical_card 2 N25.kernel N11.kernel 2 radical_eq
  norm_num [N25.kernel_card, N11.kernel_card]

end RadicalN25

namespace RadicalN26

private def word0 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .one
private def word1 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .power 0
private def word2 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mixed 0 1
private def word3 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mixed 0 2
private def word4 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mixed 1 2
private def word5 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mul word1 word1
private def word6 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mul word1 word2
private def word7 : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  .mul word1 word4

private def radicalWords (j : Fin 2) : PrimeRelativeRadicalWord (Fin 3) (Fin 3) :=
  (if j.val < 1 then word1 else word7)

private theorem radicalWords_checked : ∀ j : Fin 2,
    (radicalWords j).eval 2 generators N26.normalGenerators = N11.normalGenerators j := by
  intro j
  fin_cases j <;> decide +kernel

private def powerRow (j : Fin 3) : Fin 8 := ((if j.val < 1 then 0 else (if j.val < 2 then 7 else 7)) : Fin 8)
private def mixedRow (j : Fin 3) (i : Fin 3) : Fin 8 := ((if j.val < 1 then #[7,3,5] else (if j.val < 2 then #[3,7,6] else #[0,6,7])) : Array (Fin 8))[i.val]!

private theorem power_checked : ∀ j : Fin 3, N26.normalGenerators j ^ 2 =
    (⟨N11.normalCertificate.rows (powerRow j)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

private theorem mixed_checked : ∀ (j : Fin 3) (i : Fin 3),
    ⁅N26.normalGenerators j, generators i⁆ =
      (⟨N11.normalCertificate.rows (mixedRow j i)⟩ : Source) := by
  intro j
  fin_cases j <;> decide +kernel

theorem radical_eq : primeRelativeRadical 2 N26.kernel = N11.kernel := by
  apply primeRelativeRadical_eq_of_generator_words 2 N26.kernel N11.kernel
    generators generators_full N26.normalGenerators rfl N11.normalGenerators rfl
    radicalWords radicalWords_checked
  · intro j
    rw [power_checked]
    exact binaryNormalRow_mem N11.normalCertificate _
  · intro j k
    rw [mixed_checked]
    exact binaryNormalRow_mem N11.normalCertificate _

theorem head_eq : Module.finrank (ZMod 2) (primeRelativeCharacters 2 N26.kernel) = 3 := by
  apply primeRelativeHead_eq_of_radical_card 2 N26.kernel N11.kernel 3 radical_eq
  norm_num [N26.kernel_card, N11.kernel_card]

end RadicalN26

end SymmetricSubgroupAsymptotics.BinaryCarrierNormal8T26
