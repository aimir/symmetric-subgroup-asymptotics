import SymmetricSubgroupAsymptotics.PrimeLinearKernelLowerCertificate
import SymmetricSubgroupAsymptotics.BinaryCarrierFormTransport16T1084

/-! Exact nonzero-form kernel dimension for the same original 16T1084
character family. Four distinct displayed numerical kernel vectors give
the lower bound, complementing the existing complete decoder upper bound.
The checked actual kernel equivalence transports equality back to the
original invariant derived character and canonical evaluation space. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierFormKernelExact16T1084

abbrev CharacterCoordinates := BinaryCarrierCommutatorForms16T1084.CharacterCoordinates
abbrev Input := BinaryCarrierCommutatorForms16T1084.Input
abbrev Characters := BinaryCarrierFormTransport16T1084.Characters

private def label : Fin 7 → CharacterCoordinates :=
  ![![1, 0, 0], ![0, 1, 0], ![1, 1, 0], ![0, 0, 1], ![1, 0, 1], ![0, 1, 1], ![1, 1, 1]]

private theorem label_cover : ∀ χ : CharacterCoordinates,
    χ ≠ 0 → ∃ i : Fin 7, label i = χ := by
  decide +kernel

private def bitVector (n : ℕ) : Input := fun j => (n / 2 ^ j.val : ℕ)

private def selectedCode : Fin 7 → Fin 4 → ℕ :=
  ![![0, 14, 21, 27], ![0, 4, 8, 12], ![0, 10, 19, 25], ![0, 1, 56, 57], ![0, 11, 33, 42], ![0, 5, 49, 52], ![0, 15, 34, 45]]

private def select (i : Fin 7) (j : Fin 4) : Input :=
  bitVector (selectedCode i j)

/-- Membership is checked in the public numerical map itself. -/
private theorem select_mem_kernel : ∀ (i : Fin 7) (j : Fin 4),
    BinaryCarrierCommutatorForms16T1084.family (label i) (select i j) = 0 := by
  decide +kernel

/-- The four displayed vectors are distinct for each parameter. -/
private theorem select_injective : ∀ (i : Fin 7) (j k : Fin 4),
    select i j = select i k → j = k := by
  decide +kernel

/-- Every nonzero displayed scalar form has exact kernel dimension two. -/
theorem family_finrank_ker_eq_two (χ : CharacterCoordinates) (hχ : χ ≠ 0) :
    Module.finrank (ZMod 2) (BinaryCarrierCommutatorForms16T1084.family χ).ker = 2 := by
  apply le_antisymm (BinaryCarrierCommutatorForms16T1084.family_finrank_ker_le_two χ hχ)
  obtain ⟨i, rfl⟩ := label_cover χ hχ
  exact primeLinearMap_le_finrank_ker_of_injective_vectors 2
    (BinaryCarrierCommutatorForms16T1084.family (label i)) 2
    (select i) (select_mem_kernel i) (select_injective i)

/-- Exact dimension for the actual whole-original-group invariant derived
character form; the original group, character and quotient map are retained. -/
theorem actual_form_finrank_ker_eq_two (χ : Characters) (hχ : χ ≠ 0) :
    Module.finrank (ZMod 2)
      (derivedEvaluationBilinearMap 2
        BinaryCarrierDerived16T1084.evaluationKernel_eq_commutator χ).ker = 2 := by
  change Module.finrank (ZMod 2) (BinaryCarrierFormTransport16T1084.form χ).ker = 2
  rw [← (BinaryCarrierFormTransport16T1084.kernelEquiv χ).finrank_eq]
  apply family_finrank_ker_eq_two
  intro hz
  apply hχ
  apply BinaryCarrierDerivedCharacters16T1084.coordinateEquiv.injective
  exact hz.trans (map_zero BinaryCarrierDerivedCharacters16T1084.coordinates).symm

end SymmetricSubgroupAsymptotics.BinaryCarrierFormKernelExact16T1084
