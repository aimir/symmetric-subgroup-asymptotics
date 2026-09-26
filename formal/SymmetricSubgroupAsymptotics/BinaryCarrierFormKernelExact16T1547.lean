import SymmetricSubgroupAsymptotics.PrimeLinearKernelLowerCertificate
import SymmetricSubgroupAsymptotics.BinaryCarrierFormTransport16T1547

/-! Exact nonzero-form kernel dimension for the same original 16T1547
character family. Four distinct displayed numerical kernel vectors give
the lower bound, complementing the existing complete decoder upper bound.
The checked actual kernel equivalence transports equality back to the
original invariant derived character and canonical evaluation space. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierFormKernelExact16T1547

abbrev CharacterCoordinates := BinaryCarrierCommutatorForms16T1547.CharacterCoordinates
abbrev Input := BinaryCarrierCommutatorForms16T1547.Input
abbrev Characters := BinaryCarrierFormTransport16T1547.Characters

private def label : Fin 7 → CharacterCoordinates :=
  ![![1, 0, 0], ![0, 1, 0], ![1, 1, 0], ![0, 0, 1], ![1, 0, 1], ![0, 1, 1], ![1, 1, 1]]

private theorem label_cover : ∀ χ : CharacterCoordinates,
    χ ≠ 0 → ∃ i : Fin 7, label i = χ := by
  decide +kernel

private def bitVector (n : ℕ) : Input := fun j => (n / 2 ^ j.val : ℕ)

private def selectedCode : Fin 7 → Fin 4 → ℕ :=
  ![![0, 6, 34, 36], ![0, 4, 33, 37], ![0, 3, 32, 35], ![0, 8, 16, 24], ![0, 22, 44, 58], ![0, 12, 53, 57], ![0, 27, 40, 51]]

private def select (i : Fin 7) (j : Fin 4) : Input :=
  bitVector (selectedCode i j)

/-- Membership is checked in the public numerical map itself. -/
private theorem select_mem_kernel : ∀ (i : Fin 7) (j : Fin 4),
    BinaryCarrierCommutatorForms16T1547.family (label i) (select i j) = 0 := by
  decide +kernel

/-- The four displayed vectors are distinct for each parameter. -/
private theorem select_injective : ∀ (i : Fin 7) (j k : Fin 4),
    select i j = select i k → j = k := by
  decide +kernel

/-- Every nonzero displayed scalar form has exact kernel dimension two. -/
theorem family_finrank_ker_eq_two (χ : CharacterCoordinates) (hχ : χ ≠ 0) :
    Module.finrank (ZMod 2) (BinaryCarrierCommutatorForms16T1547.family χ).ker = 2 := by
  apply le_antisymm (BinaryCarrierCommutatorForms16T1547.family_finrank_ker_le_two χ hχ)
  obtain ⟨i, rfl⟩ := label_cover χ hχ
  exact primeLinearMap_le_finrank_ker_of_injective_vectors 2
    (BinaryCarrierCommutatorForms16T1547.family (label i)) 2
    (select i) (select_mem_kernel i) (select_injective i)

/-- Exact dimension for the actual whole-original-group invariant derived
character form; the original group, character and quotient map are retained. -/
theorem actual_form_finrank_ker_eq_two (χ : Characters) (hχ : χ ≠ 0) :
    Module.finrank (ZMod 2)
      (derivedEvaluationBilinearMap 2
        BinaryCarrierDerived16T1547.evaluationKernel_eq_commutator χ).ker = 2 := by
  change Module.finrank (ZMod 2) (BinaryCarrierFormTransport16T1547.form χ).ker = 2
  rw [← (BinaryCarrierFormTransport16T1547.kernelEquiv χ).finrank_eq]
  apply family_finrank_ker_eq_two
  intro hz
  apply hχ
  apply BinaryCarrierDerivedCharacters16T1547.coordinateEquiv.injective
  exact hz.trans (map_zero BinaryCarrierDerivedCharacters16T1547.coordinates).symm

end SymmetricSubgroupAsymptotics.BinaryCarrierFormKernelExact16T1547
