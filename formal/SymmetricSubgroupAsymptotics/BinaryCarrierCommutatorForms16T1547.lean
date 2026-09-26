import SymmetricSubgroupAsymptotics.PrimeLinearKernelCertificate
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.FinCases

/-! Small numerical commutator-form certificates for the displayed 16T1547
coordinate array. Every nonzero scalar form has kernel dimension at most
two, and every pair of independent scalar forms has zero common kernel.
All finite tests concern the displayed linear maps on the complete 64-vector
space. No identification with an original group or character space is
asserted here; that is a separate binding obligation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryCarrierCommutatorForms16T1547

abbrev CharacterCoordinates := Fin 3 → ZMod 2
abbrev Input := Fin 6 → ZMod 2

/-- The third index is the least-significant-first bit of the recorded
three-bit coefficient. The first index is the output row of the form. -/
def coefficient : Fin 6 → Fin 6 → Fin 3 → ZMod 2 :=
  ![![![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, 0], ![0, 1, 0], ![0, 0, 1]],
    ![![0, 0, 0], ![0, 0, 0], ![0, 0, 1], ![0, 1, 0], ![1, 0, 0], ![0, 0, 1]],
    ![![0, 0, 0], ![0, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, 0], ![0, 0, 0]],
    ![![1, 0, 0], ![0, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0]],
    ![![0, 1, 0], ![1, 0, 0], ![1, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, 0]],
    ![![0, 0, 1], ![0, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, 0], ![0, 0, 0]]]

/-- Reversing the two generator coordinates preserves every scalar coefficient. -/
theorem coefficient_symm : ∀ (i j : Fin 6) (k : Fin 3),
    coefficient i j k = coefficient j i k := by
  decide +kernel

/-- Each diagonal generator commutator has zero displayed coefficient. -/
theorem coefficient_diagonal : ∀ (i : Fin 6) (k : Fin 3),
    coefficient i i k = 0 := by
  decide +kernel

def matrix (χ : CharacterCoordinates) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  fun i j => ∑ k : Fin 3, coefficient i j k * χ k

/-- The displayed scalar form as an actual linear map on the same input. -/
def family (χ : CharacterCoordinates) : Input →ₗ[ZMod 2] Input :=
  (matrix χ).mulVecLin

theorem family_apply (χ : CharacterCoordinates) (x : Input) (i : Fin 6) :
    family χ x i = ∑ j : Fin 6, (∑ k : Fin 3, coefficient i j k * χ k) * x j := rfl

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

private def code (i : Fin 7) (x : Input) : Fin 4 :=
  if x = select i 0 then 0 else if x = select i 1 then 1
  else if x = select i 2 then 2 else 3

private theorem kernel_cover_0 : ∀ x : Input,
    family (label 0) x = 0 → select 0 (code 0 x) = x := by
  decide +kernel

private theorem kernel_cover_1 : ∀ x : Input,
    family (label 1) x = 0 → select 1 (code 1 x) = x := by
  decide +kernel

private theorem kernel_cover_2 : ∀ x : Input,
    family (label 2) x = 0 → select 2 (code 2 x) = x := by
  decide +kernel

private theorem kernel_cover_3 : ∀ x : Input,
    family (label 3) x = 0 → select 3 (code 3 x) = x := by
  decide +kernel

private theorem kernel_cover_4 : ∀ x : Input,
    family (label 4) x = 0 → select 4 (code 4 x) = x := by
  decide +kernel

private theorem kernel_cover_5 : ∀ x : Input,
    family (label 5) x = 0 → select 5 (code 5 x) = x := by
  decide +kernel

private theorem kernel_cover_6 : ∀ x : Input,
    family (label 6) x = 0 → select 6 (code 6 x) = x := by
  decide +kernel

private theorem kernel_cover (i : Fin 7) : ∀ x : Input,
    family (label i) x = 0 → select i (code i x) = x := by
  fin_cases i
  · exact kernel_cover_0
  · exact kernel_cover_1
  · exact kernel_cover_2
  · exact kernel_cover_3
  · exact kernel_cover_4
  · exact kernel_cover_5
  · exact kernel_cover_6

/-- A four-label decoder bounds each nonzero form's actual kernel.
This is the inequality needed by the retained-character argument. -/
theorem family_finrank_ker_le_two (χ : CharacterCoordinates) (hχ : χ ≠ 0) :
    Module.finrank (ZMod 2) (family χ).ker ≤ 2 := by
  obtain ⟨i, rfl⟩ := label_cover χ hχ
  exact primeLinearMap_finrank_ker_le_of_decoder 2 (family (label i)) 2
    (select i) (code i) (kernel_cover i)

private theorem pair_zero_0_1 : ∀ x : Input,
    family (label 0) x = 0 → family (label 1) x = 0 → x = 0 := by
  decide +kernel

private theorem pair_zero_0_2 : ∀ x : Input,
    family (label 0) x = 0 → family (label 2) x = 0 → x = 0 := by
  decide +kernel

private theorem pair_zero_0_3 : ∀ x : Input,
    family (label 0) x = 0 → family (label 3) x = 0 → x = 0 := by
  decide +kernel

private theorem pair_zero_0_4 : ∀ x : Input,
    family (label 0) x = 0 → family (label 4) x = 0 → x = 0 := by
  decide +kernel

private theorem pair_zero_0_5 : ∀ x : Input,
    family (label 0) x = 0 → family (label 5) x = 0 → x = 0 := by
  decide +kernel

private theorem pair_zero_0_6 : ∀ x : Input,
    family (label 0) x = 0 → family (label 6) x = 0 → x = 0 := by
  decide +kernel

private theorem pair_zero_1_2 : ∀ x : Input,
    family (label 1) x = 0 → family (label 2) x = 0 → x = 0 := by
  decide +kernel

private theorem pair_zero_1_3 : ∀ x : Input,
    family (label 1) x = 0 → family (label 3) x = 0 → x = 0 := by
  decide +kernel

private theorem pair_zero_1_4 : ∀ x : Input,
    family (label 1) x = 0 → family (label 4) x = 0 → x = 0 := by
  decide +kernel

private theorem pair_zero_1_5 : ∀ x : Input,
    family (label 1) x = 0 → family (label 5) x = 0 → x = 0 := by
  decide +kernel

private theorem pair_zero_1_6 : ∀ x : Input,
    family (label 1) x = 0 → family (label 6) x = 0 → x = 0 := by
  decide +kernel

private theorem pair_zero_2_3 : ∀ x : Input,
    family (label 2) x = 0 → family (label 3) x = 0 → x = 0 := by
  decide +kernel

private theorem pair_zero_2_4 : ∀ x : Input,
    family (label 2) x = 0 → family (label 4) x = 0 → x = 0 := by
  decide +kernel

private theorem pair_zero_2_5 : ∀ x : Input,
    family (label 2) x = 0 → family (label 5) x = 0 → x = 0 := by
  decide +kernel

private theorem pair_zero_2_6 : ∀ x : Input,
    family (label 2) x = 0 → family (label 6) x = 0 → x = 0 := by
  decide +kernel

private theorem pair_zero_3_4 : ∀ x : Input,
    family (label 3) x = 0 → family (label 4) x = 0 → x = 0 := by
  decide +kernel

private theorem pair_zero_3_5 : ∀ x : Input,
    family (label 3) x = 0 → family (label 5) x = 0 → x = 0 := by
  decide +kernel

private theorem pair_zero_3_6 : ∀ x : Input,
    family (label 3) x = 0 → family (label 6) x = 0 → x = 0 := by
  decide +kernel

private theorem pair_zero_4_5 : ∀ x : Input,
    family (label 4) x = 0 → family (label 5) x = 0 → x = 0 := by
  decide +kernel

private theorem pair_zero_4_6 : ∀ x : Input,
    family (label 4) x = 0 → family (label 6) x = 0 → x = 0 := by
  decide +kernel

private theorem pair_zero_5_6 : ∀ x : Input,
    family (label 5) x = 0 → family (label 6) x = 0 → x = 0 := by
  decide +kernel

private theorem pair_zero (i j : Fin 7) (hij : i < j) : ∀ x : Input,
    family (label i) x = 0 → family (label j) x = 0 → x = 0 := by
  fin_cases i <;> fin_cases j
  · exact ((by decide : ¬ ((0 : Fin 7) < (0 : Fin 7))) hij).elim
  · exact pair_zero_0_1
  · exact pair_zero_0_2
  · exact pair_zero_0_3
  · exact pair_zero_0_4
  · exact pair_zero_0_5
  · exact pair_zero_0_6
  · exact ((by decide : ¬ ((1 : Fin 7) < (0 : Fin 7))) hij).elim
  · exact ((by decide : ¬ ((1 : Fin 7) < (1 : Fin 7))) hij).elim
  · exact pair_zero_1_2
  · exact pair_zero_1_3
  · exact pair_zero_1_4
  · exact pair_zero_1_5
  · exact pair_zero_1_6
  · exact ((by decide : ¬ ((2 : Fin 7) < (0 : Fin 7))) hij).elim
  · exact ((by decide : ¬ ((2 : Fin 7) < (1 : Fin 7))) hij).elim
  · exact ((by decide : ¬ ((2 : Fin 7) < (2 : Fin 7))) hij).elim
  · exact pair_zero_2_3
  · exact pair_zero_2_4
  · exact pair_zero_2_5
  · exact pair_zero_2_6
  · exact ((by decide : ¬ ((3 : Fin 7) < (0 : Fin 7))) hij).elim
  · exact ((by decide : ¬ ((3 : Fin 7) < (1 : Fin 7))) hij).elim
  · exact ((by decide : ¬ ((3 : Fin 7) < (2 : Fin 7))) hij).elim
  · exact ((by decide : ¬ ((3 : Fin 7) < (3 : Fin 7))) hij).elim
  · exact pair_zero_3_4
  · exact pair_zero_3_5
  · exact pair_zero_3_6
  · exact ((by decide : ¬ ((4 : Fin 7) < (0 : Fin 7))) hij).elim
  · exact ((by decide : ¬ ((4 : Fin 7) < (1 : Fin 7))) hij).elim
  · exact ((by decide : ¬ ((4 : Fin 7) < (2 : Fin 7))) hij).elim
  · exact ((by decide : ¬ ((4 : Fin 7) < (3 : Fin 7))) hij).elim
  · exact ((by decide : ¬ ((4 : Fin 7) < (4 : Fin 7))) hij).elim
  · exact pair_zero_4_5
  · exact pair_zero_4_6
  · exact ((by decide : ¬ ((5 : Fin 7) < (0 : Fin 7))) hij).elim
  · exact ((by decide : ¬ ((5 : Fin 7) < (1 : Fin 7))) hij).elim
  · exact ((by decide : ¬ ((5 : Fin 7) < (2 : Fin 7))) hij).elim
  · exact ((by decide : ¬ ((5 : Fin 7) < (3 : Fin 7))) hij).elim
  · exact ((by decide : ¬ ((5 : Fin 7) < (4 : Fin 7))) hij).elim
  · exact ((by decide : ¬ ((5 : Fin 7) < (5 : Fin 7))) hij).elim
  · exact pair_zero_5_6
  · exact ((by decide : ¬ ((6 : Fin 7) < (0 : Fin 7))) hij).elim
  · exact ((by decide : ¬ ((6 : Fin 7) < (1 : Fin 7))) hij).elim
  · exact ((by decide : ¬ ((6 : Fin 7) < (2 : Fin 7))) hij).elim
  · exact ((by decide : ¬ ((6 : Fin 7) < (3 : Fin 7))) hij).elim
  · exact ((by decide : ¬ ((6 : Fin 7) < (4 : Fin 7))) hij).elim
  · exact ((by decide : ¬ ((6 : Fin 7) < (5 : Fin 7))) hij).elim
  · exact ((by decide : ¬ ((6 : Fin 7) < (6 : Fin 7))) hij).elim

/-- Distinct nonzero scalar forms over F₂ have trivial simultaneous kernel. -/
theorem family_joint_zero (χ ψ : CharacterCoordinates)
    (hχ : χ ≠ 0) (hψ : ψ ≠ 0) (hne : χ ≠ ψ) (x : Input)
    (hx : family χ x = 0) (hy : family ψ x = 0) : x = 0 := by
  obtain ⟨i, rfl⟩ := label_cover χ hχ
  obtain ⟨j, rfl⟩ := label_cover ψ hψ
  have hij : i ≠ j := fun h => hne (congrArg label h)
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact pair_zero i j hij x hx hy
  · exact pair_zero j i hji x hy hx

theorem family_ker_inf_eq_bot (χ ψ : CharacterCoordinates)
    (hχ : χ ≠ 0) (hψ : ψ ≠ 0) (hne : χ ≠ ψ) :
    (family χ).ker ⊓ (family ψ).ker = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  exact (Submodule.mem_bot (R := ZMod 2)).mpr
    (family_joint_zero χ ψ hχ hψ hne x hx.1 hx.2)

/-- The independent-pair interface does not rely on how the two
characters were selected or enumerated. -/
theorem family_ker_inf_eq_bot_of_independent (χ ψ : CharacterCoordinates)
    (h : LinearIndependent (ZMod 2) (![χ, ψ] : Fin 2 → CharacterCoordinates)) :
    (family χ).ker ⊓ (family ψ).ker = ⊥ := by
  have hχ : χ ≠ 0 := by simpa using h.ne_zero (0 : Fin 2)
  have hψ : ψ ≠ 0 := by simpa using h.ne_zero (1 : Fin 2)
  have hne : χ ≠ ψ := by
    intro he
    have he' : (![χ, ψ] : Fin 2 → CharacterCoordinates) 0 =
        (![χ, ψ] : Fin 2 → CharacterCoordinates) 1 := he
    exact (by decide : (0 : Fin 2) ≠ 1) (h.injective he')
  exact family_ker_inf_eq_bot χ ψ hχ hψ hne

/-- Stacking the original two numerical maps has the same zero kernel. -/
theorem family_prod_ker_eq_bot (χ ψ : CharacterCoordinates)
    (hχ : χ ≠ 0) (hψ : ψ ≠ 0) (hne : χ ≠ ψ) :
    ((family χ).prod (family ψ)).ker = ⊥ := by
  rw [LinearMap.ker_prod]
  exact family_ker_inf_eq_bot χ ψ hχ hψ hne

end SymmetricSubgroupAsymptotics.BinaryCarrierCommutatorForms16T1547
