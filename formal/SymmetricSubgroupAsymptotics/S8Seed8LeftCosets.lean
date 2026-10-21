import SymmetricSubgroupAsymptotics.FiniteLeftCosetCoverComposition
import SymmetricSubgroupAsymptotics.FiniteGeneratorWord
import SymmetricSubgroupAsymptotics.S8Sylow128LeftCosets
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T8
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! A selected8-row local cover composes with the existing315-row ambient
cover. No new2520-row ambient transition or inverse table is introduced. -/
set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.S8Seed8LeftCosets
abbrev Ambient := Equiv.Perm (Fin 8)
abbrev H : Subgroup Ambient := Subgroup.closure (Set.range BinaryMenuCayley8T8.generators)

def seedInSylow : FiniteGeneratorWordCertificate BinaryMenuCayley8T8.generators BinaryMenuCayley8T35.generators where
  words := ![(.mul (.generator 0) (.generator 2)), (.mul (.mul (.generator 1) (.mul (.generator 2) (.generator 2))) (.mul (.generator 0) (.mul (.generator 2) (.generator 2))))]
  equations := by
    intro j
    fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel

theorem seed_le_sylow : H ≤ S8Sylow128LeftCosets.H := seedInSylow.closure_le

def localImages (i : Fin 8) : Fin 8 → Fin 8 :=
  (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then ![0, 1, 2, 3, 4, 5, 6, 7] else ![7, 6, 5, 4, 3, 2, 1, 0]) else (if i.val < 3 then ![3, 6, 5, 4, 7, 2, 1, 0] else ![7, 2, 5, 4, 3, 6, 1, 0])) else (if i.val < 6 then (if i.val < 5 then ![3, 2, 5, 4, 7, 6, 1, 0] else ![7, 6, 1, 4, 3, 2, 5, 0]) else (if i.val < 7 then ![7, 2, 1, 4, 3, 6, 5, 0] else ![3, 2, 1, 4, 7, 6, 5, 0])))

def localInverseImages (i : Fin 8) : Fin 8 → Fin 8 :=
  (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then ![0, 1, 2, 3, 4, 5, 6, 7] else ![7, 6, 5, 4, 3, 2, 1, 0]) else (if i.val < 3 then ![7, 6, 5, 0, 3, 2, 1, 4] else ![7, 6, 1, 4, 3, 2, 5, 0])) else (if i.val < 6 then (if i.val < 5 then ![7, 6, 1, 0, 3, 2, 5, 4] else ![7, 2, 5, 4, 3, 6, 1, 0]) else (if i.val < 7 then ![7, 2, 1, 4, 3, 6, 5, 0] else ![7, 2, 1, 0, 3, 6, 5, 4])))

private theorem local_left : ∀ (i x : Fin 8), localInverseImages i (localImages i x) = x := by decide +kernel
private theorem local_right : ∀ (i x : Fin 8), localImages i (localInverseImages i x) = x := by decide +kernel

def localRepresentatives (i : Fin 8) : Ambient where
  toFun := localImages i
  invFun := localInverseImages i
  left_inv := local_left i
  right_inv := local_right i

def localNext (i : Fin 8) (j : Fin 3) : Fin 8 :=
  (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then ![3, 7, 2] else ![7, 3, 5]) else (if i.val < 3 then ![6, 6, 4] else ![0, 1, 0])) else (if i.val < 6 then (if i.val < 5 then ![5, 5, 3] else ![4, 4, 6]) else (if i.val < 7 then ![2, 2, 7] else ![1, 0, 1]))) j

def localPrevious (i : Fin 8) (j : Fin 3) : Fin 8 :=
  (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then ![3, 7, 3] else ![7, 3, 7]) else (if i.val < 3 then ![6, 6, 0] else ![0, 1, 4])) else (if i.val < 6 then (if i.val < 5 then ![5, 5, 2] else ![4, 4, 1]) else (if i.val < 7 then ![2, 2, 5] else ![1, 0, 6]))) j

def localForwardWitness (i : Fin 8) (j : Fin 3) : Fin 16 :=
  (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then ![0, 13, 10] else ![7, 10, 13]) else (if i.val < 3 then ![7, 10, 4] else ![8, 10, 14])) else (if i.val < 6 then (if i.val < 5 then ![7, 10, 4] else ![7, 10, 13]) else (if i.val < 7 then ![7, 10, 13] else ![7, 1, 4]))) j

def localBackwardWitness (i : Fin 8) (j : Fin 3) : Fin 16 :=
  (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then ![0, 13, 14] else ![7, 10, 9]) else (if i.val < 3 then ![7, 10, 10] else ![8, 10, 9])) else (if i.val < 6 then (if i.val < 5 then ![7, 10, 9] else ![7, 10, 1]) else (if i.val < 7 then ![7, 10, 1] else ![7, 1, 1]))) j

private theorem local_step_checked : ∀ (i : Fin 8) (j : Fin 3),
    permutationCode (localRepresentatives i * BinaryMenuCayley8T35.generators j *
      (localRepresentatives (localNext i j))⁻¹) =
      BinaryMenuCayley8T8.certificate.rows (localForwardWitness i j) := by decide +kernel

private theorem local_inverse_step_checked : ∀ (i : Fin 8) (j : Fin 3),
    permutationCode (localRepresentatives i * (BinaryMenuCayley8T35.generators j)⁻¹ *
      (localRepresentatives (localPrevious i j))⁻¹) =
      BinaryMenuCayley8T8.certificate.rows (localBackwardWitness i j) := by decide +kernel

private theorem row_mem (k : Fin 16) :
    BinaryMenuCayley8T8.certificate.toCayley.elements k ∈ H :=
  (BinaryMenuCayley8T8.certificate.toCayley.mem_closure_iff _).mpr ⟨k, rfl⟩

def localCertificate : FiniteLeftCosetCover BinaryMenuCayley8T35.generators H 8 where
  representatives := localRepresentatives
  identity := 0
  identity_mem := by
    have h : localRepresentatives 0 = 1 := by decide +kernel
    rw [h]
    exact H.one_mem
  next := localNext
  prev := localPrevious
  step_mem i j := by
    have hrow : permutationCode (BinaryMenuCayley8T8.certificate.toCayley.elements (localForwardWitness i j)) =
        BinaryMenuCayley8T8.certificate.rows (localForwardWitness i j) :=
      BinaryMenuCayley8T8.certificate.encode_elements _
    have he := permutationCode_injective 8 ((local_step_checked i j).trans hrow.symm)
    rw [he]
    exact row_mem _
  inverse_step_mem i j := by
    have hrow : permutationCode (BinaryMenuCayley8T8.certificate.toCayley.elements (localBackwardWitness i j)) =
        BinaryMenuCayley8T8.certificate.rows (localBackwardWitness i j) :=
      BinaryMenuCayley8T8.certificate.encode_elements _
    have he := permutationCode_injective 8 ((local_inverse_step_checked i j).trans hrow.symm)
    rw [he]
    exact row_mem _

def representatives (i : Fin 2520) : Ambient :=
  let jk := (finProdFinEquiv : Fin 8 × Fin 315 ≃ Fin 2520).symm i
  localRepresentatives jk.1 * S8Sylow128LeftCosets.representatives jk.2

theorem covers (g : Ambient) : ∃ i : Fin 2520, g * (representatives i)⁻¹ ∈ H := by
  obtain ⟨jk, hjk⟩ := localCertificate.covers_compose
    S8Sylow128LeftCosets.representatives S8Sylow128LeftCosets.covers g
  refine ⟨finProdFinEquiv jk, ?_⟩
  simpa only [representatives, Equiv.symm_apply_apply] using hjk

end SymmetricSubgroupAsymptotics.S8Seed8LeftCosets
end
