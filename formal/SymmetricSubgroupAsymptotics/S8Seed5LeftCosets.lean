import SymmetricSubgroupAsymptotics.FiniteLeftCosetCoverEquiv
import SymmetricSubgroupAsymptotics.FiniteGeneratorWord
import SymmetricSubgroupAsymptotics.S8Sylow128LeftCosets
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T5
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! A selected16-row local cover composes with the existing315-row ambient
cover. No new5040-row ambient transition or inverse table is introduced. -/
set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.S8Seed5LeftCosets
abbrev Ambient := Equiv.Perm (Fin 8)
abbrev H : Subgroup Ambient := Subgroup.closure (Set.range BinaryMenuCayley8T5.generators)

def sylowChart : Ambient where
  toFun := ![0, 1, 3, 4, 2, 7, 5, 6]
  invFun := ![0, 1, 4, 2, 3, 6, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def sylowGenerators (j : Fin 3) : Ambient :=
  (MulAut.conj sylowChart) (BinaryMenuCayley8T35.generators j)

def ambientRepresentatives (i : Fin 315) : Ambient :=
  (MulAut.conj sylowChart) (S8Sylow128LeftCosets.representatives i)

theorem ambient_covers (g : Ambient) : ∃ i : Fin 315,
    g * (ambientRepresentatives i)⁻¹ ∈ Subgroup.closure (Set.range sylowGenerators) :=
  leftCoset_covers_equiv_generators (MulAut.conj sylowChart)
    BinaryMenuCayley8T35.generators S8Sylow128LeftCosets.representatives
    S8Sylow128LeftCosets.covers g

def seedInSylow : FiniteGeneratorWordCertificate BinaryMenuCayley8T5.generators sylowGenerators where
  words := ![(.mul (.mul (.generator 0) (.mul (.generator 1) (.inv (.generator 2)))) (.mul (.generator 0) (.mul (.generator 2) (.generator 2)))), (.mul (.mul (.generator 1) (.mul (.generator 2) (.generator 0))) (.mul (.generator 2) (.mul (.generator 2) (.generator 0))))]
  equations := by
    intro j
    fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel

theorem seed_le_sylow : H ≤ Subgroup.closure (Set.range sylowGenerators) := seedInSylow.closure_le

def localImages (i : Fin 16) : Fin 8 → Fin 8 :=
  (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then ![0, 1, 2, 3, 4, 5, 6, 7] else ![6, 2, 4, 7, 5, 1, 3, 0]) else (if i.val < 3 then ![4, 2, 6, 7, 5, 1, 3, 0] else ![7, 2, 1, 6, 5, 4, 3, 0])) else (if i.val < 6 then (if i.val < 5 then ![1, 2, 7, 6, 5, 4, 3, 0] else ![7, 2, 1, 4, 5, 6, 3, 0]) else (if i.val < 7 then ![6, 2, 4, 1, 5, 7, 3, 0] else ![4, 2, 6, 1, 5, 7, 3, 0]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then ![6, 2, 4, 7, 3, 1, 5, 0] else ![4, 2, 6, 7, 3, 1, 5, 0]) else (if i.val < 11 then ![7, 2, 1, 6, 3, 4, 5, 0] else ![1, 2, 7, 6, 3, 4, 5, 0])) else (if i.val < 14 then (if i.val < 13 then ![7, 2, 1, 4, 3, 6, 5, 0] else ![1, 2, 7, 4, 3, 6, 5, 0]) else (if i.val < 15 then ![6, 2, 4, 1, 3, 7, 5, 0] else ![4, 2, 6, 1, 3, 7, 5, 0]))))

def localInverseImages (i : Fin 16) : Fin 8 → Fin 8 :=
  (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then ![0, 1, 2, 3, 4, 5, 6, 7] else ![7, 5, 1, 6, 2, 4, 0, 3]) else (if i.val < 3 then ![7, 5, 1, 6, 0, 4, 2, 3] else ![7, 2, 1, 6, 5, 4, 3, 0])) else (if i.val < 6 then (if i.val < 5 then ![7, 0, 1, 6, 5, 4, 3, 2] else ![7, 2, 1, 6, 3, 4, 5, 0]) else (if i.val < 7 then ![7, 3, 1, 6, 2, 4, 0, 5] else ![7, 3, 1, 6, 0, 4, 2, 5]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then ![7, 5, 1, 4, 2, 6, 0, 3] else ![7, 5, 1, 4, 0, 6, 2, 3]) else (if i.val < 11 then ![7, 2, 1, 4, 5, 6, 3, 0] else ![7, 0, 1, 4, 5, 6, 3, 2])) else (if i.val < 14 then (if i.val < 13 then ![7, 2, 1, 4, 3, 6, 5, 0] else ![7, 0, 1, 4, 3, 6, 5, 2]) else (if i.val < 15 then ![7, 3, 1, 4, 2, 6, 0, 5] else ![7, 3, 1, 4, 0, 6, 2, 5]))))

private theorem local_left : ∀ (i : Fin 16) (x : Fin 8), localInverseImages i (localImages i x) = x := by decide +kernel
private theorem local_right : ∀ (i : Fin 16) (x : Fin 8), localImages i (localInverseImages i x) = x := by decide +kernel

def localRepresentatives (i : Fin 16) : Ambient where
  toFun := localImages i
  invFun := localInverseImages i
  left_inv := local_left i
  right_inv := local_right i

def localNext (i : Fin 16) (j : Fin 3) : Fin 16 :=
  (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then ![13, 7, 1] else ![8, 3, 11]) else (if i.val < 3 then ![9, 5, 4] else ![10, 1, 7])) else (if i.val < 6 then (if i.val < 5 then ![11, 6, 15] else ![12, 2, 8]) else (if i.val < 7 then ![14, 4, 5] else ![15, 0, 12]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then ![1, 10, 13] else ![2, 12, 0]) else (if i.val < 11 then ![3, 8, 2] else ![4, 14, 9])) else (if i.val < 14 then (if i.val < 13 then ![5, 9, 14] else ![0, 15, 6]) else (if i.val < 15 then ![6, 11, 3] else ![7, 13, 10])))) j

def localPrevious (i : Fin 16) (j : Fin 3) : Fin 16 :=
  (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then ![13, 7, 9] else ![8, 3, 0]) else (if i.val < 3 then ![9, 5, 10] else ![10, 1, 14])) else (if i.val < 6 then (if i.val < 5 then ![11, 6, 2] else ![12, 2, 6]) else (if i.val < 7 then ![14, 4, 13] else ![15, 0, 3]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then ![1, 10, 5] else ![2, 12, 11]) else (if i.val < 11 then ![3, 8, 15] else ![4, 14, 1])) else (if i.val < 14 then (if i.val < 13 then ![5, 9, 7] else ![0, 15, 8]) else (if i.val < 15 then ![6, 11, 12] else ![7, 13, 4])))) j

def localForwardWitness (i : Fin 16) (j : Fin 3) : Fin 8 :=
  (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then ![2, 2, 6] else ![7, 7, 0]) else (if i.val < 3 then ![7, 7, 0] else ![7, 7, 5])) else (if i.val < 6 then (if i.val < 5 then ![7, 7, 5] else ![7, 7, 3]) else (if i.val < 7 then ![7, 7, 2] else ![7, 0, 2]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then ![7, 7, 0] else ![7, 7, 1]) else (if i.val < 11 then ![7, 7, 5] else ![7, 7, 5])) else (if i.val < 14 then (if i.val < 13 then ![7, 7, 3] else ![0, 7, 3]) else (if i.val < 15 then ![7, 7, 2] else ![7, 7, 2])))) j

def localBackwardWitness (i : Fin 16) (j : Fin 3) : Fin 8 :=
  (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then ![2, 2, 1] else ![7, 7, 4]) else (if i.val < 3 then ![7, 7, 3] else ![7, 7, 0])) else (if i.val < 6 then (if i.val < 5 then ![7, 7, 2] else ![7, 7, 0]) else (if i.val < 7 then ![7, 7, 5] else ![7, 0, 3]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then ![7, 7, 5] else ![7, 7, 3]) else (if i.val < 11 then ![7, 7, 0] else ![7, 7, 2])) else (if i.val < 14 then (if i.val < 13 then ![7, 7, 0] else ![0, 7, 2]) else (if i.val < 15 then ![7, 7, 5] else ![7, 7, 3])))) j

private theorem local_step_checked : ∀ (i : Fin 16) (j : Fin 3),
    permutationCode (localRepresentatives i * sylowGenerators j *
      (localRepresentatives (localNext i j))⁻¹) =
      BinaryMenuCayley8T5.certificate.rows (localForwardWitness i j) := by decide +kernel

private theorem local_inverse_step_checked : ∀ (i : Fin 16) (j : Fin 3),
    permutationCode (localRepresentatives i * (sylowGenerators j)⁻¹ *
      (localRepresentatives (localPrevious i j))⁻¹) =
      BinaryMenuCayley8T5.certificate.rows (localBackwardWitness i j) := by decide +kernel

private theorem row_mem (k : Fin 8) :
    BinaryMenuCayley8T5.certificate.toCayley.elements k ∈ H :=
  (BinaryMenuCayley8T5.certificate.toCayley.mem_closure_iff _).mpr ⟨k, rfl⟩

def localCertificate : FiniteLeftCosetCover sylowGenerators H 16 where
  representatives := localRepresentatives
  identity := 0
  identity_mem := by
    have h : localRepresentatives 0 = 1 := by decide +kernel
    rw [h]
    exact H.one_mem
  next := localNext
  prev := localPrevious
  step_mem i j := by
    have hrow : permutationCode (BinaryMenuCayley8T5.certificate.toCayley.elements (localForwardWitness i j)) =
        BinaryMenuCayley8T5.certificate.rows (localForwardWitness i j) :=
      BinaryMenuCayley8T5.certificate.encode_elements _
    have he := permutationCode_injective 8 ((local_step_checked i j).trans hrow.symm)
    rw [he]
    exact row_mem _
  inverse_step_mem i j := by
    have hrow : permutationCode (BinaryMenuCayley8T5.certificate.toCayley.elements (localBackwardWitness i j)) =
        BinaryMenuCayley8T5.certificate.rows (localBackwardWitness i j) :=
      BinaryMenuCayley8T5.certificate.encode_elements _
    have he := permutationCode_injective 8 ((local_inverse_step_checked i j).trans hrow.symm)
    rw [he]
    exact row_mem _

def representatives (i : Fin 5040) : Ambient :=
  let jk := (finProdFinEquiv : Fin 16 × Fin 315 ≃ Fin 5040).symm i
  localRepresentatives jk.1 * ambientRepresentatives jk.2

theorem covers (g : Ambient) : ∃ i : Fin 5040, g * (representatives i)⁻¹ ∈ H := by
  obtain ⟨jk, hjk⟩ := localCertificate.covers_compose
    ambientRepresentatives ambient_covers g
  refine ⟨finProdFinEquiv jk, ?_⟩
  simpa only [representatives, Equiv.symm_apply_apply] using hjk

end SymmetricSubgroupAsymptotics.S8Seed5LeftCosets
end
