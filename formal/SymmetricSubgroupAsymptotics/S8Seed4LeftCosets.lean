import SymmetricSubgroupAsymptotics.FiniteLeftCosetCoverEquiv
import SymmetricSubgroupAsymptotics.FiniteGeneratorWord
import SymmetricSubgroupAsymptotics.S8Sylow128LeftCosets
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T4
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! A selected16-row local cover composes with the existing315-row ambient
cover. No new5040-row ambient transition or inverse table is introduced. -/
set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.S8Seed4LeftCosets
abbrev Ambient := Equiv.Perm (Fin 8)
abbrev H : Subgroup Ambient := Subgroup.closure (Set.range BinaryMenuCayley8T4.generators)

def sylowChart : Ambient where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7]
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

def seedInSylow : FiniteGeneratorWordCertificate BinaryMenuCayley8T4.generators sylowGenerators where
  words := ![(.generator 2), (.mul (.mul (.mul (.generator 0) (.generator 1)) (.mul (.inv (.generator 2)) (.generator 0))) (.mul (.mul (.inv (.generator 2)) (.generator 0)) (.mul (.inv (.generator 2)) (.generator 0))))]
  equations := by
    intro j
    fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel

theorem seed_le_sylow : H ≤ Subgroup.closure (Set.range sylowGenerators) := seedInSylow.closure_le

def localImages (i : Fin 16) : Fin 8 → Fin 8 :=
  (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then ![0, 1, 2, 3, 4, 5, 6, 7] else ![7, 6, 5, 4, 3, 2, 1, 0]) else (if i.val < 3 then ![3, 6, 5, 4, 7, 2, 1, 0] else ![7, 2, 5, 4, 3, 6, 1, 0])) else (if i.val < 6 then (if i.val < 5 then ![3, 2, 5, 4, 7, 6, 1, 0] else ![5, 6, 7, 4, 1, 2, 3, 0]) else (if i.val < 7 then ![1, 6, 7, 4, 5, 2, 3, 0] else ![5, 2, 7, 4, 1, 6, 3, 0]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then ![7, 6, 1, 4, 3, 2, 5, 0] else ![3, 6, 1, 4, 7, 2, 5, 0]) else (if i.val < 11 then ![7, 2, 1, 4, 3, 6, 5, 0] else ![3, 2, 1, 4, 7, 6, 5, 0])) else (if i.val < 14 then (if i.val < 13 then ![5, 6, 3, 4, 1, 2, 7, 0] else ![1, 6, 3, 4, 5, 2, 7, 0]) else (if i.val < 15 then ![5, 2, 3, 4, 1, 6, 7, 0] else ![1, 2, 3, 4, 5, 6, 7, 0]))))

def localInverseImages (i : Fin 16) : Fin 8 → Fin 8 :=
  (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then ![0, 1, 2, 3, 4, 5, 6, 7] else ![7, 6, 5, 4, 3, 2, 1, 0]) else (if i.val < 3 then ![7, 6, 5, 0, 3, 2, 1, 4] else ![7, 6, 1, 4, 3, 2, 5, 0])) else (if i.val < 6 then (if i.val < 5 then ![7, 6, 1, 0, 3, 2, 5, 4] else ![7, 4, 5, 6, 3, 0, 1, 2]) else (if i.val < 7 then ![7, 0, 5, 6, 3, 4, 1, 2] else ![7, 4, 1, 6, 3, 0, 5, 2]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then ![7, 2, 5, 4, 3, 6, 1, 0] else ![7, 2, 5, 0, 3, 6, 1, 4]) else (if i.val < 11 then ![7, 2, 1, 4, 3, 6, 5, 0] else ![7, 2, 1, 0, 3, 6, 5, 4])) else (if i.val < 14 then (if i.val < 13 then ![7, 4, 5, 2, 3, 0, 1, 6] else ![7, 0, 5, 2, 3, 4, 1, 6]) else (if i.val < 15 then ![7, 4, 1, 2, 3, 0, 5, 6] else ![7, 0, 1, 2, 3, 4, 5, 6]))))

private theorem local_left : ∀ (i : Fin 16) (x : Fin 8), localInverseImages i (localImages i x) = x := by decide +kernel
private theorem local_right : ∀ (i : Fin 16) (x : Fin 8), localImages i (localInverseImages i x) = x := by decide +kernel

def localRepresentatives (i : Fin 16) : Ambient where
  toFun := localImages i
  invFun := localInverseImages i
  left_inv := local_left i
  right_inv := local_right i

def localNext (i : Fin 16) (j : Fin 3) : Fin 16 :=
  (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then ![2, 10, 0] else ![7, 5, 9]) else (if i.val < 3 then ![0, 12, 15] else ![5, 7, 8])) else (if i.val < 6 then (if i.val < 5 then ![6, 14, 14] else ![3, 1, 1]) else (if i.val < 7 then ![4, 8, 7] else ![1, 3, 2]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then ![14, 6, 11] else ![15, 13, 13]) else (if i.val < 11 then ![12, 0, 10] else ![13, 15, 12])) else (if i.val < 14 then (if i.val < 13 then ![10, 2, 3] else ![11, 9, 5]) else (if i.val < 15 then ![8, 4, 4] else ![9, 11, 6])))) j

def localPrevious (i : Fin 16) (j : Fin 3) : Fin 16 :=
  (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then ![2, 10, 0] else ![7, 5, 5]) else (if i.val < 3 then ![0, 12, 7] else ![5, 7, 12])) else (if i.val < 6 then (if i.val < 5 then ![6, 14, 14] else ![3, 1, 13]) else (if i.val < 7 then ![4, 8, 15] else ![1, 3, 6]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then ![14, 6, 3] else ![15, 13, 1]) else (if i.val < 11 then ![12, 0, 10] else ![13, 15, 8])) else (if i.val < 14 then (if i.val < 13 then ![10, 2, 11] else ![11, 9, 9]) else (if i.val < 15 then ![8, 4, 4] else ![9, 11, 2])))) j

def localForwardWitness (i : Fin 16) (j : Fin 3) : Fin 8 :=
  (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then ![4, 2, 0] else ![5, 7, 2]) else (if i.val < 3 then ![4, 7, 4] else ![5, 7, 2])) else (if i.val < 6 then (if i.val < 5 then ![5, 7, 4] else ![5, 7, 6]) else (if i.val < 7 then ![5, 7, 0] else ![5, 7, 6]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then ![5, 7, 2] else ![5, 7, 4]) else (if i.val < 11 then ![5, 0, 2] else ![5, 7, 4])) else (if i.val < 14 then (if i.val < 13 then ![5, 7, 6] else ![5, 7, 0]) else (if i.val < 15 then ![5, 7, 6] else ![5, 7, 0])))) j

def localBackwardWitness (i : Fin 16) (j : Fin 3) : Fin 8 :=
  (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then ![4, 2, 2] else ![5, 7, 6]) else (if i.val < 3 then ![4, 7, 6] else ![5, 7, 6])) else (if i.val < 6 then (if i.val < 5 then ![5, 7, 6] else ![5, 7, 2]) else (if i.val < 7 then ![5, 7, 2] else ![5, 7, 2]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then ![5, 7, 0] else ![5, 7, 0]) else (if i.val < 11 then ![5, 0, 0] else ![5, 7, 0])) else (if i.val < 14 then (if i.val < 13 then ![5, 7, 4] else ![5, 7, 4]) else (if i.val < 15 then ![5, 7, 4] else ![5, 7, 4])))) j

private theorem local_step_checked : ∀ (i : Fin 16) (j : Fin 3),
    permutationCode (localRepresentatives i * sylowGenerators j *
      (localRepresentatives (localNext i j))⁻¹) =
      BinaryMenuCayley8T4.certificate.rows (localForwardWitness i j) := by decide +kernel

private theorem local_inverse_step_checked : ∀ (i : Fin 16) (j : Fin 3),
    permutationCode (localRepresentatives i * (sylowGenerators j)⁻¹ *
      (localRepresentatives (localPrevious i j))⁻¹) =
      BinaryMenuCayley8T4.certificate.rows (localBackwardWitness i j) := by decide +kernel

private theorem row_mem (k : Fin 8) :
    BinaryMenuCayley8T4.certificate.toCayley.elements k ∈ H :=
  (BinaryMenuCayley8T4.certificate.toCayley.mem_closure_iff _).mpr ⟨k, rfl⟩

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
    have hrow : permutationCode (BinaryMenuCayley8T4.certificate.toCayley.elements (localForwardWitness i j)) =
        BinaryMenuCayley8T4.certificate.rows (localForwardWitness i j) :=
      BinaryMenuCayley8T4.certificate.encode_elements _
    have he := permutationCode_injective 8 ((local_step_checked i j).trans hrow.symm)
    rw [he]
    exact row_mem _
  inverse_step_mem i j := by
    have hrow : permutationCode (BinaryMenuCayley8T4.certificate.toCayley.elements (localBackwardWitness i j)) =
        BinaryMenuCayley8T4.certificate.rows (localBackwardWitness i j) :=
      BinaryMenuCayley8T4.certificate.encode_elements _
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

end SymmetricSubgroupAsymptotics.S8Seed4LeftCosets
end
