import SymmetricSubgroupAsymptotics.FiniteLeftCosetCoverEquiv
import SymmetricSubgroupAsymptotics.FiniteGeneratorWord
import SymmetricSubgroupAsymptotics.S8Sylow128LeftCosets
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T11
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! A selected8-row local cover composes with the existing315-row ambient
cover. No new2520-row ambient transition or inverse table is introduced. -/
set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.S8Seed11LeftCosets
abbrev Ambient := Equiv.Perm (Fin 8)
abbrev H : Subgroup Ambient := Subgroup.closure (Set.range BinaryMenuCayley8T11.generators)

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

def seedInSylow : FiniteGeneratorWordCertificate BinaryMenuCayley8T11.generators sylowGenerators where
  words := ![(.mul (.mul (.generator 2) (.mul (.generator 0) (.generator 2))) (.mul (.generator 2) (.mul (.generator 0) (.generator 2)))), (.mul (.mul (.generator 0) (.generator 2)) (.mul (.generator 0) (.generator 2))), (.mul (.mul (.generator 0) (.mul (.generator 1) (.generator 2))) (.mul (.generator 2) (.mul (.generator 0) (.generator 2))))]
  equations := by
    intro j
    fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel

theorem seed_le_sylow : H ≤ Subgroup.closure (Set.range sylowGenerators) := seedInSylow.closure_le

def localImages (i : Fin 8) : Fin 8 → Fin 8 :=
  (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then ![0, 1, 2, 3, 4, 5, 6, 7] else ![7, 6, 5, 4, 3, 2, 1, 0]) else (if i.val < 3 then ![3, 6, 5, 4, 7, 2, 1, 0] else ![7, 2, 5, 4, 3, 6, 1, 0])) else (if i.val < 6 then (if i.val < 5 then ![5, 6, 7, 4, 1, 2, 3, 0] else ![1, 6, 7, 4, 5, 2, 3, 0]) else (if i.val < 7 then ![5, 2, 7, 4, 1, 6, 3, 0] else ![1, 2, 7, 4, 5, 6, 3, 0])))

def localInverseImages (i : Fin 8) : Fin 8 → Fin 8 :=
  (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then ![0, 1, 2, 3, 4, 5, 6, 7] else ![7, 6, 5, 4, 3, 2, 1, 0]) else (if i.val < 3 then ![7, 6, 5, 0, 3, 2, 1, 4] else ![7, 6, 1, 4, 3, 2, 5, 0])) else (if i.val < 6 then (if i.val < 5 then ![7, 4, 5, 6, 3, 0, 1, 2] else ![7, 0, 5, 6, 3, 4, 1, 2]) else (if i.val < 7 then ![7, 4, 1, 6, 3, 0, 5, 2] else ![7, 0, 1, 6, 3, 4, 5, 2])))

private theorem local_left : ∀ (i x : Fin 8), localInverseImages i (localImages i x) = x := by decide +kernel
private theorem local_right : ∀ (i x : Fin 8), localImages i (localInverseImages i x) = x := by decide +kernel

def localRepresentatives (i : Fin 8) : Ambient where
  toFun := localImages i
  invFun := localInverseImages i
  left_inv := local_left i
  right_inv := local_right i

def localNext (i : Fin 8) (j : Fin 3) : Fin 8 :=
  (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then ![2, 7, 7] else ![3, 4, 4]) else (if i.val < 3 then ![0, 5, 6] else ![1, 6, 5])) else (if i.val < 6 then (if i.val < 5 then ![6, 1, 0] else ![7, 2, 2]) else (if i.val < 7 then ![4, 3, 3] else ![5, 0, 1]))) j

def localPrevious (i : Fin 8) (j : Fin 3) : Fin 8 :=
  (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then ![2, 7, 4] else ![3, 4, 7]) else (if i.val < 3 then ![0, 5, 5] else ![1, 6, 6])) else (if i.val < 6 then (if i.val < 5 then ![6, 1, 1] else ![7, 2, 3]) else (if i.val < 7 then ![4, 3, 2] else ![5, 0, 0]))) j

def localForwardWitness (i : Fin 8) (j : Fin 3) : Fin 16 :=
  (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then ![8, 1, 15] else ![14, 15, 1]) else (if i.val < 3 then ![8, 7, 0] else ![14, 15, 1])) else (if i.val < 6 then (if i.val < 5 then ![14, 15, 11] else ![14, 7, 5]) else (if i.val < 7 then ![14, 15, 4] else ![14, 1, 5]))) j

def localBackwardWitness (i : Fin 8) (j : Fin 3) : Fin 16 :=
  (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then ![8, 1, 2] else ![14, 15, 12]) else (if i.val < 3 then ![8, 7, 12] else ![14, 15, 4])) else (if i.val < 6 then (if i.val < 5 then ![14, 15, 1] else ![14, 7, 1]) else (if i.val < 7 then ![14, 15, 9] else ![14, 1, 15]))) j

private theorem local_step_checked : ∀ (i : Fin 8) (j : Fin 3),
    permutationCode (localRepresentatives i * sylowGenerators j *
      (localRepresentatives (localNext i j))⁻¹) =
      BinaryMenuCayley8T11.certificate.rows (localForwardWitness i j) := by decide +kernel

private theorem local_inverse_step_checked : ∀ (i : Fin 8) (j : Fin 3),
    permutationCode (localRepresentatives i * (sylowGenerators j)⁻¹ *
      (localRepresentatives (localPrevious i j))⁻¹) =
      BinaryMenuCayley8T11.certificate.rows (localBackwardWitness i j) := by decide +kernel

private theorem row_mem (k : Fin 16) :
    BinaryMenuCayley8T11.certificate.toCayley.elements k ∈ H :=
  (BinaryMenuCayley8T11.certificate.toCayley.mem_closure_iff _).mpr ⟨k, rfl⟩

def localCertificate : FiniteLeftCosetCover sylowGenerators H 8 where
  representatives := localRepresentatives
  identity := 0
  identity_mem := by
    have h : localRepresentatives 0 = 1 := by decide +kernel
    rw [h]
    exact H.one_mem
  next := localNext
  prev := localPrevious
  step_mem i j := by
    have hrow : permutationCode (BinaryMenuCayley8T11.certificate.toCayley.elements (localForwardWitness i j)) =
        BinaryMenuCayley8T11.certificate.rows (localForwardWitness i j) :=
      BinaryMenuCayley8T11.certificate.encode_elements _
    have he := permutationCode_injective 8 ((local_step_checked i j).trans hrow.symm)
    rw [he]
    exact row_mem _
  inverse_step_mem i j := by
    have hrow : permutationCode (BinaryMenuCayley8T11.certificate.toCayley.elements (localBackwardWitness i j)) =
        BinaryMenuCayley8T11.certificate.rows (localBackwardWitness i j) :=
      BinaryMenuCayley8T11.certificate.encode_elements _
    have he := permutationCode_injective 8 ((local_inverse_step_checked i j).trans hrow.symm)
    rw [he]
    exact row_mem _

def representatives (i : Fin 2520) : Ambient :=
  let jk := (finProdFinEquiv : Fin 8 × Fin 315 ≃ Fin 2520).symm i
  localRepresentatives jk.1 * ambientRepresentatives jk.2

theorem covers (g : Ambient) : ∃ i : Fin 2520, g * (representatives i)⁻¹ ∈ H := by
  obtain ⟨jk, hjk⟩ := localCertificate.covers_compose
    ambientRepresentatives ambient_covers g
  refine ⟨finProdFinEquiv jk, ?_⟩
  simpa only [representatives, Equiv.symm_apply_apply] using hjk

end SymmetricSubgroupAsymptotics.S8Seed11LeftCosets
end
