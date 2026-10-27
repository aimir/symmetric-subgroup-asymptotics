import SymmetricSubgroupAsymptotics.AmbientCyclePowerNormalizerWitness
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelvePresentationWords
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreePresentationWords
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourPresentationWords
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic.FinCases

/-! Three literal odd ambient normalizer witnesses. The primary JSON
6e582a97a9eddde83dc690b5a8d1aa239699f3bbad986eddf4da7f8bbb394b81
supplies DATA ONLY. Each inverse identity, whole-permutation conjugacy,
and sign is independently a kernel proof on the already bound small
presentation-generator images. No hash or diagnostic count is a premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.MathieuPrimeCycleOddNormalizerWitnesses
open AmbientCyclePowerNormalizerWitness

private def m12Forward (i : Fin 12) : Fin 12 :=
  match i.val with
  | 0 => 0
  | 1 => 2
  | 2 => 11
  | 3 => 7
  | 4 => 4
  | 5 => 9
  | 6 => 8
  | 7 => 5
  | 8 => 1
  | 9 => 6
  | 10 => 3
  | _ => 10

private def m12Inverse (i : Fin 12) : Fin 12 :=
  match i.val with
  | 0 => 0
  | 1 => 8
  | 2 => 1
  | 3 => 10
  | 4 => 4
  | 5 => 7
  | 6 => 9
  | 7 => 3
  | 8 => 6
  | 9 => 5
  | 10 => 11
  | _ => 2

def m12Sigma : Equiv.Perm (Fin 12) where
  toFun := m12Forward
  invFun := m12Inverse
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def m12Cycle : Equiv.Perm (Fin 12) :=
  CFSGMathieuTwelvePresentationWords.xPermutation * CFSGMathieuTwelvePresentationWords.yPermutation

theorem m12_conjugate_forward :
    m12Sigma * m12Cycle * m12Sigma⁻¹ = m12Cycle ^ 2 := by
  ext i
  fin_cases i <;> decide +kernel

theorem m12_conjugate_inverse :
    m12Sigma⁻¹ * m12Cycle * m12Sigma = m12Cycle ^ 6 := by
  ext i
  fin_cases i <;> decide +kernel

theorem m12_sign : Equiv.Perm.sign m12Sigma = (-1 : ℤˣ) := by
  decide +kernel

theorem m12_mem_normalizer :
    m12Sigma ∈ Subgroup.normalizer
      ((Subgroup.zpowers m12Cycle) : Set (Equiv.Perm (Fin 12))) :=
  mem_normalizer_zpowers m12Sigma m12Cycle 2 6
    m12_conjugate_forward m12_conjugate_inverse

private def m23Forward (i : Fin 23) : Fin 23 :=
  match i.val with
  | 0 => 0
  | 1 => 19
  | 2 => 20
  | 3 => 22
  | 4 => 6
  | 5 => 8
  | 6 => 10
  | 7 => 17
  | 8 => 13
  | 9 => 15
  | 10 => 7
  | 11 => 2
  | 12 => 14
  | 13 => 4
  | 14 => 21
  | 15 => 18
  | 16 => 12
  | 17 => 9
  | 18 => 11
  | 19 => 5
  | 20 => 16
  | 21 => 3
  | _ => 1

private def m23Inverse (i : Fin 23) : Fin 23 :=
  match i.val with
  | 0 => 0
  | 1 => 22
  | 2 => 11
  | 3 => 21
  | 4 => 13
  | 5 => 19
  | 6 => 4
  | 7 => 10
  | 8 => 5
  | 9 => 17
  | 10 => 6
  | 11 => 18
  | 12 => 16
  | 13 => 8
  | 14 => 12
  | 15 => 9
  | 16 => 20
  | 17 => 7
  | 18 => 15
  | 19 => 1
  | 20 => 2
  | 21 => 14
  | _ => 3

def m23Sigma : Equiv.Perm (Fin 23) where
  toFun := m23Forward
  invFun := m23Inverse
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def m23Cycle : Equiv.Perm (Fin 23) :=
  CFSGMathieuTwentyThreePresentationWords.xPermutation * CFSGMathieuTwentyThreePresentationWords.yPermutation

theorem m23_conjugate_forward :
    m23Sigma * m23Cycle * m23Sigma⁻¹ = m23Cycle ^ 5 := by
  ext i
  fin_cases i <;> decide +kernel

theorem m23_conjugate_inverse :
    m23Sigma⁻¹ * m23Cycle * m23Sigma = m23Cycle ^ 14 := by
  ext i
  fin_cases i <;> decide +kernel

theorem m23_sign : Equiv.Perm.sign m23Sigma = (-1 : ℤˣ) := by
  decide +kernel

theorem m23_mem_normalizer :
    m23Sigma ∈ Subgroup.normalizer
      ((Subgroup.zpowers m23Cycle) : Set (Equiv.Perm (Fin 23))) :=
  mem_normalizer_zpowers m23Sigma m23Cycle 5 14
    m23_conjugate_forward m23_conjugate_inverse

private def m24Forward (i : Fin 24) : Fin 24 :=
  match i.val with
  | 0 => 0
  | 1 => 11
  | 2 => 19
  | 3 => 20
  | 4 => 3
  | 5 => 22
  | 6 => 10
  | 7 => 16
  | 8 => 8
  | 9 => 5
  | 10 => 12
  | 11 => 21
  | 12 => 1
  | 13 => 23
  | 14 => 13
  | 15 => 7
  | 16 => 17
  | 17 => 14
  | 18 => 6
  | 19 => 18
  | 20 => 2
  | 21 => 9
  | 22 => 15
  | _ => 4

private def m24Inverse (i : Fin 24) : Fin 24 :=
  match i.val with
  | 0 => 0
  | 1 => 12
  | 2 => 20
  | 3 => 4
  | 4 => 23
  | 5 => 9
  | 6 => 18
  | 7 => 15
  | 8 => 8
  | 9 => 21
  | 10 => 6
  | 11 => 1
  | 12 => 10
  | 13 => 14
  | 14 => 17
  | 15 => 22
  | 16 => 7
  | 17 => 16
  | 18 => 19
  | 19 => 2
  | 20 => 3
  | 21 => 11
  | 22 => 5
  | _ => 13

def m24Sigma : Equiv.Perm (Fin 24) where
  toFun := m24Forward
  invFun := m24Inverse
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def m24Cycle : Equiv.Perm (Fin 24) :=
  CFSGMathieuTwentyFourPresentationWords.xPermutation * CFSGMathieuTwentyFourPresentationWords.yPermutation

theorem m24_conjugate_forward :
    m24Sigma * m24Cycle * m24Sigma⁻¹ = m24Cycle ^ 5 := by
  ext i
  fin_cases i <;> decide +kernel

theorem m24_conjugate_inverse :
    m24Sigma⁻¹ * m24Cycle * m24Sigma = m24Cycle ^ 14 := by
  ext i
  fin_cases i <;> decide +kernel

theorem m24_sign : Equiv.Perm.sign m24Sigma = (-1 : ℤˣ) := by
  decide +kernel

theorem m24_mem_normalizer :
    m24Sigma ∈ Subgroup.normalizer
      ((Subgroup.zpowers m24Cycle) : Set (Equiv.Perm (Fin 24))) :=
  mem_normalizer_zpowers m24Sigma m24Cycle 5 14
    m24_conjugate_forward m24_conjugate_inverse

end SymmetricSubgroupAsymptotics.MathieuPrimeCycleOddNormalizerWitnesses
