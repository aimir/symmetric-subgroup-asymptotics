import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveYCyclicCentralizerChart
import Mathlib.Data.Fin.VecNotation

/-! Explicit1944-code numbering for the SAME actual y ambient chart.
The24 four-point permutations and81 base-three phase vectors only number
this chart; they are not a table or membership test for original M12. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveYCentralizerFiniteEncoding
open CFSG.Certificates.Mathieu12 CFSGMathieuTwelvePresentationWords
open CFSGMathieuTwelveYCyclicCentralizerChart

private def permutationImages (i : Fin 24) : Fin 4 → Fin 4 :=
  match i.val with
  | 0 => ![0,1,2,3] | 1 => ![0,1,3,2] | 2 => ![0,2,1,3]
  | 3 => ![0,2,3,1] | 4 => ![0,3,1,2] | 5 => ![0,3,2,1]
  | 6 => ![1,0,2,3] | 7 => ![1,0,3,2] | 8 => ![1,2,0,3]
  | 9 => ![1,2,3,0] | 10 => ![1,3,0,2] | 11 => ![1,3,2,0]
  | 12 => ![2,0,1,3] | 13 => ![2,0,3,1] | 14 => ![2,1,0,3]
  | 15 => ![2,1,3,0] | 16 => ![2,3,0,1] | 17 => ![2,3,1,0]
  | 18 => ![3,0,1,2] | 19 => ![3,0,2,1] | 20 => ![3,1,0,2]
  | 21 => ![3,1,2,0] | 22 => ![3,2,0,1] | _ => ![3,2,1,0]

private def inverseIndex (i : Fin 24) : Fin 24 :=
  match i.val with
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5
  | 6 => 6 | 7 => 7 | 8 => 12 | 9 => 18 | 10 => 13 | 11 => 19
  | 12 => 8 | 13 => 10 | 14 => 14 | 15 => 20 | 16 => 16 | 17 => 22
  | 18 => 9 | 19 => 11 | 20 => 15 | 21 => 21 | 22 => 17 | _ => 23

def permutation (i : Fin 24) : Equiv.Perm (Fin 4) where
  toFun := permutationImages i
  invFun := permutationImages (inverseIndex i)
  left_inv := by
    intro p
    fin_cases i <;> fin_cases p <;> decide +kernel
  right_inv := by
    intro p
    fin_cases i <;> fin_cases p <;> decide +kernel

theorem permutation_injective : Function.Injective permutation := by
  decide +kernel

theorem permutation_surjective : Function.Surjective permutation := by
  apply ((Nat.bijective_iff_injective_and_card permutation).mpr
    ⟨permutation_injective,?_⟩).2
  norm_num [Nat.card_fin,Nat.card_perm,Fintype.card_perm,Fintype.card_fin,Nat.factorial]

def phases (j : Fin 81) (b : Fin 4) : ZMod 3 := (j.val / 3^b.val : ℕ)

theorem phases_encoding (j : Fin 81) :
    j.val = ∑ b : Fin 4, (phases j b).val * 3^b.val := by
  fin_cases j <;> decide +kernel

theorem phases_injective : Function.Injective phases := by
  intro i j hij
  apply Fin.ext
  rw [phases_encoding i,phases_encoding j]
  exact congrArg (fun d : Fin 4 → ZMod 3 => ∑ b : Fin 4, (d b).val * 3^b.val) hij

theorem phases_surjective : Function.Surjective phases := by
  apply ((Nat.bijective_iff_injective_and_card phases).mpr ⟨phases_injective,?_⟩).2
  norm_num [Nat.card_fin,Nat.card_fun,Nat.card_eq_fintype_card,ZMod.card]

def decodeCode (c : Fin 1944) : Code :=
  (permutation ⟨c.val/81,by omega⟩,phases ⟨c.val%81,Nat.mod_lt _ (by decide)⟩)

theorem decodeCode_surjective : Function.Surjective decodeCode := by
  rintro ⟨b,d⟩
  obtain ⟨i,rfl⟩ := permutation_surjective b
  obtain ⟨j,rfl⟩ := phases_surjective d
  let c : Fin 1944 := ⟨81*i.val+j.val,by omega⟩
  refine ⟨c,?_⟩
  have hd : c.val/81 = i.val := by dsimp only [c]; omega
  have hm : c.val%81 = j.val := by dsimp only [c]; omega
  apply Prod.ext
  · exact congrArg permutation (Fin.ext hd)
  · exact congrArg phases (Fin.ext hm)

def indexedChart (c : Fin 1944) : Perm12 := chart (decodeCode c)

theorem indexedChart_complete (z : Perm12) (hz : z*y.val = y.val*z) :
    ∃ c : Fin 1944, indexedChart c = z := by
  obtain ⟨d,hd⟩ := complete z hz
  obtain ⟨c,hc⟩ := decodeCode_surjective d
  exact ⟨c,by rw [indexedChart,hc,hd]⟩

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveYCentralizerFiniteEncoding
