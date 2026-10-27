import SymmetricSubgroupAsymptotics.FiniteListBooleanReflection
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoPackedPointMaps

/-! Packed-state960 algorithm pilot for the SAME checked first1/second1
cohort. The certificate computes ONLY Nat point states, Nat selectors,
literal/range Nat lists and Bool comparisons. Every22-point row is encoded in a110-bit Nat; no Fin/subtype proof term is
constructed in raw960Check. Typed range and original-group semantics enter
only AFTER its Bool equality, via the separately checked encoding bridge. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoPackedBooleanScalarPilot
open FiniteListBooleanReflection CFSGMathieuTwentyTwoPackedPointMaps
open CFSGMathieuTwentyTwoFiveTransversalCover
open CFSGMathieuTwentyTwoScalarRelationWords CFSGMathieuTwentyTwoRecoveredPairRelations

private def rawFailureCode (k l m : ℕ) : ℕ :=
  match k,l with
  | 2,5 => (match m with | 3 => 0 | 4 => 0 | _ => 22)
  | 2,6 => (match m with | 3 => 44 | 4 => 0 | _ => 44)
  | 2,7 => (match m with | 3 => 44 | 4 => 0 | _ => 0)
  | 2,8 => (match m with | 3 => 66 | 4 => 0 | _ => 0)
  | 2,9 => (match m with | 3 => 0 | 4 => 0 | _ => 44)
  | 2,10 => (match m with | 3 => 22 | 4 => 22 | _ => 0)
  | 2,11 => (match m with | 3 => 0 | 4 => 22 | _ => 0)
  | 2,12 => (match m with | 3 => 0 | 4 => 44 | _ => 0)
  | 2,15 => (match m with | 3 => 22 | 4 => 0 | _ => 0)
  | 2,16 => (match m with | 3 => 22 | 4 => 0 | _ => 0)
  | 3,8 => (match m with | 3 => 22 | 4 => 0 | _ => 0)
  | 3,9 => (match m with | 3 => 22 | 4 => 0 | _ => 0)
  | 3,10 => (match m with | 3 => 0 | 4 => 22 | _ => 0)
  | 3,12 => (match m with | 3 => 22 | 4 => 0 | _ => 0)
  | 3,13 => (match m with | 3 => 0 | 4 => 66 | _ => 44)
  | 3,16 => (match m with | 3 => 0 | 4 => 23 | _ => 44)
  | 3,17 => (match m with | 3 => 22 | 4 => 0 | _ => 0)
  | 3,18 => (match m with | 3 => 22 | 4 => 0 | _ => 0)
  | 3,19 => (match m with | 3 => 22 | 4 => 0 | _ => 0)
  | 3,20 => (match m with | 3 => 0 | 4 => 0 | _ => 22)
  | 4,7 => (match m with | 3 => 0 | 4 => 44 | _ => 0)
  | 4,9 => (match m with | 3 => 44 | 4 => 0 | _ => 22)
  | 4,10 => (match m with | 3 => 0 | 4 => 0 | _ => 22)
  | 4,11 => (match m with | 3 => 0 | 4 => 0 | _ => 22)
  | 4,14 => (match m with | 3 => 22 | 4 => 0 | _ => 0)
  | 4,15 => (match m with | 3 => 0 | 4 => 44 | _ => 0)
  | 4,17 => (match m with | 3 => 22 | 4 => 22 | _ => 0)
  | 4,18 => (match m with | 3 => 0 | 4 => 0 | _ => 22)
  | 4,19 => (match m with | 3 => 22 | 4 => 0 | _ => 0)
  | 4,20 => (match m with | 3 => 22 | 4 => 0 | _ => 0)
  | 5,9 => (match m with | 3 => 22 | 4 => 22 | _ => 44)
  | 5,10 => (match m with | 3 => 0 | 4 => 44 | _ => 22)
  | 5,13 => (match m with | 3 => 22 | 4 => 66 | _ => 0)
  | 5,14 => (match m with | 3 => 0 | 4 => 0 | _ => 66)
  | 5,16 => (match m with | 3 => 0 | 4 => 45 | _ => 0)
  | 5,17 => (match m with | 3 => 0 | 4 => 22 | _ => 0)
  | 5,19 => (match m with | 3 => 0 | 4 => 45 | _ => 0)
  | 5,20 => (match m with | 3 => 22 | 4 => 0 | _ => 0)
  | 6,7 => (match m with | 3 => 44 | 4 => 0 | _ => 66)
  | 6,8 => (match m with | 3 => 0 | 4 => 44 | _ => 0)
  | 6,10 => (match m with | 3 => 0 | 4 => 22 | _ => 0)
  | 6,12 => (match m with | 3 => 0 | 4 => 0 | _ => 44)
  | 6,15 => (match m with | 3 => 22 | 4 => 0 | _ => 0)
  | 6,17 => (match m with | 3 => 44 | 4 => 0 | _ => 0)
  | 6,18 => (match m with | 3 => 0 | 4 => 0 | _ => 22)
  | 6,19 => (match m with | 3 => 0 | 4 => 0 | _ => 22)
  | 6,20 => (match m with | 3 => 22 | 4 => 22 | _ => 22)
  | 8,5 => (match m with | 3 => 0 | 4 => 22 | _ => 22)
  | 8,7 => (match m with | 3 => 22 | 4 => 0 | _ => 0)
  | 8,8 => (match m with | 3 => 66 | 4 => 0 | _ => 0)
  | 8,9 => (match m with | 3 => 22 | 4 => 0 | _ => 0)
  | 8,10 => (match m with | 3 => 22 | 4 => 0 | _ => 0)
  | 8,11 => (match m with | 3 => 0 | 4 => 0 | _ => 23)
  | 8,15 => (match m with | 3 => 22 | 4 => 0 | _ => 22)
  | 8,16 => (match m with | 3 => 0 | 4 => 44 | _ => 0)
  | 8,17 => (match m with | 3 => 0 | 4 => 22 | _ => 0)
  | 8,20 => (match m with | 3 => 22 | 4 => 0 | _ => 0)
  | 9,6 => (match m with | 3 => 22 | 4 => 0 | _ => 0)
  | 9,7 => (match m with | 3 => 0 | 4 => 0 | _ => 22)
  | 9,8 => (match m with | 3 => 0 | 4 => 0 | _ => 22)
  | 9,9 => (match m with | 3 => 0 | 4 => 22 | _ => 0)
  | 9,10 => (match m with | 3 => 22 | 4 => 0 | _ => 22)
  | 9,12 => (match m with | 3 => 0 | 4 => 22 | _ => 0)
  | 9,17 => (match m with | 3 => 22 | 4 => 22 | _ => 0)
  | 9,18 => (match m with | 3 => 22 | 4 => 22 | _ => 22)
  | 10,5 => (match m with | 3 => 22 | 4 => 44 | _ => 66)
  | 10,7 => (match m with | 3 => 0 | 4 => 0 | _ => 23)
  | 10,8 => (match m with | 3 => 0 | 4 => 22 | _ => 0)
  | 10,9 => (match m with | 3 => 0 | 4 => 22 | _ => 24)
  | 10,11 => (match m with | 3 => 66 | 4 => 0 | _ => 0)
  | 10,15 => (match m with | 3 => 0 | 4 => 22 | _ => 0)
  | 10,16 => (match m with | 3 => 0 | 4 => 0 | _ => 22)
  | 10,17 => (match m with | 3 => 0 | 4 => 22 | _ => 0)
  | 10,20 => (match m with | 3 => 0 | 4 => 0 | _ => 22)
  | 11,7 => (match m with | 3 => 0 | 4 => 0 | _ => 22)
  | 11,8 => (match m with | 3 => 0 | 4 => 0 | _ => 22)
  | 11,9 => (match m with | 3 => 0 | 4 => 0 | _ => 22)
  | 11,10 => (match m with | 3 => 22 | 4 => 0 | _ => 0)
  | 11,11 => (match m with | 3 => 22 | 4 => 0 | _ => 0)
  | 11,16 => (match m with | 3 => 22 | 4 => 0 | _ => 0)
  | 11,17 => (match m with | 3 => 0 | 4 => 22 | _ => 0)
  | 11,18 => (match m with | 3 => 22 | 4 => 0 | _ => 44)
  | 11,19 => (match m with | 3 => 22 | 4 => 0 | _ => 44)
  | 11,20 => (match m with | 3 => 0 | 4 => 24 | _ => 0)
  | 13,5 => (match m with | 3 => 22 | 4 => 0 | _ => 0)
  | 13,6 => (match m with | 3 => 0 | 4 => 0 | _ => 22)
  | 13,7 => (match m with | 3 => 0 | 4 => 0 | _ => 66)
  | 13,10 => (match m with | 3 => 0 | 4 => 0 | _ => 22)
  | 13,12 => (match m with | 3 => 0 | 4 => 22 | _ => 0)
  | 13,14 => (match m with | 3 => 0 | 4 => 0 | _ => 45)
  | 13,16 => (match m with | 3 => 22 | 4 => 0 | _ => 0)
  | 13,17 => (match m with | 3 => 22 | 4 => 0 | _ => 0)
  | 13,18 => (match m with | 3 => 22 | 4 => 22 | _ => 0)
  | 13,19 => (match m with | 3 => 0 | 4 => 0 | _ => 22)
  | 13,20 => (match m with | 3 => 0 | 4 => 0 | _ => 23)
  | 15,5 => (match m with | 3 => 0 | 4 => 0 | _ => 22)
  | 15,7 => (match m with | 3 => 22 | 4 => 0 | _ => 0)
  | 15,8 => (match m with | 3 => 22 | 4 => 0 | _ => 0)
  | 15,11 => (match m with | 3 => 0 | 4 => 22 | _ => 0)
  | 15,12 => (match m with | 3 => 0 | 4 => 0 | _ => 22)
  | 15,14 => (match m with | 3 => 0 | 4 => 0 | _ => 44)
  | 15,15 => (match m with | 3 => 0 | 4 => 22 | _ => 22)
  | 15,16 => (match m with | 3 => 0 | 4 => 22 | _ => 0)
  | 15,17 => (match m with | 3 => 0 | 4 => 0 | _ => 22)
  | 15,20 => (match m with | 3 => 22 | 4 => 0 | _ => 66)
  | 16,5 => (match m with | 3 => 22 | 4 => 0 | _ => 0)
  | 16,6 => (match m with | 3 => 22 | 4 => 0 | _ => 0)
  | 16,7 => (match m with | 3 => 22 | 4 => 0 | _ => 22)
  | 16,8 => (match m with | 3 => 0 | 4 => 22 | _ => 0)
  | 16,9 => (match m with | 3 => 0 | 4 => 22 | _ => 0)
  | 16,11 => (match m with | 3 => 0 | 4 => 22 | _ => 0)
  | 16,13 => (match m with | 3 => 0 | 4 => 0 | _ => 66)
  | 16,14 => (match m with | 3 => 0 | 4 => 22 | _ => 22)
  | 16,16 => (match m with | 3 => 0 | 4 => 22 | _ => 0)
  | 16,18 => (match m with | 3 => 44 | 4 => 0 | _ => 0)
  | 18,7 => (match m with | 3 => 0 | 4 => 22 | _ => 44)
  | 18,13 => (match m with | 3 => 22 | 4 => 0 | _ => 0)
  | 18,14 => (match m with | 3 => 0 | 4 => 22 | _ => 22)
  | 18,15 => (match m with | 3 => 0 | 4 => 22 | _ => 44)
  | 18,17 => (match m with | 3 => 22 | 4 => 0 | _ => 22)
  | 18,18 => (match m with | 3 => 0 | 4 => 0 | _ => 22)
  | 18,19 => (match m with | 3 => 22 | 4 => 44 | _ => 0)
  | 19,7 => (match m with | 3 => 0 | 4 => 22 | _ => 0)
  | 19,8 => (match m with | 3 => 22 | 4 => 0 | _ => 22)
  | 19,10 => (match m with | 3 => 0 | 4 => 44 | _ => 0)
  | 19,11 => (match m with | 3 => 22 | 4 => 0 | _ => 22)
  | 19,12 => (match m with | 3 => 0 | 4 => 22 | _ => 0)
  | 19,15 => (match m with | 3 => 0 | 4 => 66 | _ => 0)
  | 19,16 => (match m with | 3 => 0 | 4 => 0 | _ => 22)
  | 19,18 => (match m with | 3 => 0 | 4 => 22 | _ => 22)
  | 19,20 => (match m with | 3 => 0 | 4 => 45 | _ => 0)
  | 20,5 => (match m with | 3 => 0 | 4 => 0 | _ => 44)
  | 20,6 => (match m with | 3 => 0 | 4 => 22 | _ => 44)
  | 20,8 => (match m with | 3 => 22 | 4 => 0 | _ => 0)
  | 20,12 => (match m with | 3 => 0 | 4 => 0 | _ => 44)
  | 20,13 => (match m with | 3 => 0 | 4 => 22 | _ => 0)
  | 20,15 => (match m with | 3 => 0 | 4 => 44 | _ => 22)
  | 20,17 => (match m with | 3 => 0 | 4 => 0 | _ => 22)
  | 20,19 => (match m with | 3 => 0 | 4 => 22 | _ => 0)
  | 20,20 => (match m with | 3 => 22 | 4 => 0 | _ => 22)
  | 21,6 => (match m with | 3 => 0 | 4 => 44 | _ => 0)
  | 21,7 => (match m with | 3 => 22 | 4 => 22 | _ => 0)
  | 21,10 => (match m with | 3 => 0 | 4 => 0 | _ => 22)
  | 21,12 => (match m with | 3 => 22 | 4 => 22 | _ => 0)
  | 21,14 => (match m with | 3 => 22 | 4 => 0 | _ => 22)
  | 21,18 => (match m with | 3 => 44 | 4 => 0 | _ => 23)
  | 21,19 => (match m with | 3 => 0 | 4 => 22 | _ => 0)
  | 21,20 => (match m with | 3 => 22 | 4 => 0 | _ => 0)
  | _,_ => 0

def rawThirdDomain : List ℕ := (List.range 20).map (fun k => k + 2)
def rawFourthDomain : List ℕ := (List.range 16).map (fun l => l + 5)
def rawFifthDomain : List ℕ := [3,4,21]

theorem mem_rawThirdDomain (k : Third) : k.val.val ∈ rawThirdDomain := by
  apply List.mem_map.mpr
  refine ⟨k.val.val - 2,List.mem_range.mpr ?_,?_⟩
  · have hk := k.val.isLt
    omega
  · have hk := k.property
    omega

theorem mem_rawFourthDomain (l : Fourth) : l.val.val ∈ rawFourthDomain := by
  have hnot : l.val ∉ CFSG.Certificates.Mathieu22.M22Certificates.SteinerSystem.blockB0 :=
    Finset.mem_compl.mp l.property
  have hlow : 5 ≤ l.val.val := by
    by_contra hn
    have hs : l.val.val = 0 ∨ l.val.val = 1 ∨ l.val.val = 2 ∨
        l.val.val = 3 ∨ l.val.val = 4 := by omega
    rcases hs with h | h | h | h | h
    · have he : l.val = 0 := Fin.ext h
      exact hnot (by simp [CFSG.Certificates.Mathieu22.M22Certificates.SteinerSystem.blockB0,he])
    · have he : l.val = 1 := Fin.ext h
      exact hnot (by simp [CFSG.Certificates.Mathieu22.M22Certificates.SteinerSystem.blockB0,he])
    · have he : l.val = 2 := Fin.ext h
      exact hnot (by simp [CFSG.Certificates.Mathieu22.M22Certificates.SteinerSystem.blockB0,he])
    · have he : l.val = 3 := Fin.ext h
      exact hnot (by simp [CFSG.Certificates.Mathieu22.M22Certificates.SteinerSystem.blockB0,he])
    · have he : l.val = 4 := Fin.ext h
      exact hnot (by simp [CFSG.Certificates.Mathieu22.M22Certificates.SteinerSystem.blockB0,he])
  have hne21 : l.val.val ≠ 21 := by
    intro h
    have he : l.val = 21 := Fin.ext h
    exact hnot (by simp [CFSG.Certificates.Mathieu22.M22Certificates.SteinerSystem.blockB0, he])
  apply List.mem_map.mpr
  refine ⟨l.val.val - 5,List.mem_range.mpr ?_,?_⟩ <;> have hb := l.val.isLt <;> omega

theorem mem_rawFifthDomain (m : Fifth) : m.val.val ∈ rawFifthDomain := by
  rcases m.property with h | h | h <;> simp [rawFifthDomain,h]

def rawMovedTest (k l m : ℕ) : Bool :=
  let code := rawFailureCode k l m
  let r := (code / 22) % 5
  let p := code % 22
  !(packedScalarRelation r 1 1 k l m p == p)

def raw960Check : Bool :=
  rawThirdDomain.all (fun k => rawFourthDomain.all (fun l => rawFifthDomain.all (rawMovedTest k l)))

theorem raw960Check_eq_true : raw960Check = true := by
  decide +kernel

def selectedRelator (k : Third) (l : Fourth) (m : Fifth) : Fin 5 :=
  ⟨(rawFailureCode k.val.val l.val.val m.val.val / 22) % 5,Nat.mod_lt _ (by decide)⟩

def selectedPoint (k : Third) (l : Fourth) (m : Fifth) : Fin 22 :=
  ⟨rawFailureCode k.val.val l.val.val m.val.val % 22,Nat.mod_lt _ (by decide)⟩

theorem raw_witness_moves (k : Third) (l : Fourth) (m : Fifth) :
    scalarRelation (selectedRelator k l m)
      (CFSGMathieuTwentyTwoPrefixOneOneExclusion.selectedCode k l m) (selectedPoint k l m) ≠
        selectedPoint k l m := by
  have hk := all_true_at rawThirdDomain _ raw960Check_eq_true k.val.val (mem_rawThirdDomain k)
  have hl := all_true_at rawFourthDomain _ hk l.val.val (mem_rawFourthDomain l)
  have hm := all_true_at rawFifthDomain _ hl m.val.val (mem_rawFifthDomain m)
  intro he
  apply not_beq_sound _ _ hm
  exact (packedScalarRelation_eq (selectedRelator k l m)
    (CFSGMathieuTwentyTwoPrefixOneOneExclusion.selectedCode k l m) (selectedPoint k l m)).trans
      (congrArg (fun p : Fin 22 => p.val) he)

theorem selected_excluded (k : Third) (l : Fourth) (m : Fifth) :
    ¬Accepts (decode (CFSGMathieuTwentyTwoPrefixOneOneExclusion.selectedCode k l m)) := by
  intro h
  exact raw_witness_moves k l m
    (accepts_scalarRelation (CFSGMathieuTwentyTwoPrefixOneOneExclusion.selectedCode k l m)
      h (selectedRelator k l m) (selectedPoint k l m))

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoPackedBooleanScalarPilot
