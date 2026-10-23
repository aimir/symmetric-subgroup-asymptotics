import SymmetricSubgroupAsymptotics.CFSGWeylWordBruhatCover
import Mathlib.Tactic.FinCases

/-! A twelve-word reduction from actual simple squares in a normalized
subgroup and an actual six-letter braid identity. The proof is the
explicit finite left-multiplication table; no Coxeter presentation or
faithfulness of an abstract dihedral action is presumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGRankTwoSixBraidWords
open CFSGWeylWordBruhatCover
variable {G : Type*} [Group G]

def menuWord (k : Fin 12) : List (Fin 2) :=
  match k.val with
  | 0=>[] | 1=>[0] | 2=>[1]
  | 3=>[0,1] | 4=>[1,0]
  | 5=>[0,1,0] | 6=>[1,0,1]
  | 7=>[0,1,0,1] | 8=>[1,0,1,0]
  | 9=>[0,1,0,1,0] | 10=>[1,0,1,0,1]
  | _=>[0,1,0,1,0,1]

def representative (simple : Fin 2→G) (k : Fin 12) : G :=
  wordValue simple (menuWord k)

theorem simple_prefix_representative (T : Subgroup G) (simple : Fin 2→G)
    (hsquare : ∀i,simple i*simple i∈T)
    (hbraid : wordValue simple [0,1,0,1,0,1]=wordValue simple [1,0,1,0,1,0])
    (i : Fin 2) (k : Fin 12) :
    ∃j : Fin 12,∃t∈T,simple i*representative simple k=t*representative simple j := by
  fin_cases i
  · fin_cases k
    · refine ⟨1,1,T.one_mem,?_⟩
      simp only [representative,menuWord,wordValue,one_mul] <;> rfl
    · refine ⟨0,simple 0*simple 0,hsquare 0,?_⟩
      simp only [representative,menuWord,wordValue]
      group <;> rfl
    · refine ⟨3,1,T.one_mem,?_⟩
      simp only [representative,menuWord,wordValue,one_mul] <;> rfl
    · refine ⟨2,simple 0*simple 0,hsquare 0,?_⟩
      simp only [representative,menuWord,wordValue]
      group <;> rfl
    · refine ⟨5,1,T.one_mem,?_⟩
      simp only [representative,menuWord,wordValue,one_mul] <;> rfl
    · refine ⟨4,simple 0*simple 0,hsquare 0,?_⟩
      simp only [representative,menuWord,wordValue]
      group <;> rfl
    · refine ⟨7,1,T.one_mem,?_⟩
      simp only [representative,menuWord,wordValue,one_mul] <;> rfl
    · refine ⟨6,simple 0*simple 0,hsquare 0,?_⟩
      simp only [representative,menuWord,wordValue]
      group <;> rfl
    · refine ⟨9,1,T.one_mem,?_⟩
      simp only [representative,menuWord,wordValue,one_mul] <;> rfl
    · refine ⟨8,simple 0*simple 0,hsquare 0,?_⟩
      simp only [representative,menuWord,wordValue]
      group <;> rfl
    · refine ⟨11,1,T.one_mem,?_⟩
      simp only [representative,menuWord,wordValue,one_mul] <;> rfl
    · refine ⟨10,simple 0*simple 0,hsquare 0,?_⟩
      simp only [representative,menuWord,wordValue]
      group <;> rfl
  · fin_cases k
    · refine ⟨2,1,T.one_mem,?_⟩
      simp only [representative,menuWord,wordValue,one_mul] <;> rfl
    · refine ⟨4,1,T.one_mem,?_⟩
      simp only [representative,menuWord,wordValue,one_mul] <;> rfl
    · refine ⟨0,simple 1*simple 1,hsquare 1,?_⟩
      simp only [representative,menuWord,wordValue]
      group <;> rfl
    · refine ⟨6,1,T.one_mem,?_⟩
      simp only [representative,menuWord,wordValue,one_mul] <;> rfl
    · refine ⟨1,simple 1*simple 1,hsquare 1,?_⟩
      simp only [representative,menuWord,wordValue]
      group <;> rfl
    · refine ⟨8,1,T.one_mem,?_⟩
      simp only [representative,menuWord,wordValue,one_mul] <;> rfl
    · refine ⟨3,simple 1*simple 1,hsquare 1,?_⟩
      simp only [representative,menuWord,wordValue]
      group <;> rfl
    · refine ⟨10,1,T.one_mem,?_⟩
      simp only [representative,menuWord,wordValue,one_mul] <;> rfl
    · refine ⟨5,simple 1*simple 1,hsquare 1,?_⟩
      simp only [representative,menuWord,wordValue]
      group <;> rfl
    · refine ⟨11,1,T.one_mem,?_⟩
      change wordValue simple [1,0,1,0,1,0]=1*wordValue simple [0,1,0,1,0,1]
      rw [one_mul]
      exact hbraid.symm
    · refine ⟨7,simple 1*simple 1,hsquare 1,?_⟩
      simp only [representative,menuWord,wordValue]
      group <;> rfl
    · refine ⟨9,simple 1*simple 1,hsquare 1,?_⟩
      change simple 1*wordValue simple [0,1,0,1,0,1]=
        (simple 1*simple 1)*wordValue simple [0,1,0,1,0]
      rw [hbraid]
      simp only [wordValue]
      group <;> rfl

theorem word_factor (T : Subgroup G) (simple : Fin 2→G)
    (hsquare : ∀i,simple i*simple i∈T)
    (hnormal : ∀i,simple i∈Subgroup.normalizer T)
    (hbraid : wordValue simple [0,1,0,1,0,1]=wordValue simple [1,0,1,0,1,0])
    (w : List (Fin 2)) :
    ∃k : Fin 12,∃t∈T,wordValue simple w=t*representative simple k := by
  induction w with
  | nil=>exact ⟨0,1,T.one_mem,by simp [wordValue,representative,menuWord]⟩
  | cons i w ih=>
    obtain ⟨k,t,ht,hw⟩ := ih
    obtain ⟨j,u,hu,hs⟩ := simple_prefix_representative T simple hsquare hbraid i k
    have hc : simple i*t*(simple i)⁻¹∈T :=
      (Subgroup.mem_normalizer_iff.mp (hnormal i) t).mp ht
    refine ⟨j,(simple i*t*(simple i)⁻¹)*u,T.mul_mem hc hu,?_⟩
    calc
      wordValue simple (i::w)=simple i*(t*representative simple k) := by rw [wordValue,hw]
      _=(simple i*t*(simple i)⁻¹)*(simple i*representative simple k) := by group
      _=((simple i*t*(simple i)⁻¹)*u)*representative simple j := by rw [hs];group

theorem finite_word_cells (B T : Subgroup G) (hTB : T≤B) (simple : Fin 2→G)
    (hsquare : ∀i,simple i*simple i∈T)
    (hnormal : ∀i,simple i∈Subgroup.normalizer T)
    (hbraid : wordValue simple [0,1,0,1,0,1]=wordValue simple [1,0,1,0,1,0])
    (g : G) (hg : WordCells B simple g) :
    ∃k : Fin 12,DoubleCell B (representative simple k) g := by
  obtain ⟨w,b,hb,c,hc,he⟩ := hg
  obtain ⟨k,t,ht,hw⟩ := word_factor T simple hsquare hnormal hbraid w
  refine ⟨k,b*t,B.mul_mem hb (hTB ht),c,hc,?_⟩
  rw [he,hw]
  group

end SymmetricSubgroupAsymptotics.CFSGRankTwoSixBraidWords
