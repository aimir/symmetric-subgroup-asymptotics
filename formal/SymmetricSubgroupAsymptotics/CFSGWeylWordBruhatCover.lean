import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Tactic.Group

/-! A word-indexed Bruhat-cover constructor. The input is the local
left-simple multiplication rule, not a Coxeter presentation or uniqueness
of representatives. A later actual-matrix installer must supply that
rule; this module alone does not identify a group normalizer. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGWeylWordBruhatCover
variable {G I : Type*} [Group G]

def wordValue (simple : I→G) : List I→G
  | []=>1
  | i::w=>simple i*wordValue simple w

def DoubleCell (B : Subgroup G) (n g : G) : Prop :=
  ∃b∈B,∃c∈B,g=b*n*c

def WordCells (B : Subgroup G) (simple : I→G) (g : G) : Prop :=
  ∃w : List I,DoubleCell B (wordValue simple w) g

theorem doubleCell_right_borel (B : Subgroup G) {n g c : G}
    (hg : DoubleCell B n g) (hc : c∈B) : DoubleCell B n (g*c) := by
  obtain ⟨b,hb,d,hd,rfl⟩ := hg
  exact ⟨b,hb,d*c,B.mul_mem hd hc,by group⟩

theorem wordCells_left_borel (B : Subgroup G) (simple : I→G) {b g : G}
    (hb : b∈B) (hg : WordCells B simple g) : WordCells B simple (b*g) := by
  obtain ⟨w,c,hc,d,hd,rfl⟩ := hg
  exact ⟨w,b*c,B.mul_mem hb hc,d,hd,by group⟩

theorem wordCells_left_simple (B : Subgroup G) (simple : I→G)
    (hstep : ∀(i : I)(w : List I)(b : G),b∈B→
      WordCells B simple (simple i*b*wordValue simple w))
    (i : I) {g : G} (hg : WordCells B simple g) :
    WordCells B simple (simple i*g) := by
  obtain ⟨w,b,hb,c,hc,rfl⟩ := hg
  obtain ⟨v,hv⟩ := hstep i w b hb
  refine ⟨v,?_⟩
  have hh := doubleCell_right_borel B hv hc
  simpa only [mul_assoc] using hh

theorem closure_le_wordCells (B : Subgroup G) (simple : I→G)
    (hfour : ∀i : I,(simple i)^4=1)
    (hstep : ∀(i : I)(w : List I)(b : G),b∈B→
      WordCells B simple (simple i*b*wordValue simple w)) :
    ∀g∈Subgroup.closure ((B : Set G)∪Set.range simple),WordCells B simple g := by
  intro g hg
  induction hg using Subgroup.closure_induction_left with
  | one=>
    exact ⟨[],1,B.one_mem,1,B.one_mem,by simp [wordValue]⟩
  | mul_left x hx y hy ih=>
    rcases hx with hx|⟨i,rfl⟩
    · exact wordCells_left_borel B simple hx ih
    · exact wordCells_left_simple B simple hstep i ih
  | inv_mul_cancel x hx y hy ih=>
    rcases hx with hx|⟨i,rfl⟩
    · exact wordCells_left_borel B simple (B.inv_mem hx) ih
    · have hinv : (simple i)⁻¹=simple i*simple i*simple i := by
        apply inv_eq_of_mul_eq_one_right
        calc
          simple i*(simple i*simple i*simple i)=(simple i)^4 := by
            simp only [pow_succ,pow_zero,one_mul,mul_assoc]
          _=1 := hfour i
      rw [hinv]
      have hh := wordCells_left_simple B simple hstep i
        (wordCells_left_simple B simple hstep i
          (wordCells_left_simple B simple hstep i ih))
      simpa only [mul_assoc] using hh

end SymmetricSubgroupAsymptotics.CFSGWeylWordBruhatCover
