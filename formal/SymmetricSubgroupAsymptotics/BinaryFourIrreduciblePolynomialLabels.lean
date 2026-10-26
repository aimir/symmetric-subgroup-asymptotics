import SymmetricSubgroupAsymptotics.BinaryMonicPolynomialCode
import SymmetricSubgroupAsymptotics.BinaryFourPrimaryLabelCodes
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Group.Irreducible.Lemmas
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-! The actual nonzero-constant monic irreducibles of degree at most four
in a two-element field have seven literal interior coefficient words.
The proof uses the root1 obstruction and the single remaining reducible
square, rather than an enumeration of linear maps or group elements. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Polynomial
namespace SymmetricSubgroupAsymptotics.BinaryFourIrreduciblePolynomialLabels
variable {K : Type*} [Field K] [Fintype K] [CharP K 2]

def word (i : Fin 7) : List Bool :=
  match i.val with
  | 0 => []
  | 1 => [true]
  | 2 => [true,false]
  | 3 => [false,true]
  | 4 => [true,false,false]
  | 5 => [false,false,true]
  | _ => [true,true,true]

theorem degree_eq_length_word (i : Fin 7) :
    BinaryFourPrimaryLabelCodes.degree i=(word i).length+1 := by
  fin_cases i <;> rfl

private theorem expansion (p : K[X]) (hp : p.natDegree≤4) :
    p=C (p.coeff 0)+C (p.coeff 1)*X+C (p.coeff 2)*X^2+
      C (p.coeff 3)*X^3+C (p.coeff 4)*X^4 := by
  ext n
  by_cases hn : n≤4
  · interval_cases n <;> simp
  · have hz : p.coeff n=0 := coeff_eq_zero_of_natDegree_lt (by omega)
    have h0 : n≠0 := by omega
    have h1 : n≠1 := by omega
    have h2 : n≠2 := by omega
    have h3 : n≠3 := by omega
    have h4 : n≠4 := by omega
    simp [hz,coeff_C,coeff_C_mul,coeff_X,coeff_X_pow,h0,h1,h2,h3,h4,Ne.symm h1]

theorem exists_index (hK : Fintype.card K=2) (p : K[X])
    (hp : p.Monic) (hi : Irreducible p) (hp0 : p.coeff 0≠0)
    (hd : p.natDegree≤4) :
    ∃ i : Fin 7, BinaryMonicPolynomialCode.bits p=word i ∧
      p.natDegree=BinaryFourPrimaryLabelCodes.degree i := by
  classical
  have hpos : 0<p.natDegree := hi.natDegree_pos
  have hc0 : p.coeff 0=1 := (BinaryMonicPolynomialCode.zero_or_one hK _).resolve_left hp0
  have hexp := expansion p hd
  have h11 : (1:K)+1=0 := CharTwo.add_self_eq_zero 1
  have hb : ∃ i : Fin 7, BinaryMonicPolynomialCode.bits p=word i := by
    have hcases : p.natDegree=1 ∨ p.natDegree=2 ∨ p.natDegree=3 ∨ p.natDegree=4 := by omega
    rcases hcases with hdeg | hdeg | hdeg | hdeg
    · refine ⟨0,?_⟩
      simp [BinaryMonicPolynomialCode.bits,hdeg,word]
    · have hroot : p.eval 1≠0 := hi.not_isRoot_of_natDegree_ne_one (by omega)
      have hc2 : p.coeff 2=1 := hdeg ▸ hp.coeff_natDegree
      have hc3 : p.coeff 3=0 := coeff_eq_zero_of_natDegree_lt (by omega)
      have hc4 : p.coeff 4=0 := coeff_eq_zero_of_natDegree_lt (by omega)
      rcases BinaryMonicPolynomialCode.zero_or_one hK (p.coeff 1) with hc1 | hc1
      · exact False.elim (hroot (by rw [hexp]; simp [hc0,hc1,hc2,hc3,hc4,h11]))
      · refine ⟨1,?_⟩
        simp [BinaryMonicPolynomialCode.bits,hdeg,word,List.ofFn_succ,hc1]
    · have hroot : p.eval 1≠0 := hi.not_isRoot_of_natDegree_ne_one (by omega)
      have hc3 : p.coeff 3=1 := hdeg ▸ hp.coeff_natDegree
      have hc4 : p.coeff 4=0 := coeff_eq_zero_of_natDegree_lt (by omega)
      rcases BinaryMonicPolynomialCode.zero_or_one hK (p.coeff 1) with hc1 | hc1
      · rcases BinaryMonicPolynomialCode.zero_or_one hK (p.coeff 2) with hc2 | hc2
        · exact False.elim (hroot (by rw [hexp]; simp [hc0,hc1,hc2,hc3,hc4,h11]))
        · refine ⟨3,?_⟩
          simp [BinaryMonicPolynomialCode.bits,hdeg,word,List.ofFn_succ,hc1,hc2]
      · rcases BinaryMonicPolynomialCode.zero_or_one hK (p.coeff 2) with hc2 | hc2
        · refine ⟨2,?_⟩
          simp [BinaryMonicPolynomialCode.bits,hdeg,word,List.ofFn_succ,hc1,hc2]
        · exact False.elim (hroot (by rw [hexp]; simp [hc0,hc1,hc2,hc3,hc4,h11]))
    · have hroot : p.eval 1≠0 := hi.not_isRoot_of_natDegree_ne_one (by omega)
      have hc4 : p.coeff 4=1 := hdeg ▸ hp.coeff_natDegree
      rcases BinaryMonicPolynomialCode.zero_or_one hK (p.coeff 1) with hc1 | hc1
      · rcases BinaryMonicPolynomialCode.zero_or_one hK (p.coeff 2) with hc2 | hc2
        · rcases BinaryMonicPolynomialCode.zero_or_one hK (p.coeff 3) with hc3 | hc3
          · exact False.elim (hroot (by rw [hexp]; simp [hc0,hc1,hc2,hc3,hc4,h11]))
          · refine ⟨5,?_⟩
            simp [BinaryMonicPolynomialCode.bits,hdeg,word,List.ofFn_succ,hc1,hc2,hc3]
        · rcases BinaryMonicPolynomialCode.zero_or_one hK (p.coeff 3) with hc3 | hc3
          · have hs : p=(X^2+X+1)^2 := by
              calc
                p=X^4+X^2+1 := by
                  rw [hexp]
                  simp [hc0,hc1,hc2,hc3,hc4] <;> ring
                _=(X^2+X+1)^2 := by
                  rw [add_sq,add_sq]
                  simp only [show (2:K[X])=0 from CharTwo.two_eq_zero,
                    zero_mul,mul_zero,add_zero,zero_add,one_pow]
                  ring
            exact False.elim (not_irreducible_pow (by decide : (2:ℕ)≠1) (hs ▸ hi))
          · exact False.elim (hroot (by rw [hexp]; simp [hc0,hc1,hc2,hc3,hc4,h11]))
      · rcases BinaryMonicPolynomialCode.zero_or_one hK (p.coeff 2) with hc2 | hc2
        · rcases BinaryMonicPolynomialCode.zero_or_one hK (p.coeff 3) with hc3 | hc3
          · refine ⟨4,?_⟩
            simp [BinaryMonicPolynomialCode.bits,hdeg,word,List.ofFn_succ,hc1,hc2,hc3]
          · exact False.elim (hroot (by rw [hexp]; simp [hc0,hc1,hc2,hc3,hc4,h11]))
        · rcases BinaryMonicPolynomialCode.zero_or_one hK (p.coeff 3) with hc3 | hc3
          · exact False.elim (hroot (by rw [hexp]; simp [hc0,hc1,hc2,hc3,hc4,h11]))
          · refine ⟨6,?_⟩
            simp [BinaryMonicPolynomialCode.bits,hdeg,word,List.ofFn_succ,hc1,hc2,hc3]
  obtain ⟨i,hib⟩ := hb
  refine ⟨i,hib,?_⟩
  have hl := congrArg List.length hib
  rw [BinaryMonicPolynomialCode.length_bits] at hl
  have hiw := degree_eq_length_word i
  omega

end SymmetricSubgroupAsymptotics.BinaryFourIrreduciblePolynomialLabels
