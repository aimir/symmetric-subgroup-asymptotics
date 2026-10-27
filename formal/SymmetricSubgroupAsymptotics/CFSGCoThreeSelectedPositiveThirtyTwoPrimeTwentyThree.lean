import SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoWordIteration00
import SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoWordIteration01
import SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoWordIteration02
import SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoWordIteration03
import SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoWordIteration04
import SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoWordIteration05
import SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoWordIteration06
import SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoWordIteration07
import SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoWordIteration08
import SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoWordIteration09
import SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoWordIteration10
import SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoWordIteration11
import SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoWordIteration12
import SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoWordIteration13
import SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoWordIteration14
import SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoWordIteration15
import SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoWordIteration16
import SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoWordIteration17
import SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoWordIteration18
import SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoWordIteration19
import SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoWordIteration20
import SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoWordIteration21
import SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoWordIteration22

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoPrimeTwentyThree
open CFSG.Models.MatrixGroups.Co3
open CFSGCoThreeSelectedPositiveThirtyTwoRows
abbrev Model := CFSG.Models.MatrixGroups.Co3.Model

theorem consecutive (i : Fin 23) : wordEnd (vectors i.castSucc)=vectors i.succ := by
  fin_cases i
  · exact CFSGCoThreeSelectedPositiveThirtyTwoWordIteration00.consecutive
  · exact CFSGCoThreeSelectedPositiveThirtyTwoWordIteration01.consecutive
  · exact CFSGCoThreeSelectedPositiveThirtyTwoWordIteration02.consecutive
  · exact CFSGCoThreeSelectedPositiveThirtyTwoWordIteration03.consecutive
  · exact CFSGCoThreeSelectedPositiveThirtyTwoWordIteration04.consecutive
  · exact CFSGCoThreeSelectedPositiveThirtyTwoWordIteration05.consecutive
  · exact CFSGCoThreeSelectedPositiveThirtyTwoWordIteration06.consecutive
  · exact CFSGCoThreeSelectedPositiveThirtyTwoWordIteration07.consecutive
  · exact CFSGCoThreeSelectedPositiveThirtyTwoWordIteration08.consecutive
  · exact CFSGCoThreeSelectedPositiveThirtyTwoWordIteration09.consecutive
  · exact CFSGCoThreeSelectedPositiveThirtyTwoWordIteration10.consecutive
  · exact CFSGCoThreeSelectedPositiveThirtyTwoWordIteration11.consecutive
  · exact CFSGCoThreeSelectedPositiveThirtyTwoWordIteration12.consecutive
  · exact CFSGCoThreeSelectedPositiveThirtyTwoWordIteration13.consecutive
  · exact CFSGCoThreeSelectedPositiveThirtyTwoWordIteration14.consecutive
  · exact CFSGCoThreeSelectedPositiveThirtyTwoWordIteration15.consecutive
  · exact CFSGCoThreeSelectedPositiveThirtyTwoWordIteration16.consecutive
  · exact CFSGCoThreeSelectedPositiveThirtyTwoWordIteration17.consecutive
  · exact CFSGCoThreeSelectedPositiveThirtyTwoWordIteration18.consecutive
  · exact CFSGCoThreeSelectedPositiveThirtyTwoWordIteration19.consecutive
  · exact CFSGCoThreeSelectedPositiveThirtyTwoWordIteration20.consecutive
  · exact CFSGCoThreeSelectedPositiveThirtyTwoWordIteration21.consecutive
  · exact CFSGCoThreeSelectedPositiveThirtyTwoWordIteration22.consecutive

theorem pow_initial (i : Fin 24) : (wordEnd^i.val) (vectors 0)=vectors i :=
  LinearMapSelectedKrylovPeriod.pow_apply_eq_vector wordEnd 23 vectors consecutive i

theorem return_twentyThree : (wordEnd^23) (vectors 0)=vectors 0 := by
  have h : (wordEnd^23) (vectors 0)=vectors 23 := pow_initial ⟨23,by decide⟩
  exact h.trans (show vectors 23=vectors 0 from rfl)

theorem nonreturn_one : wordEnd (vectors 0)≠vectors 0 := by
  have h : wordEnd (vectors 0)=vectors 1 := by simpa only [pow_one] using pow_initial ⟨1,by decide⟩
  have hn : vectors 1 (0 : Fin 22)≠vectors 0 0 := by decide +kernel
  intro he
  exact hn (congrFun (h.symm.trans he) 0)

private theorem wordEnd_binding :
    MatrixModelSelectedPositiveWordPrimePeriod.wordEnd 2 22 rows1 rows2 actualWord=wordEnd := rfl

attribute [local irreducible] CFSGCoThreeSelectedPositiveThirtyTwoRows.actualWord
  CFSGCoThreeSelectedPositiveThirtyTwoRows.wordEnd
  MatrixModelSelectedPositiveWordPrimePeriod.wordEnd
  CFSG.Models.MatrixData.matrix CFSG.Models.MatrixData.generators
  CFSG.Models.MatrixGroups.Co3.rows1 CFSG.Models.MatrixGroups.Co3.rows2

private theorem generic_return :
    (MatrixModelSelectedPositiveWordPrimePeriod.wordEnd 2 22 rows1 rows2 actualWord ^ 23)
      (vectors 0)=vectors 0 := by
  rw [wordEnd_binding]
  exact return_twentyThree

private theorem generic_nonreturn :
    MatrixModelSelectedPositiveWordPrimePeriod.wordEnd 2 22 rows1 rows2 actualWord
      (vectors 0)≠vectors 0 := by
  rw [wordEnd_binding]
  exact nonreturn_one

theorem exists_twenty_three_dvd_orderOf (hn : ¬IsMulCommutative Model) :
    ∃ g : Model, 23 ∣ orderOf g :=
  MatrixModelSelectedPositiveWordPrimePeriod.exists_prime_dvd_orderOf 2 22 rows1 rows2 actualWord 23
    (by decide) (vectors 0) generic_return generic_nonreturn hn

theorem twenty_three_dvd_card (hn : ¬IsMulCommutative Model) : 23 ∣ Nat.card Model :=
  MatrixModelSelectedPositiveWordPrimePeriod.prime_dvd_card 2 22 rows1 rows2 actualWord 23
    (by decide) (vectors 0) generic_return generic_nonreturn hn

end SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoPrimeTwentyThree
