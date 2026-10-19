import SymmetricSubgroupAsymptotics.Row147OriginalNaturalTwo
import SymmetricSubgroupAsymptotics.DoubleSymmetricFourPairFrameOriginalJointData
import SymmetricSubgroupAsymptotics.DoubleSymmetricFourSixImageConjugate
import SymmetricSubgroupAsymptotics.TwoAxisAbelianizationCover
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSymmetricPairNaturalFamily
import SymmetricSubgroupAsymptotics.FiniteGeneratorWord
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row147DoubleSymmetricOriginalJointData
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open DoubleSymmetricFourSixImage (Group)
open DoubleSymmetricFourSixImageConjugate (model)
def labels : Equiv.Perm (Fin 6) := { toFun := ![0,4,2,5,1,3], invFun := ![0,4,2,5,1,3], left_inv := by decide +kernel, right_inv := by decide +kernel }
def pointChart : Fin 6 × ZMod 2 ≃ Fin 12 where
  toFun z := (![0,5,7,1,3,9,11,6,8,2,4,10] : Fin 12 → Fin 12) ⟨z.1.val+6*z.2.val,by have h:=z.2.val_lt; omega⟩
  invFun := ![(0,0),(3,0),(3,1),(4,0),(4,1),(1,0),(1,1),(2,0),(2,1),(5,0),(5,1),(0,1)]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
def codes : Fin 3 → Group := ![({ toFun := ![0,1,2,3], invFun := ![0,1,2,3], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![0,3,1,2], invFun := ![0,2,3,1], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![1,0,2,3], invFun := ![1,0,2,3], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1)]
def tops : Fin 3 → Equiv.Perm (Fin 6) := fun i => model labels (codes i)
private theorem preserves : ∀ i, BinaryPairFrame.Preserves pointChart (row147Generators i) (tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel
def frame : BinaryPairFrame row147Interface.top (Fin 6) :=
  BinaryPairFrame.ofGenerators pointChart row147Generators tops preserves
private theorem generator_top (i : Fin 3) : frame.top (closureGenerators row147Generators i)=tops i :=
  BinaryPairFrame.ofGenerators_top_generator pointChart row147Generators tops preserves i
private def original := closureGenerators row147Generators
private theorem map_word (w : FiniteGeneratorWord (Fin 3)) :
    frame.top (w.eval original)=w.eval tops := by
  have ha : (fun i => frame.top (original i))=tops := by
    funext i
    exact generator_top i
  exact (FiniteGeneratorWord.map_eval frame.top original w).trans
    (congrArg (fun alphabet => w.eval alphabet) ha)
def allCodes : Fin 48 → Group := ![({ toFun := ![0,1,2,3], invFun := ![0,1,2,3], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![0,3,1,2], invFun := ![0,2,3,1], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![1,0,2,3], invFun := ![1,0,2,3], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![0,2,3,1], invFun := ![0,3,1,2], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![0,2,3,1], invFun := ![0,3,1,2], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![1,3,0,2], invFun := ![2,0,3,1], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![3,0,1,2], invFun := ![1,2,3,0], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![2,0,3,1], invFun := ![1,3,0,2], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![1,2,3,0], invFun := ![3,0,1,2], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![0,3,1,2], invFun := ![0,2,3,1], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![0,1,2,3], invFun := ![0,1,2,3], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![1,2,3,0], invFun := ![3,0,1,2], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![3,2,0,1], invFun := ![2,3,1,0], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![2,1,0,3], invFun := ![2,1,0,3], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![2,0,3,1], invFun := ![1,3,0,2], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![3,1,0,2], invFun := ![2,1,3,0], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![2,1,3,0], invFun := ![3,1,0,2], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![3,0,1,2], invFun := ![1,2,3,0], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![3,1,2,0], invFun := ![3,1,2,0], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![2,3,1,0], invFun := ![3,2,0,1], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![1,3,0,2], invFun := ![2,0,3,1], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![1,0,2,3], invFun := ![1,0,2,3], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![3,1,2,0], invFun := ![3,1,2,0], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![2,3,1,0], invFun := ![3,2,0,1], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![2,1,0,3], invFun := ![2,1,0,3], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![3,2,1,0], invFun := ![3,2,1,0], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![2,0,1,3], invFun := ![1,2,0,3], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![3,2,0,1], invFun := ![2,3,1,0], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![2,1,3,0], invFun := ![3,1,0,2], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![2,3,0,1], invFun := ![2,3,0,1], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![1,2,0,3], invFun := ![2,0,1,3], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![1,3,2,0], invFun := ![3,0,2,1], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![3,1,0,2], invFun := ![2,1,3,0], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![3,0,2,1], invFun := ![1,3,2,0], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![3,0,2,1], invFun := ![1,3,2,0], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![2,3,0,1], invFun := ![2,3,0,1], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![2,0,1,3], invFun := ![1,2,0,3], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![1,3,2,0], invFun := ![3,0,2,1], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![1,0,3,2], invFun := ![1,0,3,2], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![3,2,1,0], invFun := ![3,2,1,0], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![1,2,0,3], invFun := ![2,0,1,3], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![0,2,1,3], invFun := ![0,2,1,3], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![0,3,2,1], invFun := ![0,3,2,1], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![1,0,3,2], invFun := ![1,0,3,2], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![0,3,2,1], invFun := ![0,3,2,1], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![0,1,3,2], invFun := ![0,1,3,2], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![0,2,1,3], invFun := ![0,2,1,3], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![0,1,3,2], invFun := ![0,1,3,2], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1)]
private theorem allCodes_surjective : Function.Surjective allCodes := by decide +kernel
private def allWords : Fin 48 → FiniteGeneratorWord (Fin 3) := ![.one,(.mul (.generator 1) .one),(.mul (.generator 2) .one),(.mul (.inv (.generator 1)) .one),(.mul (.generator 1) (.mul (.generator 1) .one)),(.mul (.generator 2) (.mul (.generator 1) .one)),(.mul (.generator 1) (.mul (.generator 2) .one)),(.mul (.inv (.generator 1)) (.mul (.generator 2) .one)),(.mul (.generator 2) (.mul (.inv (.generator 1)) .one)),(.mul (.inv (.generator 1)) (.mul (.inv (.generator 1)) .one)),(.mul (.generator 1) (.mul (.generator 1) (.mul (.generator 1) .one))),(.mul (.generator 2) (.mul (.generator 1) (.mul (.generator 1) .one))),(.mul (.generator 1) (.mul (.generator 2) (.mul (.generator 1) .one))),(.mul (.inv (.generator 1)) (.mul (.generator 2) (.mul (.generator 1) .one))),(.mul (.generator 1) (.mul (.generator 1) (.mul (.generator 2) .one))),(.mul (.generator 2) (.mul (.generator 1) (.mul (.generator 2) .one))),(.mul (.generator 2) (.mul (.inv (.generator 1)) (.mul (.generator 2) .one))),(.mul (.inv (.generator 1)) (.mul (.inv (.generator 1)) (.mul (.generator 2) .one))),(.mul (.generator 1) (.mul (.generator 2) (.mul (.inv (.generator 1)) .one))),(.mul (.inv (.generator 1)) (.mul (.generator 2) (.mul (.inv (.generator 1)) .one))),(.mul (.generator 2) (.mul (.inv (.generator 1)) (.mul (.inv (.generator 1)) .one))),(.mul (.generator 2) (.mul (.generator 1) (.mul (.generator 1) (.mul (.generator 1) .one)))),(.mul (.generator 1) (.mul (.generator 2) (.mul (.generator 1) (.mul (.generator 1) .one)))),(.mul (.inv (.generator 1)) (.mul (.generator 2) (.mul (.generator 1) (.mul (.generator 1) .one)))),(.mul (.generator 1) (.mul (.generator 1) (.mul (.generator 2) (.mul (.generator 1) .one)))),(.mul (.generator 2) (.mul (.generator 1) (.mul (.generator 2) (.mul (.generator 1) .one)))),(.mul (.generator 2) (.mul (.inv (.generator 1)) (.mul (.generator 2) (.mul (.generator 1) .one)))),(.mul (.inv (.generator 1)) (.mul (.inv (.generator 1)) (.mul (.generator 2) (.mul (.generator 1) .one)))),(.mul (.generator 2) (.mul (.generator 1) (.mul (.generator 1) (.mul (.generator 2) .one)))),(.mul (.generator 1) (.mul (.generator 2) (.mul (.generator 1) (.mul (.generator 2) .one)))),(.mul (.inv (.generator 1)) (.mul (.generator 2) (.mul (.generator 1) (.mul (.generator 2) .one)))),(.mul (.generator 1) (.mul (.generator 2) (.mul (.inv (.generator 1)) (.mul (.generator 2) .one)))),(.mul (.generator 2) (.mul (.inv (.generator 1)) (.mul (.inv (.generator 1)) (.mul (.generator 2) .one)))),(.mul (.generator 2) (.mul (.generator 1) (.mul (.generator 2) (.mul (.inv (.generator 1)) .one)))),(.mul (.generator 2) (.mul (.generator 1) (.mul (.generator 2) (.mul (.generator 1) (.mul (.generator 1) .one))))),(.mul (.generator 2) (.mul (.inv (.generator 1)) (.mul (.generator 2) (.mul (.generator 1) (.mul (.generator 1) .one))))),(.mul (.generator 2) (.mul (.generator 1) (.mul (.generator 1) (.mul (.generator 2) (.mul (.generator 1) .one))))),(.mul (.inv (.generator 1)) (.mul (.generator 2) (.mul (.generator 1) (.mul (.generator 2) (.mul (.generator 1) .one))))),(.mul (.generator 1) (.mul (.generator 2) (.mul (.inv (.generator 1)) (.mul (.generator 2) (.mul (.generator 1) .one))))),(.mul (.generator 2) (.mul (.inv (.generator 1)) (.mul (.inv (.generator 1)) (.mul (.generator 2) (.mul (.generator 1) .one))))),(.mul (.generator 1) (.mul (.generator 1) (.mul (.generator 2) (.mul (.generator 1) (.mul (.generator 2) .one))))),(.mul (.generator 2) (.mul (.inv (.generator 1)) (.mul (.generator 2) (.mul (.generator 1) (.mul (.generator 2) .one))))),(.mul (.generator 2) (.mul (.generator 1) (.mul (.generator 2) (.mul (.inv (.generator 1)) (.mul (.generator 2) .one))))),(.mul (.inv (.generator 1)) (.mul (.generator 2) (.mul (.generator 1) (.mul (.generator 2) (.mul (.generator 1) (.mul (.generator 1) .one)))))),(.mul (.generator 2) (.mul (.inv (.generator 1)) (.mul (.generator 2) (.mul (.generator 1) (.mul (.generator 2) (.mul (.generator 1) .one)))))),(.mul (.generator 2) (.mul (.generator 1) (.mul (.generator 2) (.mul (.inv (.generator 1)) (.mul (.generator 2) (.mul (.generator 1) .one)))))),(.mul (.generator 2) (.mul (.generator 1) (.mul (.generator 1) (.mul (.generator 2) (.mul (.generator 1) (.mul (.generator 2) .one)))))),(.mul (.generator 2) (.mul (.inv (.generator 1)) (.mul (.generator 2) (.mul (.generator 1) (.mul (.generator 2) (.mul (.generator 1) (.mul (.generator 1) .one)))))))]
private theorem allWords_top (i : Fin 48) :
    frame.top ((allWords i).eval original)=model labels (allCodes i) := by
  rw [map_word]
  revert i
  decide +kernel
private theorem image : frame.top.range=(model labels).range := by
  apply le_antisymm
  · rw [show frame.top.range=Subgroup.closure (Set.range tops) from
      BinaryPairFrame.ofGenerators_top_range pointChart row147Generators tops preserves]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨codes i,rfl⟩
  · rintro _ ⟨g,rfl⟩
    obtain ⟨i,rfl⟩ := allCodes_surjective g
    exact ⟨(allWords i).eval original,allWords_top i⟩
private def cycleWord : FiniteGeneratorWord (Fin 3) := (.mul (.inv (.generator 1)) .one)
private theorem cycle_top : frame.top (cycleWord.eval original)=SixPairCyclicSymmetricSocles.cycle := by
  rw [map_word]
  decide +kernel
private def derived : Fin 3 → DerivedGeneratorWord (Fin 3) := ![(.mul (.mul (.mul .one (.comm 1 2)) (.conj 0 (.comm 1 2))) (.conj 0 (.conj 0 (.comm 1 2)))),.one,.one]
private def exponents : Fin 3 → ℕ × ℕ := ![(0,0),(1,0),(0,1)]
private theorem identities (i : Fin 3) : original i=(derived i).eval original *
    original 1^(exponents i).1 * original 2^(exponents i).2 := by
  apply Subtype.ext
  revert i
  decide +kernel
private theorem axes (i : Fin 3) : TwoAxisAbelianizationCover.q (original i) ∈
    TwoAxisAbelianizationCover.Left (original 1) ⊔ TwoAxisAbelianizationCover.Right (original 2) := by
  let q : row147Interface.top →* row147Interface.top ⧸ commutator row147Interface.top := TwoAxisAbelianizationCover.q
  have hd : q ((derived i).eval original)=1 :=
    (QuotientGroup.eq_one_iff _).mpr ((derived i).eval_mem_commutator original)
  change q (original i)∈_
  rw [identities i,q.map_mul,q.map_mul,hd,one_mul,q.map_pow,q.map_pow]
  exact Subgroup.mul_mem _
    (Subgroup.mem_sup_left ((TwoAxisAbelianizationCover.Left (original 1)).pow_mem
      (Subgroup.mem_zpowers (q (original 1))) _))
    (Subgroup.mem_sup_right ((TwoAxisAbelianizationCover.Right (original 2)).pow_mem
      (Subgroup.mem_zpowers (q (original 2))) _))
private def cover := TwoAxisAbelianizationCover.cover (original 1) (original 2)
private theorem cover_surjective : Function.Surjective cover :=
  TwoAxisAbelianizationCover.cover_surjective (original 1) (original 2) original
    (closureGenerators_full row147Generators) axes

def flexibleData : DegreeTwoTwelveFlexibleProfiles.Data row147Interface :=
  DegreeTwoTwelveFlexibleProfiles.Data.ofExact
    (DoubleSymmetricFourPairFrameOriginalJointData.jointData row147Interface frame
      (cycleWord.eval original) cycle_top
      (DoubleSymmetricFourSixImageConjugate.topProjection frame labels image)
      (DoubleSymmetricFourSixImageConjugate.topProjection_surjective frame labels image)
      (DoubleSymmetricFourSixImageConjugate.topProjection_kernel_card frame labels image)
      cover cover_surjective Row147OriginalNaturalTwo.natural_two)
    (by decide +kernel)
end SymmetricSubgroupAsymptotics.Row147DoubleSymmetricOriginalJointData
