import SymmetricSubgroupAsymptotics.DoubleSymmetricFourPairFrameOriginalJointData
import SymmetricSubgroupAsymptotics.DoubleSymmetricFourSixImageConjugate
import SymmetricSubgroupAsymptotics.TwoAxisAbelianizationCover
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveOppositePairNaturalFamily
import SymmetricSubgroupAsymptotics.FiniteGeneratorWord
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row103DoubleSymmetricOriginalJointData
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open DoubleSymmetricFourSixImage (Group)
open DoubleSymmetricFourSixImageConjugate (model)
def labels : Equiv.Perm (Fin 6) := { toFun := ![0,2,1,5,3,4], invFun := ![0,2,1,4,5,3], left_inv := by decide +kernel, right_inv := by decide +kernel }
def pointChart : Fin 6 × ZMod 2 ≃ Fin 12 where
  toFun z := (![0,2,1,3,5,4,6,8,7,9,11,10] : Fin 12 → Fin 12) ⟨z.1.val+6*z.2.val,by have h:=z.2.val_lt; omega⟩
  invFun := ![(0,0),(2,0),(1,0),(3,0),(5,0),(4,0),(0,1),(2,1),(1,1),(3,1),(5,1),(4,1)]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
def codes : Fin 4 → Group := ![({ toFun := ![3,2,1,0], invFun := ![3,2,1,0], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![0,1,2,3], invFun := ![0,1,2,3], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![1,3,2,0], invFun := ![3,0,2,1], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![3,1,2,0], invFun := ![3,1,2,0], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1)]
def tops : Fin 4 → Equiv.Perm (Fin 6) := fun i => model labels (codes i)
private theorem preserves : ∀ i, BinaryPairFrame.Preserves pointChart (row103Generators i) (tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel
def frame : BinaryPairFrame row103Interface.top (Fin 6) :=
  BinaryPairFrame.ofGenerators pointChart row103Generators tops preserves
private theorem generator_top (i : Fin 4) : frame.top (closureGenerators row103Generators i)=tops i :=
  BinaryPairFrame.ofGenerators_top_generator pointChart row103Generators tops preserves i
private def original : Fin 4 → row103Interface.top := closureGenerators row103Generators
private theorem map_word (w : FiniteGeneratorWord (Fin 4)) :
    frame.top (w.eval original)=w.eval tops := by
  have ha : (fun i => frame.top (original i))=tops := by
    funext i
    exact generator_top i
  exact (FiniteGeneratorWord.map_eval frame.top original w).trans
    (congrArg (fun alphabet => w.eval alphabet) ha)
def allCodes : Fin 48 → Group := ![({ toFun := ![0,1,2,3], invFun := ![0,1,2,3], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![3,2,1,0], invFun := ![3,2,1,0], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![1,3,2,0], invFun := ![3,0,2,1], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![3,1,2,0], invFun := ![3,1,2,0], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![3,0,2,1], invFun := ![1,3,2,0], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![0,2,3,1], invFun := ![0,3,1,2], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![0,2,1,3], invFun := ![0,2,1,3], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![1,2,0,3], invFun := ![2,0,1,3], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![2,0,1,3], invFun := ![1,2,0,3], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![1,0,2,3], invFun := ![1,0,2,3], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![0,3,2,1], invFun := ![0,3,2,1], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![0,3,1,2], invFun := ![0,2,3,1], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![3,1,0,2], invFun := ![2,1,3,0], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![3,2,0,1], invFun := ![2,3,1,0], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![1,2,3,0], invFun := ![3,0,1,2], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![2,1,3,0], invFun := ![3,1,0,2], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![2,1,3,0], invFun := ![3,1,0,2], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![2,3,1,0], invFun := ![3,2,0,1], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![2,3,0,1], invFun := ![2,3,0,1], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![3,0,1,2], invFun := ![1,2,3,0], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![1,0,3,2], invFun := ![1,0,3,2], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![3,1,0,2], invFun := ![2,1,3,0], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![0,3,1,2], invFun := ![0,2,3,1], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![0,1,3,2], invFun := ![0,1,3,2], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![1,0,3,2], invFun := ![1,0,3,2], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![2,1,0,3], invFun := ![2,1,0,3], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![2,3,0,1], invFun := ![2,3,0,1], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![2,0,1,3], invFun := ![1,2,0,3], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![1,2,0,3], invFun := ![2,0,1,3], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![2,1,0,3], invFun := ![2,1,0,3], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![2,0,3,1], invFun := ![1,3,0,2], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![0,1,3,2], invFun := ![0,1,3,2], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![1,3,0,2], invFun := ![2,0,3,1], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![0,2,3,1], invFun := ![0,3,1,2], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![3,0,2,1], invFun := ![1,3,2,0], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![3,0,1,2], invFun := ![1,2,3,0], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![1,3,0,2], invFun := ![2,0,3,1], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![2,3,1,0], invFun := ![3,2,0,1], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![2,0,3,1], invFun := ![1,3,0,2], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![1,3,2,0], invFun := ![3,0,2,1], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![3,2,1,0], invFun := ![3,2,1,0], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![1,2,3,0], invFun := ![3,0,1,2], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![3,2,0,1], invFun := ![2,3,1,0], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![0,1,2,3], invFun := ![0,1,2,3], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![0,3,2,1], invFun := ![0,3,2,1], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![1,0,2,3], invFun := ![1,0,2,3], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1),({ toFun := ![0,2,1,3], invFun := ![0,2,1,3], left_inv := by decide +kernel, right_inv := by decide +kernel }, 1),({ toFun := ![3,1,2,0], invFun := ![3,1,2,0], left_inv := by decide +kernel, right_inv := by decide +kernel }, Equiv.swap 0 1)]
private theorem allCodes_surjective : Function.Surjective allCodes := by decide +kernel
private def allWords : Fin 48 → FiniteGeneratorWord (Fin 4) := ![.one,(.mul (.generator 0) .one),(.mul (.generator 2) .one),(.mul (.generator 3) .one),(.mul (.inv (.generator 2)) .one),(.mul (.generator 2) (.mul (.generator 0) .one)),(.mul (.generator 3) (.mul (.generator 0) .one)),(.mul (.inv (.generator 2)) (.mul (.generator 0) .one)),(.mul (.generator 0) (.mul (.generator 2) .one)),(.mul (.generator 3) (.mul (.generator 2) .one)),(.mul (.generator 2) (.mul (.generator 3) .one)),(.mul (.generator 0) (.mul (.inv (.generator 2)) .one)),(.mul (.generator 0) (.mul (.generator 2) (.mul (.generator 0) .one))),(.mul (.generator 3) (.mul (.generator 2) (.mul (.generator 0) .one))),(.mul (.generator 2) (.mul (.generator 3) (.mul (.generator 0) .one))),(.mul (.generator 0) (.mul (.inv (.generator 2)) (.mul (.generator 0) .one))),(.mul (.generator 2) (.mul (.generator 0) (.mul (.generator 2) .one))),(.mul (.generator 3) (.mul (.generator 0) (.mul (.generator 2) .one))),(.mul (.inv (.generator 2)) (.mul (.generator 0) (.mul (.generator 2) .one))),(.mul (.generator 0) (.mul (.generator 2) (.mul (.generator 3) .one))),(.mul (.generator 2) (.mul (.generator 0) (.mul (.inv (.generator 2)) .one))),(.mul (.inv (.generator 2)) (.mul (.generator 0) (.mul (.inv (.generator 2)) .one))),(.mul (.generator 2) (.mul (.generator 0) (.mul (.generator 2) (.mul (.generator 0) .one)))),(.mul (.generator 3) (.mul (.generator 0) (.mul (.generator 2) (.mul (.generator 0) .one)))),(.mul (.inv (.generator 2)) (.mul (.generator 0) (.mul (.generator 2) (.mul (.generator 0) .one)))),(.mul (.generator 0) (.mul (.generator 2) (.mul (.generator 3) (.mul (.generator 0) .one)))),(.mul (.generator 2) (.mul (.generator 0) (.mul (.inv (.generator 2)) (.mul (.generator 0) .one)))),(.mul (.inv (.generator 2)) (.mul (.generator 0) (.mul (.inv (.generator 2)) (.mul (.generator 0) .one)))),(.mul (.generator 0) (.mul (.generator 2) (.mul (.generator 0) (.mul (.generator 2) .one)))),(.mul (.generator 3) (.mul (.generator 2) (.mul (.generator 0) (.mul (.generator 2) .one)))),(.mul (.generator 2) (.mul (.generator 3) (.mul (.generator 0) (.mul (.generator 2) .one)))),(.mul (.generator 2) (.mul (.generator 0) (.mul (.generator 2) (.mul (.generator 3) .one)))),(.mul (.inv (.generator 2)) (.mul (.generator 0) (.mul (.generator 2) (.mul (.generator 3) .one)))),(.mul (.generator 0) (.mul (.inv (.generator 2)) (.mul (.generator 0) (.mul (.inv (.generator 2)) .one)))),(.mul (.generator 0) (.mul (.generator 2) (.mul (.generator 0) (.mul (.generator 2) (.mul (.generator 0) .one))))),(.mul (.generator 3) (.mul (.generator 2) (.mul (.generator 0) (.mul (.generator 2) (.mul (.generator 0) .one))))),(.mul (.generator 2) (.mul (.generator 3) (.mul (.generator 0) (.mul (.generator 2) (.mul (.generator 0) .one))))),(.mul (.generator 2) (.mul (.generator 0) (.mul (.generator 2) (.mul (.generator 3) (.mul (.generator 0) .one))))),(.mul (.inv (.generator 2)) (.mul (.generator 0) (.mul (.generator 2) (.mul (.generator 3) (.mul (.generator 0) .one))))),(.mul (.generator 0) (.mul (.inv (.generator 2)) (.mul (.generator 0) (.mul (.inv (.generator 2)) (.mul (.generator 0) .one))))),(.mul (.generator 2) (.mul (.generator 0) (.mul (.generator 2) (.mul (.generator 0) (.mul (.generator 2) .one))))),(.mul (.generator 3) (.mul (.generator 0) (.mul (.generator 2) (.mul (.generator 0) (.mul (.generator 2) .one))))),(.mul (.generator 0) (.mul (.generator 2) (.mul (.generator 0) (.mul (.generator 2) (.mul (.generator 3) .one))))),(.mul (.generator 2) (.mul (.generator 0) (.mul (.generator 2) (.mul (.generator 0) (.mul (.generator 2) (.mul (.generator 0) .one)))))),(.mul (.generator 3) (.mul (.generator 0) (.mul (.generator 2) (.mul (.generator 0) (.mul (.generator 2) (.mul (.generator 0) .one)))))),(.mul (.generator 0) (.mul (.generator 2) (.mul (.generator 0) (.mul (.generator 2) (.mul (.generator 3) (.mul (.generator 0) .one)))))),(.mul (.generator 3) (.mul (.generator 2) (.mul (.generator 0) (.mul (.generator 2) (.mul (.generator 0) (.mul (.generator 2) .one)))))),(.mul (.generator 3) (.mul (.generator 2) (.mul (.generator 0) (.mul (.generator 2) (.mul (.generator 0) (.mul (.generator 2) (.mul (.generator 0) .one)))))))]
private theorem allWords_top (i : Fin 48) :
    frame.top ((allWords i).eval original)=model labels (allCodes i) := by
  rw [map_word]
  revert i
  decide +kernel
private theorem image : frame.top.range=(model labels).range := by
  apply le_antisymm
  · rw [show frame.top.range=Subgroup.closure (Set.range tops) from
      BinaryPairFrame.ofGenerators_top_range pointChart row103Generators tops preserves]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨codes i,rfl⟩
  · rintro _ ⟨g,rfl⟩
    obtain ⟨i,rfl⟩ := allCodes_surjective g
    exact ⟨(allWords i).eval original,allWords_top i⟩
private def cycleWord : FiniteGeneratorWord (Fin 4) := (.mul (.inv (.generator 2)) (.mul (.generator 0) .one))
private theorem cycle_top : frame.top (cycleWord.eval original)=SixPairCyclicSymmetricSocles.cycle := by
  rw [map_word]
  decide +kernel
private def derived : Fin 4 → DerivedGeneratorWord (Fin 4) := ![.one,(.mul (.mul (.mul .one (.comm 1 2)) (.conj 3 (.comm 1 2))) (.conj 3 (.conj 3 (.comm 1 2)))),(.inv (.mul .one (.comm 2 3))),.one]
private def exponents : Fin 4 → ℕ × ℕ := ![(1,0),(0,0),(0,0),(0,1)]
private theorem identities (i : Fin 4) : original i=(derived i).eval original *
    original 0^(exponents i).1 * original 3^(exponents i).2 := by
  apply Subtype.ext
  revert i
  decide +kernel
private theorem axes (i : Fin 4) : TwoAxisAbelianizationCover.q (original i) ∈
    TwoAxisAbelianizationCover.Left (original 0) ⊔ TwoAxisAbelianizationCover.Right (original 3) := by
  let q : row103Interface.top →* row103Interface.top ⧸ commutator row103Interface.top := TwoAxisAbelianizationCover.q
  have hd : q ((derived i).eval original)=1 :=
    (QuotientGroup.eq_one_iff _).mpr ((derived i).eval_mem_commutator original)
  change q (original i)∈_
  rw [identities i,q.map_mul,q.map_mul,hd,one_mul,q.map_pow,q.map_pow]
  exact Subgroup.mul_mem _
    (Subgroup.mem_sup_left ((TwoAxisAbelianizationCover.Left (original 0)).pow_mem
      (Subgroup.mem_zpowers (q (original 0))) _))
    (Subgroup.mem_sup_right ((TwoAxisAbelianizationCover.Right (original 3)).pow_mem
      (Subgroup.mem_zpowers (q (original 3))) _))
private def cover := TwoAxisAbelianizationCover.cover (original 0) (original 3)
private theorem cover_surjective : Function.Surjective cover :=
  TwoAxisAbelianizationCover.cover_surjective (original 0) (original 3) original
    (closureGenerators_full row103Generators) axes

def flexibleData : DegreeTwoTwelveFlexibleProfiles.Data row103Interface :=
  DegreeTwoTwelveFlexibleProfiles.Data.ofExact
    (DoubleSymmetricFourPairFrameOriginalJointData.jointData row103Interface frame
      (cycleWord.eval original) cycle_top
      (DoubleSymmetricFourSixImageConjugate.topProjection frame labels image)
      (DoubleSymmetricFourSixImageConjugate.topProjection_surjective frame labels image)
      (DoubleSymmetricFourSixImageConjugate.topProjection_kernel_card frame labels image)
      cover cover_surjective PrimitiveAffineDegreeTwoTwelveOppositePairNaturalFamily.row103Natural)
    (by decide +kernel)
end SymmetricSubgroupAsymptotics.Row103DoubleSymmetricOriginalJointData
