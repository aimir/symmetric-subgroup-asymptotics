import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralSchreierJointData
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveThreeBlockNaturalFamily
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralSymmetricSixActions
import SymmetricSubgroupAsymptotics.PureA4FourOriginalPairFrames
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows51To100

/-! Selected literal witnesses; no generated metadata is a proof. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow95Descriptor
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open TwelvePointRemainingStructural

private def labels : Equiv.Perm (Fin 6) where
  toFun := ![0,1,2,5,4,3]
  invFun := ![0,1,2,5,4,3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def q0 : Equiv.Perm (Fin 4) where
  toFun := ![0,1,2,3]
  invFun := ![0,1,2,3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def q1 : Equiv.Perm (Fin 4) where
  toFun := ![0,1,3,2]
  invFun := ![0,1,3,2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def q2 : Equiv.Perm (Fin 4) where
  toFun := ![0,2,1,3]
  invFun := ![0,2,1,3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def q3 : Equiv.Perm (Fin 4) where
  toFun := ![0,2,3,1]
  invFun := ![0,3,1,2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def q4 : Equiv.Perm (Fin 4) where
  toFun := ![0,3,1,2]
  invFun := ![0,2,3,1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def q5 : Equiv.Perm (Fin 4) where
  toFun := ![0,3,2,1]
  invFun := ![0,3,2,1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def q6 : Equiv.Perm (Fin 4) where
  toFun := ![1,0,2,3]
  invFun := ![1,0,2,3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def q7 : Equiv.Perm (Fin 4) where
  toFun := ![1,0,3,2]
  invFun := ![1,0,3,2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def q8 : Equiv.Perm (Fin 4) where
  toFun := ![1,2,0,3]
  invFun := ![2,0,1,3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def q9 : Equiv.Perm (Fin 4) where
  toFun := ![1,2,3,0]
  invFun := ![3,0,1,2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def q10 : Equiv.Perm (Fin 4) where
  toFun := ![1,3,0,2]
  invFun := ![2,0,3,1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def q11 : Equiv.Perm (Fin 4) where
  toFun := ![1,3,2,0]
  invFun := ![3,0,2,1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def q12 : Equiv.Perm (Fin 4) where
  toFun := ![2,0,1,3]
  invFun := ![1,2,0,3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def q13 : Equiv.Perm (Fin 4) where
  toFun := ![2,0,3,1]
  invFun := ![1,3,0,2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def q14 : Equiv.Perm (Fin 4) where
  toFun := ![2,1,0,3]
  invFun := ![2,1,0,3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def q15 : Equiv.Perm (Fin 4) where
  toFun := ![2,1,3,0]
  invFun := ![3,1,0,2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def q16 : Equiv.Perm (Fin 4) where
  toFun := ![2,3,0,1]
  invFun := ![2,3,0,1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def q17 : Equiv.Perm (Fin 4) where
  toFun := ![2,3,1,0]
  invFun := ![3,2,0,1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def q18 : Equiv.Perm (Fin 4) where
  toFun := ![3,0,1,2]
  invFun := ![1,2,3,0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def q19 : Equiv.Perm (Fin 4) where
  toFun := ![3,0,2,1]
  invFun := ![1,3,2,0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def q20 : Equiv.Perm (Fin 4) where
  toFun := ![3,1,0,2]
  invFun := ![2,1,3,0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def q21 : Equiv.Perm (Fin 4) where
  toFun := ![3,1,2,0]
  invFun := ![3,1,2,0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def q22 : Equiv.Perm (Fin 4) where
  toFun := ![3,2,0,1]
  invFun := ![2,3,1,0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def q23 : Equiv.Perm (Fin 4) where
  toFun := ![3,2,1,0]
  invFun := ![3,2,1,0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def codes : Fin 4 → Equiv.Perm (Fin 4) := ![q0,q16,q19,q6]

def topEmbedding : Equiv.Perm (Fin 4) →* Equiv.Perm (Fin 6) :=
  labels.permCongrHom.toMonoidHom.comp SymmetricFourTwelvePointSocles.edge

def generatorData : SymmetricPairGeneratorData row95Generators where
  points := PureA4FourOriginalPairFrames.points
  topEmbedding := topEmbedding
  top_injective := labels.permCongrHom.injective.comp TwelvePointRemainingStructuralSymmetricSixActions.edge_injective
  codes := codes
  cycleWord := [2,1,3]
  swapWord := [3]
  cycle_bind := by decide +kernel
  swap_bind := by decide +kernel
  preserves := by
    intro i
    revert i
    unfold BinaryPairFrame.Preserves
    decide +kernel

private def permutationCode (q : Equiv.Perm (Fin 4)) : ℕ :=
  (q 0).val+4*(q 1).val+16*(q 2).val+64*(q 3).val

def sectionWord (q : Equiv.Perm (Fin 4)) : List (Fin 4) :=
  match permutationCode q with
  | 228 => []
  | 180 => [1,3,1]
  | 216 => [3,1,2]
  | 120 => [2,1,2]
  | 156 => [1,2,1]
  | 108 => [2,3]
  | 225 => [3]
  | 177 => [1,3,1,3]
  | 201 => [1,2]
  | 57 => [2,1,3]
  | 141 => [1,3,2]
  | 45 => [2,2]
  | 210 => [2,2,1]
  | 114 => [3,2,1]
  | 198 => [1,2,3]
  | 54 => [2,1]
  | 78 => [1]
  | 30 => [3,1]
  | 147 => [1,2,1,3]
  | 99 => [2]
  | 135 => [1,2,2]
  | 39 => [3,2]
  | 75 => [1,3]
  | 27 => [3,1,3]
  | _ => []

private def selected : Option (Equiv.Perm (Fin 4) × Fin 4) := some (q0,0)

private def coefficient (x : Equiv.Perm (Fin 4) × Fin 4) : Bool :=
  match 4*permutationCode x.1+x.2.val with
  | 912 => true
  | 720 => true
  | 864 => true
  | 480 => true
  | 624 => true
  | 432 => true
  | 900 => true
  | 708 => true
  | 804 => true
  | 228 => true
  | 564 => true
  | 180 => true
  | 840 => true
  | 456 => true
  | 792 => true
  | 216 => true
  | 312 => true
  | 120 => true
  | 588 => true
  | 396 => true
  | 540 => true
  | 156 => true
  | 300 => true
  | 108 => true
  | _ => false

private def commutatorWord (x : Equiv.Perm (Fin 4) × Fin 4) :
    List ((Equiv.Perm (Fin 4) × Fin 4) × Fin 4) :=
  let c0 : (Equiv.Perm (Fin 4) × Fin 4) × Fin 4 := ((q0,0),2)
  let c1 : (Equiv.Perm (Fin 4) × Fin 4) × Fin 4 := ((q1,1),2)
  match 4*permutationCode x.1+x.2.val with
  | 721 => [c0,c1]
  | 722 => [c0,c1]
  | 864 => [c0,c1]
  | 867 => [c0,c1]
  | 480 => [c0,c1]
  | 481 => [c0]
  | 482 => [c0]
  | 483 => [c1]
  | 624 => [c0]
  | 625 => [c1]
  | 626 => [c0,c1]
  | 432 => [c0]
  | 433 => [c0]
  | 709 => [c0]
  | 710 => [c0]
  | 804 => [c0]
  | 228 => [c0]
  | 229 => [c0]
  | 230 => [c0]
  | 564 => [c0,c1]
  | 565 => [c1]
  | 180 => [c0,c1]
  | 840 => [c0,c1]
  | 841 => [c0,c1]
  | 842 => [c0,c1]
  | 843 => [c0,c1]
  | 456 => [c0,c1]
  | 457 => [c1]
  | 458 => [c1]
  | 459 => [c1]
  | 792 => [c0]
  | 216 => [c0]
  | 217 => [c1]
  | 313 => [c0]
  | 121 => [c0,c1]
  | 588 => [c0]
  | 396 => [c0]
  | 540 => [c0,c1]
  | 541 => [c1]
  | 156 => [c0,c1]
  | _ => []

def schreierData : SymmetricPairSchreierWordData row95Generators generatorData where
  sectionWords := sectionWord
  section_eval := by
    intro q
    apply Equiv.ext
    intro j
    revert q j
    decide +kernel
  section_one := by decide +kernel
  selected := selected
  coefficient := coefficient
  commutators := commutatorWord
  reduction := by
    rintro ⟨q,i⟩
    apply Equiv.ext
    intro j
    revert q i j
    decide +kernel

theorem kernel_relative_head_le_one :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 generatorData.frame.top.ker) ≤ 1 :=
  TwelvePointRemainingStructural.SymmetricPairSchreierWordData.kernel_relative_head_le_one (C := schreierData)

private theorem word_top (w : List (Fin 4)) :
    generatorData.frame.top ((w.map (closureGenerators row95Generators)).prod)=
      generatorData.topEmbedding ((w.map generatorData.codes).prod) := by
  have hgen (i : Fin 4) : generatorData.frame.top (closureGenerators row95Generators i)=
      generatorData.topEmbedding (generatorData.codes i) := by
    rw [← generatorData.beta_action,generatorData.beta_generator]
  induction w with
  | nil => simp only [List.map_nil,List.prod_nil,map_one]
  | cons i w ih =>
    simp only [List.map_cons,List.prod_cons,map_mul]
    rw [hgen,ih]

private def cubicWord : List (Fin 4) := [1,2]
private def cubicElement : Row95Top := (cubicWord.map (closureGenerators row95Generators)).prod
private def representative : Fin 2 → Fin 6 := ![0,2]
private def orbitIndex : Fin 6 → Fin 2 := ![0,0,1,1,1,0]
private def exponent : Fin 6 → ℕ := ![0,2,0,2,1,1]

def orbitCover : SymmetricPairTwoOrbitCover generatorData where
  cubic := cubicElement
  representative := representative
  cover := by
    intro x
    refine ⟨orbitIndex x,exponent x,?_⟩
    dsimp only [cubicElement]
    rw [word_top cubicWord]
    exact (by decide +kernel : ∀ y : Fin 6,
      (generatorData.topEmbedding ((cubicWord.map generatorData.codes).prod) ^ exponent y)
        (representative (orbitIndex y))=y) x

def flexibleData : DegreeTwoTwelveFlexibleProfiles.Data row95Interface :=
  schreierData.jointDataAtTwo orbitCover row95Interface rfl
    DegreeTwoTwelveThreeBlockNaturalFamily.row95Natural

end SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow95Descriptor
