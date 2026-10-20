import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralSchreierWordCertificate
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralSymmetricSixActions
import SymmetricSubgroupAsymptotics.SixPairCyclicSymmetricSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150

/-! Selected literal witnesses; no generated metadata is a proof. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow102Descriptor
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open TwelvePointRemainingStructural

private def labels : Equiv.Perm (Fin 6) where
  toFun := ![0,2,4,5,3,1]
  invFun := ![0,5,1,4,2,3]
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

def codes : Fin 4 → Equiv.Perm (Fin 4) := ![q0,q3,q20,q6]

def topEmbedding : Equiv.Perm (Fin 4) →* Equiv.Perm (Fin 6) :=
  labels.permCongrHom.toMonoidHom.comp TwelvePointRemainingStructuralSymmetricSixActions.twistedEdge

def generatorData : SymmetricPairGeneratorData row102Generators where
  points := SixPairCyclicSymmetricSocles.pointChart
  topEmbedding := topEmbedding
  top_injective := labels.permCongrHom.injective.comp TwelvePointRemainingStructuralSymmetricSixActions.twistedEdge_injective
  codes := codes
  cycleWord := [3,1]
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
  | 180 => [1,2,1,3]
  | 216 => [3,1,2]
  | 120 => [1]
  | 156 => [1,1]
  | 108 => [2,1,3]
  | 225 => [3]
  | 177 => [1,2,1]
  | 201 => [1,2]
  | 57 => [3,1]
  | 141 => [2,3]
  | 45 => [1,1,2,2]
  | 210 => [1,1,2,1]
  | 114 => [1,3]
  | 198 => [1,2,3]
  | 54 => [2,2]
  | 78 => [1,1,2]
  | 30 => [1,3,1]
  | 147 => [3,2]
  | 99 => [2,1]
  | 135 => [2]
  | 39 => [3,2,1]
  | 75 => [1,1,2,3]
  | 27 => [1,2,2]
  | _ => []

private def selected : Option (Equiv.Perm (Fin 4) × Fin 4) := some (q0,0)

private def coefficient (x : Equiv.Perm (Fin 4) × Fin 4) : Bool :=
  match 4*permutationCode x.1+x.2.val with
  | 912 => true
  | 720 => true
  | 723 => true
  | 864 => true
  | 867 => true
  | 480 => true
  | 624 => true
  | 432 => true
  | 435 => true
  | 900 => true
  | 903 => true
  | 708 => true
  | 804 => true
  | 228 => true
  | 231 => true
  | 564 => true
  | 567 => true
  | 180 => true
  | 840 => true
  | 456 => true
  | 459 => true
  | 792 => true
  | 795 => true
  | 216 => true
  | 312 => true
  | 120 => true
  | 123 => true
  | 588 => true
  | 591 => true
  | 396 => true
  | 540 => true
  | 156 => true
  | 159 => true
  | 300 => true
  | 303 => true
  | 108 => true
  | _ => false

private def commutatorWord (x : Equiv.Perm (Fin 4) × Fin 4) :
    List ((Equiv.Perm (Fin 4) × Fin 4) × Fin 4) :=
  let c0 : (Equiv.Perm (Fin 4) × Fin 4) × Fin 4 := ((q0,0),1)
  let c1 : (Equiv.Perm (Fin 4) × Fin 4) × Fin 4 := ((q1,2),1)
  match 4*permutationCode x.1+x.2.val with
  | 721 => [c0,c1]
  | 722 => [c0]
  | 723 => [c0,c1]
  | 864 => [c0]
  | 865 => [c0,c1]
  | 866 => [c1]
  | 867 => [c1]
  | 480 => [c0]
  | 624 => [c1]
  | 627 => [c0]
  | 432 => [c1]
  | 434 => [c1]
  | 435 => [c0,c1]
  | 903 => [c0,c1]
  | 804 => [c1]
  | 228 => [c1]
  | 229 => [c1]
  | 564 => [c0]
  | 565 => [c1]
  | 566 => [c0]
  | 567 => [c0,c1]
  | 180 => [c0]
  | 840 => [c0]
  | 843 => [c0]
  | 456 => [c0]
  | 458 => [c0,c1]
  | 459 => [c0,c1]
  | 792 => [c1]
  | 793 => [c0]
  | 794 => [c1]
  | 795 => [c0,c1]
  | 216 => [c1]
  | 219 => [c0,c1]
  | 121 => [c0]
  | 122 => [c0,c1]
  | 123 => [c0]
  | 588 => [c1]
  | 590 => [c0,c1]
  | 591 => [c1]
  | 396 => [c1]
  | 540 => [c0]
  | 156 => [c0]
  | 157 => [c1]
  | 158 => [c0,c1]
  | 159 => [c0,c1]
  | 301 => [c1]
  | 302 => [c1]
  | 303 => [c0,c1]
  | 111 => [c1]
  | _ => []

def schreierData : SymmetricPairSchreierWordData row102Generators generatorData where
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

end SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow102Descriptor
