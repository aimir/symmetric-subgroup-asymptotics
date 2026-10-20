import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralSchreierWordCertificate
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralSymmetricSixActions
import SymmetricSubgroupAsymptotics.SixPairCyclicSymmetricSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150

/-! Selected literal witnesses; no generated metadata is a proof. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow115Descriptor
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

def codes : Fin 4 → Equiv.Perm (Fin 4) := ![q0,q0,q19,q1]

def topEmbedding : Equiv.Perm (Fin 4) →* Equiv.Perm (Fin 6) :=
  labels.permCongrHom.toMonoidHom.comp SymmetricFourTwelvePointSocles.edge

def generatorData : SymmetricPairGeneratorData row115Generators where
  points := SixPairCyclicSymmetricSocles.pointChart
  topEmbedding := topEmbedding
  top_injective := labels.permCongrHom.injective.comp TwelvePointRemainingStructuralSymmetricSixActions.edge_injective
  codes := codes
  cycleWord := [3,2,2]
  swapWord := [2,3,2,2,3,2,3]
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
  | 180 => [3]
  | 216 => [2,3,2,2]
  | 120 => [2,3,2,2,3]
  | 156 => [3,2,3,2,2]
  | 108 => [3,2,3,2,2,3]
  | 225 => [2,3,2,2,3,2,3]
  | 177 => [2,3,2,2,3,2]
  | 201 => [3,2,2,3]
  | 57 => [3,2,2]
  | 141 => [2,2,3]
  | 45 => [2,2]
  | 210 => [3,2,3]
  | 114 => [3,2]
  | 198 => [2,2,3,2]
  | 54 => [2,2,3,2,3]
  | 78 => [2,3,2,3]
  | 30 => [2,3,2]
  | 147 => [2,3]
  | 99 => [2]
  | 135 => [3,2,2,3,2]
  | 39 => [3,2,2,3,2,3]
  | 75 => [2,2,3,2,2]
  | 27 => [3,2,3,2]
  | _ => []

private def selected : Option (Equiv.Perm (Fin 4) × Fin 4) := some (q0,1)

private def coefficient (x : Equiv.Perm (Fin 4) × Fin 4) : Bool :=
  match 4*permutationCode x.1+x.2.val with
  | 913 => true
  | 721 => true
  | 865 => true
  | 481 => true
  | 625 => true
  | 433 => true
  | 901 => true
  | 709 => true
  | 805 => true
  | 229 => true
  | 565 => true
  | 181 => true
  | 841 => true
  | 457 => true
  | 793 => true
  | 217 => true
  | 313 => true
  | 121 => true
  | 589 => true
  | 397 => true
  | 541 => true
  | 157 => true
  | 301 => true
  | 109 => true
  | _ => false

private def commutatorWord (x : Equiv.Perm (Fin 4) × Fin 4) :
    List ((Equiv.Perm (Fin 4) × Fin 4) × Fin 4) :=
  let c0 : (Equiv.Perm (Fin 4) × Fin 4) × Fin 4 := ((q0,0),2)
  let c1 : (Equiv.Perm (Fin 4) × Fin 4) × Fin 4 := ((q0,1),2)
  match 4*permutationCode x.1+x.2.val with
  | 912 => [c1]
  | 720 => [c0,c1]
  | 864 => [c1]
  | 480 => [c0]
  | 624 => [c0,c1]
  | 432 => [c0]
  | 900 => [c0,c1]
  | 901 => [c0]
  | 902 => [c0]
  | 708 => [c1]
  | 709 => [c0]
  | 710 => [c0]
  | 804 => [c0,c1]
  | 805 => [c0]
  | 228 => [c0]
  | 229 => [c0]
  | 564 => [c1]
  | 565 => [c0]
  | 180 => [c0]
  | 181 => [c0]
  | 840 => [c0]
  | 841 => [c0,c1]
  | 456 => [c1]
  | 457 => [c0,c1]
  | 792 => [c0]
  | 793 => [c0,c1]
  | 216 => [c0,c1]
  | 217 => [c0,c1]
  | 218 => [c0]
  | 312 => [c1]
  | 313 => [c0,c1]
  | 314 => [c0,c1]
  | 120 => [c0,c1]
  | 121 => [c0,c1]
  | 588 => [c0]
  | 589 => [c1]
  | 396 => [c0,c1]
  | 397 => [c1]
  | 540 => [c0]
  | 541 => [c1]
  | 542 => [c0,c1]
  | 156 => [c1]
  | 157 => [c1]
  | 158 => [c0]
  | 300 => [c0,c1]
  | 301 => [c1]
  | 303 => [c1]
  | 108 => [c1]
  | 109 => [c1]
  | 111 => [c1]
  | _ => []

def schreierData : SymmetricPairSchreierWordData row115Generators generatorData where
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

end SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow115Descriptor
