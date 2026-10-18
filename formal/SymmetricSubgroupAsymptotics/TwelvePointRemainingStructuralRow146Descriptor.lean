import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralSchreierWordCertificate
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralSymmetricSixActions
import SymmetricSubgroupAsymptotics.SixPairCyclicSymmetricSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150

/-! Selected literal witnesses; no generated metadata is a proof. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow146Descriptor
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

def codes : Fin 5 → Equiv.Perm (Fin 4) := ![q0,q0,q7,q19,q1]

def topEmbedding : Equiv.Perm (Fin 4) →* Equiv.Perm (Fin 6) :=
  labels.permCongrHom.toMonoidHom.comp TwelvePointRemainingStructuralSymmetricSixActions.twistedEdge

def generatorData : SymmetricPairGeneratorData row146Generators where
  points := SixPairCyclicSymmetricSocles.pointChart
  topEmbedding := topEmbedding
  top_injective := labels.permCongrHom.injective.comp TwelvePointRemainingStructuralSymmetricSixActions.twistedEdge_injective
  codes := codes
  cycleWord := [4,3,3]
  swapWord := [2,4]
  cycle_bind := by decide +kernel
  swap_bind := by decide +kernel
  preserves := by
    intro i
    revert i
    unfold BinaryPairFrame.Preserves
    decide +kernel

private def permutationCode (q : Equiv.Perm (Fin 4)) : ℕ :=
  (q 0).val+4*(q 1).val+16*(q 2).val+64*(q 3).val

def sectionWord (q : Equiv.Perm (Fin 4)) : List (Fin 5) :=
  match permutationCode q with
  | 228 => []
  | 180 => [4]
  | 216 => [4,3,2]
  | 120 => [2,3,3]
  | 156 => [3,2]
  | 108 => [3,2,4]
  | 225 => [2,4]
  | 177 => [2]
  | 201 => [2,3,2]
  | 57 => [4,3,3]
  | 141 => [3,3,4]
  | 45 => [3,3]
  | 210 => [3,2,3]
  | 114 => [4,3]
  | 198 => [2,3,4]
  | 54 => [2,3]
  | 78 => [3,3,2,3]
  | 30 => [3,4,3]
  | 147 => [3,4]
  | 99 => [3]
  | 135 => [3,3,2]
  | 39 => [2,4,3]
  | 75 => [2,3,4,3]
  | 27 => [3,2,3,3]
  | _ => []

private def selected : Option (Equiv.Perm (Fin 4) × Fin 5) := some (q0,1)

private def coefficient (x : Equiv.Perm (Fin 4) × Fin 5) : Bool :=
  match 5*permutationCode x.1+x.2.val with
  | 1141 => true
  | 901 => true
  | 1081 => true
  | 601 => true
  | 781 => true
  | 541 => true
  | 1126 => true
  | 886 => true
  | 1006 => true
  | 286 => true
  | 706 => true
  | 226 => true
  | 1051 => true
  | 571 => true
  | 991 => true
  | 271 => true
  | 391 => true
  | 151 => true
  | 736 => true
  | 496 => true
  | 676 => true
  | 196 => true
  | 376 => true
  | 136 => true
  | _ => false

private def commutatorWord (x : Equiv.Perm (Fin 4) × Fin 5) :
    List ((Equiv.Perm (Fin 4) × Fin 5) × Fin 5) :=
  let c0 : (Equiv.Perm (Fin 4) × Fin 5) × Fin 5 := ((q0,0),3)
  let c1 : (Equiv.Perm (Fin 4) × Fin 5) × Fin 5 := ((q0,1),2)
  let c2 : (Equiv.Perm (Fin 4) × Fin 5) × Fin 5 := ((q0,1),4)
  match 5*permutationCode x.1+x.2.val with
  | 1140 => [c1,c2]
  | 900 => [c1,c2]
  | 901 => [c2]
  | 1080 => [c0,c2]
  | 1081 => [c2]
  | 600 => [c0,c2]
  | 780 => [c0,c1,c2]
  | 540 => [c0,c1,c2]
  | 541 => [c2]
  | 1125 => [c1,c2]
  | 1126 => [c1,c2]
  | 885 => [c1,c2]
  | 886 => [c1]
  | 1005 => [c0,c1,c2]
  | 1006 => [c1]
  | 285 => [c0,c1,c2]
  | 286 => [c1,c2]
  | 705 => [c0,c2]
  | 706 => [c1,c2]
  | 225 => [c0,c2]
  | 226 => [c1]
  | 1050 => [c0,c2]
  | 1051 => [c0]
  | 570 => [c0,c2]
  | 571 => [c0,c2]
  | 990 => [c0,c1,c2]
  | 991 => [c0,c2]
  | 270 => [c0,c1,c2]
  | 271 => [c0]
  | 390 => [c1,c2]
  | 391 => [c0]
  | 150 => [c1,c2]
  | 151 => [c0,c2]
  | 735 => [c0,c1,c2]
  | 736 => [c0,c1,c2]
  | 495 => [c0,c1,c2]
  | 496 => [c0,c1]
  | 675 => [c0,c2]
  | 676 => [c0,c1]
  | 195 => [c0,c2]
  | 196 => [c0,c1,c2]
  | 375 => [c1,c2]
  | 376 => [c0,c1,c2]
  | 135 => [c1,c2]
  | 136 => [c0,c1]
  | _ => []

def schreierData : SymmetricPairSchreierWordData row146Generators generatorData where
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

end SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow146Descriptor
