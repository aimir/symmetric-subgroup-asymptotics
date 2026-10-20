import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralSchreierWordCertificate
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralSymmetricSixActions
import SymmetricSubgroupAsymptotics.SixPairCyclicSymmetricSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150

/-! Selected literal witnesses; no generated metadata is a proof. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow149Descriptor
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

def codes : Fin 5 → Equiv.Perm (Fin 4) := ![q0,q0,q19,q21,q7]

def topEmbedding : Equiv.Perm (Fin 4) →* Equiv.Perm (Fin 6) :=
  labels.permCongrHom.toMonoidHom.comp TwelvePointRemainingStructuralSymmetricSixActions.twistedEdge

def generatorData : SymmetricPairGeneratorData row149Generators where
  points := SixPairCyclicSymmetricSocles.pointChart
  topEmbedding := topEmbedding
  top_injective := labels.permCongrHom.injective.comp TwelvePointRemainingStructuralSymmetricSixActions.twistedEdge_injective
  codes := codes
  cycleWord := [4,3,2]
  swapWord := [2,3]
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
  | 180 => [2,3,4]
  | 216 => [4,3,4]
  | 120 => [4,2,2]
  | 156 => [2,4]
  | 108 => [3,2]
  | 225 => [2,3]
  | 177 => [4]
  | 201 => [4,2,4]
  | 57 => [4,3,2]
  | 141 => [3,4]
  | 45 => [2,2]
  | 210 => [2,4,2]
  | 114 => [4,3]
  | 198 => [3,4,2]
  | 54 => [4,2]
  | 78 => [3,4,3]
  | 30 => [2,4,3]
  | 147 => [3,2,4]
  | 99 => [2]
  | 135 => [2,2,4]
  | 39 => [3]
  | 75 => [2,4,3,4]
  | 27 => [2,4,2,2]
  | _ => []

private def selected : Option (Equiv.Perm (Fin 4) × Fin 5) := some (q0,1)

private def coefficient (x : Equiv.Perm (Fin 4) × Fin 5) : Bool :=
  match 5*permutationCode x.1+x.2.val with
  | 1141 => true
  | 901 => true
  | 1081 => true
  | 1082 => true
  | 1083 => true
  | 601 => true
  | 604 => true
  | 781 => true
  | 541 => true
  | 1126 => true
  | 886 => true
  | 1006 => true
  | 1007 => true
  | 286 => true
  | 289 => true
  | 706 => true
  | 226 => true
  | 1051 => true
  | 1054 => true
  | 571 => true
  | 991 => true
  | 992 => true
  | 994 => true
  | 271 => true
  | 391 => true
  | 392 => true
  | 394 => true
  | 151 => true
  | 152 => true
  | 736 => true
  | 496 => true
  | 676 => true
  | 196 => true
  | 376 => true
  | 377 => true
  | 136 => true
  | 138 => true
  | 139 => true
  | _ => false

private def commutatorWord (x : Equiv.Perm (Fin 4) × Fin 5) :
    List ((Equiv.Perm (Fin 4) × Fin 5) × Fin 5) :=
  let c0 : (Equiv.Perm (Fin 4) × Fin 5) × Fin 5 := ((q0,0),2)
  let c1 : (Equiv.Perm (Fin 4) × Fin 5) × Fin 5 := ((q0,0),3)
  let c2 : (Equiv.Perm (Fin 4) × Fin 5) × Fin 5 := ((q0,1),3)
  match 5*permutationCode x.1+x.2.val with
  | 1140 => [c0,c2]
  | 900 => [c0,c2]
  | 901 => [c1,c2]
  | 902 => [c0,c2]
  | 903 => [c0,c2]
  | 1080 => [c0,c1,c2]
  | 1081 => [c1,c2]
  | 1082 => [c0,c2]
  | 1083 => [c0]
  | 600 => [c0,c1,c2]
  | 604 => [c1,c2]
  | 780 => [c2]
  | 540 => [c2]
  | 541 => [c1,c2]
  | 1125 => [c0,c2]
  | 1126 => [c0,c2]
  | 885 => [c0,c2]
  | 886 => [c0,c1]
  | 1005 => [c2]
  | 1006 => [c0,c1]
  | 1007 => [c0,c2]
  | 1008 => [c2]
  | 285 => [c2]
  | 286 => [c0,c2]
  | 287 => [c0,c2]
  | 289 => [c1,c2]
  | 705 => [c0,c1,c2]
  | 706 => [c0,c2]
  | 225 => [c0,c1,c2]
  | 226 => [c0,c1]
  | 1050 => [c0,c1,c2]
  | 1051 => [c0]
  | 1053 => [c2]
  | 1054 => [c1,c2]
  | 570 => [c0,c1,c2]
  | 571 => [c0,c1,c2]
  | 990 => [c2]
  | 991 => [c0,c1,c2]
  | 992 => [c1,c2]
  | 993 => [c0,c1,c2]
  | 994 => [c1,c2]
  | 270 => [c2]
  | 271 => [c0]
  | 273 => [c0,c2]
  | 390 => [c0,c2]
  | 391 => [c0]
  | 392 => [c1]
  | 394 => [c0,c1]
  | 150 => [c0,c2]
  | 151 => [c0,c1,c2]
  | 152 => [c0]
  | 735 => [c2]
  | 736 => [c2]
  | 737 => [c2]
  | 738 => [c2]
  | 495 => [c2]
  | 496 => [c1]
  | 675 => [c0,c1,c2]
  | 676 => [c1]
  | 677 => [c0,c1,c2]
  | 678 => [c0,c1,c2]
  | 195 => [c0,c1,c2]
  | 196 => [c2]
  | 375 => [c0,c2]
  | 376 => [c2]
  | 377 => [c1,c2]
  | 378 => [c2]
  | 135 => [c0,c2]
  | 136 => [c1]
  | 138 => [c0]
  | 139 => [c0,c1]
  | _ => []

def schreierData : SymmetricPairSchreierWordData row149Generators generatorData where
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

end SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow149Descriptor
