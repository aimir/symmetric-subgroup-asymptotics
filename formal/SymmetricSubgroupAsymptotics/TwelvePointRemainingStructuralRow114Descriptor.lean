import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralSchreierWordCertificate
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralSymmetricSixActions
import SymmetricSubgroupAsymptotics.SixPairCyclicSymmetricSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150

/-! Selected literal witnesses; no generated metadata is a proof. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow114Descriptor
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

def codes : Fin 5 → Equiv.Perm (Fin 4) := ![q0,q0,q19,q6,q1]

def topEmbedding : Equiv.Perm (Fin 4) →* Equiv.Perm (Fin 6) :=
  labels.permCongrHom.toMonoidHom.comp SymmetricFourTwelvePointSocles.edge

def generatorData : SymmetricPairGeneratorData row114Generators where
  points := SixPairCyclicSymmetricSocles.pointChart
  topEmbedding := topEmbedding
  top_injective := labels.permCongrHom.injective.comp TwelvePointRemainingStructuralSymmetricSixActions.edge_injective
  codes := codes
  cycleWord := [4,2,2]
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

def sectionWord (q : Equiv.Perm (Fin 4)) : List (Fin 5) :=
  match permutationCode q with
  | 228 => []
  | 180 => [4]
  | 216 => [2,4,2,2]
  | 120 => [4,2,3]
  | 156 => [2,3,4]
  | 108 => [2,3]
  | 225 => [3]
  | 177 => [3,4]
  | 201 => [4,2,2,4]
  | 57 => [4,2,2]
  | 141 => [2,2,4]
  | 45 => [2,2]
  | 210 => [4,2,4]
  | 114 => [4,2]
  | 198 => [2,2,4,2]
  | 54 => [3,4,2]
  | 78 => [2,4,2,4]
  | 30 => [2,4,2]
  | 147 => [2,4]
  | 99 => [2]
  | 135 => [3,2,4]
  | 39 => [3,2]
  | 75 => [2,2,4,2,2]
  | 27 => [2,4,2,3]
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
  let c0 : (Equiv.Perm (Fin 4) × Fin 5) × Fin 5 := ((q0,0),2)
  let c1 : (Equiv.Perm (Fin 4) × Fin 5) × Fin 5 := ((q0,1),2)
  match 5*permutationCode x.1+x.2.val with
  | 1140 => [c1]
  | 900 => [c0,c1]
  | 903 => [c0]
  | 1080 => [c1]
  | 1083 => [c0]
  | 1084 => [c1]
  | 600 => [c0]
  | 602 => [c0]
  | 604 => [c1]
  | 780 => [c0,c1]
  | 782 => [c0,c1]
  | 783 => [c1]
  | 540 => [c0]
  | 1125 => [c0,c1]
  | 1126 => [c0]
  | 885 => [c1]
  | 886 => [c0]
  | 888 => [c0]
  | 1005 => [c0,c1]
  | 1006 => [c0]
  | 1007 => [c1]
  | 1008 => [c0]
  | 285 => [c0]
  | 286 => [c0]
  | 288 => [c0]
  | 705 => [c1]
  | 706 => [c0]
  | 708 => [c0,c1]
  | 225 => [c0]
  | 226 => [c0]
  | 1050 => [c0]
  | 1051 => [c0,c1]
  | 1052 => [c0]
  | 1053 => [c0]
  | 570 => [c1]
  | 571 => [c0,c1]
  | 990 => [c0]
  | 991 => [c0,c1]
  | 993 => [c0]
  | 994 => [c1]
  | 270 => [c0,c1]
  | 271 => [c0,c1]
  | 272 => [c0]
  | 273 => [c0]
  | 274 => [c1]
  | 390 => [c1]
  | 391 => [c0,c1]
  | 392 => [c0,c1]
  | 393 => [c1]
  | 150 => [c0,c1]
  | 151 => [c0,c1]
  | 735 => [c0]
  | 736 => [c1]
  | 738 => [c1]
  | 495 => [c0,c1]
  | 496 => [c1]
  | 675 => [c0]
  | 676 => [c1]
  | 677 => [c0]
  | 678 => [c0,c1]
  | 195 => [c1]
  | 196 => [c1]
  | 375 => [c0,c1]
  | 376 => [c1]
  | 378 => [c1]
  | 379 => [c0,c1]
  | 135 => [c1]
  | 136 => [c1]
  | 137 => [c1]
  | 139 => [c0,c1]
  | _ => []

def schreierData : SymmetricPairSchreierWordData row114Generators generatorData where
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

end SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow114Descriptor
