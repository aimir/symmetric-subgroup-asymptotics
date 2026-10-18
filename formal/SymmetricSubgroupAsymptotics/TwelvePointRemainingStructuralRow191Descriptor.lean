import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralSchreierWordCertificate
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralSymmetricSixActions
import SymmetricSubgroupAsymptotics.SixPairCyclicSymmetricSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows151To200

/-! Selected literal witnesses; no generated metadata is a proof. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow191Descriptor
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

def codes : Fin 4 → Equiv.Perm (Fin 4) := ![q0,q7,q19,q1]

def topEmbedding : Equiv.Perm (Fin 4) →* Equiv.Perm (Fin 6) :=
  labels.permCongrHom.toMonoidHom.comp TwelvePointRemainingStructuralSymmetricSixActions.twistedEdge

def generatorData : SymmetricPairGeneratorData row191Generators where
  points := SixPairCyclicSymmetricSocles.pointChart
  topEmbedding := topEmbedding
  top_injective := labels.permCongrHom.injective.comp TwelvePointRemainingStructuralSymmetricSixActions.twistedEdge_injective
  codes := codes
  cycleWord := [3,2,2]
  swapWord := [1,3]
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
  | 216 => [3,2,1]
  | 120 => [1,2,2]
  | 156 => [2,1]
  | 108 => [2,1,3]
  | 225 => [1,3]
  | 177 => [1]
  | 201 => [1,2,1]
  | 57 => [3,2,2]
  | 141 => [2,2,3]
  | 45 => [2,2]
  | 210 => [2,1,2]
  | 114 => [3,2]
  | 198 => [1,2,3]
  | 54 => [1,2]
  | 78 => [2,2,1,2]
  | 30 => [2,3,2]
  | 147 => [2,3]
  | 99 => [2]
  | 135 => [2,2,1]
  | 39 => [1,3,2]
  | 75 => [1,2,3,2]
  | 27 => [2,1,2,2]
  | _ => []

private def selected : Option (Equiv.Perm (Fin 4) × Fin 4) := none

private def coefficient (x : Equiv.Perm (Fin 4) × Fin 4) : Bool :=
  match 4*permutationCode x.1+x.2.val with
  | _ => false

private def commutatorWord (x : Equiv.Perm (Fin 4) × Fin 4) :
    List ((Equiv.Perm (Fin 4) × Fin 4) × Fin 4) :=
  let c0 : (Equiv.Perm (Fin 4) × Fin 4) × Fin 4 := ((q0,0),1)
  let c1 : (Equiv.Perm (Fin 4) × Fin 4) × Fin 4 := ((q0,0),2)
  let c2 : (Equiv.Perm (Fin 4) × Fin 4) × Fin 4 := ((q0,0),3)
  let c3 : (Equiv.Perm (Fin 4) × Fin 4) × Fin 4 := ((q1,0),2)
  let c4 : (Equiv.Perm (Fin 4) × Fin 4) × Fin 4 := ((q3,0),2)
  match 4*permutationCode x.1+x.2.val with
  | 912 => [c0,c1,c4]
  | 720 => [c0,c1,c2,c4]
  | 864 => [c0,c3]
  | 480 => [c0,c3,c4]
  | 624 => [c1,c3]
  | 432 => [c1,c2,c3,c4]
  | 900 => [c0,c4]
  | 708 => [c1,c4]
  | 804 => [c2,c3]
  | 228 => [c0,c3,c4]
  | 564 => [c3]
  | 180 => [c1,c2,c3,c4]
  | 840 => [c0,c1,c2,c3,c4]
  | 456 => [c1,c4]
  | 792 => [c3,c4]
  | 216 => [c0,c1,c2,c4]
  | 312 => [c3]
  | 120 => [c1,c3]
  | 588 => [c0,c1,c2,c3,c4]
  | 396 => [c0,c4]
  | 540 => [c3,c4]
  | 156 => [c0,c1,c4]
  | 300 => [c2,c3]
  | 108 => [c0,c3]
  | _ => []

def schreierData : SymmetricPairSchreierWordData row191Generators generatorData where
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

end SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow191Descriptor
