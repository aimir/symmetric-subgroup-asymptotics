import SymmetricSubgroupAsymptotics.SixPairFiveCycleWordB6Witness

/-! Selected original six_block table action; finite literal word checks only. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixPairAction147PrimitiveB6Pilot

private def g0 : Equiv.Perm (Fin 12) where
  toFun := ![8,9,2,3,10,11,0,1,4,5,6,7]
  invFun := ![6,7,2,3,8,9,10,11,0,1,4,5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def g1 : Equiv.Perm (Fin 12) where
  toFun := ![7,6,10,11,0,1,2,3,8,9,5,4]
  invFun := ![4,5,6,7,11,10,1,0,8,9,2,3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators : Fin 2 → Equiv.Perm (Fin 12) := ![g0,g1]
abbrev Original := Subgroup.closure (Set.range generators)

private def labels : Equiv.Perm (Fin 6) where
  toFun := ![0,3,1,5,2,4]
  invFun := ![0,2,4,1,5,3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def t0 : Equiv.Perm (Fin 6) where
  toFun := ![5,0,2,1,3,4]
  invFun := ![1,3,2,4,5,0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def t1 : Equiv.Perm (Fin 6) where
  toFun := ![1,2,3,4,0,5]
  invFun := ![4,0,1,2,3,5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def mover : Equiv.Perm (Fin 6) where
  toFun := ![5,0,2,1,3,4]
  invFun := ![1,3,2,4,5,0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def adjacentFrame : Fin 6 × ZMod 2 ≃ Fin 12 :=
  (Equiv.prodCongr (Equiv.refl (Fin 6)) (ZMod.finEquiv 2).symm.toEquiv).trans finProdFinEquiv

def witness : SixPairFiveCycleWordB6Witness generators where
  points := (Equiv.prodCongr labels (Equiv.refl (ZMod 2))).trans adjacentFrame
  tops := ![t0,t1]
  preserves := by
    intro i
    revert i
    unfold BinaryPairFrame.Preserves
    decide +kernel
  fiveCycleWord := [1]
  moverWord := [0]
  mover := mover
  fiveCycle_eval := by decide +kernel
  mover_eval := by decide +kernel
  moves := by decide +kernel
  matrix := by decide +kernel

def actionCertificate (h6 : PublishedPrimitiveDegreeSixClassification)
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    Non2UnipotentPrefixFiniteMenu.PreE7B6ActionCertificate Original :=
  witness.actionCertificate h6 hZmud

end SymmetricSubgroupAsymptotics.SixPairAction147PrimitiveB6Pilot
