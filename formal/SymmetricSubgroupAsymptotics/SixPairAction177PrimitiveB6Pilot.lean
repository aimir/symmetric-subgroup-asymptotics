import SymmetricSubgroupAsymptotics.SixPairFiveCycleWordB6Witness

/-! Selected original six_block table action; finite literal word checks only. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixPairAction177PrimitiveB6Pilot

private def g0 : Equiv.Perm (Fin 12) where
  toFun := ![0,1,2,3,4,5,6,7,9,8,10,11]
  invFun := ![0,1,2,3,4,5,6,7,9,8,10,11]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def g1 : Equiv.Perm (Fin 12) where
  toFun := ![0,1,2,3,4,5,6,7,8,9,11,10]
  invFun := ![0,1,2,3,4,5,6,7,8,9,11,10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def g2 : Equiv.Perm (Fin 12) where
  toFun := ![1,0,2,3,4,5,6,7,8,9,10,11]
  invFun := ![1,0,2,3,4,5,6,7,8,9,10,11]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def g3 : Equiv.Perm (Fin 12) where
  toFun := ![0,1,3,2,4,5,6,7,8,9,10,11]
  invFun := ![0,1,3,2,4,5,6,7,8,9,10,11]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def g4 : Equiv.Perm (Fin 12) where
  toFun := ![0,1,2,3,5,4,6,7,8,9,10,11]
  invFun := ![0,1,2,3,5,4,6,7,8,9,10,11]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def g5 : Equiv.Perm (Fin 12) where
  toFun := ![0,1,2,3,4,5,7,6,8,9,10,11]
  invFun := ![0,1,2,3,4,5,7,6,8,9,10,11]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def g6 : Equiv.Perm (Fin 12) where
  toFun := ![0,1,2,3,4,5,8,9,10,11,6,7]
  invFun := ![0,1,2,3,4,5,10,11,6,7,8,9]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def g7 : Equiv.Perm (Fin 12) where
  toFun := ![0,1,2,3,6,7,10,11,8,9,4,5]
  invFun := ![0,1,2,3,10,11,4,5,8,9,6,7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def g8 : Equiv.Perm (Fin 12) where
  toFun := ![0,1,8,9,4,5,2,3,6,7,10,11]
  invFun := ![0,1,6,7,4,5,8,9,2,3,10,11]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def g9 : Equiv.Perm (Fin 12) where
  toFun := ![6,7,0,1,4,5,10,11,2,3,8,9]
  invFun := ![2,3,8,9,4,5,0,1,10,11,6,7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators : Fin 10 → Equiv.Perm (Fin 12) := ![g0,g1,g2,g3,g4,g5,g6,g7,g8,g9]
abbrev Original := Subgroup.closure (Set.range generators)

private def labels : Equiv.Perm (Fin 6) where
  toFun := ![0,3,5,4,1,2]
  invFun := ![0,4,5,1,3,2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def t0 : Equiv.Perm (Fin 6) where
  toFun := ![0,1,2,3,4,5]
  invFun := ![0,1,2,3,4,5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def t1 : Equiv.Perm (Fin 6) where
  toFun := ![0,1,2,3,4,5]
  invFun := ![0,1,2,3,4,5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def t2 : Equiv.Perm (Fin 6) where
  toFun := ![0,1,2,3,4,5]
  invFun := ![0,1,2,3,4,5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def t3 : Equiv.Perm (Fin 6) where
  toFun := ![0,1,2,3,4,5]
  invFun := ![0,1,2,3,4,5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def t4 : Equiv.Perm (Fin 6) where
  toFun := ![0,1,2,3,4,5]
  invFun := ![0,1,2,3,4,5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def t5 : Equiv.Perm (Fin 6) where
  toFun := ![0,1,2,3,4,5]
  invFun := ![0,1,2,3,4,5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def t6 : Equiv.Perm (Fin 6) where
  toFun := ![0,3,1,2,4,5]
  invFun := ![0,2,3,1,4,5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def t7 : Equiv.Perm (Fin 6) where
  toFun := ![0,2,5,3,4,1]
  invFun := ![0,5,1,3,4,2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def t8 : Equiv.Perm (Fin 6) where
  toFun := ![0,4,2,1,3,5]
  invFun := ![0,3,2,4,1,5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def t9 : Equiv.Perm (Fin 6) where
  toFun := ![1,2,3,4,0,5]
  invFun := ![4,0,1,2,3,5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def mover : Equiv.Perm (Fin 6) where
  toFun := ![0,2,5,3,4,1]
  invFun := ![0,5,1,3,4,2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def adjacentFrame : Fin 6 × ZMod 2 ≃ Fin 12 :=
  (Equiv.prodCongr (Equiv.refl (Fin 6)) (ZMod.finEquiv 2).symm.toEquiv).trans finProdFinEquiv

def witness : SixPairFiveCycleWordB6Witness generators where
  points := (Equiv.prodCongr labels (Equiv.refl (ZMod 2))).trans adjacentFrame
  tops := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9]
  preserves := by
    intro i
    revert i
    unfold BinaryPairFrame.Preserves
    decide +kernel
  fiveCycleWord := [9]
  moverWord := [7]
  mover := mover
  fiveCycle_eval := by decide +kernel
  mover_eval := by decide +kernel
  moves := by decide +kernel
  matrix := by decide +kernel

def actionCertificate (h6 : PublishedPrimitiveDegreeSixClassification)
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    Non2UnipotentPrefixFiniteMenu.PreE7B6ActionCertificate Original :=
  witness.actionCertificate h6 hZmud

end SymmetricSubgroupAsymptotics.SixPairAction177PrimitiveB6Pilot
