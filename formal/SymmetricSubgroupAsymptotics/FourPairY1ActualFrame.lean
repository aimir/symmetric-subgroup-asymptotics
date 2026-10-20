import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow21TopCertificate
import SymmetricSubgroupAsymptotics.BinaryPairFrameGenerators
import SymmetricSubgroupAsymptotics.Non2PreE7NaturalS4Group

/-! Actual retained top12 admits the consecutive four-pair frame. This is
proved on its five original generator arrays, independently of any family
nickname, abstract isomorphism or historical classification. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FourPairY1ActualFrame
abbrev Original := Subgroup.closure
  (Set.range PrimitiveAffineEightFrameRow21TopCertificate.generators)
private def points : Fin 4 × ZMod 2 ≃ Fin 8 :=
  (Equiv.prodCongr (Equiv.refl (Fin 4)) (ZMod.finEquiv 2).symm.toEquiv).trans
    finProdFinEquiv
private def tops : Fin 5 → Equiv.Perm (Fin 4) :=
  ![1,1,1,Equiv.swap 0 1 * Equiv.swap 1 2,NaturalS4.c1]
private theorem coordinates_checked : ∀ (j : Fin 5) (i : Fin 4) (b : ZMod 2),
    (points.symm (PrimitiveAffineEightFrameRow21TopCertificate.generators j
      (points (i,b)))).1 = tops j i := by
  decide +kernel

def pairFrame : BinaryPairFrame Original (Fin 4) :=
  BinaryPairFrame.ofGenerators points PrimitiveAffineEightFrameRow21TopCertificate.generators
    tops (fun j x => coordinates_checked j x.1 x.2)
end SymmetricSubgroupAsymptotics.FourPairY1ActualFrame
end
