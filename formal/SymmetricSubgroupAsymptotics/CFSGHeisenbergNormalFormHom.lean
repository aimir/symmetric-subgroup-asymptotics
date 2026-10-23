import Mathlib.Tactic.Group
import SymmetricSubgroupAsymptotics.CFSGHeisenbergCoordinateGroup
import Mathlib.GroupTheory.NoncommPiCoprod

/-! The division-free ordered normal form for Heisenberg coordinates.
The collecting relation is stated on actual homomorphisms and will be
discharged by the selected root relations in the exceptional installer. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHeisenbergNormalFormHom
open CFSGHeisenbergCoordinateGroup
variable {K G:Type*} [CommRing K] [Group G] {m:ℕ}
variable (X Y:Multiplicative (Fin m→K)→*G) (Z:Multiplicative K→*G)
variable (hXZ:∀a c,Commute (X (Multiplicative.ofAdd a)) (Z (Multiplicative.ofAdd c)))
  (hYZ:∀b c,Commute (Y (Multiplicative.ofAdd b)) (Z (Multiplicative.ofAdd c)))
  (hcollect:∀a b,Y (Multiplicative.ofAdd b)*X (Multiplicative.ofAdd a)=
    X (Multiplicative.ofAdd a)*Y (Multiplicative.ofAdd b)*Z (Multiplicative.ofAdd (dot b a)))

def normalForm (g:Element K m) : G :=
  X (Multiplicative.ofAdd g.a)*Y (Multiplicative.ofAdd g.b)*Z (Multiplicative.ofAdd g.c)

include hXZ hYZ hcollect in
theorem normalForm_mul (g h:Element K m) : normalForm X Y Z (g*h)=normalForm X Y Z g*normalForm X Y Z h := by
  let Xa:=X (Multiplicative.ofAdd g.a)
  let Yb:=Y (Multiplicative.ofAdd g.b)
  let Zc:=Z (Multiplicative.ofAdd g.c)
  let Xa':=X (Multiplicative.ofAdd h.a)
  let Yb':=Y (Multiplicative.ofAdd h.b)
  let Zc':=Z (Multiplicative.ofAdd h.c)
  let Zd:=Z (Multiplicative.ofAdd (dot g.b h.a))
  have hc:Commute Zc (Xa'*Yb') :=
    (hXZ h.a g.c).symm.mul_right (hYZ h.b g.c).symm
  have hd:Commute Zd Yb' := (hYZ h.b (dot g.b h.a)).symm
  have hxy:Yb*Xa'=Xa'*Yb*Zd := hcollect h.a g.b
  have hz:Zd*(Zc*Zc')=Z (Multiplicative.ofAdd (g.c+h.c+dot g.b h.a)) := by
    change Z (Multiplicative.ofAdd (dot g.b h.a)) *
      (Z (Multiplicative.ofAdd g.c)*Z (Multiplicative.ofAdd h.c))=_
    rw [←map_mul,←map_mul]
    congr 1
    change dot g.b h.a+(g.c+h.c)=g.c+h.c+dot g.b h.a
    abel
  symm
  calc
    _=Xa*Yb*(Zc*(Xa'*Yb'))*Zc' := by change (Xa*Yb*Zc)*(Xa'*Yb'*Zc')=_;group
    _=Xa*Yb*((Xa'*Yb')*Zc)*Zc' := by rw [hc.eq]
    _=Xa*(Yb*Xa')*Yb'*(Zc*Zc') := by group
    _=Xa*(Xa'*Yb*Zd)*Yb'*(Zc*Zc') := by rw [hxy]
    _=(Xa*Xa')*(Yb*(Zd*Yb'))*(Zc*Zc') := by group
    _=(Xa*Xa')*(Yb*(Yb'*Zd))*(Zc*Zc') := by rw [hd.eq]
    _=(Xa*Xa')*(Yb*Yb')*(Zd*(Zc*Zc')) := by group
    _=(Xa*Xa')*(Yb*Yb')*Z (Multiplicative.ofAdd (g.c+h.c+dot g.b h.a)) := by rw [hz]
    _=normalForm X Y Z (g*h) := by
      dsimp only [Xa,Xa',Yb,Yb',normalForm]
      rw [←X.map_mul (Multiplicative.ofAdd g.a) (Multiplicative.ofAdd h.a),
        ←Y.map_mul (Multiplicative.ofAdd g.b) (Multiplicative.ofAdd h.b)]
      rfl

def coordinateHom : Element K m→*G where
  toFun := normalForm X Y Z
  map_one' := by change X 1*Y 1*Z 1=1;rw [map_one,map_one,map_one,mul_one,mul_one]
  map_mul' := normalForm_mul X Y Z hXZ hYZ hcollect

theorem coordinateHom_central (c:Multiplicative K) : coordinateHom X Y Z hXZ hYZ hcollect (central c)=Z c := by
  change X 1*Y 1*Z c=Z c
  rw [map_one,map_one,one_mul,one_mul]

end SymmetricSubgroupAsymptotics.CFSGHeisenbergNormalFormHom
