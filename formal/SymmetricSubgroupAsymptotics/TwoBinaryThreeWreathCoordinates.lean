import SymmetricSubgroupAsymptotics.TwoBinaryThreeWreathKernel
import SymmetricSubgroupAsymptotics.TwoBinaryThreeFixedPart
import SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates

/-! Simultaneous central and scalar coordinates on the two-head wreath.
The scalar kernel is central in the WHOLE retained top, since the two
physical invariant heads are constant on the three original labels. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwoBinaryThreeWreathCoordinates
open TwoBinaryThreeWreathKernel

variable (T : Subgroup (Equiv.Perm (Fin 3)))
  (hrotation : OddMarkerTernaryChart.rotation∈T)

abbrev ambient := TwoBinaryThreePermutationCoordinates.coordinates T hrotation

def active : (top T).ker →* (Fin 2 → ScalarFour) where
  toFun k j := Multiplicative.ofAdd ((ambient T hrotation).scalar j (vector T k).toAdd)
  map_one' := by funext j; simp
  map_mul' a b := by
    funext j
    apply Multiplicative.toAdd.injective
    change (ambient T hrotation).scalar j (vector T (a*b)).toAdd=_
    rw [map_mul]
    exact ((ambient T hrotation).scalar j).map_add _ _

def centralCoordinates : (active T hrotation).ker →*
    (Fin 2 → Multiplicative (ZMod 2)) where
  toFun z j := Multiplicative.ofAdd
    ((ambient T hrotation).invariant j (vector T z.val).toAdd)
  map_one' := by funext j; simp
  map_mul' a b := by
    funext j
    apply Multiplicative.toAdd.injective
    change (ambient T hrotation).invariant j (vector T (a.val*b.val)).toAdd=_
    rw [map_mul]
    exact ((ambient T hrotation).invariant j).map_add _ _

theorem scalar_zero (z : (active T hrotation).ker) (j : Fin 2) :
    (ambient T hrotation).scalar j (vector T z.val).toAdd=0 := by
  exact congrArg (fun f : Fin 2 → ScalarFour => (f j).toAdd) z.property

theorem central (z : (active T hrotation).ker) (g : Wreath T) :
    z.val.val*g=g*z.val.val := by
  have hc : MulAut.conjNormal g z.val=z.val := by
    apply vector_injective T
    apply Multiplicative.toAdd.injective
    rw [vector_conjugate]
    exact TwoBinaryThreePermutationCoordinates.scalar_zero_fixed T hrotation
      (vector T z.val).toAdd (scalar_zero T hrotation z) g.right
  have hc' : g*z.val.val*g⁻¹=z.val.val := congrArg Subtype.val hc
  calc
    z.val.val*g=(g*z.val.val*g⁻¹)*g := congrArg (fun x : Wreath T => x*g) hc'.symm
    _=g*z.val.val := by simp [mul_assoc]

theorem centralCoordinates_injective :
    Function.Injective (centralCoordinates T hrotation) := by
  intro z w h
  apply Subtype.ext
  apply vector_injective T
  apply Multiplicative.toAdd.injective
  apply (ambient T hrotation).joint
  apply Prod.ext
  · apply Prod.ext
    · exact congrArg (fun f : Fin 2 → Multiplicative (ZMod 2) => (f 0).toAdd) h
    · exact congrArg (fun f : Fin 2 → Multiplicative (ZMod 2) => (f 1).toAdd) h
  · apply Prod.ext
    · exact (scalar_zero T hrotation z 0).trans (scalar_zero T hrotation w 0).symm
    · exact (scalar_zero T hrotation z 1).trans (scalar_zero T hrotation w 1).symm

/-- Two central bits and two scalar planes, tied to the same original
kernel map. This supplies actual structural data, not a source capacity. -/
def coordinates : ScalarFourCentralTopCoordinates (Wreath T) T 2 2 where
  top := top T
  top_surjective := fun t => ⟨PermutationalWreathProduct.topHom t,rfl⟩
  cubic := TwoBinaryThreePermutationCoordinates.cubicHom T hrotation
    (Multiplicative.ofAdd 1)
  active := active T hrotation
  central := central T hrotation
  centralCoordinates := centralCoordinates T hrotation
  centralCoordinates_injective := centralCoordinates_injective T hrotation
  cubic_action := by
    intro v hv k j
    apply Multiplicative.toAdd.injective
    change (ambient T hrotation).scalar j
      (vector T (MulAut.conjNormal v k)).toAdd=_
    rw [vector_conjugate]
    have hv' : v.right=TwoBinaryThreePermutationCoordinates.cubicHom T hrotation
        (Multiplicative.ofAdd 1) := hv
    rw [hv']
    exact (ambient T hrotation).scalar_twisted (Multiplicative.ofAdd 1)
      (vector T k).toAdd j

end SymmetricSubgroupAsymptotics.TwoBinaryThreeWreathCoordinates
