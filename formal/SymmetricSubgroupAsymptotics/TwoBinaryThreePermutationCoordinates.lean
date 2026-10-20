import SymmetricSubgroupAsymptotics.CubicRegularBinaryCoordinates
import SymmetricSubgroupAsymptotics.OddMarkerTernaryChart

/-! The two physical binary heads over three coarse labels have the
already checked simultaneous trace/twisted coordinates. Only the actual
cubic embedding in the retained top is used; no dimension or capacity
bound is supplied. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwoBinaryThreePermutationCoordinates

abbrev Points := Fin 2 × Fin 3
abbrev Vector := Points → ZMod 2

instance pointAction (T : Subgroup (Equiv.Perm (Fin 3))) : MulAction T Points where
  smul t x := (x.1,(t : Equiv.Perm (Fin 3)) x.2)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

abbrev representation (T : Subgroup (Equiv.Perm (Fin 3))) :
    Representation (ZMod 2) T Vector :=
  permutationFunctionRepresentation (ZMod 2) T Points

def cubicHom (T : Subgroup (Equiv.Perm (Fin 3)))
    (hrotation : OddMarkerTernaryChart.rotation∈T) : CyclicThree →* T :=
  OddMarkerTernaryChart.embedding.codRestrict T (fun c => by
    change OddMarkerTernaryChart.rotation^c.toAdd.val∈T
    exact T.pow_mem hrotation _)

private theorem embedding_action : ∀ c x : CyclicThree,
    OddMarkerTernaryChart.embedding c x.toAdd=(c*x).toAdd := by decide +kernel

theorem rotation_eq_finRotate : OddMarkerTernaryChart.rotation=finRotate 3 := by decide +kernel

/-- Physical regrouping of the two heads into the existing two regular
C3 modules. The original vector itself is retained. -/
def reindex (T : Subgroup (Equiv.Perm (Fin 3)))
    (hrotation : OddMarkerTernaryChart.rotation∈T) :
    Representation.IntertwiningMap (A := ZMod 2)
      ((representation T).comp (cubicHom T hrotation))
      CubicBinaryCoordinateUniform.regular where
  toLinearMap := {
    toFun := fun v x => v (x.1,x.2.toAdd)
    map_add' := by intro v w; rfl
    map_smul' := by intro a v; rfl }
  isIntertwining' := by
    intro c
    apply LinearMap.ext
    intro v
    funext x
    change v (x.1,(((cubicHom T hrotation c)⁻¹ : T) : Equiv.Perm (Fin 3)) x.2.toAdd)=
      v (x.1,(c⁻¹*x.2).toAdd)
    rw [←map_inv]
    change v (x.1,OddMarkerTernaryChart.embedding (c⁻¹) x.2.toAdd)=_
    exact congrArg (fun i : Fin 3 => v (x.1,i)) (embedding_action (c⁻¹) x.2)

theorem reindex_injective (T : Subgroup (Equiv.Perm (Fin 3)))
    (hrotation : OddMarkerTernaryChart.rotation∈T) :
    Function.Injective (reindex T hrotation) := by
  intro v w h
  funext x
  exact congrArg (fun f : CubicRegularBinaryCoordinates.Vector =>
    f (x.1,Multiplicative.ofAdd (x.2 : ZMod 3))) h

/-- The actual ambient two-head module has TWO joint invariant/twisted
coordinates, pulled through the same faithful physical regrouping. -/
def coordinates (T : Subgroup (Equiv.Perm (Fin 3)))
    (hrotation : OddMarkerTernaryChart.rotation∈T) :
    CubicBinaryCoordinates ((representation T).comp (cubicHom T hrotation)) :=
  CubicRegularBinaryCoordinates.coordinates.ofInjective
    (reindex T hrotation) (reindex_injective T hrotation)

end SymmetricSubgroupAsymptotics.TwoBinaryThreePermutationCoordinates
