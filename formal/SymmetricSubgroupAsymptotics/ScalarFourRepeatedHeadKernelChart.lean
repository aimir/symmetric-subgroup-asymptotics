import SymmetricSubgroupAsymptotics.ScalarFourRepeatedHeadModel
import SymmetricSubgroupAsymptotics.CubicAllNormalB6Envelope

/-! The actual repeated-head fiber-product kernel in simultaneous vector
coordinates. This supplies the all-normal source, without listing normals. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
namespace ScalarFourRepeatedHeadModel

abbrev KernelVector := (ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2)

private def scalarRepresentation : Representation (ZMod 2) CyclicThree (ZMod 2 × ZMod 2) where
  toFun c := (scalarFourTwistAdd (Multiplicative.toAdd c)).toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro v
    apply Multiplicative.ofAdd.injective
    exact scalarFourTwist_zero (Multiplicative.ofAdd v)
  map_mul' c d := by
    apply LinearMap.ext
    intro v
    apply Multiplicative.ofAdd.injective
    exact scalarFourTwist_add (Multiplicative.toAdd c) (Multiplicative.toAdd d)
      (Multiplicative.ofAdd v)

def kernelRepresentation : Representation (ZMod 2) CyclicThree KernelVector :=
  scalarRepresentation.prod scalarRepresentation

def kernelModule : Rep (ZMod 2) CyclicThree := Rep.of kernelRepresentation

private def toCoordinates : top.ker →* Multiplicative KernelVector where
  toFun p := Multiplicative.ofAdd ((coord 0 p).toAdd,(coord 1 p).toAdd)
  map_one' := by simp
  map_mul' p q := by
    apply Multiplicative.toAdd.injective
    apply Prod.ext
    · exact congrArg Multiplicative.toAdd ((coord 0).map_mul p q)
    · exact congrArg Multiplicative.toAdd ((coord 1).map_mul p q)

private theorem toCoordinates_bijective : Function.Bijective toCoordinates := by
  constructor
  · intro p q he
    apply coord_joint
    have hh := congrArg Multiplicative.toAdd he
    exact Prod.ext (Multiplicative.toAdd.injective (congrArg Prod.fst hh))
      (Multiplicative.toAdd.injective (congrArg Prod.snd hh))
  · intro v
    obtain ⟨p,hp⟩ := NaturalA4ScalarFourHead.coord_surjective (Multiplicative.ofAdd v.toAdd.1)
    obtain ⟨q,hq⟩ := NaturalA4ScalarFourHead.coord_surjective (Multiplicative.ofAdd v.toAdd.2)
    let g : G := ⟨((p : NaturalA4ScalarFourHead.G),(q : NaturalA4ScalarFourHead.G)),
      (MonoidHom.mem_ker.mp p.2).trans (MonoidHom.mem_ker.mp q.2).symm⟩
    let r : top.ker := ⟨g,p.2⟩
    refine ⟨r,?_⟩
    apply Multiplicative.toAdd.injective
    exact Prod.ext (congrArg Multiplicative.toAdd hp) (congrArg Multiplicative.toAdd hq)

private def coordinateEquiv : top.ker ≃* Multiplicative KernelVector :=
  MulEquiv.ofBijective toCoordinates toCoordinates_bijective

private theorem coordinates_conj (q : G) (p : top.ker) :
    coordinateEquiv (MulAut.conjNormal q p) =
      Multiplicative.ofAdd (kernelRepresentation (top q) (coordinateEquiv p).toAdd) := by
  apply Multiplicative.toAdd.injective
  exact Prod.ext
    (congrArg Multiplicative.toAdd (headed.coord_twisted q p 0))
    (congrArg Multiplicative.toAdd (headed.coord_twisted q p 1))

def originalKernelChart : OriginalKernelModuleChart top kernelModule where
  equiv := coordinateEquiv.symm
  conjugate q a := by
    have he : coordinateEquiv.symm
        (Multiplicative.ofAdd (kernelRepresentation (top q) a)) =
        MulAut.conjNormal q (coordinateEquiv.symm (Multiplicative.ofAdd a)) := by
      apply coordinateEquiv.injective
      rw [MulEquiv.apply_symm_apply,coordinates_conj,MulEquiv.apply_symm_apply]
      rfl
    exact congrArg Subtype.val he

def kernelCoordinates : CubicBinaryCoordinates kernelModule.ρ where
  invariant := fun _ => 0
  scalar := fun j => if j=0 then LinearMap.fst _ _ _ else LinearMap.snd _ _ _
  invariant_fixed := by simp
  scalar_twisted := by
    intro c v j
    fin_cases j <;> rfl
  joint := by
    intro v w he
    exact congrArg Prod.snd he

theorem scalar_nonzero : ∃ j : Fin 2, ∃ p : top.ker,
    CubicElementaryKernelCoordinates.scalar top kernelModule.ρ
      originalKernelChart.equiv.symm kernelCoordinates j p ≠ 1 := by
  obtain ⟨p,hp⟩ := headed.coord_zero_surjective (Multiplicative.ofAdd ((1 : ZMod 2),0))
  refine ⟨0,p,?_⟩
  change coord 0 p ≠ 1
  change coord 0 p = Multiplicative.ofAdd ((1 : ZMod 2),0) at hp
  rw [hp]
  decide +kernel

/-- Every actual normal quotient of the repeated-head model has a B6
certificate, using only the existing explicit KP published input. -/
def allNormalB6Certificate (hKP : KovacsPraegerAbelianizationBound)
    (N : Subgroup G) [N.Normal] :
    PreE7B6QuotientCertificate (G ⧸ N) :=
  CubicAllNormalB6Envelope.quotientCertificate top headed.top_surjective
    kernelModule originalKernelChart kernelCoordinates scalar_nonzero hKP N

end ScalarFourRepeatedHeadModel
end SymmetricSubgroupAsymptotics
end
