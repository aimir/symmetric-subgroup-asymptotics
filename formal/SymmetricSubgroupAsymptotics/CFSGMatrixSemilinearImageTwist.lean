import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticDiagramFieldTwist
import Mathlib.LinearAlgebra.GeneralLinearGroup

/-! A literal diagram--field matrix twist restricts to an actual tensor
image when its source has a proved surjective intertwiner. This shared
construction proves image preservation and bijectivity; it does not
assume surjectivity on fixed points. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMatrixSemilinearImageTwist
open CFSGSerreQuadraticDiagramFieldTwist
variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype I] [DecidableEq I]
    (f : V→ₗ[K]Matrix I I K) (e : Equiv.Perm I) (sigma : K≃+*K)
    (s : V→V) (hs : Function.Surjective s)
    (hcov : ∀x,f (s x)=matrixTwist e K sigma (f x))

local instance invPair : RingHomInvPair sigma.toRingHom sigma.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv sigma
local instance symmInvPair : RingHomInvPair sigma.symm.toRingHom sigma.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm sigma

def imageSemilinearMap : f.range→ₛₗ[sigma.toRingHom]f.range where
  toFun y:=⟨matrixTwist e K sigma y.val,by
    obtain ⟨x,hx⟩ := y.property
    refine ⟨s x,?_⟩
    rw [hcov,hx]⟩
  map_add' x y:=Subtype.ext (map_add (matrixTwist e K sigma) x.val y.val)
  map_smul' a y:=by
    apply Subtype.ext
    ext i j
    change sigma (a*y.val (e.symm i) (e.symm j))=
      sigma a*sigma (y.val (e.symm i) (e.symm j))
    exact map_mul sigma _ _

include hs in
theorem imageSemilinearMap_bijective : Function.Bijective (imageSemilinearMap f e sigma s hcov) := by
  constructor
  · intro x y he
    apply Subtype.ext
    exact (matrixTwist e K sigma).injective (congrArg Subtype.val he)
  · rintro ⟨y,⟨x,rfl⟩⟩
    obtain ⟨p,hp⟩ := hs x
    refine ⟨f.rangeRestrict p,?_⟩
    apply Subtype.ext
    change matrixTwist e K sigma (f p)=f x
    rw [←hcov,hp]

def imageSemilinearEquiv : f.range≃ₛₗ[sigma.toRingHom]f.range :=
  LinearEquiv.ofBijective (imageSemilinearMap f e sigma s hcov)
    (imageSemilinearMap_bijective f e sigma s hs hcov)

theorem imageSemilinearEquiv_val (y : f.range) :
    (imageSemilinearEquiv f e sigma s hs hcov y).val=matrixTwist e K sigma y.val := rfl

def imageAmbientTwist : MulAut (f.range≃ₗ[K]f.range) :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv K f.range).symm.trans
    (LinearMap.GeneralLinearGroup.congrLinearEquiv (imageSemilinearEquiv f e sigma s hs hcov))).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K f.range)

theorem imageAmbientTwist_apply (g : f.range≃ₗ[K]f.range) (y : f.range) :
    imageAmbientTwist f e sigma s hs hcov g y=imageSemilinearEquiv f e sigma s hs hcov
      (g ((imageSemilinearEquiv f e sigma s hs hcov).symm y)) := rfl

end SymmetricSubgroupAsymptotics.CFSGMatrixSemilinearImageTwist
