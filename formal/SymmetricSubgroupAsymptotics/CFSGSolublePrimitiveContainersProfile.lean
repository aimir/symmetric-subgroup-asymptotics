import SymmetricSubgroupAsymptotics.CFSGSolublePrimitiveContainersAffine
import SymmetricSubgroupAsymptotics.PrimitiveAffineProfileStructure

/-! An actual affine profile is contained in the labelled affine envelope
attached to its SAME point stabilizer and an explicit translation chart.
The point relabelling and every original permutation are retained. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSolublePrimitiveContainers

variable {G X T : Type} [Group G] [MulAction G X] [Group T]
    (P : PrimitiveAffineProfile G X) (x : X) (a : P.V ≃* T)

def profileComplementHom : P.complement x →* MulAut T :=
  (MulAut.congr a).toMonoidHom.comp (P.complementAction x)

abbrev profileComplement : Subgroup (MulAut T) := (profileComplementHom P x a).range

def profileComplementMap : P.complement x →* profileComplement P x a :=
  (profileComplementHom P x a).rangeRestrict

theorem profileComplement_compatible (c : P.complement x) (v : P.V) :
    a (P.complementAction x c v) =
      (profileComplementMap P x a c : MulAut T) (a v) := by
  change a (P.complementAction x c v) =
    a (P.complementAction x c (a.symm (a v)))
  rw [MulEquiv.symm_apply_apply]

def profileSemidirectMap : P.V ⋊[P.complementAction x] P.complement x →*
    AffineGroup T (profileComplement P x a) :=
  SemidirectProduct.map a.toMonoidHom (profileComplementMap P x a) (by
    intro c
    apply MonoidHom.ext
    intro v
    exact profileComplement_compatible P x a c v)

def profileEmbedding : G →* AffineGroup T (profileComplement P x a) :=
  (profileSemidirectMap P x a).comp (P.semidirectEquiv x).symm.toMonoidHom

def profilePoints : T ≃ X := a.symm.toEquiv.trans (P.pointEquiv x)

theorem profilePoints_apply (v : P.V) : profilePoints P x a (a v) = P.pointEquiv x v := by
  change P.pointEquiv x (a.symm (a v)) = _
  rw [MulEquiv.symm_apply_apply]

theorem profile_semidirect_point
    (g : P.V ⋊[P.complementAction x] P.complement x) (v : P.V) :
    P.pointEquiv x (g.left * P.complementAction x g.right v) =
      P.semidirectEquiv x g • P.pointEquiv x v := by
  change ((g.left : G) * ((g.right : G) * (v : G) * (g.right : G)⁻¹)) • x = _
  have hval : P.semidirectEquiv x g = (g.left : G) * (g.right : G) := rfl
  rw [hval]
  change _ = ((g.left : G) * (g.right : G)) • ((v : G) • x)
  rw [mul_smul, mul_smul, mul_smul, mul_smul]
  have hfix : (g.right : G)⁻¹ • x = x := (g.right⁻¹).property
  rw [hfix]

theorem profileEmbedding_point (g : G) (t : T) :
    profilePoints P x a (affineAction T (profileComplement P x a)
      (profileEmbedding P x a g) t) = g • profilePoints P x a t := by
  obtain ⟨u, rfl⟩ := (P.semidirectEquiv x).surjective g
  obtain ⟨v, rfl⟩ := a.surjective t
  rw [show profileEmbedding P x a (P.semidirectEquiv x u) = profileSemidirectMap P x a u by
    change profileSemidirectMap P x a ((P.semidirectEquiv x).symm
      (P.semidirectEquiv x u)) = _
    rw [MulEquiv.symm_apply_apply]]
  have hcoord : affineAction T (profileComplement P x a)
      (profileSemidirectMap P x a u) (a v) =
      a (u.left * P.complementAction x u.right v) := by
    change a u.left * (profileComplementMap P x a u.right : MulAut T) (a v) = _
    rw [← profileComplement_compatible P x a u.right v, map_mul]
  rw [hcoord, profilePoints_apply, profilePoints_apply]
  exact profile_semidirect_point P x u v

theorem profile_range_le_labelledEnvelope :
    (MulAction.toPermHom G X).range ≤
      labelledEnvelope T (profileComplement P x a) (profilePoints P x a) := by
  rintro _ ⟨g, rfl⟩
  refine ⟨profileEmbedding P x a g, ?_⟩
  apply Equiv.ext
  intro y
  obtain ⟨t, rfl⟩ := (profilePoints P x a).surjective y
  change profilePoints P x a (affineAction T (profileComplement P x a)
      (profileEmbedding P x a g)
      ((profilePoints P x a).symm (profilePoints P x a t))) =
    g • profilePoints P x a t
  rw [Equiv.symm_apply_apply]
  exact profileEmbedding_point P x a g t

theorem profileComplement_soluble [IsSolvable G] :
    IsSolvable (profileComplement P x a) :=
  solvable_of_surjective (profileComplementHom P x a).rangeRestrict_surjective

theorem profile_labelledEnvelope_soluble [IsSolvable G] [IsSolvable T] :
    IsSolvable (labelledEnvelope T (profileComplement P x a) (profilePoints P x a)) := by
  letI solublePrimitiveProfile_complement : IsSolvable (profileComplement P x a) :=
    profileComplement_soluble P x a
  exact labelledEnvelope_soluble T _ _

end SymmetricSubgroupAsymptotics.CFSGSolublePrimitiveContainers
