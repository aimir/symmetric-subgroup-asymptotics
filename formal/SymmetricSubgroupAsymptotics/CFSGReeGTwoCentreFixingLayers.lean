import SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveAutomorphismLayers
import SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveCube

/-! Fixing the literal centre pointwise fixes the first U3 coordinate
by cubing, and the middle coordinate on U3-derived by the actual mixed
commutator. No torus equivariance is needed for these two facts. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoCentreFixingLayers
open CFSGReeGTwoFieldParameters CFSGReeGTwoOriginalPositiveSubgroup
open CFSGReeGTwoPositiveFirstQuotient CFSGReeGTwoPositiveCentre
open CFSGReeGTwoPositiveCube CFSGReeGTwoPositiveCharacteristicLayers
open scoped commutatorElement

theorem cube_coordinates (m : ℕ) (u : fixedPositiveGroup m) :
    u^3=centralHom m (Multiplicative.ofAdd (cubeScalar m (coordinates m u 0))) := by
  obtain ⟨x,rfl⟩ := fixedPositiveChart_surjective m u
  simpa only [coordinates_chart] using chart_cube m x

theorem first_fixed (m : ℕ) (f : MulAut (fixedPositiveGroup m))
    (hcentre : ∀ d : Field m,f (centralHom m (Multiplicative.ofAdd d))=
      centralHom m (Multiplicative.ofAdd d)) (u : fixedPositiveGroup m) :
    coordinates m (f u) 0=coordinates m u 0 := by
  have he : f (u^3)=u^3 := by rw [cube_coordinates,hcentre]
  rw [map_pow,cube_coordinates,cube_coordinates] at he
  apply cubeScalar_injective m
  exact congrArg (fun z : Multiplicative (Field m) => z.toAdd) (centralHom_injective m he)

theorem middle_derived_fixed (m : ℕ) (f : MulAut (fixedPositiveGroup m))
    (hcentre : ∀ d : Field m,f (centralHom m (Multiplicative.ofAdd d))=
      centralHom m (Multiplicative.ofAdd d)) (u : fixedPositiveGroup m)
    (hu : u∈commutator (fixedPositiveGroup m)) : coordinates m (f u) 1=coordinates m u 1 := by
  let a : fixedPositiveGroup m := fixedPositiveChart m ![1,0,0]
  have hfu : f u∈commutator (fixedPositiveGroup m) :=
    Subgroup.characteristic_iff_le_comap.mp inferInstance f hu
  have he := map_commutatorElement f (g₁ := u) (g₂ := a)
  rw [derived_mixed_commutator m u a hu,hcentre,
    derived_mixed_commutator m (f u) (f a) hfu,first_fixed m f hcentre a] at he
  have hc := congrArg (fun z : Multiplicative (Field m) => z.toAdd) (centralHom_injective m he)
  have ha : coordinates m a 0=1 := by exact congrFun (coordinates_chart m ![1,0,0]) 0
  rw [ha,neg_mul,one_mul,neg_mul,one_mul] at hc
  exact (neg_injective hc).symm

end SymmetricSubgroupAsymptotics.CFSGReeGTwoCentreFixingLayers
