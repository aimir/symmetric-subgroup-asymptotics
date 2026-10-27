import SymmetricSubgroupAsymptotics.TernaryHeisenbergGeneratorExt
import SymmetricSubgroupAsymptotics.QuaternaryPauliFourierPhaseNormalization
import SymmetricSubgroupAsymptotics.TernaryHeisenbergCompatibleNormalizerIndex

/-! Explicit generator conjugations extend to all Heisenberg coordinates.
The central Fourier relation is algebraic, and a lower transvection is
obtained from the already available upper transvection. No normalization
or capacity is introduced as an unproved model input. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TernaryHeisenbergGeneratorNormalizer
open TernaryHeisenbergGeneratorExt
open QuaternaryPauliFourierPhaseNormalization (rotation shear)
variable {G : Type*} [Group G]

theorem central_fixed_of_fourier (x y z q : G) (hxz : Commute x z)
    (hcollect : y*x=x*y*z) (hqx : q*x*q⁻¹=y) (hqy : q*y*q⁻¹=x⁻¹) : q*z*q⁻¹=z := by
  have hz : y⁻¹*x⁻¹*y*x=z := by
    calc
      y⁻¹*x⁻¹*y*x = (x*y)⁻¹*(y*x) := by group
      _ = (x*y)⁻¹*(x*y*z) := by rw [hcollect]
      _ = z := by group
  calc
    q*z*q⁻¹ = q*(y⁻¹*x⁻¹*y*x)*q⁻¹ := by rw [hz]
    _ = (q*y*q⁻¹)⁻¹*(q*x*q⁻¹)⁻¹*(q*y*q⁻¹)*(q*x*q⁻¹) := by group
    _ = x*y⁻¹*x⁻¹*y := by rw [hqx,hqy]; group
    _ = x*(y⁻¹*x⁻¹*y*x)*x⁻¹ := by group
    _ = x*z*x⁻¹ := by rw [hz]
    _ = z := by rw [hxz.eq]; group

private theorem inverse_conjugation (u x y : G) (h : u*x*u⁻¹=y) : u⁻¹*y*u=x := by
  rw [←h]
  group

def lowerWord (q a : G) : G := q*a⁻¹*q⁻¹

theorem lower_first (x y a q : G)
    (hax : a*x*a⁻¹=x) (hay : a*y*a⁻¹=x*y)
    (hqx : q*x*q⁻¹=y) (hqy : q*y*q⁻¹=x⁻¹) :
    lowerWord q a*x*(lowerWord q a)⁻¹=x*y := by
  have hqix : q⁻¹*x*q=y⁻¹ := by
    calc
      q⁻¹*x*q = (q⁻¹*x⁻¹*q)⁻¹ := by group
      _ = y⁻¹ := by rw [inverse_conjugation q y x⁻¹ hqy]
  have haiy : a⁻¹*y*a=x⁻¹*y := by
    calc
      a⁻¹*y*a = (a⁻¹*x*a)⁻¹*(a⁻¹*(x*y)*a) := by group
      _ = x⁻¹*y := by rw [inverse_conjugation a x x hax,
          inverse_conjugation a y (x*y) hay]
  calc
    lowerWord q a*x*(lowerWord q a)⁻¹ = q*(a⁻¹*(q⁻¹*x*q)*a)*q⁻¹ := by
      dsimp only [lowerWord]
      group
    _ = q*(a⁻¹*y⁻¹*a)*q⁻¹ := by rw [hqix]
    _ = q*(a⁻¹*y*a)⁻¹*q⁻¹ := by group
    _ = q*(x⁻¹*y)⁻¹*q⁻¹ := by rw [haiy]
    _ = (q*y*q⁻¹)⁻¹*(q*x*q⁻¹) := by group
    _ = x*y := by rw [hqx,hqy,inv_inv]

theorem lower_second (x y a q : G)
    (hax : a*x*a⁻¹=x) (hqx : q*x*q⁻¹=y) :
    lowerWord q a*y*(lowerWord q a)⁻¹=y := by
  calc
    lowerWord q a*y*(lowerWord q a)⁻¹ = q*(a⁻¹*(q⁻¹*y*q)*a)*q⁻¹ := by
      dsimp only [lowerWord]
      group
    _ = q*(a⁻¹*x*a)*q⁻¹ := by rw [inverse_conjugation q x y hqx]
    _ = q*x*q⁻¹ := by rw [inverse_conjugation a x x hax]
    _ = y := hqx

theorem lower_third (z a q : G) (haz : a*z*a⁻¹=z) (hqz : q*z*q⁻¹=z) :
    lowerWord q a*z*(lowerWord q a)⁻¹=z := by
  calc
    lowerWord q a*z*(lowerWord q a)⁻¹ = q*(a⁻¹*(q⁻¹*z*q)*a)*q⁻¹ := by
      dsimp only [lowerWord]
      group
    _ = q*(a⁻¹*z*a)*q⁻¹ := by rw [inverse_conjugation q z z hqz]
    _ = q*z*q⁻¹ := by rw [inverse_conjugation a z z haz]
    _ = z := hqz

theorem conjugation_from_generators (f : H →* G) (u : G) (α : MulAut H)
    (hx : u*f first*u⁻¹=f (α first)) (hy : u*f second*u⁻¹=f (α second))
    (hz : u*f third*u⁻¹=f (α third)) : ∀ h, u*f h*u⁻¹=f (α h) := by
  let F : H →* G := (MulAut.conj u).toMonoidHom.comp f
  let J : H →* G := f.comp α.toMonoidHom
  have he : F=J := hom_ext F J hx hy hz
  intro h
  exact DFunLike.congr_fun he h

theorem rotation_first : rotation first=second := by decide +kernel
theorem rotation_second : rotation second=first⁻¹ := by decide +kernel
theorem rotation_third : rotation third=third := by decide +kernel
theorem shear_first : shear first=first*second := by decide +kernel
theorem shear_second : shear second=second := by decide +kernel
theorem shear_third : shear third=third := by decide +kernel

theorem rotation_normalizes (f : H →* G) (u : G)
    (hx : u*f first*u⁻¹=f second) (hy : u*f second*u⁻¹=(f first)⁻¹)
    (hz : u*f third*u⁻¹=f third) : ∀ h, u*f h*u⁻¹=f (rotation h) := by
  apply conjugation_from_generators f u rotation
  · simpa only [rotation_first] using hx
  · simpa only [rotation_second,map_inv] using hy
  · simpa only [rotation_third] using hz

theorem shear_normalizes (f : H →* G) (v : G)
    (hx : v*f first*v⁻¹=f first*f second) (hy : v*f second*v⁻¹=f second)
    (hz : v*f third*v⁻¹=f third) : ∀ h, v*f h*v⁻¹=f (shear h) := by
  apply conjugation_from_generators f v shear
  · simpa only [shear_first,map_mul] using hx
  · simpa only [shear_second] using hy
  · simpa only [shear_third] using hz

theorem proper_index_ge_twentySeven [Finite G] [IsSimpleGroup G]
    (f : H →* G) (hf : Function.Injective f) (u v : G)
    (hux : u*f first*u⁻¹=f second) (huy : u*f second*u⁻¹=(f first)⁻¹)
    (huz : u*f third*u⁻¹=f third)
    (hvx : v*f first*v⁻¹=f first*f second) (hvy : v*f second*v⁻¹=f second)
    (hvz : v*f third*v⁻¹=f third) (J : Subgroup G) (hJ : J≠⊤) : 27≤J.index :=
  TernaryHeisenbergCompatibleNormalizerIndex.proper_index_ge_twentySeven f hf u v rotation shear
    (rotation_normalizes f u hux huy huz) (shear_normalizes f v hvx hvy hvz)
    QuaternaryPauliFourierPhaseNormalization.rotation_coordinates
    QuaternaryPauliFourierPhaseNormalization.shear_coordinates J hJ

end SymmetricSubgroupAsymptotics.TernaryHeisenbergGeneratorNormalizer
