import SymmetricSubgroupAsymptotics.TernaryHeisenbergCyclicVectorNormalizerIndex
import SymmetricSubgroupAsymptotics.CFSGHeisenbergTernarySingerAction

/-! Genuine group-word data give an injective Heisenberg27 chart and an
actual compatible Singer normalizer. No ambient h-order, splitting,
cardinality, capacity or index assertion is a field of the certificate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TernaryHeisenbergSingerGeneratorFrame
open TernaryHeisenbergGeneratorExt
open CFSGHeisenbergTernarySingerAction (singer singerVector)

structure Frame (G : Type*) [Group G] where
  x : G
  y : G
  z : G
  h : G
  x_cube : x^3=1
  y_cube : y^3=1
  z_cube : z^3=1
  commute_xz : Commute x z
  commute_yz : Commute y z
  collect : y*x=x*y*z
  central_ne_one : z≠1
  singer_x : h*x*h⁻¹=x^2*y*z
  singer_y : h*y*h⁻¹=x
  singer_z : h*z*h⁻¹=z^2

variable {G : Type*} [Group G] (F : Frame G)

def embedding : H →* G :=
  TernaryHeisenbergThreeGeneratorHom.hom F.x F.y F.z F.x_cube F.y_cube F.z_cube
    F.commute_xz F.commute_yz F.collect

theorem embedding_first : embedding F first=F.x :=
  hom_first F.x F.y F.z F.x_cube F.y_cube F.z_cube F.commute_xz F.commute_yz F.collect

theorem embedding_second : embedding F second=F.y :=
  hom_second F.x F.y F.z F.x_cube F.y_cube F.z_cube F.commute_xz F.commute_yz F.collect

theorem embedding_third : embedding F third=F.z :=
  hom_third F.x F.y F.z F.x_cube F.y_cube F.z_cube F.commute_xz F.commute_yz F.collect

theorem embedding_injective : Function.Injective (embedding F) :=
  TernaryHeisenbergThreeGeneratorHom.hom_injective F.x F.y F.z F.x_cube F.y_cube F.z_cube
    F.commute_xz F.commute_yz F.collect F.central_ne_one

theorem normalizes : ∀ g : H, F.h*embedding F g*F.h⁻¹=embedding F (singer g) := by
  let A : H →* G := (MulAut.conj F.h).toMonoidHom.comp (embedding F)
  let B : H →* G := (embedding F).comp singer.toMonoidHom
  have he : A=B := by
    apply hom_ext
    · change F.h*embedding F first*F.h⁻¹=embedding F (singer first)
      rw [CFSGHeisenbergTernarySingerAction.singer_first,map_mul,map_mul,map_pow,
        embedding_first F,embedding_second F,embedding_third F]
      exact F.singer_x
    · change F.h*embedding F second*F.h⁻¹=embedding F (singer second)
      rw [CFSGHeisenbergTernarySingerAction.singer_second,embedding_second F,embedding_first F]
      exact F.singer_y
    · change F.h*embedding F third*F.h⁻¹=embedding F (singer third)
      rw [CFSGHeisenbergTernarySingerAction.singer_third,map_pow,embedding_third F]
      exact F.singer_z
  intro g
  exact DFunLike.congr_fun he g

include F in
theorem proper_index_ge_twentySeven [Finite G] [IsSimpleGroup G]
    (J : Subgroup G) (hJ : J≠⊤) : 27 ≤ J.index := by
  apply TernaryHeisenbergCyclicVectorNormalizerIndex.proper_index_ge_twentySeven
    (embedding F) F.h singer singerVector (normalizes F)
  · exact CFSGHeisenbergTernarySingerAction.projection_compatibility
  · intro v w hv hw
    obtain ⟨k,hk⟩ := CFSGHeisenbergTernarySingerAction.vector_transitive v w hv hw
    exact ⟨k.val,hk⟩
  · simpa only [embedding_third F] using F.central_ne_one
  · exact hJ

end SymmetricSubgroupAsymptotics.TernaryHeisenbergSingerGeneratorFrame
