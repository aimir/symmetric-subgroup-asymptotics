import SymmetricSubgroupAsymptotics.SimpleCoordinateSupportCover
import SymmetricSubgroupAsymptotics.PermutationalWreathQuotient

/-! Actual FullComponent proves the normal-image condition in the literal
support cover. The kernel image retains EVERY original block/factor
coordinate; no diagonal chart, single-orbit guess or full-product claim
replaces that image. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.ActualWreathKernelSupportCover
open PermutationalWreathProduct PermutationalWreathProduct.Compression

variable {G D D' Q I : Type} [Group G] [Group D] [Group D'] [Group Q] [MulAction Q I]
variable (rho : G →* PermutationalWreathProduct D Q I) (phi : D →* D')
    (C : SemisimpleNormalChart phi.ker)

def coordinates : kernel rho phi →* (∀ p : I×C.ι,C.factor p.2) where
  toFun x p := C.coordinate (kernelCoordinate rho phi) p.1 p.2 x
  map_one' := by funext p; exact (C.coordinate (kernelCoordinate rho phi) p.1 p.2).map_one
  map_mul' x y := by funext p; exact (C.coordinate (kernelCoordinate rho phi) p.1 p.2).map_mul x y

theorem coordinates_injective (hrho : Function.Injective rho) :
    Function.Injective (coordinates rho phi C) := by
  intro x y h
  apply kernelCoordinate_joint_injective rho phi hrho
  funext i
  apply C.equiv.injective
  funext j
  exact congrFun h (i,j)

theorem original_coordinate_range_normal (hfull : FullComponent rho) (p : I×C.ι) :
    (C.coordinate (kernelCoordinate rho phi) p.1 p.2).range.Normal := by
  let q : phi.ker →* C.factor p.2 :=
    (Pi.evalMonoidHom C.factor p.2).comp C.equiv.toMonoidHom
  have hq : Function.Surjective q := by
    intro y
    let z : (j : C.ι) → C.factor j := Function.update 1 p.2 y
    obtain ⟨x,hx⟩ := C.equiv.surjective z
    refine ⟨x,?_⟩
    change C.equiv x p.2=y
    rw [hx]
    simp [z]
  have hn := Subgroup.Normal.map
    (kernelCoordinate_range_normal rho phi hfull p.1) q hq
  simpa [SemisimpleNormalChart.coordinate,q,MonoidHom.range_comp,Subgroup.map_map] using hn

def kernelImage (hfull : FullComponent rho) :
    SimpleCoordinateSupportCover.Family (fun p : I×C.ι => C.factor p.2) := by
  refine ⟨(coordinates rho phi C).range,?_⟩
  intro p
  have he :
      (SimpleCoordinateSupportCover.coordinate (fun p : I×C.ι => C.factor p.2)
        (coordinates rho phi C).range p).range=
      (C.coordinate (kernelCoordinate rho phi) p.1 p.2).range := by
    ext t
    constructor
    · rintro ⟨v,hv⟩
      obtain ⟨x,hx⟩ := v.property
      refine ⟨x,?_⟩
      change coordinates rho phi C x p=t
      rw [hx]
      exact hv
    · rintro ⟨x,rfl⟩
      exact ⟨⟨coordinates rho phi C x,⟨x,rfl⟩⟩,rfl⟩
  rw [he]
  exact original_coordinate_range_normal rho phi C hfull p

theorem kernelImage_decode_code (hfull : FullComponent rho) :
    SimpleCoordinateSupportCover.decode (fun p : I×C.ι => C.factor p.2)
      (SimpleCoordinateSupportCover.code _ (kernelImage rho phi C hfull)).1
      (SimpleCoordinateSupportCover.code _ (kernelImage rho phi C hfull)).2.val=
      (coordinates rho phi C).range := by
  letI (p : I×C.ι) : IsSimpleGroup (C.factor p.2) := C.simple p.2
  exact SimpleCoordinateSupportCover.decode_code _ (kernelImage rho phi C hfull)

end SymmetricSubgroupAsymptotics.ActualWreathKernelSupportCover
