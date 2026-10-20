import SymmetricSubgroupAsymptotics.BinaryFourOriginalSourceAmbientStability
import SymmetricSubgroupAsymptotics.BinaryFourMiddleSectionFactor
import SymmetricSubgroupAsymptotics.BinaryFourSymmetricKleinNormalCover

/-! Transport the actual original target map to its literal ambient
source. The normal binary core supplies Klein-triviality internally to
original consumers; only ordinary equivariance is transported here. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

open BinaryFourFullBlockCoordinates BinaryFourSymmetricBlockActions

variable {G W : Type} [Group G] [AddCommGroup W] [_root_.Module Scalar W]
    (gamma : G →* SymmetricComplement) (hgamma : ∀ r : Complement, ∃ g : G, gamma g = SemidirectProduct.inl r)
    (L : Subrepresentation (canonicalFull.comp gamma))
    (tau : Representation Scalar G W) (f : L.toRepresentation.IntertwiningMap tau)

def originalAmbientEquiv : L.toSubmodule ≃ₗ[Scalar] originalAmbientSource gamma L :=
  fullChart.submoduleMap L.toSubmodule

def originalAmbientTargetMap : originalAmbientSource gamma L →ₗ[Scalar] W :=
  f.toLinearMap.comp (originalAmbientEquiv gamma L).symm.toLinearMap

theorem originalAmbientEquiv_differenceU (g : G) (hg : gamma g = canonicalU)
    (x : L.toSubmodule) :
    originalAmbientEquiv gamma L (L.toRepresentation g x - x) =
      ⟨ambientDifferenceU (originalAmbientEquiv gamma L x),
        originalAmbientSource_differenceU gamma hgamma L _ (originalAmbientEquiv gamma L x).2⟩ := by
  apply Subtype.ext
  change fullChart (canonicalFull (gamma g) x.1 - x.1) = ambientDifferenceU (fullChart x.1)
  rw [hg]
  exact (LinearMap.congr_fun fullChart_differenceU x.1).symm

theorem originalAmbientEquiv_differenceV (g : G) (hg : gamma g = canonicalV)
    (x : L.toSubmodule) :
    originalAmbientEquiv gamma L (L.toRepresentation g x - x) =
      ⟨ambientDifferenceV (originalAmbientEquiv gamma L x),
        originalAmbientSource_differenceV gamma hgamma L _ (originalAmbientEquiv gamma L x).2⟩ := by
  apply Subtype.ext
  change fullChart (canonicalFull (gamma g) x.1 - x.1) = ambientDifferenceV (fullChart x.1)
  rw [hg]
  exact (LinearMap.congr_fun fullChart_differenceV x.1).symm

theorem originalAmbientEquiv_cycle (g : G) (hg : gamma g = canonicalC)
    (x : L.toSubmodule) :
    originalAmbientEquiv gamma L (L.toRepresentation g x) =
      ⟨ambientCycle (originalAmbientEquiv gamma L x),
        originalAmbientSource_cycle gamma hgamma L _ (originalAmbientEquiv gamma L x).2⟩ := by
  apply Subtype.ext
  change fullChart (canonicalFull (gamma g) x.1) = ambientCycle (fullChart x.1)
  rw [hg]
  exact (LinearMap.congr_fun fullChart_cycle x.1).symm

include hgamma

theorem originalAmbientTargetMap_middle_kernel
    (hproper : originalAmbientSource gamma L ≠ ⊤)
    (w : Module) (hw : w ∈ originalAmbientSource gamma L)
    (hnotbottom : ¬ ∃ a : Local, w = diagonal a)
    (hfixed : ∀ g : G, gamma g ∈ BinaryFourSymmetricKleinNormalCover.klein →
      ∀ v : W, tau g v = v) :
    LinearMap.ker (submoduleMiddleMap (originalAmbientSource gamma L)) ≤
      LinearMap.ker (originalAmbientTargetMap gamma L tau f) := by
  let e := originalAmbientEquiv gamma L
  let F := originalAmbientTargetMap gamma L tau f
  obtain ⟨gU, hgU⟩ := hgamma (SemidirectProduct.inl (Multiplicative.ofAdd ![1, 0]))
  obtain ⟨gV, hgV⟩ := hgamma (SemidirectProduct.inl (Multiplicative.ofAdd ![0, 1]))
  obtain ⟨gC, hgC⟩ := hgamma (SemidirectProduct.inr (Multiplicative.ofAdd 1))
  have hU := originalAmbientSource_differenceU gamma hgamma L
  have hV := originalAmbientSource_differenceV gamma hgamma L
  have hC := originalAmbientSource_cycle gamma hgamma L
  have hfixU := hfixed gU (by
    rw [hgU]
    exact (BinaryFourSymmetricKleinNormalCover.mem_klein _).mpr ⟨rfl, rfl⟩)
  have hfixV := hfixed gV (by
    rw [hgV]
    exact (BinaryFourSymmetricKleinNormalCover.mem_klein _).mpr ⟨rfl, rfl⟩)
  have hfU : ∀ x : originalAmbientSource gamma L,
      F ⟨ambientDifferenceU x, hU x x.2⟩ = 0 := by
    intro x
    have he := originalAmbientEquiv_differenceU gamma hgamma L gU hgU (e.symm x)
    rw [e.apply_symm_apply] at he
    rw [← he]
    change f (e.symm (e (L.toRepresentation gU (e.symm x) - e.symm x))) = 0
    rw [e.symm_apply_apply, map_sub, Representation.IntertwiningMap.isIntertwining, hfixU, sub_self]
  have hfV : ∀ x : originalAmbientSource gamma L,
      F ⟨ambientDifferenceV x, hV x x.2⟩ = 0 := by
    intro x
    have he := originalAmbientEquiv_differenceV gamma hgamma L gV hgV (e.symm x)
    rw [e.apply_symm_apply] at he
    rw [← he]
    change f (e.symm (e (L.toRepresentation gV (e.symm x) - e.symm x))) = 0
    rw [e.symm_apply_apply, map_sub, Representation.IntertwiningMap.isIntertwining, hfixV, sub_self]
  have hfC : ∀ x : originalAmbientSource gamma L,
      F ⟨ambientCycle x, hC x x.2⟩ = tau gC (F x) := by
    intro x
    have he := originalAmbientEquiv_cycle gamma hgamma L gC hgC (e.symm x)
    rw [e.apply_symm_apply] at he
    rw [← he]
    change f (e.symm (e (L.toRepresentation gC (e.symm x)))) = tau gC (f (e.symm x))
    rw [e.symm_apply_apply]
    exact Representation.IntertwiningMap.isIntertwining _ _ f gC (e.symm x)
  obtain ⟨q, hq⟩ := klein_trivial_map_factors_middle
    (originalAmbientSource gamma L) hproper hU hV hC w hw hnotbottom F (tau gC) hfU hfV hfC
  intro x hx
  have hxzero : (LinearMap.ker (submoduleMiddleMap (originalAmbientSource gamma L))).mkQ x = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hx
  have heq := LinearMap.congr_fun hq x
  change F x = 0
  rw [← heq]
  change q ((submoduleMiddleMap (originalAmbientSource gamma L)).ker.mkQ x) = 0
  rw [hxzero, map_zero]

end SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

end
