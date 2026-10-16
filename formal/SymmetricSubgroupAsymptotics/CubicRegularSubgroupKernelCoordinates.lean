import SymmetricSubgroupAsymptotics.CubicRegularBinaryCoordinates
import SymmetricSubgroupAsymptotics.BinaryThreeQuartetCubicImageSocles
import SymmetricSubgroupAsymptotics.CubicAllNormalB6Envelope

/-! Simultaneous invariant/scalar coordinates on the retained kernel of an
ACTUAL subgroup of two regular binary C3 modules. The subgroup need not
split or contain pure complement elements. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CubicRegularSubgroupKernelCoordinates
open LinearSemidirectSubgroupKernelChart LinearSemidirectCoprimeSocleBounds
open BinaryThreeQuartetCubicImageSocles (linear Model)

variable (K : Subgroup Model)
    (hs : Function.Surjective (projection linear K))

abbrev top := projection linear K
abbrev quotientEquiv := QuotientGroup.quotientKerEquivOfSurjective (top K) hs

theorem quotientEquiv_symm_top (q : K) :
    (quotientEquiv K hs).symm (top K q) = QuotientGroup.mk' (top K).ker q := by
  apply (quotientEquiv K hs).injective
  rw [MulEquiv.apply_symm_apply]
  rfl

def moduleRep : Rep (ZMod 2) CyclicThree :=
  Rep.of ((chart linear K).quotientRepresentation.ρ.comp
    (quotientEquiv K hs).symm.toMonoidHom)

/-- Exact inclusion of the retained translation space, with full C3 action
obtained from the actual surjective projection. -/
def inclusion : (moduleRep K hs).ρ.IntertwiningMap CubicBinaryCoordinateUniform.regular where
  toLinearMap := (translationSpace linear K).subtype
  isIntertwining' c := by
    obtain ⟨q,rfl⟩ := hs c
    have he := (LinearSemidirectSubgroupKernelChart.inclusion linear K).isIntertwining' q
    apply LinearMap.ext
    intro v
    change (translationSpace linear K).subtype
      ((chart linear K).quotientRepresentation.ρ
        ((quotientEquiv K hs).symm (top K q)) v) =
      CubicBinaryCoordinateUniform.regular (top K q) ((translationSpace linear K).subtype v)
    rw [quotientEquiv_symm_top]
    exact LinearMap.congr_fun he v

def coordinates : CubicBinaryCoordinates (moduleRep K hs).ρ :=
  CubicRegularBinaryCoordinates.coordinates.ofInjective (inclusion K hs)
    (fun _ _ he => Subtype.ext he)

/-- The original kernel equivalence retains the original subgroup action. -/
def originalKernelChart : OriginalKernelModuleChart (top K) (moduleRep K hs) where
  equiv := (kernelEquiv linear K).symm
  conjugate q a := by
    have he := (LinearSemidirectSubgroupKernelChart.inclusion linear K).isIntertwining' q
    have hv := LinearMap.congr_fun he a
    apply Subtype.ext
    change SemidirectProduct.inl
      (Multiplicative.ofAdd ((translationSpace linear K).subtype
        ((moduleRep K hs).ρ (top K q) a))) =
      (q : Model) * SemidirectProduct.inl (Multiplicative.ofAdd
        ((translationSpace linear K).subtype a)) * (q : Model)⁻¹
    rw [conjugate_translation]
    apply congrArg SemidirectProduct.inl
    apply Multiplicative.toAdd.injective
    change (translationSpace linear K).subtype
      ((chart linear K).quotientRepresentation.ρ
        ((quotientEquiv K hs).symm (top K q)) a) =
      linearRepresentation linear (top K q) ((translationSpace linear K).subtype a)
    rw [quotientEquiv_symm_top]
    exact hv

/-- No scalar counting premise is needed; the optional nonzero coordinate
is an actual kernel-element witness supplied by an original literal word. -/
def allNormalCertificate
    (hscalar : ∃ j : Fin 2, ∃ p : (top K).ker,
      CubicElementaryKernelCoordinates.scalar (top K) (moduleRep K hs).ρ
        (originalKernelChart K hs).equiv.symm (coordinates K hs) j p ≠ 1)
    (hKP : KovacsPraegerAbelianizationBound) (N : Subgroup K) [N.Normal] :
    PreE7B6QuotientCertificate (K ⧸ N) :=
  CubicAllNormalB6Envelope.quotientCertificate (top K) hs (moduleRep K hs)
    (originalKernelChart K hs) (coordinates K hs) hscalar hKP N

end SymmetricSubgroupAsymptotics.CubicRegularSubgroupKernelCoordinates
end
