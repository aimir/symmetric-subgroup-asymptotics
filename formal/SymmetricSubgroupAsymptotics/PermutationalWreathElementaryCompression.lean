import SymmetricSubgroupAsymptotics.PermutationalWreathQuotient
import SymmetricSubgroupAsymptotics.RefinedElementaryLayerEnvelope
import SymmetricSubgroupAsymptotics.MinimalNormalCompositionCharts

/-!
# Elementary layers in an actual wreath compression

This is the abelian companion to
`Compression.kernelSemisimpleChartOfFullComponent`.  A faithful subgroup of
`D wr Q` is compressed by a surjection `D -> D'` whose literal kernel has
prime-field coordinates.  The kernel in the original ambient group is
identified with its actual correlated coordinate submodule of `V^I`; no
replacement by the full product is made.

The quotient embedding is again full on the displayed local component.  It
can therefore be compressed repeatedly along an actual local chief series.
Finally, a supplied Schur-capacity bound for all literal normal sections is
fed into the already proved complete one-layer incidence theorem.  Thus the
same source `J`, every original normal axis, and all extension/transgression
fibres survive the compression.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PermutationalWreathProduct
namespace Compression

variable {p : ℕ} [Fact p.Prime]
variable {A D D' Q I V : Type}
  [Group A] [Finite A] [Group D] [Finite D] [Group D'] [Group Q]
  [Fintype I] [Nonempty I] [MulAction Q I]
  [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]

variable (rho : A →* PermutationalWreathProduct D Q I)
  (phi : D →* D')
  (e : Multiplicative V ≃* phi.ker)

/-- One actual coordinate of the compressed kernel, in the given local
prime-field coordinates. -/
def elementaryCoordinate (i : I) :
    kernel rho phi →* Multiplicative V :=
  e.symm.toMonoidHom.comp (kernelCoordinate rho phi i)

/-- All actual coordinates together.  Its range remembers diagonal and
other correlated block kernels. -/
def elementaryCoordinates :
    kernel rho phi →* Multiplicative (I → V) where
  toFun x := Multiplicative.ofAdd (fun i ↦ (elementaryCoordinate rho phi e i x).toAdd)
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext i
    change (elementaryCoordinate rho phi e i 1).toAdd = 0
    simp
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    funext i
    change (elementaryCoordinate rho phi e i (x * y)).toAdd =
      (elementaryCoordinate rho phi e i x).toAdd +
        (elementaryCoordinate rho phi e i y).toAdd
    simp

theorem elementaryCoordinates_injective (hrho : Function.Injective rho) :
    Function.Injective (elementaryCoordinates rho phi e) := by
  intro x y hxy
  apply kernelCoordinate_joint_injective rho phi hrho
  funext i
  apply e.symm.injective
  exact congrArg (fun z ↦ Multiplicative.ofAdd (z.toAdd i)) hxy

def elementaryCoordinatesAdd :
    Additive (kernel rho phi) →+ (I → V) :=
  MonoidHom.toAdditiveLeft (elementaryCoordinates rho phi e)

theorem elementaryCoordinatesAdd_injective (hrho : Function.Injective rho) :
    Function.Injective (elementaryCoordinatesAdd rho phi e) := by
  intro x y hxy
  apply Additive.toMul.injective
  apply elementaryCoordinates_injective rho phi e hrho
  exact congrArg Multiplicative.ofAdd hxy

/-- The literal correlated ambient kernel as a submodule of the product of
the local elementary kernels. -/
abbrev ElementarySubmodule : Submodule (ZMod p) (I → V) :=
  AddSubgroup.toZModSubmodule p (elementaryCoordinatesAdd rho phi e).range

def elementaryAddEquiv (hrho : Function.Injective rho) :
    Additive (kernel rho phi) ≃+ ElementarySubmodule (p := p) rho phi e :=
  AddEquiv.ofBijective (elementaryCoordinatesAdd rho phi e).rangeRestrict (by
    constructor
    · intro x y hxy
      apply elementaryCoordinatesAdd_injective rho phi e hrho
      exact congrArg Subtype.val hxy
    · exact (elementaryCoordinatesAdd rho phi e).rangeRestrict_surjective)

def elementaryMulEquiv (hrho : Function.Injective rho) :
    kernel rho phi ≃*
      Multiplicative (ElementarySubmodule (p := p) rho phi e) :=
  (elementaryAddEquiv rho phi e hrho).toMultiplicative

/-- Exact elementary chart on the actual intersection. -/
def kernelElementaryChart (hrho : Function.Injective rho) :
    ElementaryMinimalNormalChart (kernel rho phi) :=
  { p := p
    p_prime := Fact.out
    primeFact := inferInstance
    V := ElementarySubmodule (p := p) rho phi e
    addCommGroup := inferInstance
    module := inferInstance
    finiteDimensional := FiniteDimensional.of_injective
      (ElementarySubmodule (p := p) rho phi e).subtype
      (ElementarySubmodule (p := p) rho phi e).subtype_injective
    equiv := elementaryMulEquiv (p := p) rho phi e hrho }

/-- Surjective local compression preserves exact-component fullness on the
literal quotient embedding. -/
theorem quotientEmbedding_fullComponent
    (hphi : Function.Surjective phi) (hfull : FullComponent rho) :
    FullComponent (quotientEmbedding rho phi) := by
  intro i d'
  obtain ⟨d, rfl⟩ := hphi d'
  obtain ⟨a, hai, had⟩ := hfull i d
  refine ⟨QuotientGroup.mk' (kernel rho phi) a, ?_, ?_⟩
  · exact hai
  · exact congrArg phi had

namespace ElementaryLayerSectionCapacityBound

/-- Complete source transfer across one actual elementary wreath layer.
Only the numerical Schur-capacity estimate is external to this theorem; the
ambient kernel, its correlated module, the quotient, and every normal-axis
incidence are the literal ones constructed above. -/
theorem completeQuotientWeight_le
    (hrho : Function.Injective rho)
    (H : ElementaryLayerSectionCapacityBound p
      (QuotientGroup.mk' (kernel rho phi))
      (kernelElementaryChart rho phi e hrho).quotientRepresentation
      (kernelElementaryChart rho phi e hrho).originalKernelChart)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := A) J ≤
      elementaryLayerEnvelopeConstant p
          (QuotientGroup.mk' (kernel rho phi))
          (kernelElementaryChart rho phi e hrho).quotientRepresentation
          (kernelElementaryChart rho phi e hrho).originalKernelChart *
        (p : ℝ) ^ (H.capacity * ((b : ℝ) / p)) *
        completeQuotientWeight (R := A ⧸ kernel rho phi) J := by
  let C := kernelElementaryChart (p := p) rho phi e hrho
  letI : Finite V := Finite.of_injective
    (fun v : V ↦ e (Multiplicative.ofAdd v)) e.injective
  letI : Finite (ElementarySubmodule (p := p) rho phi e) :=
    Finite.of_injective (ElementarySubmodule (p := p) rho phi e).subtype
      (ElementarySubmodule (p := p) rho phi e).subtype_injective
  letI : Finite C.V := by
    change Finite (ElementarySubmodule (p := p) rho phi e)
    infer_instance
  letI : Finite C.quotientRepresentation :=
    inferInstanceAs (Finite C.V)
  exact H.completeQuotientWeight_le p
    (QuotientGroup.mk' (kernel rho phi))
    (QuotientGroup.mk'_surjective (kernel rho phi))
    C.quotientRepresentation C.originalKernelChart J

end ElementaryLayerSectionCapacityBound

end Compression
end PermutationalWreathProduct
end SymmetricSubgroupAsymptotics

end
