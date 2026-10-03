import SymmetricSubgroupAsymptotics.PermutationalWreathProduct
import SymmetricSubgroupAsymptotics.SemisimpleSubdirectChart

/-!
# Quotients of a permutational wreath embedding

A homomorphism on the local component extends coordinatewise across an
arbitrary faithful top action.  Restricting this map to an actual embedded
group constructs both the literal kernel and an injective map from the
actual quotient.  When the local kernel is semisimple, exact-component
normality of its coordinate images supplies the semisimple chart by the
Scott induction in `SemisimpleSubdirectChart`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PermutationalWreathProduct

variable {D D' Q I A : Type}
  [Group D] [Group D'] [Group Q] [Group A] [MulAction Q I]

/-- Apply a homomorphism independently to every base coordinate while
retaining the literal top. -/
def mapBase (phi : D →* D') :
    PermutationalWreathProduct D Q I →*
      PermutationalWreathProduct D' Q I where
  toFun w := ⟨fun i ↦ phi (w.left i), w.right⟩
  map_one' := by ext <;> simp
  map_mul' x y := by
    ext i <;> simp

@[simp] theorem mapBase_left (phi : D →* D')
    (w : PermutationalWreathProduct D Q I) :
    (mapBase phi w).left = fun i ↦ phi (w.left i) := rfl

@[simp] theorem mapBase_right (phi : D →* D')
    (w : PermutationalWreathProduct D Q I) :
    (mapBase phi w).right = w.right := rfl

theorem mem_mapBase_ker_iff (phi : D →* D')
    (w : PermutationalWreathProduct D Q I) :
    w ∈ (mapBase phi).ker ↔
      w.right = 1 ∧ ∀ i, w.left i ∈ phi.ker := by
  constructor
  · intro hw
    have heq : mapBase phi w = 1 := MonoidHom.mem_ker.mp hw
    refine ⟨congrArg right heq, ?_⟩
    intro i
    apply MonoidHom.mem_ker.mpr
    have hleft := congrArg (fun z ↦ z.left i) heq
    simpa only [mapBase_left, one_left, Pi.one_apply] using hleft
  · rintro ⟨hright, hleft⟩
    apply MonoidHom.mem_ker.mpr
    apply PermutationalWreathProduct.ext
    · funext i
      exact MonoidHom.mem_ker.mp (hleft i)
    · exact hright

/-- Conjugation in a fixed block is literal conjugation by that block's
local component. -/
theorem conj_left_of_fixed (a e : PermutationalWreathProduct D Q I) (i : I)
    (ha : a.right • i = i) (he : e.right = 1) :
    (a * e * a⁻¹).left i = a.left i * e.left i * (a.left i)⁻¹ := by
  have hainv : a.right⁻¹ • i = i := by
    calc
      a.right⁻¹ • i = a.right⁻¹ • (a.right • i) := congrArg (a.right⁻¹ • ·) ha.symm
      _ = i := inv_smul_smul a.right i
  simp [mul_left, mul_right, inv_left, he, hainv, smul_smul]

namespace Compression

/-- The compressed map on the actual group. -/
def map (rho : A →* PermutationalWreathProduct D Q I)
    (phi : D →* D') :
    A →* PermutationalWreathProduct D' Q I :=
  (mapBase phi).comp rho

/-- The literal intersection with the local kernels in every block
coordinate. -/
def kernel (rho : A →* PermutationalWreathProduct D Q I)
    (phi : D →* D') : Subgroup A :=
  (map rho phi).ker

instance kernel_normal (rho : A →* PermutationalWreathProduct D Q I)
    (phi : D →* D') : (kernel rho phi).Normal := by
  unfold kernel
  infer_instance

/-- The actual quotient embeds in the compressed wreath product. -/
def quotientEmbedding (rho : A →* PermutationalWreathProduct D Q I)
    (phi : D →* D') :
    A ⧸ kernel rho phi →* PermutationalWreathProduct D' Q I :=
  QuotientGroup.lift (kernel rho phi) (map rho phi) le_rfl

theorem quotientEmbedding_injective
    (rho : A →* PermutationalWreathProduct D Q I)
    (phi : D →* D') :
    Function.Injective (quotientEmbedding rho phi) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rw [quotientEmbedding, QuotientGroup.ker_lift]
  change Subgroup.map (QuotientGroup.mk' (kernel rho phi))
    (kernel rho phi) = ⊥
  exact QuotientGroup.map_mk'_self (kernel rho phi)

/-- One literal block coordinate of the actual intersection, valued in the
local kernel. -/
def kernelCoordinate
    (rho : A →* PermutationalWreathProduct D Q I)
    (phi : D →* D') (i : I) : kernel rho phi →* phi.ker where
  toFun x := ⟨(rho x.1).left i, by
    have hx : rho x.1 ∈ (mapBase phi).ker := x.2
    exact (mem_mapBase_ker_iff phi (rho x.1)).mp hx |>.2 i⟩
  map_one' := by simp
  map_mul' x y := by
    apply Subtype.ext
    change (rho (x.1 * y.1)).left i =
      (rho x.1).left i * (rho y.1).left i
    rw [MonoidHom.map_mul, mul_left]
    have hx : (rho x.1).right = 1 :=
      ((mem_mapBase_ker_iff phi (rho x.1)).mp x.2).1
    rw [hx]
    simp

/-- Faithfulness of the actual wreath embedding makes all kernel
coordinates jointly faithful.  The top coordinate vanishes because these
elements lie in the compressed kernel. -/
theorem kernelCoordinate_joint_injective
    (rho : A →* PermutationalWreathProduct D Q I)
    (phi : D →* D') (hrho : Function.Injective rho) :
    Function.Injective (fun x i ↦ kernelCoordinate rho phi i x) := by
  intro x y hxy
  apply Subtype.ext
  apply hrho
  apply PermutationalWreathProduct.ext
  · funext i
    exact congrArg Subtype.val (congrFun hxy i)
  · have hx : rho x.1 ∈ (mapBase phi).ker := x.2
    have hy : rho y.1 ∈ (mapBase phi).ker := y.2
    exact ((mem_mapBase_ker_iff phi (rho x.1)).mp hx).1.trans
      ((mem_mapBase_ker_iff phi (rho y.1)).mp hy).1.symm

/-- The exact-component condition: every local element is realized by an
actual group element whose top fixes the selected block. -/
def FullComponent (rho : A →* PermutationalWreathProduct D Q I) : Prop :=
  ∀ (i : I) (d : D), ∃ a : A,
    (rho a).right • i = i ∧ (rho a).left i = d

/-- Under exact-component fullness, each literal block image of the
intersection is normal in the local kernel. -/
theorem kernelCoordinate_range_normal
    (rho : A →* PermutationalWreathProduct D Q I)
    (phi : D →* D') (hfull : FullComponent rho) (i : I) :
    (kernelCoordinate rho phi i).range.Normal := by
  constructor
  rintro x ⟨e, rfl⟩ c
  obtain ⟨a, ha, hac⟩ := hfull i c.1
  let z : kernel rho phi := ⟨a * e.1 * a⁻¹, by
    exact (kernel_normal rho phi).conj_mem e.1 e.2 a⟩
  refine ⟨z, ?_⟩
  apply Subtype.ext
  change (rho (a * e.1 * a⁻¹)).left i =
    c.1 * (rho e.1).left i * c.1⁻¹
  rw [MonoidHom.map_mul, MonoidHom.map_mul, MonoidHom.map_inv]
  have he : (rho e.1).right = 1 :=
    ((mem_mapBase_ker_iff phi (rho e.1)).mp e.2).1
  rw [conj_left_of_fixed (rho a) (rho e.1) i ha he, hac]

/-- Exact-component normality plus the local semisimple chart gives a chart
on the actual intersection which still records the block/local coordinate
from which every diagonal representative was selected. -/
def kernelSemisimpleChartOrigins
    [Fintype I]
    (rho : A →* PermutationalWreathProduct D Q I)
    (phi : D →* D') (hrho : Function.Injective rho)
    (C : SemisimpleNormalChart phi.ker)
    (hn : ∀ (i : I) (j : C.ι),
      (C.coordinate (kernelCoordinate rho phi) i j).range.Normal) :
    SemisimpleGroupChartOrigins (kernel rho phi) (I × C.ι)
      (fun p ↦ C.factor p.2) :=
  C.chartOfNormalCoordinateMapsOrigins (kernelCoordinate rho phi) hn
    (kernelCoordinate_joint_injective rho phi hrho)

/-- Counting-facing chart with the retained origin map forgotten. -/
def kernelSemisimpleChart
    [Fintype I]
    (rho : A →* PermutationalWreathProduct D Q I)
    (phi : D →* D') (hrho : Function.Injective rho)
    (C : SemisimpleNormalChart phi.ker)
    (hn : ∀ (i : I) (j : C.ι),
      (C.coordinate (kernelCoordinate rho phi) i j).range.Normal) :
    SemisimpleNormalChart (kernel rho phi) :=
  (kernelSemisimpleChartOrigins rho phi hrho C hn).toSemisimpleGroupChart.toNormalChart _

/-- Exact-component fullness makes every retained simple-coordinate range
normal, so the chart is automatic. -/
def kernelSemisimpleChartOfFullComponent
    [Fintype I]
    (rho : A →* PermutationalWreathProduct D Q I)
    (phi : D →* D') (hrho : Function.Injective rho)
    (hfull : FullComponent rho) (C : SemisimpleNormalChart phi.ker) :
    SemisimpleNormalChart (kernel rho phi) := by
  apply kernelSemisimpleChart rho phi hrho C
  intro i j
  let q : phi.ker →* C.factor j :=
    (Pi.evalMonoidHom C.factor j).comp C.equiv.toMonoidHom
  have hq : Function.Surjective q := by
    intro y
    let z : (k : C.ι) → C.factor k := Function.update 1 j y
    obtain ⟨x, hx⟩ := C.equiv.surjective z
    refine ⟨x, ?_⟩
    change C.equiv x j = y
    rw [hx]
    simp [z]
  have hn := Subgroup.Normal.map
    (kernelCoordinate_range_normal rho phi hfull i) q hq
  simpa [SemisimpleNormalChart.coordinate, q, MonoidHom.range_comp,
    Subgroup.map_map] using hn

/-- The provenance-retaining spelling of the full-component chart. -/
def kernelSemisimpleChartOriginsOfFullComponent
    [Fintype I]
    (rho : A →* PermutationalWreathProduct D Q I)
    (phi : D →* D') (hrho : Function.Injective rho)
    (hfull : FullComponent rho) (C : SemisimpleNormalChart phi.ker) :
    SemisimpleGroupChartOrigins (kernel rho phi) (I × C.ι)
      (fun p ↦ C.factor p.2) := by
  apply kernelSemisimpleChartOrigins rho phi hrho C
  intro i j
  let q : phi.ker →* C.factor j :=
    (Pi.evalMonoidHom C.factor j).comp C.equiv.toMonoidHom
  have hq : Function.Surjective q := by
    intro y
    let z : (k : C.ι) → C.factor k := Function.update 1 j y
    obtain ⟨x, hx⟩ := C.equiv.surjective z
    refine ⟨x, ?_⟩
    change C.equiv x j = y
    rw [hx]
    simp [z]
  have hn := Subgroup.Normal.map
    (kernelCoordinate_range_normal rho phi hfull i) q hq
  simpa [SemisimpleNormalChart.coordinate, q, MonoidHom.range_comp,
    Subgroup.map_map] using hn

theorem kernelSemisimpleChartOfFullComponent_factor_card
    [Fintype I]
    (rho : A →* PermutationalWreathProduct D Q I)
    (phi : D →* D') (hrho : Function.Injective rho)
    (hfull : FullComponent rho) (C : SemisimpleNormalChart phi.ker)
    (j : (kernelSemisimpleChartOfFullComponent rho phi hrho hfull C).ι) :
    ∃ p : I × C.ι,
      Nat.card ((kernelSemisimpleChartOfFullComponent
        rho phi hrho hfull C).factor j) = Nat.card (C.factor p.2) := by
  let O := kernelSemisimpleChartOriginsOfFullComponent rho phi hrho hfull C
  refine ⟨O.origin j, ?_⟩
  exact O.factor_card_eq j

end Compression
end PermutationalWreathProduct
end SymmetricSubgroupAsymptotics

end
