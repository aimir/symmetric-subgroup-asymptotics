import SymmetricSubgroupAsymptotics.BinaryCarrierActualRoutedSourceCode
import SymmetricSubgroupAsymptotics.BinaryDegreeEightNormalizerSaturatedDirect

/-!
# Variable-chart aggregation for actual degree-eight carrier residuals

The routed carrier construction counts a subgroup after its ambient product
chart has been fixed.  This file isolates the exact extra argument needed
when the chart varies with the original subgroup.

The decoration records a value `c` which determines one ambient product
homomorphism.  The exact-axis comap is the fixed cell.  The pair `(c, comap)`
recovers the original subgroup by `Subgroup.map_comap_eq_self`, so no orbit,
axis, quotient, route, or profile witness has to be added to the decoration.

The final section specializes this mechanism to the intrinsic degree-eight
carrier residual family.  Constructing the displayed complete-chart package
with a small chart type is the remaining physical orbit-assembly theorem;
the existing one-orbit chart only supplies one eight-point factor and its
undivided complement, and therefore does not by itself construct that
package.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryDegreeEightVariableChartAggregation

open BinaryCarrierActualDecoratedProducer
open BinaryCarrierActualDecoratedTransport
open BinaryCarrierActualRoutedSourceCode
open BinaryCarrierParameterProfiles
open BinaryCarrierProfileTransport
open BinaryCarrierRoutedWordClosure
open BinaryCarrierWordClosure
open BinaryDegreeEightNormalizerSaturatedDirect
open BinaryDegreeEightPhysicalAnalyticClosure

local instance subgroupFinite {G : Type*} [Group G] [Finite G] :
    Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G ↦ (H : Set G)) SetLike.coe_injective

attribute [local instance] Fintype.ofFinite

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  (A : ι → Type) [∀ i, Group (A i)] [∀ i, Finite (A i)]
  (N : ∀ i, Subgroup (A i))
  (R : ∀ i, AxisSlot (A i) (N i))

/-! ## Generic variable ambient charts -/

/-- A bounded chart code whose value determines the ambient product action.

The source may be any type of actual objects, provided `subgroup` embeds it
in the ambient subgroup lattice.  For each object, its subgroup lies in the
range of the chart homomorphism, and its comap is a full product subgroup with
the prescribed literal axes.  These are precisely the hypotheses needed by
the fixed-cell routed source code. -/
structure VariableAmbientChart (Actual G : Type*) [Group G] where
  subgroup : Actual → Subgroup G
  subgroup_injective : Function.Injective subgroup
  Chart : Type
  chartFinite : Finite Chart
  chart : Actual → Chart
  ambientHom : Chart → ((∀ i, A i) →* G)
  le_range : ∀ x, subgroup x ≤ (ambientHom (chart x)).range
  full : ∀ x, CarrierProductFull ((subgroup x).comap (ambientHom (chart x)))
  axis : ∀ x i,
    carrierAxis ((subgroup x).comap (ambientHom (chart x))) i = N i

namespace VariableAmbientChart

variable {A N R}
  {Actual G : Type*} [Group G]

/-- The exact-axis fixed cell attached to an actual object and its chart. -/
def fixedCell (C : VariableAmbientChart A N Actual G) (x : Actual) :
    FixedCell A N :=
  ⟨(C.subgroup x).comap (C.ambientHom (C.chart x)), C.full x, C.axis x⟩

/-- Mapping the fixed cell back through the chart recovers the literal actual
subgroup.  Injectivity of the ambient homomorphism is not required. -/
theorem recover (C : VariableAmbientChart A N Actual G) (x : Actual) :
    (C.fixedCell x).1.map (C.ambientHom (C.chart x)) = C.subgroup x :=
  Subgroup.map_comap_eq_self (C.le_range x)

/-- The varying chart and its exact-axis fixed cell jointly determine the
actual object. -/
theorem chart_fixedCell_injective (C : VariableAmbientChart A N Actual G) :
    Function.Injective (fun x ↦ (C.chart x, C.fixedCell x)) := by
  intro x y h
  apply C.subgroup_injective
  have hdecoded := congrArg
    (fun z : C.Chart × FixedCell A N ↦
      z.2.1.map (C.ambientHom z.1)) h
  calc
    C.subgroup x =
        (C.fixedCell x).1.map (C.ambientHom (C.chart x)) :=
      (C.recover x).symm
    _ = (C.fixedCell y).1.map (C.ambientHom (C.chart y)) := hdecoded
    _ = C.subgroup y := C.recover y

/-- Forget the reconstruction proof to the bounded-decoration ambient-cell
interface. -/
def toAmbientCellCode (C : VariableAmbientChart A N Actual G) :
    AmbientCellCode A N Actual where
  Decoration := C.Chart
  decorationFinite := C.chartFinite
  decoration := C.chart
  fixedCell := C.fixedCell
  joint_injective := C.chart_fixedCell_injective

/-- Compose a variable ambient chart with the canonical routed source of its
fixed exact-axis cell. -/
def toSourceCode (C : VariableAmbientChart A N Actual G)
    {Cold K : ℕ}
    (hcard : Nat.card C.Chart ≤
      (2 * wordParameter (cellSlots A N R) + 2) ^ (K * (2 * Cold))) :
    SourceCode (cellSlots A N R) Actual Cold K :=
  AmbientCellCode.toSourceCode A N R C.toAmbientCellCode hcard

/-- Variable-chart aggregation followed by the reversible routed-word
transport.  The sole multiplicative loss is the chart-code budget. -/
theorem card_le_bound_mul_sum [Finite Actual]
    (C : VariableAmbientChart A N Actual G)
    {Cold K B : ℕ}
    (hnoncritical : ∃ c : Σ i, cells (cellSlots A N R) i,
      ∃ t, colors (cellSlots A N R) c = .inr t)
    (Q : Retention (cellSlots A N R) Cold)
    (hchart : Nat.card C.Chart ≤ B)
    (hB : B ≤
      (2 * wordParameter (cellSlots A N R) + 2) ^ (K * (2 * Cold))) :
    Nat.card Actual ≤
      (2 * wordParameter (cellSlots A N R) + 2) ^ (K * (2 * Cold)) *
        ∑ b : RetainedBin (wordParameter (cellSlots A N R)) Cold,
          Nat.card (PhysicalFamily
            (wordParameter (cellSlots A N R) - binSupport b.1)
            b.1.1.1 b.1.1.2
            (Fin (2 * wordParameter (cellSlots A N R)))) :=
  ambientCell_card_le_bound_mul_sum A N R hnoncritical Q
    C.toAmbientCellCode hchart hB

end VariableAmbientChart

/-! ## The intrinsic degree-eight carrier residual family -/

/-- The unmarked actual carrier residuals at the degree dictated by the
fixed routed slot word. -/
abbrev DegreeEightCarrierResidual :=
  {H : Subgroup
      (Equiv.Perm (Fin (2 * wordParameter (cellSlots A N R)))) //
    H ∈ carrierResidualFamily
      (2 * wordParameter (cellSlots A N R))}

/-- The honest complete-chart producer still required for the actual
degree-eight residual family.

Unlike `OrbitWitness.chart`, a value of `Chart` must determine one homomorphism
from the *complete* fixed product.  Thus equality of chart codes really gives
the same ambient map, after which equality of the exact-axis comaps recovers
the original subgroup. -/
structure DegreeEightResidualChart where
  Chart : Type
  chartFinite : Finite Chart
  chart : DegreeEightCarrierResidual A N R → Chart
  ambientHom : Chart →
    ((∀ i, A i) →*
      Equiv.Perm (Fin (2 * wordParameter (cellSlots A N R))))
  le_range : ∀ H : DegreeEightCarrierResidual A N R,
    H.1 ≤ (ambientHom (chart H)).range
  full : ∀ H : DegreeEightCarrierResidual A N R,
    CarrierProductFull (H.1.comap (ambientHom (chart H)))
  axis : ∀ (H : DegreeEightCarrierResidual A N R) i,
    carrierAxis (H.1.comap (ambientHom (chart H))) i = N i

namespace DegreeEightResidualChart

variable {A N R}

/-- A complete residual chart is a variable ambient chart with the literal
subgroup projection as its embedded actual subgroup. -/
def toVariableAmbientChart (C : DegreeEightResidualChart A N R) :
    VariableAmbientChart A N (DegreeEightCarrierResidual A N R)
      (Equiv.Perm (Fin (2 * wordParameter (cellSlots A N R)))) where
  subgroup := fun H ↦ H.1
  subgroup_injective := Subtype.coe_injective
  Chart := C.Chart
  chartFinite := C.chartFinite
  chart := C.chart
  ambientHom := C.ambientHom
  le_range := C.le_range
  full := C.full
  axis := C.axis

/-- The requested bounded `DecorationCode + fixed AmbientCellCode`: the chart
is the only decoration, while the comap supplies the fixed routed cell. -/
def toAmbientCellCode (C : DegreeEightResidualChart A N R) :
    AmbientCellCode A N (DegreeEightCarrierResidual A N R) :=
  C.toVariableAmbientChart.toAmbientCellCode

/-- The complete actual residual-to-routed-word source code, conditional only
on the numerical chart-code bound. -/
def toSourceCode (C : DegreeEightResidualChart A N R)
    {Cold K : ℕ}
    (hcard : Nat.card C.Chart ≤
      (2 * wordParameter (cellSlots A N R) + 2) ^ (K * (2 * Cold))) :
    SourceCode (cellSlots A N R)
      (DegreeEightCarrierResidual A N R) Cold K :=
  C.toVariableAmbientChart.toSourceCode (R := R) hcard

/-- Final retained-bin count for a bounded complete chart of every actual
degree-eight carrier residual subgroup. -/
theorem carrierResidual_card_le_bound_mul_sum
    (C : DegreeEightResidualChart A N R)
    {Cold K B : ℕ}
    (hnoncritical : ∃ c : Σ i, cells (cellSlots A N R) i,
      ∃ t, colors (cellSlots A N R) c = .inr t)
    (Q : Retention (cellSlots A N R) Cold)
    (hchart : Nat.card C.Chart ≤ B)
    (hB : B ≤
      (2 * wordParameter (cellSlots A N R) + 2) ^ (K * (2 * Cold))) :
    Nat.card (DegreeEightCarrierResidual A N R) ≤
      (2 * wordParameter (cellSlots A N R) + 2) ^ (K * (2 * Cold)) *
        ∑ b : RetainedBin (wordParameter (cellSlots A N R)) Cold,
          Nat.card (PhysicalFamily
            (wordParameter (cellSlots A N R) - binSupport b.1)
            b.1.1.1 b.1.1.2
            (Fin (2 * wordParameter (cellSlots A N R)))) :=
  C.toVariableAmbientChart.card_le_bound_mul_sum (R := R)
    hnoncritical Q hchart hB

end DegreeEightResidualChart

end SymmetricSubgroupAsymptotics.BinaryDegreeEightVariableChartAggregation
