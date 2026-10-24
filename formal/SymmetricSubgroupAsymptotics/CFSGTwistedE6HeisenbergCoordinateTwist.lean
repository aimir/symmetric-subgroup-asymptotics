import SymmetricSubgroupAsymptotics.CFSGTwistedE6HeisenbergParameterSigns
import SymmetricSubgroupAsymptotics.CFSGCommutingParameterTwist
import SymmetricSubgroupAsymptotics.CFSGExceptionalHeisenbergPositive

/-! The actual diagram--field twist on ordered Heisenberg root products.
The normalization of the Y roots is retained in its signed coefficient
map.  Separate stability of the commuting X and Y families prevents a
central reordering correction.  Fixedness is tested through the actual
faithful positive-root product, not assumed on its quotient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6HeisenbergCoordinateTwist
open CFSGExceptionalCartanPositiveDefinite CFSGExceptionalHeisenbergRootRelations
open CFSGExceptionalHeisenbergProduct CFSGExceptionalHeisenbergPositive
open CFSGTwistedE6HeisenbergStableRootFamilies CFSGTwistedE6HeisenbergParameterSigns
open CFSGTwistedE6GeckMatrixTwist CFSGCommutingParameterTwist
open CFSGHeisenbergCoordinateGroup
private abbrev ActualUnits (K : Type) [CommRing K] :=
  (Matrix CFSGTwistedE6GeckDiagramCovariance.GeckIndex
    CFSGTwistedE6GeckDiagramCovariance.GeckIndex K)ˣ
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

def firstWeight (i : Fin 10) : ℤ := twistSign (configuration.xRoot i).val
def secondWeight (i : Fin 10) : ℤ :=
  pairSign A hd hs hp ho configuration (partner i) *
    pairSign A hd hs hp ho configuration i * twistSign (configuration.yRoot i).val
def centralWeight : ℤ := twistSign configuration.zRoot.val

private theorem signs_mul {a b : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b = 1 ∨ a * b = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

theorem firstWeight_unit (i : Fin 10) : firstWeight i = 1 ∨ firstWeight i = -1 :=
  twistSign_unit _

theorem secondWeight_unit (i : Fin 10) : secondWeight i = 1 ∨ secondWeight i = -1 :=
  signs_mul (signs_mul (pairSign_unit A hd hs hp ho configuration (partner i))
    (pairSign_unit A hd hs hp ho configuration i)) (twistSign_unit _)

theorem centralWeight_unit : centralWeight = 1 ∨ centralWeight = -1 := twistSign_unit _

theorem firstProduct_twist (K : Type) [CommRing K] (sigma : K ≃+* K) (v : Fin 10 → K) :
    unitTwist K sigma (X A hd hs hp ho configuration K (Multiplicative.ofAdd v)) =
      X A hd hs hp ho configuration K
        (Multiplicative.ofAdd (coefficientMap sigma partner firstWeight v)) := by
  have hc : Pairwise (fun i j => ∀ a b,
      Commute (xHom A hd hs hp ho configuration K i a)
        (xHom A hd hs hp ho configuration K j b)) := by
    intro i j _ a b
    exact x_commute A hd hs hp ho configuration K i j a.toAdd b.toAdd
  apply map_parameterHom sigma partner firstWeight
    (xHom A hd hs hp ho configuration K) hc (unitTwist K sigma).toMonoidHom
  intro i a
  change unitTwist K sigma (rootParameter K (configuration.xRoot i).val a) =
    rootParameter K (configuration.xRoot (partner i)).val ((firstWeight i : K) * sigma a)
  exact firstParameter_twist K sigma i a

theorem secondProduct_twist (K : Type) [CommRing K] (sigma : K ≃+* K) (v : Fin 10 → K) :
    unitTwist K sigma (Y A hd hs hp ho configuration K (Multiplicative.ofAdd v)) =
      Y A hd hs hp ho configuration K
        (Multiplicative.ofAdd (coefficientMap sigma partner secondWeight v)) := by
  have hc : Pairwise (fun i j => ∀ a b,
      Commute (yNegative A hd hs hp ho configuration K i a)
        (yNegative A hd hs hp ho configuration K j b)) := by
    intro i j _ a b
    exact y_commute A hd hs hp ho configuration K i j (-a.toAdd) (-b.toAdd)
  apply map_parameterHom sigma partner secondWeight
    (yNegative A hd hs hp ho configuration K) hc (unitTwist K sigma).toMonoidHom
  intro i a
  change unitTwist K sigma (rootParameter K (configuration.yRoot i).val
      ((pairSign A hd hs hp ho configuration i : K) * (-a))) =
    rootParameter K (configuration.yRoot (partner i)).val
      ((pairSign A hd hs hp ho configuration (partner i) : K) *
        (-((secondWeight i : K) * sigma a)))
  rw [secondParameter_twist]
  apply congrArg (rootParameter K (configuration.yRoot (partner i)).val)
  simp only [secondWeight, Int.cast_mul, map_mul, map_neg, map_intCast]
  rcases pairSign_unit A hd hs hp ho configuration (partner i) with hh | hh <;>
    simp only [hh, Int.cast_one, Int.cast_neg] <;> ring

def coordinateTwist (K : Type) [CommRing K] (sigma : K ≃+* K)
    (g : Element K 10) : Element K 10 :=
  ⟨coefficientMap sigma partner firstWeight g.a,
    coefficientMap sigma partner secondWeight g.b, (centralWeight : K) * sigma g.c⟩

theorem rawHom_apply (K : Type) [CommRing K] (g : Element K 10) :
    rawHom A hd hs hp ho configuration K g =
      X A hd hs hp ho configuration K (Multiplicative.ofAdd g.a) *
        Y A hd hs hp ho configuration K (Multiplicative.ofAdd g.b) *
          zHom A hd hs hp ho configuration K (Multiplicative.ofAdd g.c) := rfl

private theorem map_three {G H : Type*} [Monoid G] [Monoid H]
    (f : G →* H) (a b c : G) : f (a * b * c) = f a * f b * f c := by
  rw [map_mul, map_mul]

theorem rawHom_twist (K : Type) [CommRing K] (sigma : K ≃+* K) (g : Element K 10) :
    unitTwist K sigma (rawHom A hd hs hp ho configuration K g) =
      rawHom A hd hs hp ho configuration K (coordinateTwist K sigma g) := by
  have hm := map_three (unitTwist K sigma).toMonoidHom
    (X A hd hs hp ho configuration K (Multiplicative.ofAdd g.a))
    (Y A hd hs hp ho configuration K (Multiplicative.ofAdd g.b))
    (zHom A hd hs hp ho configuration K (Multiplicative.ofAdd g.c))
  simp only [MulEquiv.coe_toMonoidHom] at hm
  rw [rawHom_apply, rawHom_apply]
  calc
    _ = unitTwist K sigma (X A hd hs hp ho configuration K (Multiplicative.ofAdd g.a)) *
        unitTwist K sigma (Y A hd hs hp ho configuration K (Multiplicative.ofAdd g.b)) *
          unitTwist K sigma (zHom A hd hs hp ho configuration K (Multiplicative.ofAdd g.c)) := hm
    _ = _ := congrArg₂ (fun a b : ActualUnits K => a * b)
      (congrArg₂ (fun a b : ActualUnits K => a * b)
        (firstProduct_twist K sigma g.a) (secondProduct_twist K sigma g.b))
      (centralParameter_twist K sigma g.c)

theorem rawHom_fixed_iff (K : Type) [Field K] (sigma : K ≃+* K) (g : Element K 10) :
    unitTwist K sigma (rawHom A hd hs hp ho configuration K g) =
        rawHom A hd hs hp ho configuration K g ↔ coordinateTwist K sigma g = g := by
  rw [rawHom_twist]
  constructor
  · intro he
    exact rawHom_injective A hd hs hp ho configuration K he
  · exact congrArg (rawHom A hd hs hp ho configuration K)

end SymmetricSubgroupAsymptotics.CFSGTwistedE6HeisenbergCoordinateTwist
