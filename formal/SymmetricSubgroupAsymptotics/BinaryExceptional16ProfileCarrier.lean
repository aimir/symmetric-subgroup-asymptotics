import SymmetricSubgroupAsymptotics.BinaryCarrierProfileTransport
import SymmetricSubgroupAsymptotics.BinaryExceptional16PhysicalProfile

/-!
# The proper 16T1086 carrier in literal profile-product coordinates

The exceptional carrier is kept as a proper group.  Its faithful physical
action is merely rewritten in the one-C4/three-D8 occurrence coordinates of
the completed mixture.  This supplies the exact replacement subgroup and
quotient map required by simultaneous `BinaryTransport`; it never replaces
the carrier by the product of its four projections.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryExceptional16ProfileCarrier

open SymmetricSubgroupAsymptotics
open BinaryExceptional16PhysicalProfile.ExactProfile
open BinaryCarrierProfileTransport

abbrev Source := BinaryNormalTransport16T1086.chart.source
abbrev ActualCarrier := BinaryNormalTransport16T1086.chart.carrier
abbrev Quotient := BinaryNormalTransport16T1086.chart.quotient

abbrev Kind := CriticalActionKind ⊕
  BinaryCarrierOriginalCyclicFourHall.Target

abbrev Points : Kind → Type := pointFamily
abbrev Action : (i : Kind) → Subgroup (Equiv.Perm (Points i)) := actionFamily
abbrev Multiplicity : Kind → ℕ := multiplicity
abbrev Product := OrbitProfileProductGroup Multiplicity Action
abbrev Occurrence := Σ i, Fin (Multiplicity i)
abbrev FlatProduct := (o : Occurrence) → Action o.1

/-- The proper carrier on the profile model points. -/
def model : Subgroup (Equiv.Perm ModelPoints) :=
  relabelSubgroup chart.symm ActualCarrier

theorem model_full : OrbitProfileFull Action 1 model := by
  apply (orbitProfileFullOn_iff Action 1 model).mp
  simpa only [Equiv.self_trans_symm] using carrier_full.relabel chart.symm

/-- The same proper carrier as a subgroup of the literal independent action
product.  The comap is exact because the product action is faithful. -/
def productCarrier : Subgroup Product :=
  model.comap (orbitProfileProductAction Multiplicity Action)

theorem productCarrier_full :
    OrbitProfileProductFull Multiplicity Action productCarrier :=
  orbitProfileFull_comap model_full

def productToModel : productCarrier →* model :=
  ((orbitProfileProductAction Multiplicity Action).comp productCarrier.subtype).codRestrict
    model (fun x => x.2)

theorem productToModel_injective : Function.Injective productToModel := by
  intro x y h
  apply Subtype.ext
  apply orbitProfileProductAction_injective Multiplicity Action
  have hv := congrArg Subtype.val h
  change orbitProfileProductAction Multiplicity Action x.1 =
    orbitProfileProductAction Multiplicity Action y.1 at hv
  exact hv

theorem productToModel_surjective : Function.Surjective productToModel := by
  intro y
  obtain ⟨d,hd⟩ := orbitProfileFull_le_product_range model_full y.2
  refine ⟨⟨d,?_⟩,?_⟩
  · change orbitProfileProductAction Multiplicity Action d ∈ model
    rw [hd]
    exact y.2
  · apply Subtype.ext
    change orbitProfileProductAction Multiplicity Action d = y.1
    exact hd

def productModelEquiv : productCarrier ≃* model :=
  MulEquiv.ofBijective productToModel
    ⟨productToModel_injective,productToModel_surjective⟩

/-- Relabelling the actual sixteen physical points gives the exact model
subgroup, with no abstract-action substitution. -/
def actualModelEquiv : ActualCarrier ≃* model :=
  ActualCarrier.equivMapOfInjective chart.symm.permCongrHom.toMonoidHom
    chart.symm.permCongrHom.injective

def flatCarrier : Subgroup FlatProduct :=
  productCarrier.map (profileCurry Action Multiplicity).toMonoidHom

def productFlatEquiv : productCarrier ≃* flatCarrier :=
  productCarrier.equivMapOfInjective
    (profileCurry Action Multiplicity).toMonoidHom
    (profileCurry Action Multiplicity).injective

/-- Exact equivalence from the original proper carrier to its flat displayed
profile cells. -/
def actualFlatEquiv : ActualCarrier ≃* flatCarrier :=
  actualModelEquiv.trans (productModelEquiv.symm.trans productFlatEquiv)

/-- The original checked quotient map, transported through the exact carrier
coordinate equivalence. -/
def beta : flatCarrier →* Quotient :=
  BinaryNormalTransport16T1086.chart.beta.comp actualFlatEquiv.symm.toMonoidHom

theorem beta_surjective : Function.Surjective beta := by
  intro q
  obtain ⟨y,hy⟩ := BinaryNormalTransport16T1086.chart.beta_surjective q
  exact ⟨actualFlatEquiv y,by simpa [beta] using hy⟩

/-- The proper displayed carrier is full on every one of its four mixture
cells.  No assertion of independence between the cells is made. -/
theorem flatCarrier_full : CarrierProductFull flatCarrier := by
  intro o u
  obtain ⟨x,hx⟩ := productCarrier_full o.1 o.2 u
  refine ⟨⟨profileCurry Action Multiplicity x.1,
    Subgroup.mem_map.mpr ⟨x.1,x.2,rfl⟩⟩,?_⟩
  exact hx

/-- The source side is still the checked original 16T1086 map. -/
abbrev alpha : Source →* Quotient := BinaryNormalTransport16T1086.chart.alpha

theorem alpha_surjective : Function.Surjective alpha :=
  BinaryNormalTransport16T1086.chart.alpha_surjective

theorem alpha_kernel :
    alpha.ker.map Source.subtype = BinaryNormalTransport16T1086.chart.axis :=
  BinaryNormalTransport16T1086.chart.alpha_kernel

end SymmetricSubgroupAsymptotics.BinaryExceptional16ProfileCarrier
