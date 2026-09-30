import SymmetricSubgroupAsymptotics.BinaryCarrierWordClosure
import SymmetricSubgroupAsymptotics.BinaryExceptionalCarriers
import SymmetricSubgroupAsymptotics.BinaryExceptionalBlocks

/-!
# The three exceptional degree-eight carriers as original profile cells

The carrier in each exceptional width-eight chart is the original `8T27`
action after its checked full-block coordinate change.  This file turns that
fact into the one-cell carrier, quotient map, and fullness statement required
by `BinaryCarrierWordClosure`.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryExceptional8ProfileCarriers

open SymmetricSubgroupAsymptotics
open BinaryCarrierProfileTransport

abbrev Target : MixtureKind :=
  .inr (some (.degree8 .t27))

abbrev Action := mixtureAction Target

/-- The ambient group is equivalent to its top subgroup. -/
def ambientTopEquiv (G : Type*) [Group G] : G ≃* (⊤ : Subgroup G) where
  toFun g := ⟨g,Subgroup.mem_top g⟩
  invFun g := g.1
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- A single displayed block covering every physical point is faithful. -/
theorem singleBlockHom_injective {X Y ρ : Type*}
    {s : ρ → Equiv.Perm X} (B : PermutationBlockChart (Y := Y) s)
    (hcover : ∀ x : X, ∃ y, B.embedding y = x) :
    Function.Injective B.hom := by
  intro g h he
  apply Subtype.ext
  ext x
  obtain ⟨y,rfl⟩ := hcover x
  rw [B.hom_intertwine,B.hom_intertwine,he]

/-- Swapping the two checked generators does not change the original `8T27`
subgroup. -/
theorem closure_eq_t27 (g : Fin 2 → Equiv.Perm (Fin 8))
    (hswap : ∀ j, g j = BinaryMenuCayley8T27.generators
      ⟨1-j.val,by omega⟩) :
    Subgroup.closure (Set.range g) =
      BinaryCarrierRoutes8.originalSubgroup .t27 := by
  change Subgroup.closure (Set.range g) =
    Subgroup.closure (Set.range BinaryMenuCayley8T27.generators)
  congr 1
  ext x
  simp only [Set.mem_range]
  constructor
  · rintro ⟨j,rfl⟩
    exact ⟨⟨1-j.val,by omega⟩,(hswap j).symm⟩
  · rintro ⟨j,rfl⟩
    let k : Fin 2 := ⟨1-j.val,by omega⟩
    refine ⟨k,?_⟩
    rw [hswap k]
    congr
    dsimp [k]
    omega

/-- Turn an equivalence with the target action into the literal one-cell top
carrier used by the simultaneous word theorem. -/
def oneCellEquiv {G : Type*} [Group G] (e : G ≃* Action) :
    G ≃* (⊤ : Subgroup (∀ _ : Fin 1, Action)) :=
  e.trans ((MulEquiv.piUnique (fun _ : Fin 1 => Action)).symm.trans
    (ambientTopEquiv (∀ _ : Fin 1, Action)))

def oneCellCarrier : Subgroup (∀ _ : Fin 1, Action) := ⊤

theorem oneCellCarrier_full : CarrierProductFull oneCellCarrier := by
  intro j u
  exact ⟨⟨fun _ => u,Subgroup.mem_top _⟩,rfl⟩

namespace T16

abbrev chart := BinaryChart8T16.chart
abbrev Source := chart.source
abbrev ActualCarrier := chart.carrier
abbrev Quotient := chart.quotient

theorem base_eq_action :
    Subgroup.closure (Set.range BinaryChart8T16.block0BaseGenerators) = Action := by
  apply closure_eq_t27
  intro j
  revert j
  decide +kernel

def carrierActionHom : ActualCarrier →* Action :=
  BinaryChart8T16.block0.hom.codRestrict Action (fun x => by
    rw [← base_eq_action,← BinaryChart8T16.block0_range]
    exact ⟨x,rfl⟩)

theorem carrierActionHom_surjective : Function.Surjective carrierActionHom := by
  intro y
  have hy : y.1 ∈ BinaryChart8T16.block0.hom.range := by
    rw [BinaryChart8T16.block0_range,base_eq_action]
    exact y.2
  obtain ⟨x,hx⟩ := hy
  exact ⟨x,Subtype.ext hx⟩

theorem carrierActionHom_injective : Function.Injective carrierActionHom := by
  intro x y h
  apply singleBlockHom_injective BinaryChart8T16.block0 BinaryChart8T16.blocks_cover
  exact congrArg Subtype.val h

def carrierActionEquiv : ActualCarrier ≃* Action :=
  MulEquiv.ofBijective carrierActionHom
    ⟨carrierActionHom_injective,carrierActionHom_surjective⟩

abbrev flatCarrier := oneCellCarrier
def actualFlatEquiv : ActualCarrier ≃* flatCarrier :=
  oneCellEquiv carrierActionEquiv

abbrev alpha : Source →* Quotient := chart.alpha
def beta : flatCarrier →* Quotient :=
  chart.beta.comp actualFlatEquiv.symm.toMonoidHom

theorem alpha_surjective : Function.Surjective alpha := chart.alpha_surjective
theorem beta_surjective : Function.Surjective beta := by
  intro q
  obtain ⟨x,hx⟩ := chart.beta_surjective q
  exact ⟨actualFlatEquiv x,by simpa [beta] using hx⟩
theorem flatCarrier_full : CarrierProductFull flatCarrier := oneCellCarrier_full
theorem alpha_kernel : alpha.ker.map Source.subtype = chart.axis := chart.alpha_kernel

end T16

namespace T20

abbrev chart := BinaryChart8T20.chart
abbrev Source := chart.source
abbrev ActualCarrier := chart.carrier
abbrev Quotient := chart.quotient

theorem base_eq_action :
    Subgroup.closure (Set.range BinaryChart8T20.block0BaseGenerators) = Action := by
  apply closure_eq_t27
  intro j
  revert j
  decide +kernel

def carrierActionHom : ActualCarrier →* Action :=
  BinaryChart8T20.block0.hom.codRestrict Action (fun x => by
    rw [← base_eq_action,← BinaryChart8T20.block0_range]
    exact ⟨x,rfl⟩)

theorem carrierActionHom_surjective : Function.Surjective carrierActionHom := by
  intro y
  have hy : y.1 ∈ BinaryChart8T20.block0.hom.range := by
    rw [BinaryChart8T20.block0_range,base_eq_action]
    exact y.2
  obtain ⟨x,hx⟩ := hy
  exact ⟨x,Subtype.ext hx⟩

theorem carrierActionHom_injective : Function.Injective carrierActionHom := by
  intro x y h
  apply singleBlockHom_injective BinaryChart8T20.block0 BinaryChart8T20.blocks_cover
  exact congrArg Subtype.val h

def carrierActionEquiv : ActualCarrier ≃* Action :=
  MulEquiv.ofBijective carrierActionHom
    ⟨carrierActionHom_injective,carrierActionHom_surjective⟩

abbrev flatCarrier := oneCellCarrier
def actualFlatEquiv : ActualCarrier ≃* flatCarrier :=
  oneCellEquiv carrierActionEquiv

abbrev alpha : Source →* Quotient := chart.alpha
def beta : flatCarrier →* Quotient :=
  chart.beta.comp actualFlatEquiv.symm.toMonoidHom

theorem alpha_surjective : Function.Surjective alpha := chart.alpha_surjective
theorem beta_surjective : Function.Surjective beta := by
  intro q
  obtain ⟨x,hx⟩ := chart.beta_surjective q
  exact ⟨actualFlatEquiv x,by simpa [beta] using hx⟩
theorem flatCarrier_full : CarrierProductFull flatCarrier := oneCellCarrier_full
theorem alpha_kernel : alpha.ker.map Source.subtype = chart.axis := chart.alpha_kernel

end T20

namespace T21

abbrev chart := BinaryChart8T21.chart
abbrev Source := chart.source
abbrev ActualCarrier := chart.carrier
abbrev Quotient := chart.quotient

theorem base_eq_action :
    Subgroup.closure (Set.range BinaryChart8T21.block0BaseGenerators) = Action := by
  apply closure_eq_t27
  intro j
  revert j
  decide +kernel

def carrierActionHom : ActualCarrier →* Action :=
  BinaryChart8T21.block0.hom.codRestrict Action (fun x => by
    rw [← base_eq_action,← BinaryChart8T21.block0_range]
    exact ⟨x,rfl⟩)

theorem carrierActionHom_surjective : Function.Surjective carrierActionHom := by
  intro y
  have hy : y.1 ∈ BinaryChart8T21.block0.hom.range := by
    rw [BinaryChart8T21.block0_range,base_eq_action]
    exact y.2
  obtain ⟨x,hx⟩ := hy
  exact ⟨x,Subtype.ext hx⟩

theorem carrierActionHom_injective : Function.Injective carrierActionHom := by
  intro x y h
  apply singleBlockHom_injective BinaryChart8T21.block0 BinaryChart8T21.blocks_cover
  exact congrArg Subtype.val h

def carrierActionEquiv : ActualCarrier ≃* Action :=
  MulEquiv.ofBijective carrierActionHom
    ⟨carrierActionHom_injective,carrierActionHom_surjective⟩

abbrev flatCarrier := oneCellCarrier
def actualFlatEquiv : ActualCarrier ≃* flatCarrier :=
  oneCellEquiv carrierActionEquiv

abbrev alpha : Source →* Quotient := chart.alpha
def beta : flatCarrier →* Quotient :=
  chart.beta.comp actualFlatEquiv.symm.toMonoidHom

theorem alpha_surjective : Function.Surjective alpha := chart.alpha_surjective
theorem beta_surjective : Function.Surjective beta := by
  intro q
  obtain ⟨x,hx⟩ := chart.beta_surjective q
  exact ⟨actualFlatEquiv x,by simpa [beta] using hx⟩
theorem flatCarrier_full : CarrierProductFull flatCarrier := oneCellCarrier_full
theorem alpha_kernel : alpha.ker.map Source.subtype = chart.axis := chart.alpha_kernel

end T21

end SymmetricSubgroupAsymptotics.BinaryExceptional8ProfileCarriers
