import SymmetricSubgroupAsymptotics.BinaryCarrierRoutedWordClosure

/-!
# Routed exact-axis closure for arbitrary physical action profiles

Physical orbit profiles are curried by an action kind and an occurrence
number, whereas routed carrier words use one flat coordinate per occurrence.
The canonical curry equivalence preserves coordinate fullness and every
literal embedded normal axis.  This module supplies that bridge for an
arbitrary finite family of source permutation actions; the sources need not
already be colours of the completed mixture alphabet.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierRoutedProfileAxisClosure

open SymmetricSubgroupAsymptotics
open BinaryCarrierProfileTransport
open BinaryCarrierWordClosure
open BinaryCarrierRoutedWordClosure
open BinaryDegreeEightPhysicalAnalyticClosure

variable {γ : Type*} [Fintype γ] [DecidableEq γ]
  (Ω : γ → Type) [∀ g, Fintype (Ω g)]
  (A : ∀ g, Subgroup (Equiv.Perm (Ω g)))
  (m : γ → ℕ)

abbrev Occurrence (m : γ → ℕ) := Σ g, Fin (m g)
abbrev FlatGroup (Ω : γ → Type)
    (A : ∀ g, Subgroup (Equiv.Perm (Ω g))) (m : γ → ℕ) :=
  ∀ o : Occurrence m, A o.1

/-- Curry a literal action profile into its flat occurrence word. -/
abbrev flatten :
    OrbitProfileProductGroup m A ≃* FlatGroup Ω A m :=
  profileCurry A m

/-- Full projection on every physical occurrence is exactly product fullness
after flattening. -/
theorem full_flatten_iff
    (H : Subgroup (OrbitProfileProductGroup m A)) :
    OrbitProfileProductFull m A H ↔
      CarrierProductFull (H.map (flatten Ω A m).toMonoidHom) := by
  constructor
  · intro hfull o u
    obtain ⟨h,hh⟩ := hfull o.1 o.2 u
    refine ⟨⟨flatten Ω A m h.1,Subgroup.mem_map.mpr ⟨h.1,h.2,rfl⟩⟩,?_⟩
    exact hh
  · intro hfull g j u
    obtain ⟨h,hh⟩ := hfull ⟨g,j⟩ u
    obtain ⟨x,hx,he⟩ := Subgroup.mem_map.mp h.2
    refine ⟨⟨x,hx⟩,?_⟩
    change x g j = u
    exact (congrArg (fun y : FlatGroup Ω A m => y ⟨g,j⟩) he).trans hh

variable
  (N : ∀ o : Occurrence m, Subgroup (A o.1))
  [∀ o, (N o).Normal]

/-- The original physical profile stratum with its canonical flat-coordinate
axes fixed.  Its elements are only the original full subgroups. -/
abbrev ProfileExactAxisFamily :=
  {H : Subgroup (OrbitProfileProductGroup m A) //
    OrbitProfileProductFull m A H ∧
      ∀ o, carrierAxis (H.map (flatten Ω A m).toMonoidHom) o = N o}

/-- Flattening is an exact equivalence to the routed word's source stratum. -/
def profileExactAxisFamilyEquiv :
    ProfileExactAxisFamily Ω A m N ≃
      BinaryCarrierRoutedWordClosure.ExactAxisFamily
        (fun o : Occurrence m => A o.1) N :=
  (flatten Ω A m).mapSubgroup.toEquiv.subtypeEquiv (fun H => by
    change
      (OrbitProfileProductFull m A H ∧
        ∀ o, carrierAxis (H.map (flatten Ω A m).toMonoidHom) o = N o) ↔
      (CarrierProductFull (H.map (flatten Ω A m).toMonoidHom) ∧
        ∀ o, carrierAxis (H.map (flatten Ω A m).toMonoidHom) o = N o)
    exact and_congr (full_flatten_iff Ω A m H) Iff.rfl)

/-- Any routed fixed-axis physical profile with a displayed noncritical cell
enters the completed mixture, with no occurrence or axis marking. -/
theorem profile_exact_axis_family_card_le_mixture
    (R : ∀ o : Occurrence m, AxisSlot (A o.1) (N o))
    (hsupport : ∃ c : Σ o, (R o).slot.Cells,
      ∃ t, (R c.1).slot.color c.2 = .inr t) :
    Nat.card (ProfileExactAxisFamily Ω A m N) ≤
      Nat.card (BinaryCarrierMixtureCompletion.Family
        (parameter
          (cells (fun o => (R o).slot))
          (colors (fun o => (R o).slot)))) := by
  rw [Nat.card_congr (profileExactAxisFamilyEquiv Ω A m N)]
  exact exact_axis_word_card_le_mixture
    (fun o : Occurrence m => A o.1) N R hsupport

end SymmetricSubgroupAsymptotics.BinaryCarrierRoutedProfileAxisClosure
