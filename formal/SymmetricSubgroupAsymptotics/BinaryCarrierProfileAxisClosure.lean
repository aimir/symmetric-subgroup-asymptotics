import SymmetricSubgroupAsymptotics.BinaryCarrierSourceExtraction

/-!
# Exact-axis closure on a literal original-action profile

The completed carrier estimate is naturally stated on a flat word of orbit
occurrences.  Physical profile counting uses the curried product indexed by
an action colour and an occurrence number.  This file proves that the two
presentations are equivalent while retaining every literal coordinate axis.
Thus the fixed-axis stratum contains only the original full subgroup; no
occurrence assignment, quotient map, or normal-axis marking is counted.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierProfileAxisClosure

open SymmetricSubgroupAsymptotics
open BinaryCarrierProfileTransport
open BinaryCarrierWordClosure
open BinaryCarrierMenuSlots
open BinaryCarrierSourceExtraction

variable (m : MixtureKind → ℕ)

abbrev Occurrence := Σ g, Fin (m g)
abbrev occurrenceColor (o : Occurrence m) : MixtureKind := o.1
abbrev FlatGroup := ∀ o : Occurrence m, mixtureAction o.1

/-- Curry the literal profile product into its flat occurrence word. -/
abbrev flatten :
    OrbitProfileProductGroup m mixtureAction ≃* FlatGroup m :=
  profileCurry mixtureAction m

/-- Full projection on every profile occurrence is exactly coordinate
fullness after flattening. -/
theorem full_flatten_iff
    (H : Subgroup (OrbitProfileProductGroup m mixtureAction)) :
    OrbitProfileProductFull m mixtureAction H ↔
      CarrierProductFull (H.map (flatten m).toMonoidHom) := by
  constructor
  · intro hfull o u
    obtain ⟨h,hh⟩ := hfull o.1 o.2 u
    refine ⟨⟨flatten m h.1,Subgroup.mem_map.mpr ⟨h.1,h.2,rfl⟩⟩,?_⟩
    exact hh
  · intro hfull g j u
    obtain ⟨h,hh⟩ := hfull ⟨g,j⟩ u
    obtain ⟨x,hx,he⟩ := Subgroup.mem_map.mp h.2
    refine ⟨⟨x,hx⟩,?_⟩
    change x g j = u
    exact (congrArg (fun y : FlatGroup m => y ⟨g,j⟩) he).trans hh

section FixedAxes

variable (N : ∀ o : Occurrence m, Subgroup (mixtureAction o.1))
  [∀ o, (N o).Normal]

/-- The literal curried profile stratum with prescribed embedded axes after
the canonical flattening. -/
abbrev ProfileExactAxisFamily :=
  {H : Subgroup (OrbitProfileProductGroup m mixtureAction) //
    OrbitProfileProductFull m mixtureAction H ∧
      ∀ o, carrierAxis (H.map (flatten m).toMonoidHom) o = N o}

/-- Flattening is an equivalence from the physical profile stratum to the
unmarked exact-axis word stratum. -/
def profileExactAxisFamilyEquiv :
    ProfileExactAxisFamily m N ≃
      ExactAxisFamily (occurrenceColor m) N :=
  (flatten m).mapSubgroup.toEquiv.subtypeEquiv (fun H => by
    change
      (OrbitProfileProductFull m mixtureAction H ∧
        ∀ o, carrierAxis (H.map (flatten m).toMonoidHom) o = N o) ↔
      (CarrierProductFull (H.map (flatten m).toMonoidHom) ∧
        ∀ o, carrierAxis (H.map (flatten m).toMonoidHom) o = N o)
    exact and_congr (full_flatten_iff m H) Iff.rfl)

/-- Every fixed exact-axis stratum of a literal original-action profile with
positive noncritical support is absorbed by the completed mixture. -/
theorem profile_exact_axis_family_card_le_mixture
    (hnoncritical : ∃ g, 0 < m (.inr g)) :
    Nat.card (ProfileExactAxisFamily m N) ≤
      Nat.card (BinaryCarrierMixtureCompletion.Family
        (parameter
          (cells (quotientIdentityWord (occurrenceColor m) N
            (fun o => inferInstance)))
          (colors (quotientIdentityWord (occurrenceColor m) N
            (fun o => inferInstance))))) := by
  rw [Nat.card_congr (profileExactAxisFamilyEquiv m N)]
  apply exact_axis_family_card_le_mixture
  obtain ⟨g,hg⟩ := hnoncritical
  exact ⟨⟨.inr g,⟨0,hg⟩⟩,g,rfl⟩

end FixedAxes

end SymmetricSubgroupAsymptotics.BinaryCarrierProfileAxisClosure
