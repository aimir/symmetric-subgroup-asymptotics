import SymmetricSubgroupAsymptotics.SmallFibreKnownModelGlobalClassGap
import SymmetricSubgroupAsymptotics.CFSGClassificationTransport

/-! Every nonaffine small-fibre top outside the proved global profiles
retains a literal Tits or sporadic model. The selected simple factor,
model equivalence, original block system and original source are unchanged.
The positive-parameter Ree family is now excluded in its entirety. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallFibreNonaffineFiniteModelNormalization
open PrimitiveSocleRawStructure OriginalBlockClassBound
open SmallFibreKnownModelGlobalClassGap

theorem index_is_tits_or_sporadic
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (E : NonaffineData G X) (i : CFSG.Index) (e : E.Simple ≃* i.Model)
    (h : ¬ Profile E.Simple) :
    i = .tits ∨ ∃ s : CFSG.Sporadic, i = .sporadic s := by
  cases i with
  | cyclic p hp =>
    have hc : IsMulCommutative (CFSG.Index.cyclic p hp).Model := by
      change IsMulCommutative (Multiplicative (ZMod p))
      infer_instance
    exact (E.noncommutative ((CFSGReduction.isMulCommutative_congr e).mpr hc)).elim
  | alternating m hm => exact (h (alternating_closed m hm e)).elim
  | A r q hr hs =>
    by_cases h1 : r = 1
    · subst r
      exact (h (pslTwo_closed q (hs rfl) e)).elim
    · exact (h (typeA_closed r (by omega) q e)).elim
  | B r q hr =>
    by_cases hp : q.prime = 2
    · exact (h (.strong (.charTwoTypeBFull r hr q hp e))).elim
    · exact (h (.strong (.oddTypeB r hr q hp e))).elim
  | C r q hr hs =>
    by_cases hp : q.prime = 2
    · exact (h (.strong (.charTwoTypeCFull r hr q hp hs e))).elim
    · exact (h (.strong (.oddTypeC r hr q hp e))).elim
  | D r q hr => exact (h (.strong (.typeD r hr q e))).elim
  | E6 q => exact (h (.strong (.eSix q e))).elim
  | E7 q => exact (h (.strong (.eSeven q e))).elim
  | E8 q => exact (h (.strong (.eEight q e))).elim
  | F4 q => exact (h (.strong (.fFour q e))).elim
  | G2 q hs => exact (h (.strong (.gTwo q hs e))).elim
  | twistedA r q hr hs => exact (h (.strong (.unitaryComplete r hr q hs e))).elim
  | twistedD r q hr => exact (h (.strong (.twistedD r hr q e))).elim
  | twistedE6 q => exact (h (.strong (.twistedESix q e))).elim
  | trialityD4 q => exact (h (.strong (.triality q e))).elim
  | suzuki m hm => exact (h (.strong (.suzuki m hm e))).elim
  | reeG2 m hm => exact (h (.strong (.reeGTwo m hm e))).elim
  | reeF4 m hm =>
    by_cases h1 : m = 1
    · subst m
      exact (h (reeFFourFieldEight_closed e)).elim
    · exact (h (.strong (.reeFFourLarge m (by omega) e))).elim
  | tits => exact Or.inl rfl
  | sporadic s => exact Or.inr ⟨s, rfl⟩

variable {A Ω : Type} [Group A] [MulAction A Ω] [MulAction.IsPretransitive A Ω]
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)

theorem original_top_index_is_tits_or_sporadic
    (h : ¬ HasClosedTop D)
    (E : NonaffineData D.Top D.Points) (i : CFSG.Index)
    (e : E.Simple ≃* i.Model) :
    i = .tits ∨ ∃ s : CFSG.Sporadic, i = .sporadic s := by
  exact index_is_tits_or_sporadic E i e
    (fun hp => h (Or.inl ⟨E, hp⟩))

end SymmetricSubgroupAsymptotics.SmallFibreNonaffineFiniteModelNormalization
