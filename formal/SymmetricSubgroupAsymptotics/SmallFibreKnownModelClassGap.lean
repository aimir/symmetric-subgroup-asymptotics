import SymmetricSubgroupAsymptotics.SmallFibreExceptionalLargeIndexClassGap
import SymmetricSubgroupAsymptotics.SmallFibreTypeAUnitaryLargeParameterGap
import SymmetricSubgroupAsymptotics.SmallFibreReeGTwoClassGap
import SymmetricSubgroupAsymptotics.SmallFibreClassicalLargeParameterGap
import SymmetricSubgroupAsymptotics.SmallFibreFFourTrialityClassGap
import SymmetricSubgroupAsymptotics.SmallFibreSuzukiClassGap
import SymmetricSubgroupAsymptotics.SmallFibreGTwoCompleteClassGap
import SymmetricSubgroupAsymptotics.SmallFibreReeFFourLargeParameterGap
import SymmetricSubgroupAsymptotics.OriginalMinimalBlockComponentTransport

/-! Concrete original model profiles whose actual binary/ternary-fibre
class gap is proved. The profile records literal equivalences and parameter
inequalities; it is not a historical owner label or an assumed class budget.
The native installer uses the SAME original minimal block and source. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallFibreKnownModelClassGap
open PrimitiveSocleRawStructure OriginalBlockClassBound

inductive Profile (S : Type) [Group S] : Prop
  | eSix (q : CFSG.PrimePower) (e : S ≃* CFSG.Models.E6 q) : Profile S
  | eSeven (q : CFSG.PrimePower) (e : S ≃* CFSG.Models.E7 q) : Profile S
  | eEight (q : CFSG.PrimePower) (e : S ≃* CFSG.Models.E8 q) : Profile S
  | twistedESix (q : CFSG.PrimePower) (e : S ≃* CFSG.Models.TwistedE6 q) : Profile S
  | reeGTwo (m : ℕ) (hm : 1 ≤ m) (e : S ≃* CFSG.Models.ReeG2 m) : Profile S
  | fFour (q : CFSG.PrimePower) (e : S ≃* CFSG.Models.F4 q) : Profile S
  | triality (q : CFSG.PrimePower) (e : S ≃* CFSG.Models.TrialityD4 q) : Profile S
  | suzuki (m : ℕ) (hm : 1 ≤ m) (e : S ≃* CFSG.Models.Suzuki m) : Profile S
  | gTwo (q : CFSG.PrimePower) (hs : q.order ≠ 2) (e : S ≃* CFSG.Models.G2 q) : Profile S
  | reeFFourLarge (m : ℕ) (hm : 2 ≤ m) (e : S ≃* CFSG.Models.ReeF4 m) : Profile S
  | higherA (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
      (hlarge : 2048 ≤ q.order^r) (e : S ≃* CFSG.Models.A r q) : Profile S
  | pslTwo (q : CFSG.PrimePower) (hlarge : 4096 ≤ q.order)
      (e : S ≃* CFSG.Models.A 1 q) : Profile S
  | unitary (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
      (hsmall : r=2 → q.order≠2) (hlarge : 2048 ≤ q.order^r)
      (e : S ≃* CFSG.Models.TwistedA r q) : Profile S
  | typeB (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
      (hlarge : 2048 ≤ q.order^(r-1)) (e : S ≃* CFSG.Models.B r q) : Profile S
  | typeC (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
      (hsmall : r=2 → q.order≠2) (hlarge : 2048 ≤ q.order^(r-1))
      (e : S ≃* CFSG.Models.C r q) : Profile S
  | typeD (r : ℕ) (hr : 4 ≤ r) (q : CFSG.PrimePower)
      (hlarge : 2048 ≤ q.order^(r-1)) (e : S ≃* CFSG.Models.D r q) : Profile S
  | twistedD (r : ℕ) (hr : 4 ≤ r) (q : CFSG.PrimePower)
      (hlarge : 2048 ≤ q.order^(r-2)) (e : S ≃* CFSG.Models.TwistedD r q) : Profile S

theorem subnormal_class_cube_gap
    {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]
    (pi : Ω → X) (hpi : ∀ (g : A) (w : Ω), pi (g • w)=g • pi w)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre pi x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (hprofile : Profile E.Simple) (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) := by
  cases hprofile with
  | eSix q e =>
    exact SmallFibreExceptionalLargeIndexClassGap.subnormal_class_cube_gap_of_eSix
      pi hpi c hc hsize E q e H hH
  | eSeven q e =>
    exact SmallFibreExceptionalLargeIndexClassGap.subnormal_class_cube_gap_of_eSeven
      pi hpi c hc hsize E q e H hH
  | eEight q e =>
    exact SmallFibreExceptionalLargeIndexClassGap.subnormal_class_cube_gap_of_eEight
      pi hpi c hc hsize E q e H hH
  | twistedESix q e =>
    exact SmallFibreExceptionalLargeIndexClassGap.subnormal_class_cube_gap_of_twistedESix
      pi hpi c hc hsize E q e H hH
  | reeGTwo m hm e =>
    exact SmallFibreReeGTwoClassGap.subnormal_class_cube_gap_of_reeGTwo
      pi hpi c hc hsize E m hm e H hH
  | fFour q e =>
    exact SmallFibreFFourTrialityClassGap.subnormal_class_cube_gap_of_fFour
      pi hpi c hc hsize E q e H hH
  | triality q e =>
    exact SmallFibreFFourTrialityClassGap.subnormal_class_cube_gap_of_triality
      pi hpi c hc hsize E q e H hH
  | suzuki m hm e =>
    exact SmallFibreSuzukiClassGap.subnormal_class_cube_gap_of_suzuki
      pi hpi c hc hsize E m hm e H hH
  | gTwo q hs e =>
    exact SmallFibreGTwoCompleteClassGap.subnormal_class_cube_gap_of_gTwo
      pi hpi c hc hsize E q hs e H hH
  | reeFFourLarge m hm e =>
    exact SmallFibreReeFFourLargeParameterGap.subnormal_class_cube_gap_of_reeFFour_large_parameter
      pi hpi c hc hsize E m hm e H hH
  | higherA r hr q hlarge e =>
    rcases SmallFibreTypeAUnitaryLargeParameterGap.subnormal_gap_or_higherA_small_parameter
      pi hpi c hc hsize E r hr q e H hH with h | h
    · exact h
    · omega
  | pslTwo q hlarge e =>
    rcases SmallFibreTypeAUnitaryLargeParameterGap.subnormal_gap_or_pslTwo_small_field
      pi hpi c hc hsize E q (by omega) e H hH with h | h
    · exact h
    · omega
  | unitary r hr q hsmall hlarge e =>
    rcases SmallFibreTypeAUnitaryLargeParameterGap.subnormal_gap_or_unitary_small_parameter
      pi hpi c hc hsize E r hr q hsmall e H hH with h | h
    · exact h
    · omega
  | typeB r hr q hlarge e =>
    rcases SmallFibreClassicalLargeParameterGap.subnormal_gap_or_typeB_small_parameter
      pi hpi c hc hsize E r hr q e H hH with h | h
    · exact h
    · omega
  | typeC r hr q hsmall hlarge e =>
    rcases SmallFibreClassicalLargeParameterGap.subnormal_gap_or_typeC_small_parameter
      pi hpi c hc hsize E r hr q hsmall e H hH with h | h
    · exact h
    · omega
  | typeD r hr q hlarge e =>
    rcases SmallFibreClassicalLargeParameterGap.subnormal_gap_or_typeD_small_parameter
      pi hpi c hc hsize E r hr q e H hH with h | h
    · exact h
    · omega
  | twistedD r hr q hlarge e =>
    rcases SmallFibreClassicalLargeParameterGap.subnormal_gap_or_twistedD_small_parameter
      pi hpi c hc hsize E r hr q e H hH with h | h
    · exact h
    · omega

variable {A Ω : Type} [Group A] [MulAction A Ω] [MulAction.IsPretransitive A Ω]
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    {w : Ω} (D : OriginalMinimalBlock (A := A) w)

def HasClosedTop : Prop :=
  ∃ E : NonaffineData (Top (A := A) (X := D.Points)) D.Points, Profile E.Simple

theorem class_cube_gap_of_closed_top
    (hc : Nat.card D.Fibre=2 ∨ Nat.card D.Fibre=3) (htop : HasClosedTop D) :
    Nat.card (ConjClasses A)^3 ≤ 5^(Nat.card Ω-2) := by
  obtain ⟨E, hprofile⟩ := htop
  have h := subnormal_class_cube_gap D.map D.map_equivariant
    (Nat.card D.Fibre) hc D.fibre_card_at E hprofile ⊤
      (Subgroup.Normal.isSubnormal inferInstance)
  have he := conjugacyClass_card_congr (Subgroup.topEquiv : (⊤ : Subgroup A) ≃* A)
  rwa [he] at h

end SymmetricSubgroupAsymptotics.SmallFibreKnownModelClassGap
