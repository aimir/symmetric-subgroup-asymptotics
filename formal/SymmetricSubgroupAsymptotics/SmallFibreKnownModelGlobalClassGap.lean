import SymmetricSubgroupAsymptotics.SmallFibreClassicalBoundedHeadParameters
import SymmetricSubgroupAsymptotics.SmallFibreTypeARankThreeBinaryOrdinaryClassGap

/-! The original global class-count induction needs the exponent
`card Ω - 1`. Keep the stronger local `card Ω - 2` API intact, and
install the actual rank-three binary model using precisely the global
margin. Its ternary eight-block case therefore needs no extra local
fusion estimate. All original kernels, subnormal sources and degree
forms are retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallFibreKnownModelGlobalClassGap
open PrimitiveSocleRawStructure OriginalBlockClassBound

inductive Profile (S : Type) [Group S] : Prop
  | strong (h : SmallFibreKnownModelClassGap.Profile S) : Profile S
  | typeARankThreeBinary (q : CFSG.PrimePower) (hq : q.order=2)
      (e : S ≃* CFSG.Models.A 3 q) : Profile S

theorem subnormal_class_cube_gap_at_original_degree
    {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]
    (pi : Ω → X) (hpi : ∀ (g : A) (w : Ω), pi (g • w)=g • pi w)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre pi x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (hprofile : Profile E.Simple) (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-1) := by
  cases hprofile with
  | strong h =>
    exact (SmallFibreKnownModelClassGap.subnormal_class_cube_gap
      pi hpi c hc hsize E h H hH).trans
        (Nat.pow_le_pow_right (by decide) (by omega))
  | typeARankThreeBinary q hq e =>
    exact SmallFibreTypeARankThreeBinaryOrdinaryClassGap.subnormal_class_cube_gap_at_original_degree
      pi hpi c hc hsize E q hq e H hH

/-- All higher type-A parameters are paid at the degree required by the
global GM induction. This does not assert the stronger local margin. -/
theorem typeA_closed {S : Type} [Group S] (r : ℕ) (hr : 2≤r)
    (q : CFSG.PrimePower) (e : S ≃* CFSG.Models.A r q) : Profile S := by
  classical
  by_cases hs : SmallFibreKnownModelClassGap.Profile S
  · exact .strong hs
  · have h := SmallFibreClassicalBoundedHeadParameters.typeA_remaining_parameters_of_not_closed
      r hr q e hs
    have hp : r=3 ∧ q.order=2 := by
      simpa only [SmallFibreClassicalBoundedHeadParameters.typeARemainingHeads,
        Finset.mem_singleton,Prod.mk.injEq] using h
    rcases hp with ⟨rfl,hq⟩
    exact .typeARankThreeBinary q hq e

variable {A Ω : Type} [Group A] [MulAction A Ω] [MulAction.IsPretransitive A Ω]
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    {w : Ω} (D : OriginalMinimalBlock (A := A) w)

def HasClosedTop : Prop :=
  ∃ E : NonaffineData (Top (A := A) (X := D.Points)) D.Points, Profile E.Simple

theorem class_cube_gap_of_closed_top
    (hc : Nat.card D.Fibre=2 ∨ Nat.card D.Fibre=3) (htop : HasClosedTop D) :
    Nat.card (ConjClasses A)^3 ≤ 5^(Nat.card Ω-1) := by
  obtain ⟨E,hprofile⟩ := htop
  have h := subnormal_class_cube_gap_at_original_degree D.map D.map_equivariant
    (Nat.card D.Fibre) hc D.fibre_card_at E hprofile ⊤
      (Subgroup.Normal.isSubnormal inferInstance)
  have he := conjugacyClass_card_congr (Subgroup.topEquiv : (⊤ : Subgroup A) ≃* A)
  rwa [he] at h

end SymmetricSubgroupAsymptotics.SmallFibreKnownModelGlobalClassGap
