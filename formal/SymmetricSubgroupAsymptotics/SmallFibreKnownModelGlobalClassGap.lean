import SymmetricSubgroupAsymptotics.SmallFibreClassicalBoundedHeadParameters
import SymmetricSubgroupAsymptotics.SmallFibreTypeARankThreeBinaryOrdinaryClassGap
import SymmetricSubgroupAsymptotics.CFSGPSLTwoEightClassGap
import SymmetricSubgroupAsymptotics.CFSGPSLTwoNineOrdinaryClassGap
import SymmetricSubgroupAsymptotics.SmallFibrePSLTwoAlternatingFiveOrdinaryClassGap
import SymmetricSubgroupAsymptotics.OriginalNaturalSymmetricTopOrdinaryClassBound
import SymmetricSubgroupAsymptotics.SmallFibreAlternatingSixOrdinaryClassGap
import SymmetricSubgroupAsymptotics.SmallFibreAlternatingOrdinaryClassGap
import SymmetricSubgroupAsymptotics.SmallFibreReeFFourFieldEightBinaryResidual
import SymmetricSubgroupAsymptotics.OriginalMinimalBlockSupportedAffineTopClassBound

/-! The original global class-count induction needs the exponent
`card Ω - 1`. Keep the stronger local `card Ω - 2` API intact, and
install the actual rank-three binary model using precisely the global
margin. The rank-three ternary eight-block case and the remaining
small rank-one fields therefore need no extra stronger local estimate.
All original kernels, subnormal sources and degree forms are retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallFibreKnownModelGlobalClassGap
open PrimitiveSocleRawStructure OriginalBlockClassBound

inductive Profile (S : Type) [Group S] : Prop
  | strong (h : SmallFibreKnownModelClassGap.Profile S) : Profile S
  | typeARankThreeBinary (q : CFSG.PrimePower) (hq : q.order=2)
      (e : S ≃* CFSG.Models.A 3 q) : Profile S
  | pslTwoEight (q : CFSG.PrimePower) (hq : q.order=8)
      (e : S ≃* CFSG.Models.A 1 q) : Profile S
  | pslTwoNine (q : CFSG.PrimePower) (hq : q.order=9)
      (e : S ≃* CFSG.Models.A 1 q) : Profile S
  | pslTwoAlternatingFive (q : CFSG.PrimePower) (hq : q.order=4 ∨ q.order=5)
      (e : S ≃* CFSG.Models.A 1 q) : Profile S
  | alternatingFive (e : S ≃* alternatingGroup (Fin 5)) : Profile S
  | alternating (m : ℕ) (hm : 5 ≤ m)
      (e : S ≃* alternatingGroup (Fin m)) : Profile S

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
  | pslTwoEight q hq e =>
    exact CFSGPSLTwoEightClassGap.subnormal_ordinary_class_cube_gap
      pi hpi c hc hsize E q hq e H hH
  | pslTwoNine q hq e =>
    exact CFSGPSLTwoNineOrdinaryClassGap.subnormal_ordinary_class_cube_gap
      pi hpi c hc hsize E q hq e H hH
  | pslTwoAlternatingFive q hq e =>
    exact SmallFibrePSLTwoAlternatingFiveOrdinaryClassGap.subnormal_class_cube_le_of_typeA_rank_one_order_four_or_five
      pi hpi c hc hsize E q hq e H hH
  | alternatingFive e =>
    exact SmallFibreAlternatingFiveOrdinaryClassGap.subnormal_class_cube_le_at_original_degree
      pi hpi c hc hsize E e H hH
  | alternating m hm e =>
    by_cases h5 : m=5
    · subst m
      exact SmallFibreAlternatingFiveOrdinaryClassGap.subnormal_class_cube_le_at_original_degree
        pi hpi c hc hsize E e H hH
    by_cases h6 : m=6
    · subst m
      exact SmallFibreAlternatingSixOrdinaryClassGap.subnormal_ordinary_class_cube_gap
        pi hpi c hc hsize E e H hH
    exact SmallFibreAlternatingOrdinaryClassGap.subnormal_class_cube_le_at_original_degree
      pi hpi c hc hsize E m (by omega) e H hH

/-- Every alternating model is paid on the original action, including
the nonnatural short-index degrees. No subgroup-index classification
or action-catalogue premise is retained. -/
theorem alternating_closed {S : Type} [Group S] (m : ℕ) (hm : 5 ≤ m)
    (e : S ≃* alternatingGroup (Fin m)) : Profile S :=
  .alternating m hm e

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

/-- The entire admissible rank-one family is paid at the original GM degree. -/
theorem pslTwo_closed {S : Type} [Group S]
    (q : CFSG.PrimePower) (hq : 4≤q.order) (e : S ≃* CFSG.Models.A 1 q) : Profile S := by
  classical
  by_cases hs : SmallFibreKnownModelClassGap.Profile S
  · exact .strong hs
  · have ht := SmallFibreClassicalBoundedHeadParameters.pslTwo_remaining_parameters_of_not_closed
      q hq e hs
    simp only [SmallFibreClassicalBoundedHeadParameters.pslTwoRemainingOrders,
      Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with h4 | h5 | h8 | h9
    · exact .pslTwoAlternatingFive q (Or.inl h4) e
    · exact .pslTwoAlternatingFive q (Or.inr h5) e
    · exact .pslTwoEight q h8 e
    · exact .pslTwoNine q h9 e

def pslTwoRemainingOrders : Finset ℕ := ∅

theorem pslTwoRemainingOrders_card : pslTwoRemainingOrders.card=0 := by decide +kernel

theorem pslTwo_remaining_parameters_of_not_closed {S : Type} [Group S]
    (q : CFSG.PrimePower) (hq : 4≤q.order) (e : S ≃* CFSG.Models.A 1 q)
    (h : ¬Profile S) : q.order∈pslTwoRemainingOrders := by
  exact (h (pslTwo_closed q hq e)).elim

variable {A Ω : Type} [Group A] [MulAction A Ω] [MulAction.IsPretransitive A Ω]
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    {w : Ω} (D : OriginalMinimalBlock (A := A) w)

def HasClosedTop : Prop :=
  (∃ E : NonaffineData (Top (A := A) (X := D.Points)) D.Points, Profile E.Simple) ∨
    (5≤Nat.card D.Points ∧ (Top (A := A) (X := D.Points)).IsSubnormal) ∨
    (∃ E : NonaffineData (Top (A := A) (X := D.Points)) D.Points,
      Nonempty (E.Simple ≃* CFSG.Models.ReeF4 1) ∧
        ¬ SmallFibreReeFFourFieldEightBinaryResidual.BinarySingleIndex E (Nat.card D.Fibre)) ∨
    D.HasSupportedAffineTop

theorem affine_top_remaining_degree_of_not_closed
    (h : ¬HasClosedTop D) (P : PrimitiveAffineProfile D.Top D.Points) :
    Nat.card D.Points≤127 := by
  by_contra hn
  exact h (Or.inr (Or.inr (Or.inr ⟨P,Or.inl (by omega)⟩)))

theorem class_cube_gap_of_closed_top
    (hc : Nat.card D.Fibre=2 ∨ Nat.card D.Fibre=3) (htop : HasClosedTop D) :
    Nat.card (ConjClasses A)^3 ≤ 5^(Nat.card Ω-1) := by
  have h : Nat.card (ConjClasses (⊤ : Subgroup A))^3≤5^(Nat.card Ω-1) := by
    rcases htop with ⟨E,hprofile⟩ | ⟨hn,hTop⟩ | ⟨E,⟨e⟩,hnot⟩ | haffine
    · exact subnormal_class_cube_gap_at_original_degree D.map D.map_equivariant
        (Nat.card D.Fibre) hc D.fibre_card_at E hprofile ⊤
          (Subgroup.Normal.isSubnormal inferInstance)
    · exact OriginalNaturalSymmetricTopOrdinaryClassBound.subnormal_class_cube_le_at_original_degree
        D.map D.map_equivariant D.base (Nat.card D.Fibre) hc (D.fibre_card_at D.base)
        hn hTop ⊤ (Subgroup.Normal.isSubnormal inferInstance)
    · rcases SmallFibreReeFFourFieldEightBinaryResidual.subnormal_ordinary_gap_or_binary_single_index
        D.map D.map_equivariant (Nat.card D.Fibre) hc D.fibre_card_at E e ⊤
          (Subgroup.Normal.isSubnormal inferInstance) with hgap|hindex
      · exact hgap
      · exact (hnot hindex).elim
    · exact D.subnormal_class_cube_le_of_supported_affine_top hc haffine ⊤
        (Subgroup.Normal.isSubnormal inferInstance)
  have he := conjugacyClass_card_congr (Subgroup.topEquiv : (⊤ : Subgroup A) ≃* A)
  rwa [he] at h

end SymmetricSubgroupAsymptotics.SmallFibreKnownModelGlobalClassGap
