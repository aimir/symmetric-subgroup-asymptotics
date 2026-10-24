import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Sum

/-! A finite quotient whose fibres are the orbits of an actual
involution has the usual two-sheet counting formula. The proof builds
an explicit bijection between two copies of the quotient and the
disjoint union of the source with its fixed points; no action-orbit
cardinality formula is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteInvolutionQuotientCardinality
variable {X Y : Type*} [Finite X] [Finite Y]

theorem twice_card_eq (f : X → Y) (hf : Function.Surjective f)
    (s : X → X) (hs : Function.Involutive s) (hmap : ∀ x, f (s x)=f x)
    (hfibre : ∀ x x', f x=f x' → x=x' ∨ x=s x') :
    2*Nat.card Y=Nat.card X+Nat.card {x : X // s x=x} := by
  classical
  let r : Y → X := fun y => Classical.choose (hf y)
  have hr (y : Y) : f (r y)=y := Classical.choose_spec (hf y)
  let code : Y × Bool → X ⊕ {x : X // s x=x} := fun p =>
    match p.2 with
    | false => Sum.inl (r p.1)
    | true => if h : s (r p.1)=r p.1 then Sum.inr ⟨r p.1,h⟩ else Sum.inl (s (r p.1))
  let recover : X ⊕ {x : X // s x=x} → Y := fun u =>
    match u with
    | Sum.inl x => f x
    | Sum.inr x => f x.val
  have hrec (p : Y × Bool) : recover (code p)=p.1 := by
    rcases p with ⟨y,b⟩
    cases b
    · exact hr y
    · by_cases h : s (r y)=r y
      · simpa only [code, dif_pos h] using hr y
      · simpa only [code, dif_neg h] using (hmap (r y)).trans (hr y)
  have hinj : Function.Injective code := by
    rintro ⟨y,b⟩ ⟨y',b'⟩ he
    have hy : y=y' := (hrec (y,b)).symm.trans
      ((congrArg recover he).trans (hrec (y',b')))
    subst y'
    apply congrArg (fun t : Bool => (y,t))
    cases b <;> cases b'
    · rfl
    · by_cases h : s (r y)=r y
      · simp only [code, dif_pos h, Sum.inl_ne_inr] at he
      · have hh : r y=s (r y) := Sum.inl.inj (by simpa only [code, dif_neg h] using he)
        exact False.elim (h hh.symm)
    · by_cases h : s (r y)=r y
      · simp only [code, dif_pos h, Sum.inr_ne_inl] at he
      · have hh : s (r y)=r y := Sum.inl.inj (by simpa only [code, dif_neg h] using he)
        exact False.elim (h hh)
    · rfl
  have hsurj : Function.Surjective code := by
    intro u
    cases u with
    | inl x =>
      rcases hfibre x (r (f x)) (hr (f x)).symm with h | h
      · refine ⟨(f x,false),?_⟩
        exact congrArg Sum.inl h.symm
      · by_cases ht : s (r (f x))=r (f x)
        · refine ⟨(f x,false),?_⟩
          exact congrArg Sum.inl (h.trans ht).symm
        · refine ⟨(f x,true),?_⟩
          simpa only [code, dif_neg ht] using congrArg Sum.inl h.symm
    | inr x =>
      have hx : r (f x.val)=x.val := by
        rcases hfibre x.val (r (f x.val)) (hr (f x.val)).symm with h | h
        · exact h.symm
        · have hh := congrArg s h
          rw [hs, x.property] at hh
          exact hh.symm
      have ht : s (r (f x.val))=r (f x.val) := by rw [hx]; exact x.property
      refine ⟨(f x.val,true),?_⟩
      simp only [code, dif_pos ht]
      congr 1
      exact Subtype.ext hx
  have hc := Nat.card_congr (Equiv.ofBijective code ⟨hinj,hsurj⟩)
  have hb : Nat.card Bool=2 := by simp only [Nat.card_eq_fintype_card, Fintype.card_bool]
  simpa only [Nat.card_prod, Nat.card_sum, hb, Nat.mul_comm] using hc

end SymmetricSubgroupAsymptotics.FiniteInvolutionQuotientCardinality
