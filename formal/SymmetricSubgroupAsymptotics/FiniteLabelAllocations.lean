import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Logic.Equiv.Sum
import Mathlib.SetTheory.Cardinal.Finite

/-! Exact allocation of original labelled positions to an already selected
finite type of distinct labels. Prescribed fibre sizes have the multinomial
cardinality g!/prod a_q!. The label type is not ordered or quotiented by its
permutations, so no additional label-factorial occurs.

The proof partitions actual permutations of Fin g. Their fibres are products
of bijections between the actual allocation fibres, including repeated sizes.
There is no physical subgroup count or normalizer premise in these identities.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.FiniteLabelAllocations

section FibreCharts

variable {X Q : Type*}

/-- A permutation respecting two given label maps is exactly a family
of bijections of their literal fibres. Labels of equal size are not swapped. -/
def fibreBijectionsEquiv (f g : X → Q) :
    {e : Equiv.Perm X // ∀ x, g (e x)=f x} ≃
      (∀ q : Q, {x : X // f x=q} ≃ {x : X // g x=q}) where
  toFun e q := e.val.subtypeEquiv (fun x => by rw [e.property x])
  invFun e := ⟨((Equiv.sigmaFiberEquiv f).symm.trans
    (Equiv.sigmaCongrRight e)).trans (Equiv.sigmaFiberEquiv g),fun x => (e (f x) ⟨x,rfl⟩).property⟩
  left_inv e := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    rfl
  right_inv e := by
    funext q
    apply Equiv.ext
    rintro ⟨x,hx⟩
    subst q
    rfl

private def sigmaFirstFibreEquiv (a : Q → ℕ) (q : Q) :
    {x : Σ q, Fin (a q) // x.1=q} ≃ Fin (a q) where
  toFun x := x.property ▸ x.val.2
  invFun j := ⟨⟨q,j⟩,rfl⟩
  left_inv x := by
    rcases x with ⟨⟨q',j⟩,h⟩
    change q'=q at h
    subst q'
    rfl
  right_inv _ := rfl

end FibreCharts

variable {Q : Type*} [Fintype Q] (g : ℕ)

/-- Actual labelled allocations with these exact original fibre sizes. -/
def Allocation (a : Q → ℕ) :=
  {f : Fin g → Q // ∀ q, Fintype.card {x : Fin g // f x=q}=a q}

instance allocationFinite (a : Q → ℕ) : Finite (Allocation g a) :=
  inferInstanceAs (Finite {f : Fin g → Q // ∀ q, Fintype.card {x : Fin g // f x=q}=a q})

theorem allocation_nonempty (a : Q → ℕ) (ha : ∑ q, a q=g) :
    Nonempty (Allocation g a) := by
  have hc : Fintype.card (Σ q, Fin (a q))=Fintype.card (Fin g) := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using ha
  let e : (Σ q, Fin (a q)) ≃ Fin g := Fintype.equivOfCardEq hc
  let f : Fin g → Q := fun x => (e.symm x).1
  refine ⟨⟨f,fun q => ?_⟩⟩
  let ef : {x : Fin g // f x=q} ≃ Fin (a q) :=
    (e.symm.subtypeEquiv (fun _ => Iff.rfl)).trans (sigmaFirstFibreEquiv a q)
  exact (Fintype.card_congr ef).trans (Fintype.card_fin (a q))

theorem allocation_surjective (a : Q → ℕ) (ha : ∀ q, 0<a q)
    (f : Allocation g a) : Function.Surjective f.val := by
  intro q
  have hc : 0<Fintype.card {x : Fin g // f.val x=q} := by rw [f.property q]; exact ha q
  obtain ⟨x⟩ := Fintype.card_pos_iff.mp hc
  exact ⟨x.val,x.property⟩

/-- Permuting the original positions preserves the fibre sizes. -/
def permute (a : Q → ℕ) (f : Allocation g a) (e : Equiv.Perm (Fin g)) : Allocation g a :=
  ⟨fun x => f.val (e x),fun q =>
    (Fintype.card_congr (e.subtypeEquiv (fun _ => Iff.rfl))).trans (f.property q)⟩

private def permutationFibreEquiv (a : Q → ℕ) (f₀ f : Allocation g a) :
    {e : Equiv.Perm (Fin g) // permute g a f₀ e=f} ≃
      (∀ q : Q, {x : Fin g // f.val x=q} ≃ {x : Fin g // f₀.val x=q}) :=
  (Equiv.subtypeEquivRight (fun e => by
    constructor
    · intro he x
      exact congrArg (fun f : Allocation g a => f.val x) he
    · intro he
      apply Subtype.ext
      funext x
      exact he x)).trans (fibreBijectionsEquiv f.val f₀.val)

private theorem permutation_fibre_card (a : Q → ℕ) (f₀ f : Allocation g a) :
    Nat.card {e : Equiv.Perm (Fin g) // permute g a f₀ e=f}=∏ q, (a q).factorial := by
  rw [Nat.card_congr (permutationFibreEquiv g a f₀ f),Nat.card_pi]
  apply Finset.prod_congr rfl
  intro q _
  let e : {x : Fin g // f.val x=q} ≃ {x : Fin g // f₀.val x=q} :=
    Fintype.equivOfCardEq ((f.property q).trans (f₀.property q).symm)
  rw [Nat.card_eq_fintype_card,Fintype.card_equiv e,f.property q]

/-- Each original label permutation occurs in one allocation fibre;
only within-fibre permutations contribute to its multiplicity. -/
theorem allocation_card_mul_factorials (a : Q → ℕ) (ha : ∑ q, a q=g) :
    Nat.card (Allocation g a)*(∏ q, (a q).factorial)=g.factorial := by
  let f₀ : Allocation g a := Classical.choice (allocation_nonempty g a ha)
  have h : Nat.card (Equiv.Perm (Fin g))=
      Nat.card (Allocation g a)*(∏ q, (a q).factorial) := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (permute g a f₀)),Nat.card_sigma]
    simp_rw [permutation_fibre_card]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card,
      Nat.cast_id]
  have hp : Nat.card (Equiv.Perm (Fin g))=g.factorial := by
    rw [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
  exact h.symm.trans hp

theorem allocation_card_multinomial (a : Q → ℕ) (ha : ∑ q, a q=g) :
    Nat.card (Allocation g a)=Nat.multinomial Finset.univ a := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.prod_factorial_pos Finset.univ a)
  calc
    (∏ q, (a q).factorial)*Nat.card (Allocation g a)=g.factorial := by
      rw [mul_comm]
      exact allocation_card_mul_factorials g a ha
    _ = (∏ q, (a q).factorial)*Nat.multinomial Finset.univ a := by
      rw [Nat.multinomial_spec,ha]

/-- The stated allocation coefficient, with no extra factorial of the
already selected distinct-label type. Zero-size labels are also allowed. -/
theorem allocation_card (a : Q → ℕ) (ha : ∑ q, a q=g) :
    Nat.card (Allocation g a)=g.factorial/(∏ q, (a q).factorial) := by
  rw [allocation_card_multinomial g a ha,Nat.multinomial,ha]

/-- A fibre-cardinality weight is constant on the actual allocation
fibre. This permits any later ternary full-subspace weight as its value. -/
theorem weighted_allocation_sum {R : Type*} [CommSemiring R]
    (a : Q → ℕ) (ha : ∑ q, a q=g) (w : Q → ℕ → R) :
    (∑ f : Allocation g a, ∏ q, w q (Fintype.card {x : Fin g // f.val x=q}))=
      (g.factorial/(∏ q, (a q).factorial) : ℕ) • (∏ q, w q (a q)) := by
  have he (f : Allocation g a) :
      (∏ q, w q (Fintype.card {x : Fin g // f.val x=q}))=∏ q, w q (a q) := by
    apply Finset.prod_congr rfl
    intro q _
    rw [f.property q]
  simp_rw [he]
  rw [Finset.sum_const,Finset.card_univ,← Nat.card_eq_fintype_card,
    allocation_card g a ha]

/-- Positive multiplicities for a fixed, already selected label type. The
finite bound records that each literal fibre is a subset of the g positions. -/
def PositiveProfile :=
  {a : Q → Fin (g+1) // (∀ q, 0 < (a q).val) ∧ ∑ q, (a q).val=g}

instance positiveProfileFinite : Finite (PositiveProfile (Q := Q) g) :=
  inferInstanceAs (Finite
    {a : Q → Fin (g+1) // (∀ q, 0 < (a q).val) ∧ ∑ q, (a q).val=g})

/-- All actual surjective maps to the selected labels, before choosing
multiplicities. Neither these maps nor the label type are quotiented. -/
def Surjection := {f : Fin g → Q // Function.Surjective f}

instance surjectionFinite : Finite (Surjection (Q := Q) g) :=
  inferInstanceAs (Finite {f : Fin g → Q // Function.Surjective f})

def surjectionProfile (f : Surjection (Q := Q) g) : PositiveProfile (Q := Q) g := by
  let a : Q → Fin (g+1) := fun q =>
    ⟨Fintype.card {x : Fin g // f.val x=q},Nat.lt_succ_of_le (by
      simpa only [Fintype.card_fin] using
        Fintype.card_subtype_le (fun x : Fin g => f.val x=q))⟩
  refine ⟨a,?_,?_⟩
  · intro q
    obtain ⟨x,hx⟩ := f.property q
    change 0 < Fintype.card {x : Fin g // f.val x=q}
    exact Fintype.card_pos_iff.mpr ⟨⟨x,hx⟩⟩
  · have h := Fintype.card_congr (Equiv.sigmaFiberEquiv f.val)
    simpa only [Fintype.card_sigma,Fintype.card_fin] using h

/-- Exact regrouping by the positive fibre-cardinality profile. In particular,
permuting equal-sized distinct labels still gives a different allocation. -/
def surjectionsEquivProfiles : Surjection (Q := Q) g ≃
    Σ a : PositiveProfile (Q := Q) g, Allocation g (fun q => (a.val q).val) where
  toFun f := ⟨surjectionProfile g f,⟨f.val,fun _ => rfl⟩⟩
  invFun af := ⟨af.2.val,allocation_surjective g _ af.1.property.1 af.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv af := by
    rcases af with ⟨a,f⟩
    have hp : surjectionProfile g
        ⟨f.val,allocation_surjective g _ a.property.1 f⟩=a := by
      apply Subtype.ext
      funext q
      apply Fin.ext
      exact f.property q
    apply Sigma.ext hp
    apply (Subtype.heq_iff_coe_eq (fun u => by
      dsimp only
      rw [hp])).mpr
    rfl

/-- The complete weighted allocation identity for labelled marker positions
and an already selected finite set of distinct characters. Each positive
profile has coefficient g!/prod a_q!; there is no additional label factorial. -/
theorem weighted_surjection_sum {R : Type*} [CommSemiring R] (w : Q → ℕ → R) :
    (∑ f : Surjection (Q := Q) g,
      ∏ q, w q (Fintype.card {x : Fin g // f.val x=q}))=
    ∑ a : PositiveProfile (Q := Q) g,
      (g.factorial/(∏ q, ((a.val q).val).factorial) : ℕ) •
        (∏ q, w q (a.val q).val) := by
  rw [Fintype.sum_equiv (surjectionsEquivProfiles (Q := Q) g)
    (fun f => ∏ q, w q (Fintype.card {x : Fin g // f.val x=q}))
    (fun af => ∏ q, w q (Fintype.card {x : Fin g // af.2.val x=q}))
    (fun _ => rfl),Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro a _
  exact weighted_allocation_sum g _ a.property.2 w

end SymmetricSubgroupAsymptotics.FiniteLabelAllocations
