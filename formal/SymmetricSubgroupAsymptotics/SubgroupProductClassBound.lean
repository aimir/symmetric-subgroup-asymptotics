import SymmetricSubgroupAsymptotics.ConjugacyClassExtension
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.BigOperators.Fin

/-! Class bounds for correlated subgroups of finite products.
The hypothesis bounds every actual subgroup of each coordinate. The proof
filters the original source by coordinate kernels and uses the actual image
at each step. It does not use monotonicity of class count under inclusion,
and it does not replace a correlated subgroup by a full product.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

universe u v w

/-- Bounds for every actual coordinate subgroup control any finite original
group whose coordinate homomorphisms jointly separate its elements. -/
theorem conjugacyClass_card_le_coordinate_bounds (n : ℕ)
    (V : Fin n → Type u) [∀ i, Group (V i)] [∀ i, Finite (V i)]
    (c : Fin n → ℕ)
    (hc : ∀ i (L : Subgroup (V i)), Nat.card (ConjClasses L) ≤ c i)
    (H : Type w) [Group H] [Finite H]
    (f : ∀ i, H →* V i)
    (hf : Function.Injective (fun h i => f i h)) :
    Nat.card (ConjClasses H) ≤ ∏ i, c i := by
  induction n generalizing H with
  | zero =>
    letI : Subsingleton H :=
      ⟨fun x y => hf (funext (fun i => Fin.elim0 i))⟩
    have h := Nat.card_le_card_of_surjective
      (@ConjClasses.mk H _) ConjClasses.mk_surjective
    simpa only [Nat.card_unique, Fin.prod_univ_zero] using h
  | succ n ih =>
    let K := (f 0).ker
    let tail : ∀ i : Fin n, K →* V i.succ :=
      fun i => (f i.succ).comp K.subtype
    have htail : Function.Injective (fun x i => tail i x) := by
      intro x y h
      apply Subtype.ext
      apply hf
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · have hx : f 0 (x : H) = 1 := x.property
        have hy : f 0 (y : H) = 1 := y.property
        exact hx.trans hy.symm
      · exact congrFun h j
    have hrec := ih (fun i : Fin n => V i.succ) (fun i => c i.succ)
      (fun i => hc i.succ) K tail htail
    let e : H ⧸ K ≃* (f 0).range := QuotientGroup.quotientKerEquivRange (f 0)
    have hquot : Nat.card (ConjClasses (H ⧸ K)) ≤
        Nat.card (ConjClasses (f 0).range) :=
      Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
        (ConjClasses.map_surjective e.symm.surjective)
    have hfirst := hquot.trans (hc 0 (f 0).range)
    have hsplit := conjugacyClass_card_le_normal_mul_quotient K
    rw [Fin.prod_univ_succ]
    exact hsplit.trans ((Nat.mul_le_mul hrec hfirst).trans_eq (Nat.mul_comm _ _))

/-- The same actual-coordinate argument for an arbitrary finite index type. -/
theorem conjugacyClass_card_le_finite_coordinate_bounds
    {ι : Type v} [Fintype ι]
    (V : ι → Type u) [∀ i, Group (V i)] [∀ i, Finite (V i)]
    (c : ι → ℕ)
    (hc : ∀ i (L : Subgroup (V i)), Nat.card (ConjClasses L) ≤ c i)
    (H : Type w) [Group H] [Finite H]
    (f : ∀ i, H →* V i)
    (hf : Function.Injective (fun h i => f i h)) :
    Nat.card (ConjClasses H) ≤ ∏ i, c i := by
  let e := (Fintype.equivFin ι).symm
  have hi : Function.Injective (fun h j => f (e j) h) := by
    intro x y h
    apply hf
    funext i
    obtain ⟨j, rfl⟩ := e.surjective i
    exact congrFun h j
  have h := conjugacyClass_card_le_coordinate_bounds (Fintype.card ι)
    (fun j => V (e j)) (fun j => c (e j)) (fun j => hc (e j))
    H (fun j => f (e j)) hi
  simpa only [e.prod_comp] using h

/-- A literal subgroup of a finite product satisfies the product bound,
including arbitrary correlations between its original coordinates. -/
theorem subgroupProduct_conjugacyClass_card_le
    {ι : Type v} [Fintype ι]
    (V : ι → Type u) [∀ i, Group (V i)] [∀ i, Finite (V i)]
    (H : Subgroup (∀ i, V i)) (c : ι → ℕ)
    (hc : ∀ i (L : Subgroup (V i)), Nat.card (ConjClasses L) ≤ c i) :
    Nat.card (ConjClasses H) ≤ ∏ i, c i := by
  let f : ∀ i, H →* V i :=
    fun i => (Pi.evalMonoidHom V i).comp H.subtype
  apply conjugacyClass_card_le_finite_coordinate_bounds V c hc H f
  intro x y h
  apply Subtype.ext
  exact h

/-- The homogeneous bound needed for a block kernel embedded in `n` copies
of the permutations of one block. No independence of the copies is assumed. -/
theorem subgroupPower_conjugacyClass_card_le
    (G : Type u) [Group G] [Finite G] (n c : ℕ)
    (hc : ∀ L : Subgroup G, Nat.card (ConjClasses L) ≤ c)
    (H : Subgroup (Fin n → G)) : Nat.card (ConjClasses H) ≤ c ^ n := by
  simpa using subgroupProduct_conjugacyClass_card_le
    (fun _ : Fin n => G) H (fun _ => c) (fun _ => hc)

end SymmetricSubgroupAsymptotics

end
