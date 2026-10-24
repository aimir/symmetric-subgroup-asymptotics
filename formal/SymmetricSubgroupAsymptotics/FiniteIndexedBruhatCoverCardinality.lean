import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! An indexed four-factor cover with its actual residual subgroups.
The right factor is charged by cosets of a subgroup whose conjugate
can be absorbed into the left factor. Residual containment suffices;
no exact intersection formula or unique Bruhat coordinates are required. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.FiniteIndexedBruhatCoverCardinality

variable {G I : Type*} [Group G] [Finite G] [Fintype I]

theorem card_le_of_indexed_cover
    (U D : Subgroup G) (w : I → G) (R : I → Subgroup U) (c : I → ℕ)
    (hcover : ∀ g : G, ∃ (u : U) (d : D) (i : I) (v : U),
      g=u.val*d.val*w i*v.val)
    (hD : ∀ (d : D) (u : U), d.val*u.val*d.val⁻¹ ∈ U)
    (hR : ∀ (i : I) (r : R i), w i*r.val.val*(w i)⁻¹ ∈ U)
    (hindex : ∀ i, (R i).index ≤ c i) :
    Nat.card G ≤ Nat.card U * Nat.card D * ∑ i, c i := by
  let Q : I → Type _ := fun i => Quotient (QuotientGroup.rightRel (R i))
  let encode : (Σ i, U × D × Q i) → G := fun p =>
    p.2.1.val*p.2.2.1.val*w p.1*(Quotient.out p.2.2.2).val
  have hs : Function.Surjective encode := by
    intro g
    obtain ⟨u,d,i,v,he⟩ := hcover g
    let q : Q i := Quotient.mk _ v
    let t : U := Quotient.out q
    have hmem : v*t⁻¹ ∈ R i :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact' (Quotient.out_eq' q))
    let r : R i := ⟨v*t⁻¹,hmem⟩
    let a : U := ⟨w i*r.val.val*(w i)⁻¹,hR i r⟩
    let u' : U := ⟨u.val*(d.val*a.val*d.val⁻¹),U.mul_mem u.property (hD d a)⟩
    refine ⟨⟨i,u',d,q⟩,?_⟩
    change u'.val*d.val*w i*t.val=g
    rw [he]
    dsimp only [u',a,r]
    change u.val*(d.val*(w i*(v.val*t.val⁻¹)*(w i)⁻¹)*d.val⁻¹)*d.val*w i*t.val = _
    group
  have hQ (i : I) : Nat.card (Q i) = (R i).index :=
    (Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel (R i))).trans
      (R i).index_eq_card.symm
  have hb := Nat.card_le_card_of_surjective encode hs
  calc
    Nat.card G ≤ ∑ i, Nat.card U*Nat.card D*(R i).index := by
      simpa only [Nat.card_sigma,Nat.card_prod,hQ,Nat.mul_assoc] using hb
    _ ≤ ∑ i, Nat.card U*Nat.card D*c i :=
      Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (hindex i)
    _ = Nat.card U*Nat.card D*∑ i, c i := (Finset.mul_sum _ _ _).symm

theorem card_le_of_residual_card_factors
    (U D : Subgroup G) (w : I → G) (R : I → Subgroup U) (c : I → ℕ)
    (hcover : ∀ g : G, ∃ (u : U) (d : D) (i : I) (v : U),
      g=u.val*d.val*w i*v.val)
    (hD : ∀ (d : D) (u : U), d.val*u.val*d.val⁻¹ ∈ U)
    (hR : ∀ (i : I) (r : R i), w i*r.val.val*(w i)⁻¹ ∈ U)
    (hcard : ∀ i, Nat.card U = Nat.card (R i)*c i) :
    Nat.card G ≤ Nat.card U * Nat.card D * ∑ i, c i := by
  apply card_le_of_indexed_cover U D w R c hcover hD hR
  intro i
  have he : Nat.card (R i)*(R i).index = Nat.card (R i)*c i :=
    (R i).card_mul_index.trans (hcard i)
  exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos he).le

end SymmetricSubgroupAsymptotics.FiniteIndexedBruhatCoverCardinality
