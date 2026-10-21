import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Tactic.Ring

/-! Exact cardinality from an actual rank-one two-cell decomposition.
No group order is assumed: the original B and B*w*U cells are disjoint,
and the latter has unique original B-times-U coordinates. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGRankOneTwoCellCardinality

variable {G : Type*} [Group G] (B U : Subgroup G) (w : G)

def cellMap : B ⊕ (B×U) → G
  | .inl b => b.val
  | .inr bu => bu.1.val*w*bu.2.val

theorem small_ne_large (hUB : U≤B) (hw : w∉B) (b c : B) (u : U) :
    (b : G)≠(c : G)*w*(u : G) := by
  intro he
  have hm : (c : G)*w*(u : G)∈B := he ▸ b.property
  have hc := B.mul_mem (B.mul_mem (B.inv_mem c.property) hm)
    (B.inv_mem (hUB u.property))
  exact hw (by simpa [mul_assoc] using hc)

theorem large_injective
    (hcap : B ⊓ U.map (MulAut.conj w).toMonoidHom=⊥) :
    Function.Injective (fun bu : B×U => bu.1.val*w*bu.2.val) := by
  rintro ⟨b,u⟩ ⟨c,v⟩ he
  have hconj : w*((u : G)*(v : G)⁻¹)*w⁻¹=(b : G)⁻¹*(c : G) := by
    have h := congrArg (fun z : G => (b : G)⁻¹*z*(v : G)⁻¹*w⁻¹) he
    simpa [mul_assoc] using h
  have hmem : w*((u : G)*(v : G)⁻¹)*w⁻¹∈
      B ⊓ U.map (MulAut.conj w).toMonoidHom := by
    refine ⟨?_,?_⟩
    · rw [hconj]
      exact B.mul_mem (B.inv_mem b.property) c.property
    · exact ⟨(u : G)*(v : G)⁻¹,U.mul_mem u.property (U.inv_mem v.property),rfl⟩
  rw [hcap] at hmem
  have h1 : w*((u : G)*(v : G)⁻¹)*w⁻¹=1 := hmem
  have huv : (u : G)*(v : G)⁻¹=1 := by
    have h := congrArg (fun z : G => w⁻¹*z*w) h1
    simpa [mul_assoc] using h
  have huv' : u=v := Subtype.ext (mul_inv_eq_one.mp huv)
  subst v
  exact Prod.ext (Subtype.ext (mul_right_cancel (mul_right_cancel he))) rfl

theorem cellMap_injective (hUB : U≤B) (hw : w∉B)
    (hcap : B ⊓ U.map (MulAut.conj w).toMonoidHom=⊥) :
    Function.Injective (cellMap B U w) := by
  rintro (b | ⟨b,u⟩) (c | ⟨c,v⟩) he
  · exact congrArg Sum.inl (Subtype.ext he)
  · exact False.elim (small_ne_large B U w hUB hw b c v he)
  · exact False.elim (small_ne_large B U w hUB hw c b u he.symm)
  · exact congrArg Sum.inr (large_injective B U w hcap he)

theorem cellMap_surjective
    (hcover : ∀ g : G,g∈B ∨ ∃ (b : B) (u : U),g=b.val*w*u.val) :
    Function.Surjective (cellMap B U w) := by
  intro g
  rcases hcover g with hg | ⟨b,u,he⟩
  · exact ⟨.inl ⟨g,hg⟩,rfl⟩
  · exact ⟨.inr (b,u),he.symm⟩

theorem card_eq [Finite G] (hUB : U≤B) (hw : w∉B)
    (hcap : B ⊓ U.map (MulAut.conj w).toMonoidHom=⊥)
    (hcover : ∀ g : G,g∈B ∨ ∃ (b : B) (u : U),g=b.val*w*u.val) :
    Nat.card G=Nat.card B*(1+Nat.card U) := by
  let e : B ⊕ (B×U) ≃ G := Equiv.ofBijective (cellMap B U w)
    ⟨cellMap_injective B U w hUB hw hcap,cellMap_surjective B U w hcover⟩
  calc
    Nat.card G=Nat.card (B ⊕ (B×U)) := Nat.card_congr e.symm
    _ = Nat.card B+Nat.card B*Nat.card U := by rw [Nat.card_sum,Nat.card_prod]
    _ = Nat.card B*(1+Nat.card U) := by ring

end SymmetricSubgroupAsymptotics.CFSGRankOneTwoCellCardinality
