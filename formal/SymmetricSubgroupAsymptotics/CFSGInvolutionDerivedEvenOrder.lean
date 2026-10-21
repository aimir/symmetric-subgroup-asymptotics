import SymmetricSubgroupAsymptotics.CFSGInvolutionOrder
import SymmetricSubgroupAsymptotics.ConnectedInvolutionDerivedGeneration

/-! A common even-order argument for quotients of derived Coxeter groups.
If all involutions have the same abelianization image, and the graph of
involutory pair-products is connected, every odd-order quotient of the
actual derived subgroup is trivial. This retains the literal quotient
map, rather than transferring parity through a possibly even kernel. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGReduction
open CFSGGeneration

def derivedInvolutionProduct {G : Type*} [Group G] {ι : Type*}
    (g : ι → G) (base : ι) (hsq : ∀ i, g i * g i = 1)
    (hsame : ∀ i, Abelianization.of (g i) = Abelianization.of (g base))
    (i j : ι) : commutator G := by
  refine ⟨g i * g j, ?_⟩
  rw [← Abelianization.ker_of G]
  change Abelianization.of (g i * g j) = 1
  rw [map_mul, hsame i, hsame j, ← map_mul, hsq base, map_one]

theorem even_card_of_derived_involution_quotient
    {G H : Type*} [Group G] [Group H] {ι : Type*}
    (g : ι → G) (base : ι)
    (hgen : Subgroup.closure (Set.range g) = ⊤)
    (hsq : ∀ i, g i * g i = 1)
    (hsame : ∀ i, Abelianization.of (g i) = Abelianization.of (g base))
    (R : ι → ι → Prop) (hedge : ∀ i j, R i j → (g i * g j) ^ 2 = 1)
    (hconn : ∀ i, Relation.ReflTransGen R base i)
    (q : commutator G →* H) (hq : Function.Surjective q)
    (hn : ¬ IsMulCommutative H) : Even (Nat.card H) := by
  by_contra heven
  have hodd : Odd (Nat.card H) := Nat.not_even_iff_odd.mp heven
  let p : ι → ι → commutator G := derivedInvolutionProduct g base hsq hsame
  have hpval (i j : ι) : (p i j).val = g i * g j := rfl
  have hstep (i j : ι) (hij : R i j) : q (p base i) = q (p base j) := by
    have hs : (p i j) ^ 2 = 1 := by
      apply Subtype.ext
      exact hedge i j hij
    have hqij : q (p i j) = 1 :=
      eq_one_of_square_eq_one_of_odd_card hodd _ (by rw [← map_pow, hs, map_one])
    have hmul : p base i * p i j = p base j := by
      apply Subtype.ext
      change (g base * g i) * (g i * g j) = g base * g j
      calc
        _ = g base * (g i * g i) * g j := by group
        _ = _ := by rw [hsq i, mul_one]
    have hh := congrArg q hmul
    simpa only [map_mul, hqij, mul_one] using hh
  have hpath : ∀ {i j}, Relation.ReflTransGen R i j → q (p base i) = q (p base j) := by
    intro i j h
    induction h with
    | refl => rfl
    | tail _ hlast ih => exact ih.trans (hstep _ _ hlast)
  have hpone (i : ι) : q (p base i) = 1 := by
    have hbase : p base base = 1 := Subtype.ext (hsq base)
    rw [← hpath (hconn i), hbase, map_one]
  have hall : ∀ x : commutator G, q x = 1 := by
    let K : Subgroup G := q.ker.map (commutator G).subtype
    have hK : commutator G ≤ K := by
      rw [commutator_eq_involution_even_products g base hgen hsq hsame]
      apply (Subgroup.closure_le K).mpr
      rintro _ ⟨i, rfl⟩
      exact ⟨p base i.val, hpone i.val, rfl⟩
    intro x
    obtain ⟨y, hy, hxy⟩ := hK x.property
    have hEq : y = x := Subtype.ext hxy
    exact hEq ▸ hy
  have hone (h : H) : h = 1 := by
    obtain ⟨x, rfl⟩ := hq h
    exact hall x
  haveI : Subsingleton H := ⟨fun a b => (hone a).trans (hone b).symm⟩
  exact hn inferInstance

end SymmetricSubgroupAsymptotics.CFSGReduction
