import Mathlib.GroupTheory.Sylow
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! A finite abelian minimal normal subgroup is either elementary at
the specified prime or has order coprime to that prime. The proof uses
the actual invariant torsion subgroup and Cauchy's theorem. It does not
replace the number of abelian composition factors by the group-order
valuation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped IsMulCommutative
namespace SymmetricSubgroupAsymptotics
variable {A : Type} [Group A] (N : Subgroup A) [N.Normal]
    [IsMulCommutative N] (p : ℕ) [Fact p.Prime]

def normalPrimeTorsion : Subgroup N := (powMonoidHom (α := N) p).ker

omit [Fact p.Prime] in
theorem normalPrimeTorsion_ambient_normal :
    ((normalPrimeTorsion N p).map N.subtype).Normal := by
  constructor
  rintro _ ⟨n,hn,rfl⟩ a
  refine ⟨MulAut.conjNormal a n,?_,rfl⟩
  change (MulAut.conjNormal a n)^p=1
  rw [←map_pow,show n^p=1 from hn,map_one]

theorem abelian_minimal_normal_prime_dichotomy [Finite A]
    (hmin : ∀ K : Subgroup A, K.Normal → K≤N → K=⊥ ∨ K=N) :
    (∀n:N,n^p=1) ∨ Nat.Coprime (Nat.card N) p := by
  let T := normalPrimeTorsion N p
  rcases hmin (T.map N.subtype) (normalPrimeTorsion_ambient_normal N p)
      (Subgroup.map_subtype_le T) with h|h
  · right
    apply Nat.Coprime.symm
    apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    intro hd
    obtain ⟨n,hn⟩ := exists_prime_orderOf_dvd_card' (G := N) p hd
    have hp : n^p=1 := by rw [←hn]; exact pow_orderOf_eq_one n
    have hm : (n:A)∈T.map N.subtype := ⟨n,hp,rfl⟩
    rw [h] at hm
    have he : n=1 := Subtype.ext hm
    rw [he,orderOf_one] at hn
    exact (Fact.out : p.Prime).ne_one hn.symm
  · left
    intro n
    have hm : (n:A)∈T.map N.subtype := by rw [h]; exact n.property
    obtain ⟨x,hx,he⟩ := hm
    have hxn : x=n := Subtype.ext he
    exact hxn ▸ hx

def elementaryAdditiveChart : N≃*Multiplicative (Additive N) where
  toFun n := Multiplicative.ofAdd (Additive.ofMul n)
  invFun n := n.toAdd.toMul
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The elementary alternative supplies an actual additive vector space
and an exact group chart, suitable for the local-chief construction. -/
theorem abelian_minimal_normal_elementary_or_coprime [Finite A]
    (hmin : ∀ K : Subgroup A, K.Normal → K≤N → K=⊥ ∨ K=N) :
    (∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V)
      (_ : FiniteDimensional (ZMod p) V), Nonempty (N≃*Multiplicative V)) ∨
      Nat.Coprime (Nat.card N) p := by
  rcases abelian_minimal_normal_prime_dichotomy N p hmin with hp|hc
  · left
    letI : Module (ZMod p) (Additive N) :=
      AddCommGroup.zmodModule (n := p) (fun x=>by
        apply Additive.toMul.injective
        exact hp x.toMul)
    have hfinite : Module.Finite (ZMod p) (Additive N) := Module.Finite.of_finite
    exact ⟨Additive N,inferInstance,inferInstance,hfinite,⟨elementaryAdditiveChart N⟩⟩
  · exact Or.inr hc

end SymmetricSubgroupAsymptotics
