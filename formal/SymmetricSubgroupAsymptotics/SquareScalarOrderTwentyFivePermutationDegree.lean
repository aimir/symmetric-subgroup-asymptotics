import SymmetricSubgroupAsymptotics.CFSGSquareScalarPermutationDegree
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.GroupAction.FixedPoints

/-! A genuine additive action of a field of order25 with square-scalar
invariant fixed counts and no nonzero kernel needs at least15 points.
The same actual fixed counts enter Burnside and the modulo-five bound;
no line-orbit catalogue, source group order or minimum-index theorem is
used. The diagonal square torus has at most two multiplicative cosets. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.SquareScalarOrderTwentyFivePermutationDegree
open MulAction
private theorem weighted_coset_sum {A : Type*} [Group A] [Fintype A]
    (H : Subgroup A) (f : A→ℕ) (hinv : ∀ (a : A) (h : H), f (a*h)=f a) :
    H.index*(∑ a : A, f a)=Fintype.card A*∑ q : A ⧸ H, f q.out := by
  have hcos : (∑ a : A, f a)=Fintype.card H*∑ q : A ⧸ H, f q.out :=
    CFSGUniformCosetSum.sum_eq_card_subgroup_mul_sum_quotient H f hinv
  have hcard : H.index*Fintype.card H=Fintype.card A := by
    have hh := H.card_mul_index
    rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card] at hh
    rw [Nat.mul_comm] at hh
    exact hh
  calc
    _=H.index*(Fintype.card H*∑ q : A ⧸ H, f q.out) :=
      congrArg (fun n : ℕ => H.index*n) hcos
    _=(H.index*Fintype.card H)*∑ q : A ⧸ H, f q.out := (Nat.mul_assoc _ _ _).symm
    _=_ := by rw [hcard]

private theorem degree_ge_fifteen_of_fixedBy_cosets {P A X : Type*}
    [Group P] [Group A] [Fintype P] [Fintype A] [Fintype X] [MulAction P X]
    (H : Subgroup A) (f : A→ℕ)
    (hinv : ∀ (a : A) (h : H), f (a*h)=f a)
    (hfix : ∀ a : A, f a<Fintype.card X)
    (hlow : ∀ a : A, Fintype.card X%5≤f a)
    (hk : H.index≤2) (hP : Fintype.card P=25) (hA : Fintype.card A=24)
    (hsum : (∑ a ∈ (Finset.univ : Finset P).erase 1,
      Fintype.card (fixedBy X a))=∑ a : A, f a) : 15≤Fintype.card X := by
  by_contra hsmall
  have hn : Fintype.card X<15 := Nat.lt_of_not_ge hsmall
  let S : ℕ := ∑ q : A ⧸ H, f q.out
  have hS : S<H.index*Fintype.card X := by
    have hh := Finset.sum_lt_sum_of_nonempty
      (Finset.univ_nonempty : (Finset.univ : Finset (A ⧸ H)).Nonempty)
      (fun q _ => hfix q.out)
    simpa only [S,Finset.sum_const,Finset.card_univ,smul_eq_mul,
      ←Nat.card_eq_fintype_card] using hh
  have hquotcard : Fintype.card (A ⧸ H)=H.index := by
    rw [←Nat.card_eq_fintype_card,←H.index_eq_card]
  have hSlo : H.index*(Fintype.card X%5)≤S := by
    have hh := Finset.sum_le_sum (fun (q : A ⧸ H) (_ : q∈Finset.univ) => hlow q.out)
    simpa only [S,Finset.sum_const,Finset.card_univ,smul_eq_mul,hquotcard] using hh
  have hav : H.index*(∑ a ∈ (Finset.univ : Finset P).erase 1,
      Fintype.card (fixedBy X a))=24*S := by
    rw [hsum]
    have hh := weighted_coset_sum H f hinv
    rw [hA] at hh
    exact hh
  have hone : Fintype.card (fixedBy X (1 : P))=Fintype.card X :=
    Fintype.card_congr
      { toFun := Subtype.val
        invFun := fun x => ⟨x,one_smul P x⟩
        left_inv := fun _ => Subtype.ext rfl
        right_inv := fun _ => rfl }
  have hburn := sum_card_fixedBy_eq_card_orbits_mul_card_group P X
  rw [←Finset.add_sum_erase _ _ (Finset.mem_univ (1 : P)),hone] at hburn
  have hw : H.index*Fintype.card X+24*S=
      25*(H.index*Fintype.card (Quotient (orbitRel P X))) := by
    calc
      _=H.index*(Fintype.card X+∑ a ∈ (Finset.univ : Finset P).erase 1,
          Fintype.card (fixedBy X a)) := by rw [Nat.mul_add,hav]
      _=H.index*(Fintype.card (Quotient (orbitRel P X))*25) := by rw [hburn,hP]
      _=_ := by ring
  have hdecomp : (H.index*Fintype.card X-S)+25*S=H.index*Fintype.card X+24*S := by
    calc
      _=(H.index*Fintype.card X-S+S)+24*S := by ring
      _=_ := by rw [Nat.sub_add_cancel hS.le]
  have hd : 25∣(H.index*Fintype.card X-S)+25*S := by
    rw [hdecomp,hw]
    exact dvd_mul_right _ _
  have hdiv : 25∣H.index*Fintype.card X-S := by
    have hh := Nat.dvd_sub hd (dvd_mul_right 25 S)
    simpa only [Nat.add_sub_cancel] using hh
  have h25 : 25≤H.index*Fintype.card X-S := Nat.le_of_dvd (by omega) hdiv
  have hdiff : Fintype.card X-Fintype.card X%5≤10 := by omega
  have hbound : H.index*Fintype.card X-S≤H.index*(Fintype.card X-Fintype.card X%5) := by
    rw [Nat.mul_sub_left_distrib]
    exact Nat.sub_le_sub_left hSlo _
  have h20 : H.index*Fintype.card X-S≤20 := hbound.trans (Nat.mul_le_mul hk hdiff)
  omega

variable {F X : Type*} [Field F] [Fintype F] [Fintype X]
    [MulAction (Multiplicative F) X]

omit [Fintype F] in
private theorem fixed_remainder_le (hF : Nat.card F=25) (g : Multiplicative F) :
    Fintype.card X%5≤Fintype.card (fixedBy X g) := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hP : IsPGroup 5 (Multiplicative F) := IsPGroup.of_card (n:=2)
    ((Nat.card_congr Multiplicative.toAdd).trans hF)
  have hmod := (hP.to_subgroup (Subgroup.zpowers g)).card_modEq_card_fixedPoints X
  have hset : fixedPoints (Subgroup.zpowers g) X=fixedBy X g := by
    ext x
    constructor
    · intro hx
      exact (mem_fixedPoints.mp hx) ⟨g,Subgroup.mem_zpowers g⟩
    · intro hx
      apply mem_fixedPoints.mpr
      intro a
      exact smul_eq_self_of_mem_zpowers a.property hx
  rw [hset] at hmod
  have hm : Fintype.card X%5=Fintype.card (fixedBy X g)%5 := by
    simpa only [Nat.card_eq_fintype_card] using hmod
  rw [hm]
  exact Nat.mod_le _ _

/-- The actual square-normalized faithful additive action has at least
three characteristic-prime orbits' worth of points. -/
theorem fifteen_le_card_of_square_fixedBy (hF : Nat.card F=25)
    (hsquare : ∀ (a c : Fˣ),
      Nat.card (fixedBy X (Multiplicative.ofAdd ((a:F)*(c:F)^2)))=
        Nat.card (fixedBy X (Multiplicative.ofAdd (a:F))))
    (hmove : ∀ a : Fˣ, ∃ x : X, Multiplicative.ofAdd (a:F) • x≠x) :
    15≤Nat.card X := by
  let H : Subgroup Fˣ := (powMonoidHom 2 : Fˣ→*Fˣ).range
  let f : Fˣ→ℕ := fun a => Fintype.card (fixedBy X (Multiplicative.ofAdd (a:F)))
  have hinv : ∀ (a : Fˣ) (h : H), f (a*h)=f a := by
    intro a h
    obtain ⟨c,hc⟩ := h.property
    have hc' : c^2=(h:Fˣ) := hc
    rw [←hc']
    simpa only [f,Units.val_mul,Units.val_pow_eq_pow_val,Nat.card_eq_fintype_card]
      using hsquare a c
  have hk : H.index≤2 := by
    change (powMonoidHom 2 : Fˣ→*Fˣ).range.index≤2
    rw [IsCyclic.index_powMonoidHom_range]
    exact Nat.gcd_le_right _ (by decide)
  have hfix (a : Fˣ) : f a<Fintype.card X := by
    obtain ⟨x,hx⟩ := hmove a
    apply Fintype.card_lt_of_injective_of_notMem
      (fun y : fixedBy X (Multiplicative.ofAdd (a:F)) => y.val)
      Subtype.val_injective (b:=x)
    rintro ⟨y,rfl⟩
    exact hx y.property
  have hsum : (∑ a ∈ (Finset.univ : Finset (Multiplicative F)).erase 1,
      Fintype.card (fixedBy X a))=∑ a : Fˣ, f a := by
    symm
    change (∑ a ∈ (Finset.univ : Finset Fˣ), f a)=_
    apply Finset.sum_bij (fun (a : Fˣ) _ => Multiplicative.ofAdd (a:F))
    · intro a _
      simp only [Finset.mem_erase,Finset.mem_univ,and_true]
      intro he
      exact a.ne_zero (congrArg Multiplicative.toAdd he)
    · intro a _ b _ he
      exact Units.ext (congrArg Multiplicative.toAdd he)
    · intro b hb
      have hb0 : b.toAdd≠0 := by
        intro he
        exact (Finset.mem_erase.mp hb).1 (congrArg Multiplicative.ofAdd he)
      exact ⟨Units.mk0 b.toAdd hb0,Finset.mem_univ _,rfl⟩
    · intro a _
      rfl
  have hFcard : Fintype.card F=25 := by
    simpa only [Nat.card_eq_fintype_card] using hF
  have hPcard : Fintype.card (Multiplicative F)=25 := by
    simpa only [Fintype.card_multiplicative] using hFcard
  have hAcard : Fintype.card Fˣ=24 := by rw [Fintype.card_units,hFcard]
  have hh : 15≤Fintype.card X := degree_ge_fifteen_of_fixedBy_cosets H f hinv hfix
    (fun a => fixed_remainder_le (X:=X) hF (Multiplicative.ofAdd (a:F)))
    hk hPcard hAcard hsum
  simpa only [Nat.card_eq_fintype_card] using hh

end SymmetricSubgroupAsymptotics.SquareScalarOrderTwentyFivePermutationDegree
