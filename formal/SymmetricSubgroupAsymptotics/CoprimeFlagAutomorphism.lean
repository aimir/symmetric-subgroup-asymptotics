import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

/-! Coprime automorphisms fixing a finite exponent-p flag. The elementary
kernel step does not require an abelian ambient group. The prime-order
factors use the actual automorphism cardinal p-1 of a cyclic group of
order p, not a recognition theorem for the whole group. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CoprimeFlagAutomorphism

variable {G : Type*} [Group G]

theorem eq_one_of_fixed_kernel_of_coprime (N : Subgroup G)
    (p q : ℕ) (hpq : p.Coprime q) (α : MulAut G) (hαq : α ^ q = 1)
    (hexp : ∀ n ∈ N, n ^ p = 1) (hfix : ∀ n ∈ N, α n = n)
    (hmod : ∀ g : G, g⁻¹ * α g ∈ N) : α = 1 := by
  ext g
  let d : G := g⁻¹ * α g
  have hdN : d ∈ N := hmod g
  have hαd : α d = d := hfix d hdN
  have hgd : α g = g * d := by dsimp [d]; group
  have hiter (k : ℕ) : (α ^ k) g = g * d ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hαd, hgd]
      simp only [pow_succ', mul_assoc]
  have hdq : d ^ q = 1 := by
    have h := hiter q
    rw [hαq] at h
    change g = g * d ^ q at h
    exact (mul_left_cancel (h.symm.trans (mul_one g).symm))
  have hdp : d ^ p = 1 := hexp d hdN
  have hd1 : d = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.dvd_one.mp
    have hh := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hdp)
      (orderOf_dvd_of_pow_eq_one hdq)
    simpa only [hpq.gcd_eq_one] using hh
  simpa only [hd1, mul_one] using hgd

theorem prime_card_aut_eq_one [Finite G] {p q : ℕ} (hp : p.Prime)
    (hG : Nat.card G = p) (α : MulAut G) (hαq : α ^ q = 1)
    (hcop : q.Coprime (p - 1)) : α = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : IsCyclic G := isCyclic_of_prime_card (p := p) hG
  have hcard : Nat.card (MulAut G) = p - 1 := by
    rw [IsCyclic.card_mulAut, hG, Nat.totient_prime hp]
  apply orderOf_eq_one_iff.mp
  apply Nat.dvd_one.mp
  have hh := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hαq) (orderOf_dvd_natCard α)
  simpa only [hcard, hcop.gcd_eq_one] using hh

def restriction (α : MulAut G) (F : Subgroup G)
    (hF : F.map α.toMonoidHom = F) : MulAut F :=
  (α.subgroupMap F).trans (MulEquiv.subgroupCongr hF)

theorem restriction_pow_value (α : MulAut G) (F : Subgroup G)
    (hF : F.map α.toMonoidHom = F) (k : ℕ) (f : F) :
    (((restriction α F hF ^ k) f) : G) = (α ^ k) (f : G) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, pow_succ', MulAut.mul_apply]
    change α (((restriction α F hF ^ k) f) : G) = _
    exact congrArg α ih

theorem quotient_pow_value (N : Subgroup G) [N.Normal] (α : MulAut G)
    (hN : N.map α.toMonoidHom = N) (k : ℕ) (g : G) :
    ((QuotientGroup.congr N N α hN ^ k) (QuotientGroup.mk' N g)) =
      QuotientGroup.mk' N ((α ^ k) g) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, ih, QuotientGroup.congr_mk',
      pow_succ', MulAut.mul_apply]

theorem eq_one_of_fixed_kernel_and_prime_quotient [Finite G]
    (N : Subgroup G) [N.Normal] {p q : ℕ} (hp : p.Prime)
    (hquot : Nat.card (G ⧸ N) = p) (hpq : p.Coprime q)
    (hcop : q.Coprime (p - 1)) (α : MulAut G) (hαq : α ^ q = 1)
    (hexp : ∀ n ∈ N, n ^ p = 1) (hfix : ∀ n ∈ N, α n = n) : α = 1 := by
  have hN : N.map α.toMonoidHom = N := by
    ext n
    constructor
    · rintro ⟨m, hm, rfl⟩
      change α m ∈ N
      rwa [hfix m hm]
    · intro hn
      exact ⟨n, hn, hfix n hn⟩
  let β : MulAut (G ⧸ N) := QuotientGroup.congr N N α hN
  have hβq : β ^ q = 1 := by
    ext z
    refine QuotientGroup.induction_on z ?_
    intro g
    change ((QuotientGroup.congr N N α hN ^ q) (QuotientGroup.mk' N g)) = _
    rw [quotient_pow_value, hαq]
    rfl
  have hβ1 : β = 1 := prime_card_aut_eq_one hp hquot β hβq hcop
  apply eq_one_of_fixed_kernel_of_coprime N p q hpq α hαq hexp hfix
  intro g
  have hval := congrArg (fun f : MulAut (G ⧸ N) => f (QuotientGroup.mk' N g)) hβ1
  change QuotientGroup.mk' N (α g) = QuotientGroup.mk' N g at hval
  apply (QuotientGroup.eq_one_iff _).mp
  change QuotientGroup.mk' N (g⁻¹ * α g) = 1
  rw [map_mul, map_inv, hval, inv_mul_cancel]

/-- An invariant flag with two cyclic prime-order factors admits no
nontrivial automorphism of order coprime to both p and p-1 once its first
subgroup is fixed pointwise. Exponent p is used only in the fixed-kernel
steps; no whole-group classification is involved. -/
theorem eq_one_of_prime_flag [Finite G] (N F : Subgroup G)
    [N.Normal] [F.Normal] (hNF : N ≤ F) {p q : ℕ} (hp : p.Prime)
    (hNFindex : N.relIndex F = p) (hFindex : F.index = p)
    (hpq : p.Coprime q) (hcop : q.Coprime (p - 1))
    (hexp : ∀ g : G, g ^ p = 1) (α : MulAut G) (hαq : α ^ q = 1)
    (hfixN : ∀ n ∈ N, α n = n) (hF : F.map α.toMonoidHom = F) : α = 1 := by
  let β : MulAut F := restriction α F hF
  have hβq : β ^ q = 1 := by
    ext f
    change (((restriction α F hF ^ q) f) : G) = (f : G)
    rw [restriction_pow_value, hαq]
    rfl
  have hβ1 : β = 1 := eq_one_of_fixed_kernel_and_prime_quotient
    (N.subgroupOf F) hp hNFindex hpq hcop β hβq
    (fun n _ => Subtype.ext (hexp n.val))
    (fun n hn => Subtype.ext (hfixN n.val hn))
  have hfixF : ∀ f ∈ F, α f = f := by
    intro f hf
    exact congrArg Subtype.val
      (congrArg (fun e : MulAut F => e ⟨f, hf⟩) hβ1)
  exact eq_one_of_fixed_kernel_and_prime_quotient F hp hFindex hpq hcop α hαq
    (fun g _ => hexp g) hfixF

end SymmetricSubgroupAsymptotics.CoprimeFlagAutomorphism
