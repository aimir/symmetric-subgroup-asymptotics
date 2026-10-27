import SymmetricSubgroupAsymptotics.FiniteOddKernelDivisor
import SymmetricSubgroupAsymptotics.PrimeCyclicSylowFixedFibreOuterBound
import SymmetricSubgroupAsymptotics.FiniteNormalizerCardDivisor
import Mathlib.GroupTheory.SpecificGroups.Alternating

/-! Parity sharpening with an EXPLICIT odd ambient normalizer witness.
No witness, candidate capacity, or sporadic model fact is assumed globally. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimeCycleParityNormalizer
open PrimitiveSocleRawStructure

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {p q n : ℕ} [Fact p.Prime] [Fact q.Prime]
    [MulAction G (Fin n)] [FaithfulSMul G (Fin n)]

theorem source_sign_one (hn : ¬IsMulCommutative G) (g : G) :
    Equiv.Perm.sign (MulAction.toPermHom G (Fin n) g) = 1 := by
  let f : G →* ℤˣ := Equiv.Perm.sign.comp (MulAction.toPermHom G (Fin n))
  rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with hb | ht
  · have hi : Function.Injective f := f.ker_eq_bot_iff.mp hb
    apply (hn ?_).elim
    refine ⟨⟨fun x y => hi ?_⟩⟩
    rw [map_mul,map_mul,mul_comm]
  · have hg : g ∈ f.ker := by rw [ht]; trivial
    exact hg

theorem normalizer_card_dvd_prime_half (hnon : ¬IsMulCommutative G)
    (P : Sylow p G) (a : G) (hgen : (P : Subgroup G) = Subgroup.zpowers a)
    (hn : n=p ∨ n=p+1)
    (htype : (MulAction.toPermHom G (Fin n) a).cycleType = {p})
    (hhalf : p-1=2*q)
    (sigma : Equiv.Perm (Fin n))
    (hsigma : sigma ∈ Subgroup.normalizer
      ((Subgroup.zpowers (MulAction.toPermHom G (Fin n) a)) : Set (Equiv.Perm (Fin n))))
    (hodd : Equiv.Perm.sign sigma = -1) :
    Nat.card (Subgroup.normalizer (P : Set G)) ∣ p*q := by
  let rho := MulAction.toPermHom G (Fin n)
  let Q := Subgroup.zpowers (rho a)
  let H := Subgroup.normalizer (Q : Set (Equiv.Perm (Fin n)))
  let chi : H →* ℤˣ := Equiv.Perm.sign.comp H.subtype
  have horder : orderOf (rho a) = p := by
    change orderOf (MulAction.toPermHom G (Fin n) a) = p
    rw [←Equiv.Perm.lcm_cycleType,htype]
    simp
  have hQ : Nat.card Q = p := by
    rw [Nat.card_zpowers,horder]
  letI : IsCyclic Q := isCyclic_of_prime_card hQ
  have hC : Nat.card (Subgroup.centralizer (Q : Set (Equiv.Perm (Fin n)))) = p := by
    change Nat.card (Subgroup.centralizer
      ((Subgroup.zpowers (rho a)) : Set (Equiv.Perm (Fin n)))) = p
    rw [Subgroup.zpowers_eq_closure,Subgroup.centralizer_closure]
    exact PrimeCycleSylowNormalizerSolvable.ambient_centralizer_card (rho a) hn htype
  have hAut : Nat.card (MulAut Q) = p-1 := by
    rw [IsCyclic.card_mulAut,hQ,Nat.totient_prime Fact.out]
  have hH : Nat.card H ∣ 2*(p*q) := by
    have hd := normalizer_card_dvd_centralizer_mul_aut Q
    rw [hC,hAut,hhalf] at hd
    have he : p*(2*q) = 2*(p*q) := by ac_rfl
    simpa only [he] using hd
  have hmap : (P : Subgroup G).map rho = Q := by
    rw [hgen,MonoidHom.map_zpowers]
  let f : Subgroup.normalizer (P : Set G) →* chi.ker := {
    toFun := fun z => ⟨⟨rho z.val,by
      have hh := (P : Subgroup G).le_normalizer_map rho
        (show rho z.val ∈ (Subgroup.normalizer (P : Set G)).map rho from
          ⟨z.val,z.property,rfl⟩)
      rw [hmap] at hh
      exact hh⟩,by
        change Equiv.Perm.sign (rho z.val) = 1
        exact source_sign_one hnon z.val⟩
    map_one' := by apply Subtype.ext; apply Subtype.ext; exact rho.map_one
    map_mul' z w := by apply Subtype.ext; apply Subtype.ext; exact rho.map_mul z.val w.val }
  have hf : Function.Injective f := by
    intro z w he
    apply Subtype.ext
    exact MulAction.toPerm_injective
      (congrArg (fun k : chi.ker => k.val.val) he)
  exact FiniteOddKernelDivisor.card_dvd_of_injective_to_odd_kernel
    chi ⟨sigma,hsigma⟩ hodd f hf (p*q) hH

theorem normalizer_card_eq_prime_half (hnon : ¬IsMulCommutative G)
    (P : Sylow p G) (hP : Nat.card P = p) (a : G)
    (hgen : (P : Subgroup G) = Subgroup.zpowers a)
    (hn : n=p ∨ n=p+1)
    (htype : (MulAction.toPermHom G (Fin n) a).cycleType = {p})
    (hhalf : p-1=2*q) (sigma : Equiv.Perm (Fin n))
    (hsigma : sigma ∈ Subgroup.normalizer
      ((Subgroup.zpowers (MulAction.toPermHom G (Fin n) a)) : Set (Equiv.Perm (Fin n))))
    (hodd : Equiv.Perm.sign sigma = -1) :
    Nat.card (Subgroup.normalizer (P : Set G)) = p*q := by
  have hd := normalizer_card_dvd_prime_half hnon P a hgen hn htype hhalf sigma hsigma hodd
  have hpN : p ∣ Nat.card (Subgroup.normalizer (P : Set G)) := by
    have hh := Subgroup.card_dvd_of_le (P : Subgroup G).le_normalizer
    simpa only [hP] using hh
  obtain ⟨k,hk⟩ := hpN
  have hkq : k ∣ q := by
    rw [hk] at hd
    exact (Nat.mul_dvd_mul_iff_left (Fact.out : Nat.Prime p).pos).mp hd
  rcases (Fact.out : Nat.Prime q).eq_one_or_self_of_dvd _ hkq with h1 | hq
  · have hb := SimplePrimeSylowSuccessorIndexSquare.normalizer_card_ge_twice_prime hnon P hP
    rw [hk,h1,mul_one] at hb
    have := (Fact.out : Nat.Prime p).pos
    omega
  · simpa only [hq] using hk

theorem prime_mul_outer_le_twice_fixed (hnon : ¬IsMulCommutative G)
    (P : Sylow p G) (hP : Nat.card P = p) (a : G)
    (hgen : (P : Subgroup G) = Subgroup.zpowers a)
    (hn : n=p ∨ n=p+1)
    (htype : (MulAction.toPermHom G (Fin n) a).cycleType = {p})
    (hhalf : p-1=2*q) (sigma : Equiv.Perm (Fin n))
    (hsigma : sigma ∈ Subgroup.normalizer
      ((Subgroup.zpowers (MulAction.toPermHom G (Fin n) a)) : Set (Equiv.Perm (Fin n))))
    (hodd : Equiv.Perm.sign sigma = -1) :
    p * Nat.card (Outer G) ≤
      2 * Nat.card (OuterFixedElementEvaluationBound.fixedAutomorphisms a) := by
  have he := PrimeCyclicSylowFixedFibreOuterBound.outer_mul_normalizer_eq_preserving hnon P
  rw [normalizer_card_eq_prime_half hnon P hP a hgen hn htype hhalf sigma hsigma hodd] at he
  have hb := PrimeCyclicSylowFixedFibreOuterBound.preserving_card_le_fixed_mul_pred P hP a hgen
  rw [←he,hhalf] at hb
  have hh : (p * Nat.card (Outer G)) * q ≤
      (2 * Nat.card (OuterFixedElementEvaluationBound.fixedAutomorphisms a)) * q := by
    simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hb
  exact Nat.le_of_mul_le_mul_right hh (Fact.out : Nat.Prime q).pos

end SymmetricSubgroupAsymptotics.PrimeCycleParityNormalizer
