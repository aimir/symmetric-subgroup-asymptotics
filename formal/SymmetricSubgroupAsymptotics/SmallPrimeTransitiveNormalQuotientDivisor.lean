import Mathlib.Data.Finite.Perm
import SymmetricSubgroupAsymptotics.FiniteNormalizerCardDivisor
import SymmetricSubgroupAsymptotics.ElevenCycleOddInverter
import SymmetricSubgroupAsymptotics.SylowNormalizerImageLift
import SymmetricSubgroupAsymptotics.PrimitiveRelativeHeadOrderBudgets

/-! In degrees7,11,13 the quotient by an actual transitive normal
subgroup has order dividing p−1. Frattini retains divisibility, not merely
an order inequality, and therefore excludes an elementary order9 quotient
at degrees11/13 without classifying primitive actions. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SmallPrimeTransitiveNormalQuotientDivisor

private theorem cycle_centralizer_card {p : ℕ} (hp : p.Prime)
    (hsmall : p=7 ∨ p=11 ∨ p=13)
    (g : Equiv.Perm (Fin p)) (hg : orderOf g=p) :
    Nat.card (Subgroup.centralizer ({g} : Set (Equiv.Perm (Fin p))))=p := by
  have hc : g.IsCycle := Equiv.Perm.isCycle_of_prime_order''
    (by simpa only [Fintype.card_fin] using hp)
    (by simpa only [Fintype.card_fin] using hg)
  have hs : g.support.card=p := hc.orderOf.symm.trans hg
  rw [Equiv.Perm.nat_card_centralizer,hc.cycleType,hs]
  rcases hsmall with rfl|rfl|rfl <;> norm_num

theorem normalizer_card_dvd {p : ℕ} (hp : p.Prime)
    (hsmall : p=7 ∨ p=11 ∨ p=13)
    {G : Type} [Group G] [Finite G] [MulAction G (Fin p)]
    [FaithfulSMul G (Fin p)] (P : Subgroup G) (hP : Nat.card P=p) :
    Nat.card (Subgroup.normalizer (P : Set G))∣p*(p-1) := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := P) p (by rw [hP])
  let f := MulAction.toPermHom G (Fin p)
  have hf : Function.Injective f := MulAction.toPerm_injective
  have hgo : orderOf (f (g : G))=p :=
    (orderOf_injective f hf (g : G)).trans ((Subgroup.orderOf_coe g).trans hg)
  let c : Subgroup.centralizer (P : Set G) →*
      Subgroup.centralizer ({f (g : G)} : Set (Equiv.Perm (Fin p))) := {
    toFun := fun x => ⟨f x.val,by
      apply Subgroup.mem_centralizer_iff.mpr
      intro y hy
      have hy' : y=f (g : G) := Set.mem_singleton_iff.mp hy
      subst y
      have hx := Subgroup.mem_centralizer_iff.mp x.property (g : G) g.property
      change f (g : G)*f x.val=f x.val*f (g : G)
      simpa only [←map_mul] using congrArg f hx⟩
    map_one' := Subtype.ext f.map_one
    map_mul' x y := Subtype.ext (f.map_mul x.val y.val) }
  have hc : Function.Injective c := by
    intro x y he
    apply Subtype.ext
    exact hf (congrArg Subtype.val he)
  have hcdiv : Nat.card (Subgroup.centralizer (P : Set G))∣p := by
    have h := Subgroup.card_dvd_of_injective c hc
    rwa [cycle_centralizer_card hp hsmall _ hgo] at h
  letI : IsCyclic P := isCyclic_of_prime_card hP
  letI : CommGroup P := IsCyclic.commGroup
  let k : P → Subgroup.centralizer (P : Set G) := fun x => ⟨x.val,by
    apply Subgroup.mem_centralizer_iff.mpr
    intro y hy
    exact congrArg Subtype.val (mul_comm (⟨y,hy⟩ : P) x)⟩
  have hk : Function.Injective k := by
    intro x y he
    exact Subtype.ext (congrArg (fun z : Subgroup.centralizer (P : Set G) => (z : G)) he)
  have hcent : Nat.card (Subgroup.centralizer (P : Set G))=p :=
    Nat.le_antisymm (Nat.le_of_dvd hp.pos hcdiv)
      (hP ▸ Nat.card_le_card_of_injective k hk)
  have hAut : Nat.card (MulAut P)=p-1 := by
    rw [IsCyclic.card_mulAut,hP,Nat.totient_prime hp]
  simpa only [hcent,hAut] using normalizer_card_dvd_centralizer_mul_aut P

theorem quotient_card_dvd {p : ℕ} (hp : p.Prime)
    (hsmall : p=7 ∨ p=11 ∨ p=13)
    {G : Type} [Group G] [Finite G] [MulAction G (Fin p)]
    [FaithfulSMul G (Fin p)] (S : Subgroup G) [S.Normal]
    [MulAction.IsPretransitive S (Fin p)] : Nat.card (G⧸S)∣p-1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hd : Nat.card S∣p.factorial := by
    have h := Subgroup.card_dvd_of_injective (MulAction.toPermHom S (Fin p))
      (show Function.Injective (MulAction.toPermHom S (Fin p)) from MulAction.toPerm_injective)
    simpa only [Nat.card_perm,Nat.card_fin] using h
  have hpdiv : p∣Nat.card S := by
    simpa only [Nat.card_fin] using
      degree_dvd_card_of_transitive_normal (X := Fin p) S
  have hv : (Nat.card S).factorization p=1 := by
    have hhi := (Nat.factorization_le_iff_dvd (Nat.card_pos (α := S)).ne'
      (Nat.factorial_ne_zero p)).mpr hd p
    have hlo := hp.factorization_pos_of_dvd (Nat.card_pos (α := S)).ne' hpdiv
    have hconst : (p.factorial).factorization p=1 := by
      rcases hsmall with rfl|rfl|rfl <;> decide +kernel
    rw [hconst] at hhi
    omega
  let P : Sylow p S := Classical.choice inferInstance
  have hP : Nat.card P=p := by rw [P.card_eq_multiplicity,hv,pow_one]
  let H : Subgroup G := (P : Subgroup S).map S.subtype
  have hHS : H≤S := by rintro _ ⟨x,hx,rfl⟩; exact x.property
  have hH : Nat.card H=p := by
    dsimp only [H]
    rw [Subgroup.card_map_of_injective S.subtype_injective]
    exact hP
  let pi := QuotientGroup.mk' S
  have hS0 : S.map pi=⊥ := (Subgroup.map_eq_bot_iff S).mpr
    (QuotientGroup.ker_mk' S).ge
  have hH0 : H.map pi=⊥ := (Subgroup.map_eq_bot_iff H).mpr
    (hHS.trans (QuotientGroup.ker_mk' S).ge)
  have hsurj := SylowNormalizerImageLift.map_normalizer_eq_top pi
    (QuotientGroup.mk'_surjective S) S P (hS0.trans hH0.symm)
  let N := Subgroup.normalizer (H : Set G)
  let beta : N →* (G⧸S) := pi.comp N.subtype
  have hbeta : Function.Surjective beta := by
    intro q
    have hq : q∈N.map pi := by
      change q∈(Subgroup.normalizer (P.map S.subtype)).map pi
      rw [hsurj]
      trivial
    obtain ⟨x,hx,he⟩ := hq
    exact ⟨⟨x,hx⟩,he⟩
  let k : H →* beta.ker := {
    toFun := fun x => ⟨⟨x.val,H.le_normalizer x.property⟩,by
      change pi x.val=1
      exact (QuotientGroup.eq_one_iff x.val).mpr (hHS x.property)⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hk : Function.Injective k := by
    intro x y he
    apply Subtype.ext
    exact congrArg (fun z : beta.ker => (z.val.val : G)) he
  have hker : p∣Nat.card beta.ker := by
    rw [←hH]
    exact Subgroup.card_dvd_of_injective k hk
  have hm := beta.ker.card_mul_index
  rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr hbeta,Subgroup.card_top] at hm
  have hprice : p*Nat.card (G⧸S)∣Nat.card N := by
    rw [←hm]
    exact Nat.mul_dvd_mul_right hker (Nat.card (G⧸S))
  have hn : Nat.card N∣p*(p-1) := normalizer_card_dvd hp hsmall H hH
  exact (Nat.mul_dvd_mul_iff_left hp.pos).mp (hprice.trans hn)

end SymmetricSubgroupAsymptotics.SmallPrimeTransitiveNormalQuotientDivisor
