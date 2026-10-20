import SymmetricSubgroupAsymptotics.NaturalFourNormalChains
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Index
import Mathlib.Data.Nat.Factorization.Basic

/-! Order twelve inside S₃ × S₃ identifies S₃ × C₂. Projection kernels
retain all correlations; the obstruction to two full projections is the
absence of a normal order-two subgroup in S₃. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.DegreeSixThreeByTwoProductRecognition
abbrev S3 := Equiv.Perm (Fin 3)
abbrev C2 := Multiplicative (ZMod 2)

theorem card_s3 : Nat.card S3 = 6 := by rw [Nat.card_perm,Nat.card_fin]; decide
theorem card_c2 : Nat.card C2 = 2 := by rw [Nat.card_congr Multiplicative.toAdd,Nat.card_zmod]

private theorem divisors_six (n : ℕ) (hn : n ∣ 6) :
    n=1 ∨ n=2 ∨ n=3 ∨ n=6 := by
  have hm := Nat.mem_divisors.mpr ⟨hn,by decide⟩
  have hs : Nat.divisors 6 = {1,2,3,6} := by decide
  rw [hs] at hm
  simpa only [Finset.mem_insert,Finset.mem_singleton] using hm

theorem no_normal_two (N : Subgroup S3) [N.Normal] (hn : Nat.card N = 2) : False := by
  have hc : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [nat_card_alternatingGroup,Nat.card_fin]
    decide
  rcases NaturalFourNormalChains.symmetric_three_normal_total N (alternatingGroup (Fin 3))
      inferInstance inferInstance with h | h
  · have hd := Subgroup.card_dvd_of_le h
    rw [hn,hc] at hd
    norm_num at hd
  · have hd := Subgroup.card_dvd_of_le h
    rw [hn,hc] at hd
    norm_num at hd

def equiv_of_full_first {K : Type} [Group K] [Finite K]
    (f g : K →* S3) (hjoint : Function.Injective (fun x => (f x,g x)))
    (hcard : Nat.card K = 12) (hf : Function.Surjective f) : K ≃* S3 × C2 := by
  let R := g.range
  have hd : Nat.card R ∣ 6 := card_s3 ▸ R.card_subgroup_dvd_card
  have hnfull : Nat.card R ≠ 6 := by
    intro hr
    have hRtop : R = ⊤ := R.eq_top_of_card_eq (hr.trans card_s3.symm)
    have hg : Function.Surjective g := MonoidHom.range_eq_top.mp hRtop
    have hi : f.ker.index = 6 := by
      rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr hf,Subgroup.card_top,card_s3]
    have hk : Nat.card f.ker = 2 := by
      have h := f.ker.card_mul_index
      rw [hi,hcard] at h
      omega
    let N := f.ker.map g
    letI : N.Normal := Subgroup.Normal.map inferInstance g hg
    let phi : f.ker →* N := (g.comp f.ker.subtype).codRestrict N
      (fun x => ⟨x.1,x.2,rfl⟩)
    have hphi : Function.Bijective phi := by
      constructor
      · intro x y he
        apply Subtype.ext
        apply hjoint
        apply Prod.ext
        · exact (MonoidHom.mem_ker.mp x.2).trans (MonoidHom.mem_ker.mp y.2).symm
        · exact congrArg Subtype.val he
      · rintro ⟨z,x,hx,rfl⟩
        exact ⟨⟨x,hx⟩,rfl⟩
    have hN : Nat.card N = 2 :=
      (Nat.card_congr (MulEquiv.ofBijective phi hphi).toEquiv).symm.trans hk
    exact no_normal_two N hN
  let m : K →* S3 × R := f.prod g.rangeRestrict
  have hm : Function.Injective m := by
    intro x y h
    apply hjoint
    exact Prod.ext (congrArg (fun z : S3 × R => z.1) h)
      (congrArg (fun z : S3 × R => z.2.1) h)
  have hdiv : 12 ∣ 6 * Nat.card R := by
    have h := Subgroup.card_dvd_of_injective m hm
    simpa only [hcard,Nat.card_prod,card_s3] using h
  have hR : Nat.card R = 2 := by
    rcases divisors_six _ hd with h | h | h | h
    · rw [h] at hdiv
      norm_num at hdiv
    · exact h
    · rw [h] at hdiv
      norm_num at hdiv
    · exact (hnfull h).elim
  have hmb : Function.Bijective m := by
    apply (Nat.bijective_iff_injective_and_card m).mpr
    refine ⟨hm,?_⟩
    rw [hcard,Nat.card_prod,card_s3,hR]
  exact (MulEquiv.ofBijective m hmb).trans <|
    (MulEquiv.refl S3).prodCongr (mulEquivOfPrimeCardEq hR card_c2)

/-- Any literal order-twelve subgroup of S₃² is S₃ × C₂. -/
def subgroup_twelve (H : Subgroup (S3 × S3)) (hH : Nat.card H = 12) :
    H ≃* S3 × C2 := Classical.choice <| by
  let f : H →* S3 := (MonoidHom.fst S3 S3).comp H.subtype
  let g : H →* S3 := (MonoidHom.snd S3 S3).comp H.subtype
  let m : H →* f.range × g.range := f.rangeRestrict.prod g.rangeRestrict
  have hj : Function.Injective (fun x : H => (f x,g x)) := by
    intro x y h
    exact Subtype.ext h
  have hm : Function.Injective m := by
    intro x y h
    apply hj
    exact Prod.ext (congrArg (fun z => z.1.1) h) (congrArg (fun z => z.2.1) h)
  have hdF : Nat.card f.range ∣ 6 := card_s3 ▸ f.range.card_subgroup_dvd_card
  have hdG : Nat.card g.range ∣ 6 := card_s3 ▸ g.range.card_subgroup_dvd_card
  have hb := Nat.card_le_card_of_injective m hm
  rw [hH,Nat.card_prod] at hb
  have hfull : Nat.card f.range = 6 ∨ Nat.card g.range = 6 := by
    by_contra hn
    push Not at hn
    have hF : Nat.card f.range ≤ 3 := by
      rcases divisors_six _ hdF with h | h | h | h <;> omega
    have hG : Nat.card g.range ≤ 3 := by
      rcases divisors_six _ hdG with h | h | h | h <;> omega
    have hh := Nat.mul_le_mul hF hG
    omega
  rcases hfull with h | h
  · have hf : Function.Surjective f := MonoidHom.range_eq_top.mp
      (f.range.eq_top_of_card_eq (h.trans card_s3.symm))
    exact ⟨equiv_of_full_first f g hj hH hf⟩
  · have hg : Function.Surjective g := MonoidHom.range_eq_top.mp
      (g.range.eq_top_of_card_eq (h.trans card_s3.symm))
    have hj' : Function.Injective (fun x : H => (g x,f x)) := by
      intro x y h
      apply hj
      exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
    exact ⟨equiv_of_full_first g f hj' hH hg⟩

end SymmetricSubgroupAsymptotics.DegreeSixThreeByTwoProductRecognition
