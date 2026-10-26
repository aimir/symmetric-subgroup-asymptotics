import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Subgroup.Centralizer

/-! Actual outer quotient counting with the centralizer factor retained.
Inner normalization onto the fixed-v automorphisms identifies their
quotient kernel with the original centralizer, provided conjugation is
injective. Generation by u,v then bounds these automorphisms by their
literal accepted images of u. No simple-model facts are assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.OuterFixedElementEvaluationBound
open PrimitiveSocleRawStructure

variable {G : Type} [Group G] [Finite G]

private instance automorphismFinite : Finite (MulAut G) := Finite.of_injective
  (fun f : MulAut G => (f : G → G)) DFunLike.coe_injective

theorem conj_injective_of_center_eq_bot (hcenter : Subgroup.center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  apply (MulAut.conj : G →* MulAut G).ker_eq_bot_iff.mp
  apply bot_unique
  intro g hg
  have hc : g ∈ Subgroup.center G := by
    apply Subgroup.mem_center_iff.mpr
    intro n
    have he := congrArg (fun f : MulAut G => f n) (MonoidHom.mem_ker.mp hg)
    change g * n * g⁻¹ = n at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  rwa [hcenter] at hc

def fixedAutomorphisms (v : G) : Subgroup (MulAut G) where
  carrier := {f | f v = v}
  one_mem' := rfl
  mul_mem' := by
    intro f h hf hh
    change f (h v) = v
    rw [hh,hf]
  inv_mem' := by
    intro f hf
    change f.symm v = v
    apply f.injective
    rw [f.apply_symm_apply,hf]

theorem outer_mul_centralizer_eq_fixedAutomorphisms
    (v : G) (hconj : Function.Injective (MulAut.conj : G →* MulAut G))
    (hnormalize : ∀ f : MulAut G, ∃ g : G, (MulAut.conj g * f) v = v) :
    Nat.card (Outer G) * Nat.card (Subgroup.centralizer ({v} : Set G)) =
      Nat.card (fixedAutomorphisms v) := by
  let S := fixedAutomorphisms v
  let C := Subgroup.centralizer ({v} : Set G)
  let out : MulAut G →* Outer G := QuotientGroup.mk' (Inner G)
  let q : S →* Outer G := out.comp S.subtype
  have hq : Function.Surjective q := by
    intro o
    obtain ⟨f,hf⟩ := QuotientGroup.mk'_surjective (Inner G) o
    obtain ⟨g,hg⟩ := hnormalize f
    refine ⟨⟨MulAut.conj g * f,hg⟩,?_⟩
    change out (MulAut.conj g * f) = o
    have hi : out (MulAut.conj g) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨g,rfl⟩
    rw [map_mul,hi,one_mul]
    exact hf
  let j : C → q.ker := fun c => ⟨⟨MulAut.conj c.val,by
    change c.val * v * c.val⁻¹ = v
    have hc := Subgroup.mem_centralizer_singleton_iff.mp c.property
    rw [hc,mul_inv_cancel_right]⟩,by
      change out (MulAut.conj c.val) = 1
      exact (QuotientGroup.eq_one_iff _).mpr ⟨c.val,rfl⟩⟩
  have hj : Function.Bijective j := by
    constructor
    · intro c d h
      apply Subtype.ext
      apply hconj
      exact congrArg (fun k : q.ker => k.val.val) h
    · intro k
      have hk : out k.val.val = 1 := k.property
      obtain ⟨g,hg⟩ := (QuotientGroup.eq_one_iff _).mp hk
      have hgv : g * v * g⁻¹ = v := by
        change (MulAut.conj g) v = v
        rw [hg]
        exact k.val.property
      have hgC : g ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr
        (mul_inv_eq_iff_eq_mul.mp hgv)
      refine ⟨⟨g,hgC⟩,?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hg
  have hker : Nat.card C = Nat.card q.ker :=
    Nat.card_congr (Equiv.ofBijective j hj)
  have hprod : Nat.card q.ker * Nat.card q.range = Nat.card S := by
    rw [← Subgroup.index_ker,q.ker.card_mul_index]
  have hrange : q.range = ⊤ := MonoidHom.range_eq_top.mpr hq
  rw [hrange,Subgroup.card_top,← hker] at hprod
  simpa only [Nat.mul_comm] using hprod

theorem fixedAutomorphisms_card_le_accepted
    (u v : G) (hgen : Subgroup.closure ({u,v} : Set G) = ⊤)
    (accepted : Finset G)
    (haccepted : ∀ f : fixedAutomorphisms v, f.val u ∈ accepted) :
    Nat.card (fixedAutomorphisms v) ≤ accepted.card := by
  let eval : fixedAutomorphisms v → accepted := fun f => ⟨f.val u,haccepted f⟩
  have hinj : Function.Injective eval := by
    intro f h he
    apply Subtype.ext
    apply MulEquiv.ext
    intro n
    have heval : f.val u = h.val u := congrArg Subtype.val he
    have hmaps : f.val.toMonoidHom = h.val.toMonoidHom := by
      apply MonoidHom.eq_of_eqOn_dense hgen
      rintro z (rfl|rfl)
      · exact heval
      · exact f.property.trans h.property.symm
    exact DFunLike.congr_fun hmaps n
  have hc := Nat.card_le_card_of_injective eval hinj
  simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using hc

theorem outer_mul_centralizer_le_accepted
    (u v : G) (hgen : Subgroup.closure ({u,v} : Set G) = ⊤)
    (hconj : Function.Injective (MulAut.conj : G →* MulAut G))
    (hnormalize : ∀ f : MulAut G, ∃ g : G, (MulAut.conj g * f) v = v)
    (accepted : Finset G)
    (haccepted : ∀ f : fixedAutomorphisms v, f.val u ∈ accepted) :
    Nat.card (Outer G) * Nat.card (Subgroup.centralizer ({v} : Set G)) ≤ accepted.card := by
  rw [outer_mul_centralizer_eq_fixedAutomorphisms v hconj hnormalize]
  exact fixedAutomorphisms_card_le_accepted u v hgen accepted haccepted

theorem outer_mul_centralizer_le_accepted_of_center_eq_bot
    (u v : G) (hgen : Subgroup.closure ({u,v} : Set G) = ⊤)
    (hcenter : Subgroup.center G = ⊥)
    (hnormalize : ∀ f : MulAut G, ∃ g : G, (MulAut.conj g * f) v = v)
    (accepted : Finset G)
    (haccepted : ∀ f : fixedAutomorphisms v, f.val u ∈ accepted) :
    Nat.card (Outer G) * Nat.card (Subgroup.centralizer ({v} : Set G)) ≤ accepted.card :=
  outer_mul_centralizer_le_accepted u v hgen (conj_injective_of_center_eq_bot hcenter)
    hnormalize accepted haccepted

end SymmetricSubgroupAsymptotics.OuterFixedElementEvaluationBound
