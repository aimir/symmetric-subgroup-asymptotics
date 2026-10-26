import SymmetricSubgroupAsymptotics.OuterFixedElementEvaluationBound

/-! Exact restricted outer-quotient counting. Inner normalization makes
the restricted quotient onto; the stated inner-membership condition
identifies its kernel with the same literal subgroup of the source. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.OuterAutomorphismSubgroupExactCardinality
open PrimitiveSocleRawStructure

variable {G : Type} [Group G] [Finite G]

private instance automorphismFinite : Finite (MulAut G) := Finite.of_injective
  (fun f : MulAut G => (f : G → G)) DFunLike.coe_injective

theorem outer_mul_subgroup_eq_automorphism_subgroup
    (S : Subgroup (MulAut G)) (N : Subgroup G)
    (hconj : Function.Injective (MulAut.conj : G →* MulAut G))
    (hnormalize : ∀ f : MulAut G, ∃ g : G, MulAut.conj g * f ∈ S)
    (hinner : ∀ g : G, MulAut.conj g ∈ S ↔ g ∈ N) :
    Nat.card (Outer G) * Nat.card N = Nat.card S := by
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
  let j : N → q.ker := fun n => ⟨⟨MulAut.conj n.val,(hinner n.val).mpr n.property⟩,by
    change out (MulAut.conj n.val) = 1
    exact (QuotientGroup.eq_one_iff _).mpr ⟨n.val,rfl⟩⟩
  have hj : Function.Bijective j := by
    constructor
    · intro n m h
      apply Subtype.ext
      apply hconj
      exact congrArg (fun k : q.ker => k.val.val) h
    · intro k
      have hk : out k.val.val = 1 := k.property
      obtain ⟨g,hg⟩ := (QuotientGroup.eq_one_iff _).mp hk
      have hgS : MulAut.conj g ∈ S := by
        rw [hg]
        exact k.val.property
      refine ⟨⟨g,(hinner g).mp hgS⟩,?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hg
  have hker : Nat.card N = Nat.card q.ker :=
    Nat.card_congr (Equiv.ofBijective j hj)
  have hprod : Nat.card q.ker * Nat.card q.range = Nat.card S := by
    rw [← Subgroup.index_ker,q.ker.card_mul_index]
  have hrange : q.range = ⊤ := MonoidHom.range_eq_top.mpr hq
  rw [hrange,Subgroup.card_top,← hker] at hprod
  simpa only [Nat.mul_comm] using hprod

theorem outer_mul_subgroup_eq_automorphism_subgroup_of_center_eq_bot
    (S : Subgroup (MulAut G)) (N : Subgroup G)
    (hcenter : Subgroup.center G = ⊥)
    (hnormalize : ∀ f : MulAut G, ∃ g : G, MulAut.conj g * f ∈ S)
    (hinner : ∀ g : G, MulAut.conj g ∈ S ↔ g ∈ N) :
    Nat.card (Outer G) * Nat.card N = Nat.card S :=
  outer_mul_subgroup_eq_automorphism_subgroup S N
    (OuterFixedElementEvaluationBound.conj_injective_of_center_eq_bot hcenter)
    hnormalize hinner

end SymmetricSubgroupAsymptotics.OuterAutomorphismSubgroupExactCardinality
