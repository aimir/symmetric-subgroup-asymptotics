import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.Index

/-! Every actual quotient subgroup, including a centralizer of a proper
normal image, is charged through its original kernel and literal top fibres.
Neither a chosen extension splitting nor a whole-quotient specialization is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.QuotientSubgroupProjectionCard

variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

theorem preimage_card (N : Subgroup G) [N.Normal] (S : Subgroup (G ⧸ N)) :
    Nat.card ((S).comap (QuotientGroup.mk' N)) =
      Nat.card N * Nat.card (S) := by
  let q := QuotientGroup.mk' N
  let P := (S).comap q
  let f : P →* S :=
    (q.comp P.subtype).codRestrict _ (fun x => x.property)
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
    exact ⟨⟨x, hy⟩, rfl⟩
  let e : f.ker ≃ N := {
    toFun x := ⟨x.val.val, (QuotientGroup.eq_one_iff _).mp
      (congrArg Subtype.val x.property)⟩
    invFun x := ⟨⟨x.val, by
      change q x.val ∈ S
      have hx : q x.val = 1 := (QuotientGroup.eq_one_iff _).mpr x.property
      rw [hx]
      exact (S).one_mem⟩, by
        apply Subtype.ext
        exact (QuotientGroup.eq_one_iff _).mpr x.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hc := f.ker.card_mul_index
  rw [Subgroup.index_ker, f.range_eq_top_of_surjective hf,
    Nat.card_congr (Subgroup.topEquiv).toEquiv, Nat.card_congr e] at hc
  exact hc.symm

/-- The SAME quotient subgroup retains its original kernel fibre and top
predicate. This applies in particular to a proper-normal-image centralizer. -/
theorem card_mul_le (N : Subgroup G) [N.Normal] (S : Subgroup (G ⧸ N))
    (q : G →* H) (A : Subgroup G) (T : H → Prop)
    (hker : ∀ g : G, q g = 1 →
      QuotientGroup.mk' N g ∈ S → g ∈ A)
    (htop : ∀ g : G,
      QuotientGroup.mk' N g ∈ S → T (q g)) :
    Nat.card N * Nat.card (S) ≤
      Nat.card A * Nat.card {t : H // T t} := by
  let P := (S).comap (QuotientGroup.mk' N)
  let f : P →* H := q.comp P.subtype
  let k : f.ker → A := fun x =>
    ⟨x.val.val, hker x.val.val x.property x.val.property⟩
  have hk : Function.Injective k := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : A => (z : G)) h
  have hkc : Nat.card f.ker ≤ Nat.card A := Nat.card_le_card_of_injective k hk
  let r : f.range → {t : H // T t} := fun x => ⟨x.val, by
    obtain ⟨g, hg⟩ := x.property
    simpa only [← hg] using htop g.val g.property⟩
  have hr : Function.Injective r := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : {t : H // T t} => z.val) h)
  have hrc : Nat.card f.range ≤ Nat.card {t : H // T t} :=
    Nat.card_le_card_of_injective r hr
  have hf := f.ker.card_mul_index
  rw [Subgroup.index_ker] at hf
  rw [← preimage_card N S]
  change Nat.card P ≤ _
  rw [← hf]
  exact Nat.mul_le_mul hkc hrc

end SymmetricSubgroupAsymptotics.QuotientSubgroupProjectionCard
