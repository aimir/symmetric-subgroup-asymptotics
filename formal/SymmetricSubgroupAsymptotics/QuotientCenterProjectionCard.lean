import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.Index

/-! Bound the original quotient centre by its actual kernel and top fibres.
The top predicate need not be a subgroup. No extension splitting or chosen
independent lift is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.QuotientCenterProjectionCard

variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

theorem preimage_card (N : Subgroup G) [N.Normal] :
    Nat.card ((Subgroup.center (G ⧸ N)).comap (QuotientGroup.mk' N)) =
      Nat.card N * Nat.card (Subgroup.center (G ⧸ N)) := by
  let q := QuotientGroup.mk' N
  let P := (Subgroup.center (G ⧸ N)).comap q
  let f : P →* Subgroup.center (G ⧸ N) :=
    (q.comp P.subtype).codRestrict _ (fun x => x.property)
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
    exact ⟨⟨x, hy⟩, rfl⟩
  let e : f.ker ≃ N := {
    toFun x := ⟨x.val.val, (QuotientGroup.eq_one_iff _).mp
      (congrArg Subtype.val x.property)⟩
    invFun x := ⟨⟨x.val, by
      change q x.val ∈ Subgroup.center (G ⧸ N)
      have hx : q x.val = 1 := (QuotientGroup.eq_one_iff _).mpr x.property
      rw [hx]
      exact (Subgroup.center (G ⧸ N)).one_mem⟩, by
        apply Subtype.ext
        exact (QuotientGroup.eq_one_iff _).mpr x.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hc := f.ker.card_mul_index
  rw [Subgroup.index_ker, f.range_eq_top_of_surjective hf,
    Nat.card_congr (Subgroup.topEquiv).toEquiv, Nat.card_congr e] at hc
  exact hc.symm

/-- Each actual central preimage has its original kernel fibre. Arbitrary
nonzero top components are paid by their literal top predicate. -/
theorem card_mul_le (N : Subgroup G) [N.Normal]
    (q : G →* H) (A : Subgroup G) (T : H → Prop)
    (hker : ∀ g : G, q g = 1 →
      QuotientGroup.mk' N g ∈ Subgroup.center (G ⧸ N) → g ∈ A)
    (htop : ∀ g : G,
      QuotientGroup.mk' N g ∈ Subgroup.center (G ⧸ N) → T (q g)) :
    Nat.card N * Nat.card (Subgroup.center (G ⧸ N)) ≤
      Nat.card A * Nat.card {t : H // T t} := by
  let P := (Subgroup.center (G ⧸ N)).comap (QuotientGroup.mk' N)
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
  rw [← preimage_card N]
  change Nat.card P ≤ _
  rw [← hf]
  exact Nat.mul_le_mul hkc hrc

end SymmetricSubgroupAsymptotics.QuotientCenterProjectionCard
