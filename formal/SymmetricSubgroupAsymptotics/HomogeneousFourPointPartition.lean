import SymmetricSubgroupAsymptotics.TransitiveKernelClassMultiplicity

/-! A homogeneous literal partition of a four-element carrier has one,
two, or four classes. This is a finite partition argument, with no group
or permutation-action catalogue. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Fintype.ofFinite
namespace SymmetricSubgroupAsymptotics.HomogeneousFourPointPartition

theorem single_or_two_or_injective {I K : Type} [Finite I] (key : I → K)
    (hcard : Nat.card I = 4)
    (htransport : ∀ i j : I, ∃ e : I ≃ I, e i = j ∧
      ∀ x y, key (e x) = key (e y) ↔ key x = key y) :
    (∃ i : I, ∀ k : I, key k = key i) ∨
    (∃ i j : I, key i ≠ key j ∧ ∀ k : I, key k = key i ∨ key k = key j) ∨
    Function.Injective key := by
  by_cases hinj : Function.Injective key
  · exact Or.inr (Or.inr hinj)
  obtain ⟨x,y,hxy,hne⟩ := Function.not_injective_iff.mp hinj
  by_cases hsingle : ∀ k : I, key k = key x
  · exact Or.inl ⟨x,hsingle⟩
  obtain ⟨j,hj⟩ := not_forall.mp hsingle
  have hxj : key x ≠ key j := Ne.symm hj
  let A := {i : I // key i = key x}
  let B := {i : I // key i = key j}
  letI : Nontrivial A := ⟨⟨⟨x,rfl⟩,⟨y,hxy.symm⟩,
    fun he => hne (congrArg Subtype.val he)⟩⟩
  have hA : 2 ≤ Nat.card A := by
    have hh := Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial A)
    omega
  have hAB : Nat.card A = Nat.card B :=
    Nat.card_congr (TransitiveKernelClassMultiplicity.fibreEquiv key htransport x j)
  have hcover (k : I) : key k = key x ∨ key k = key j := by
    by_contra hk
    have hkx : key k ≠ key x := fun h => hk (Or.inl h)
    have hkj : key k ≠ key j := fun h => hk (Or.inr h)
    let join : A ⊕ (B ⊕ PUnit.{1}) → I := fun z =>
      match z with
      | Sum.inl a => a.val
      | Sum.inr (Sum.inl b) => b.val
      | Sum.inr (Sum.inr _) => k
    have hinjJoin : Function.Injective join := by
      intro u v he
      cases u with
      | inl a =>
        cases v with
        | inl a' => exact congrArg Sum.inl (Subtype.ext he)
        | inr v =>
          cases v with
          | inl b => exact (hxj (a.property.symm.trans ((congrArg key he).trans b.property))).elim
          | inr z => exact (hkx ((congrArg key he).symm.trans a.property)).elim
      | inr u =>
        cases u with
        | inl b =>
          cases v with
          | inl a => exact (hxj (a.property.symm.trans ((congrArg key he.symm).trans b.property))).elim
          | inr v =>
            cases v with
            | inl b' => exact congrArg (fun z : B => Sum.inr (Sum.inl z)) (Subtype.ext he)
            | inr z => exact (hkj ((congrArg key he).symm.trans b.property)).elim
        | inr z =>
          cases v with
          | inl a => exact (hkx ((congrArg key he).trans a.property)).elim
          | inr v =>
            cases v with
            | inl b => exact (hkj ((congrArg key he).trans b.property)).elim
            | inr z' => exact congrArg (fun w : PUnit.{1} => Sum.inr (Sum.inr w)) (Subsingleton.elim z z')
    have hh := Nat.card_le_card_of_injective join hinjJoin
    change Nat.card (A ⊕ (B ⊕ PUnit.{1})) ≤ Nat.card I at hh
    have hunit : Nat.card PUnit.{1} = 1 := by simp
    rw [Nat.card_sum,Nat.card_sum,hunit] at hh
    omega
  exact Or.inr (Or.inl ⟨x,j,hxj,hcover⟩)

end SymmetricSubgroupAsymptotics.HomogeneousFourPointPartition
