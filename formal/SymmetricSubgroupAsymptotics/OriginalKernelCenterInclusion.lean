import SymmetricSubgroupAsymptotics.OriginalKernelCenter

/-! The exact center from an actual kernel-containment proof.

Faithfulness of the base representation is one way to prove center
containment, but is not needed once that inclusion has been established
on the original extension by other means.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

section General

variable {k Q B : Type} [CommRing k] [Group Q] [Group B]
    {π : Q →* B} {A : Rep k B} (E : OriginalKernelModuleChart π A)

/-- Fixed kernel vectors identify the full original center whenever
the full original center has already been proved to lie in the kernel. -/
def OriginalKernelModuleChart.invariantsCenterEquivOfCenterLe
    (hπ : Function.Surjective π) (hcenter : Subgroup.center Q≤π.ker) :
    A.ρ.invariants ≃ Subgroup.center Q := by
  let f : A.ρ.invariants → Subgroup.center Q := fun a =>
    ⟨E.element a,(E.element_mem_center_iff hπ a).mpr a.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b h
    have hab : E.element (a:A)=E.element (b:A) :=
      congrArg (fun z : Subgroup.center Q => (z:Q)) h
    exact Subtype.ext (E.element_injective hab)
  · intro z
    let q : π.ker := ⟨z,hcenter z.property⟩
    let a : A := (E.equiv.symm q).toAdd
    have ha : E.element a=(z:Q) :=
      congrArg Subtype.val (E.equiv.apply_symm_apply q)
    have hafix : a∈A.ρ.invariants :=
      (E.element_mem_center_iff hπ a).mp (ha.symm ▸ z.property)
    exact ⟨⟨a,hafix⟩,Subtype.ext ha⟩

end General

section Binary

variable {Q B : Type} [Group Q] [Group B]
    {π : Q →* B} {A : Rep (ZMod 2) B} (E : OriginalKernelModuleChart π A)

include E in
/-- Exact omega cardinality on the same original extension. No faithful
base action, splitting, or monotonicity under a normal quotient is used. -/
theorem OriginalKernelModuleChart.binaryCentralOmega_card_of_center_le
    [Finite A] (hπ : Function.Surjective π) (hcenter : Subgroup.center Q≤π.ker) :
    Nat.card (binaryCentralOmega Q)=
      2^Module.finrank (ZMod 2) A.ρ.invariants := by
  let e := E.invariantsCenterEquivOfCenterLe hπ hcenter
  have hsq (z : Subgroup.center Q) : (z:Q)^2=1 := by
    obtain ⟨a,rfl⟩ := e.surjective z
    exact E.element_sq a
  let eΩ : binaryCentralOmega Q ≃ Subgroup.center Q := {
    toFun := Subtype.val
    invFun z := ⟨z,Subtype.ext (hsq z)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  calc
    Nat.card (binaryCentralOmega Q)=Nat.card (Subgroup.center Q) := Nat.card_congr eΩ
    _ = Nat.card A.ρ.invariants := (Nat.card_congr e).symm
    _ = 2^Module.finrank (ZMod 2) A.ρ.invariants := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]

end Binary

end SymmetricSubgroupAsymptotics
