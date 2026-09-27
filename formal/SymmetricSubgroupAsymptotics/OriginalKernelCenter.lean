import SymmetricSubgroupAsymptotics.Non2LiftBound
import SymmetricSubgroupAsymptotics.BinaryNormalCharacterCriterion

/-! Faithful action on the actual abelian kernel puts the entire center
of the original extension back in that kernel. Fixed kernel vectors then
identify the whole center. No splitting or faithful action of the original
quotient on an unrelated point set is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

section General

variable {k Q B : Type} [CommRing k] [Group Q] [Group B]
    {π : Q →* B} {A : Rep k B} (E : OriginalKernelModuleChart π A)

def OriginalKernelModuleChart.element (a : A) : Q :=
  (E.equiv (Multiplicative.ofAdd a) : Q)

theorem OriginalKernelModuleChart.element_injective : Function.Injective E.element := by
  intro a b h
  exact Multiplicative.ofAdd.injective (E.equiv.injective (Subtype.ext h))

/-- Fixed vectors correspond exactly to central elements of the actual
kernel; surjectivity is used only to lift each element of the acting base. -/
theorem OriginalKernelModuleChart.element_mem_center_iff
    (hπ : Function.Surjective π) (a : A) :
    E.element a∈Subgroup.center Q ↔ a∈A.ρ.invariants := by
  constructor
  · intro ha b
    obtain ⟨q,rfl⟩ := hπ b
    apply E.element_injective
    change (E.equiv (Multiplicative.ofAdd (A.ρ (π q) a)) : Q)=E.element a
    rw [E.conjugate]
    change q*E.element a*q⁻¹=E.element a
    rw [Subgroup.mem_center_iff.mp ha q]
    simp only [mul_assoc,mul_inv_cancel,mul_one]
  · intro ha
    apply Subgroup.mem_center_iff.mpr
    intro q
    have hconj : q*E.element a*q⁻¹=E.element a := by
      exact (E.conjugate q a).symm.trans (congrArg E.element (ha (π q)))
    have h := congrArg (fun z : Q => z*q) hconj
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using h

include E in
/-- Every central original element acts trivially on the whole actual
kernel. A faithful base action therefore kills its actual base image. -/
theorem OriginalKernelModuleChart.center_le_ker
    (hfaithful : Function.Injective A.ρ) : Subgroup.center Q≤π.ker := by
  intro q hq
  apply MonoidHom.mem_ker.mpr
  apply hfaithful
  rw [map_one]
  apply LinearMap.ext
  intro a
  change A.ρ (π q) a=a
  apply E.element_injective
  change (E.equiv (Multiplicative.ofAdd (A.ρ (π q) a)) : Q)=E.element a
  rw [E.conjugate]
  change q*E.element a*q⁻¹=E.element a
  rw [← Subgroup.mem_center_iff.mp hq (E.element a)]
  simp only [mul_assoc,mul_inv_cancel,mul_one]

include E in
/-- An exact equivalence with the center, retaining the literal original
extension and the actual kernel chart. -/
def OriginalKernelModuleChart.invariantsCenterEquiv
    (hπ : Function.Surjective π) (hfaithful : Function.Injective A.ρ) :
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
    let q : π.ker := ⟨z,E.center_le_ker hfaithful z.property⟩
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

theorem OriginalKernelModuleChart.element_sq (a : A) : E.element a^2=1 := by
  have ha : a+a=0 := by
    calc
      a+a=((1:ZMod 2)+(1:ZMod 2)) • a := by rw [add_smul,one_smul]
      _ = 0 := by rw [show (1:ZMod 2)+(1:ZMod 2)=0 from rfl,zero_smul]
  have hm : (Multiplicative.ofAdd a)^2=1 := by
    apply Multiplicative.toAdd.injective
    simpa only [pow_two] using ha
  have h := congrArg Subtype.val (congrArg E.equiv hm)
  simpa only [map_pow,map_one] using h

include E in
/-- The center is elementary binary because it is contained in the
actual elementary kernel. Its complete omega cardinality is exactly the
cardinality of the original fixed space. -/
theorem OriginalKernelModuleChart.binaryCentralOmega_card
    [Finite A] (hπ : Function.Surjective π) (hfaithful : Function.Injective A.ρ) :
    Nat.card (binaryCentralOmega Q)=
      2^Module.finrank (ZMod 2) A.ρ.invariants := by
  let e := E.invariantsCenterEquiv hπ hfaithful
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
