import SymmetricSubgroupAsymptotics.BinaryPairSharedBinding
import SymmetricSubgroupAsymptotics.BinaryNormalCharacterCriterion
import Mathlib.Algebra.CharP.Two

/-! A faithful quotient action on the retained correlated kernel forces
every central original quotient class back into that kernel. Its complete
central omega subgroup is then measured by the actual fixed preimage.
No quotient-element or original-source row enumeration is needed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

private theorem centralOmega_card_of_square (G : Type*) [Group G]
    (hsq : ∀ x : Subgroup.center G, (x:G)^2=1) :
    Nat.card (binaryCentralOmega G)=Nat.card (Subgroup.center G) := by
  let e : binaryCentralOmega G ≃ Subgroup.center G := {
    toFun := Subtype.val
    invFun x := ⟨x,Subtype.ext (hsq x)⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  exact Nat.card_congr e

/-- The full central preimage has the exact original normal fibre size. -/
private theorem central_preimage_card {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] :
    Nat.card ((Subgroup.center (G ⧸ N)).comap (QuotientGroup.mk' N))=
      Nat.card N*Nat.card (Subgroup.center (G ⧸ N)) := by
  let q := QuotientGroup.mk' N
  let D := (Subgroup.center (G ⧸ N)).comap q
  let f : D →* Subgroup.center (G ⧸ N) :=
    (q.comp D.subtype).codRestrict _ (fun x => x.property)
  have hf : Function.Surjective f := by
    rintro ⟨y,hy⟩
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective N y
    exact ⟨⟨x,hy⟩,rfl⟩
  let e : f.ker ≃ N := {
    toFun x := ⟨x.val.val,(QuotientGroup.eq_one_iff _).mp
      (congrArg Subtype.val x.property)⟩
    invFun x := ⟨⟨x.val,by
      change q x.val∈Subgroup.center (G ⧸ N)
      have hx : q x.val=1 := (QuotientGroup.eq_one_iff _).mpr x.property
      rw [hx]
      exact (Subgroup.center (G ⧸ N)).one_mem⟩,by
        apply Subtype.ext
        exact (QuotientGroup.eq_one_iff _).mpr x.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hc := f.ker.card_mul_index
  rw [Subgroup.index_ker,f.range_eq_top_of_surjective hf,
    Nat.card_congr (Subgroup.topEquiv).toEquiv,Nat.card_congr e] at hc
  exact hc.symm

namespace BinaryPairFrame
variable {X : Type} {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

/-- A central original quotient class acts trivially on every retained
kernel vector modulo the exact coordinate normal. -/
theorem central_quotient_displacement
    (A : Subrepresentation F.coordinateTopAction) (u : U)
    (hu : QuotientGroup.mk' (F.coordinateSubgroup A.toSubmodule) u∈
      Subgroup.center (U ⧸ F.coordinateSubgroup A.toSubmodule))
    (k : F.top.ker) :
    F.coordinateTopAction (F.top.rangeRestrict u) (F.bits k)-F.bits k∈A.toSubmodule := by
  let q := QuotientGroup.mk' (F.coordinateSubgroup A.toSubmodule)
  have hc := (Subgroup.mem_center_iff.mp hu) (q (k:U))
  change q (k:U)*q u=q u*q (k:U) at hc
  have he : q ((k:U)⁻¹*(u*(k:U)*u⁻¹))=1 := by
    simp only [map_mul,map_inv]
    rw [← hc]
    simp [mul_assoc]
  have hm : ((k⁻¹*MulAut.conjNormal u k : F.top.ker):U)∈
      F.coordinateSubgroup A.toSubmodule := (QuotientGroup.eq_one_iff _).mp he
  rwa [F.kernel_mem_coordinateSubgroup,F.bits_commutator] at hm

/-- Faithfulness on K/A rules out every nontrivial top component of a
central quotient class. It does not assert a splitting of the extension. -/
theorem central_quotient_mem_kernel
    (A : Subrepresentation F.coordinateTopAction)
    (hfaithful : ∀ t : F.top.range,
      (∀ v, v∈F.kernelSpace → F.coordinateTopAction t v-v∈A.toSubmodule) → t=1)
    (u : U)
    (hu : QuotientGroup.mk' (F.coordinateSubgroup A.toSubmodule) u∈
      Subgroup.center (U ⧸ F.coordinateSubgroup A.toSubmodule)) : u∈F.top.ker := by
  have ht : F.top.rangeRestrict u=1 := by
    apply hfaithful
    intro v hv
    obtain ⟨k,hk⟩ := hv
    change F.bits k.toMul=v at hk
    rw [← hk]
    exact F.central_quotient_displacement A u hu k.toMul
  exact congrArg Subtype.val ht

/-- A finite shared-basis check certifies the required faithful action on
the original quotient kernel, through the same specified top isomorphism. -/
theorem shared_central_quotient_mem_kernel_of_basis {H : Type} [Group H] {d : ℕ}
    (ρ : Representation (ZMod 2) H (Fin w → ZMod 2))
    (e : H ≃* F.top.range) (he : ∀ g v,ρ g v=F.coordinateTopAction (e g) v)
    (K : BinaryCoordinateSpace w d) (hK : K.space=F.kernelSpace)
    (A : Subrepresentation ρ)
    (hfaithful : ∀ g : H,
      (∀ i,ρ g (K.inclusion (Pi.single i 1))-K.inclusion (Pi.single i 1)∈A.toSubmodule) →
      g=1)
    (u : U)
    (hu : QuotientGroup.mk' (F.coordinateSubgroup (F.sharedSubrepresentation ρ e he A).toSubmodule) u∈
      Subgroup.center (U ⧸ F.coordinateSubgroup (F.sharedSubrepresentation ρ e he A).toSubmodule)) : u∈F.top.ker := by
  apply F.central_quotient_mem_kernel (F.sharedSubrepresentation ρ e he A) ?_ u hu
  intro t ht
  have hg : e.symm t=1 := by
    apply hfaithful
    intro i
    rw [he,e.apply_symm_apply]
    exact ht _ (hK ▸ (show K.inclusion (Pi.single i 1)∈K.space from ⟨_,rfl⟩))
  simpa only [e.apply_symm_apply,map_one] using congrArg e hg

theorem kernel_square (k : F.top.ker) : (k:U)^2=1 := by
  have he : k^2=1 := by
    apply F.bitsHom_injective
    rw [map_pow,map_one,pow_two]
    apply Multiplicative.toAdd.injective
    change F.bits k+F.bits k=0
    funext i
    exact CharTwo.add_self_eq_zero _
  exact congrArg Subtype.val he

/-- Once every central class lies in the actual flip kernel, all central
classes are involutions. The exact omega cardinal is the fixed-preimage
cardinal divided by the original normal cardinal. -/
theorem centralOmega_card_mul_axis
    (A : Subrepresentation F.coordinateTopAction)
    (hcentral : ∀ u : U,
      QuotientGroup.mk' (F.coordinateSubgroup A.toSubmodule) u∈
        Subgroup.center (U ⧸ F.coordinateSubgroup A.toSubmodule) → u∈F.top.ker) :
    Nat.card (F.coordinateSubgroup A.toSubmodule)*
      Nat.card (binaryCentralOmega (U ⧸ F.coordinateSubgroup A.toSubmodule))=
      Nat.card (binaryPairFixedSubgroup F.top.ker (F.coordinateSubgroup A.toSubmodule)) := by
  let N := F.coordinateSubgroup A.toSubmodule
  have he : binaryPairFixedSubgroup F.top.ker N=
      (Subgroup.center (U ⧸ N)).comap (QuotientGroup.mk' N) :=
    inf_eq_right.mpr hcentral
  have hs : ∀ x : Subgroup.center (U ⧸ N), (x:U ⧸ N)^2=1 := by
    rintro ⟨x,hx⟩
    obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective N x
    rw [← map_pow,F.kernel_square ⟨u,hcentral u hx⟩,map_one]
  rw [he,centralOmega_card_of_square _ hs,central_preimage_card]

/-- A complete coordinate fixed preimage gives the actual quotient omega
dimension after central top components have been excluded. -/
theorem centralOmega_card_of_fixed_chart [Finite X]
    (A D : Subrepresentation F.coordinateTopAction)
    (hfixed : BinaryCoordinateCutData F.coordinateTopAction F.kernelSubrepresentation A A D)
    (hcentral : ∀ u : U,
      QuotientGroup.mk' (F.coordinateSubgroup A.toSubmodule) u∈
        Subgroup.center (U ⧸ F.coordinateSubgroup A.toSubmodule) → u∈F.top.ker) :
    Nat.card (binaryCentralOmega (U ⧸ F.coordinateSubgroup A.toSubmodule))=
      2^(Module.finrank (ZMod 2) D.toSubmodule-Module.finrank (ZMod 2) A.toSubmodule) := by
  have hc := (F.sharedKernelCut A A D hfixed (fun _ : Unit => (1:U))).fixed_card
  change Nat.card (binaryPairFixedSubgroup F.top.ker (F.coordinateSubgroup A.toSubmodule))=
    Nat.card (F.coordinateSubgroup A.toSubmodule)*
      2^(Module.finrank (ZMod 2) D.toSubmodule-Module.finrank (ZMod 2) A.toSubmodule) at hc
  exact mul_left_cancel₀ (Nat.card_pos (α := F.coordinateSubgroup A.toSubmodule)).ne'
    ((F.centralOmega_card_mul_axis A hcentral).trans hc)

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
