import SymmetricSubgroupAsymptotics.PrimeRelativeHeadSurjectiveKernel
import SymmetricSubgroupAsymptotics.PGroupNormalGeneratorCharacterEquality

/-! The derived-order equality for an actual elementary-kernel quotient.
The SAME original derived denominator is retained in the image/radical
intersection and the exact relative-head price. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {G Q H : Type} [Group G] [Group Q] [Group H]

/-- A kernel contained in the right subgroup permits this intersection
image equality; arbitrary intersection images need not be equal. -/
theorem subgroup_map_inf_eq_of_kernel_le_right
    (q : G →* Q) (K D : Subgroup G) (hker : q.ker≤D) :
    (K ⊓ D).map q=K.map q ⊓ D.map q := by
  apply le_antisymm (Subgroup.map_inf_le K D q)
  rintro x ⟨⟨a,ha,hax⟩,⟨b,hb,hbx⟩⟩
  have hab : q (a*b⁻¹)=1 := by
    rw [map_mul,map_inv,hax,hbx,mul_inv_cancel]
  have haD : a∈D := by
    have hh := D.mul_mem (hker (MonoidHom.mem_ker.mpr hab)) hb
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh
  exact ⟨a,⟨ha,haD⟩,hax⟩

/-- Only a literal source derived denominator is used in transporting
this equality to the actual image kernel. -/
theorem primeRelativeRadical_map_eq_inf_commutator_of_derived_kernel
    (p : ℕ) [Fact p.Prime] (q : G →* Q) (hq : Function.Surjective q)
    (K : Subgroup G) [K.Normal]
    (hR : primeRelativeRadical p K=K ⊓ commutator G)
    (hker : q.ker≤commutator G) :
    letI : (K.map q).Normal := Subgroup.Normal.map inferInstance q hq
    primeRelativeRadical p (K.map q)=K.map q ⊓ commutator Q := by
  letI : (K.map q).Normal := Subgroup.Normal.map inferInstance q hq
  rw [←primeRelativeRadical_map_surjective p q hq K,hR,
    subgroup_map_inf_eq_of_kernel_le_right q K (commutator G) hker]
  have hm : (commutator G).map q=commutator Q := by
    rw [map_commutator_eq,MonoidHom.range_eq_top.mpr hq]
    rfl
  rw [hm]

/-- The full order identity underlying RDT5.6(ii). No division, truncated
power, or replacement of the original normal denominator is involved. -/
theorem pGroup_derived_card_kernel_image_identity
    (p : ℕ) [Fact p.Prime] [Finite G] [Finite Q] [Finite H]
    (hG : IsPGroup p G) (q : G →* Q) (hq : Function.Surjective q)
    (K : Subgroup G) [K.Normal]
    (hR : primeRelativeRadical p K=K ⊓ commutator G)
    (hker : q.ker≤commutator G)
    (f : Q →* H) (hf : Function.Surjective f) (hfker : f.ker=K.map q) :
    p^MarkedC4.normalGen K*Nat.card (commutator Q)=
      Nat.card (K.map q)*Nat.card (commutator H) := by
  letI : (K.map q).Normal := Subgroup.Normal.map inferInstance q hq
  have hkill : K ⊓ q.ker≤primeRelativeRadical p K := by
    rw [hR]
    exact inf_le_inf le_rfl hker
  have hhead := primeRelativeHead_map_eq_of_kernel_inf_le_radical p q hq K hkill
  have hRW := primeRelativeRadical_map_eq_inf_commutator_of_derived_kernel p q hq K hR hker
  have hw := primeRelativeRadical_card_factorization p (K.map q)
  rw [hhead,←pGroup_normalGen_eq_primeRelativeHead p hG K,hRW] at hw
  have hd := subgroup_card_eq_map_mul_kernel_intersection f (commutator Q)
  have hm : (commutator Q).map f=commutator H := by
    rw [map_commutator_eq,MonoidHom.range_eq_top.mpr hf]
    rfl
  rw [hm,hfker,inf_comm] at hd
  calc
    _ = p^MarkedC4.normalGen K *
        (Nat.card (commutator H)*Nat.card (K.map q ⊓ commutator Q : Subgroup Q)) := by rw [hd]
    _ = (p^MarkedC4.normalGen K*Nat.card (K.map q ⊓ commutator Q : Subgroup Q))*
        Nat.card (commutator H) := by ring
    _ = _ := by rw [←hw]

end SymmetricSubgroupAsymptotics
