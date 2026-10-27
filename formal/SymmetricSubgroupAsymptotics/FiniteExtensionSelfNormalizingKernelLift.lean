import SymmetricSubgroupAsymptotics.SimplePowerSubdirectSelfNormalizer

/-! At a fixed kernel that is self-normalizing inside the ambient kernel,
there is at most one full-image subgroup. This counts whole lift fibres,
without a splitting hypothesis or an assumed extension class. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.FiniteExtensionSelfNormalizingKernelLift

variable {E Q : Type} [Group E] [Group Q]

theorem le_normalizer_of_intersection_kernel (π : E →* Q)
    (L K : Subgroup E) (hK : L⊓π.ker=K) :
    L≤Subgroup.normalizer (K : Set E) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro l hl k hk
  rw [←hK] at hk ⊢
  refine ⟨L.mul_mem (L.mul_mem hl hk.1) (L.inv_mem hl),?_⟩
  change π (l*k*l⁻¹)=1
  rw [map_mul,map_mul,map_inv,show π k=1 from hk.2,mul_one,mul_inv_cancel]

theorem eq_of_self_normalizing_intersection (π : E →* Q)
    (K L M : Subgroup E)
    (hL : L.map π=⊤) (hM : M.map π=⊤)
    (hLK : L⊓π.ker=K) (hMK : M⊓π.ker=K)
    (hself : ∀ g : E,g∈π.ker → g∈Subgroup.normalizer (K : Set E) → g∈K) : L=M := by
  have hLN := le_normalizer_of_intersection_kernel π L K hLK
  have hMN := le_normalizer_of_intersection_kernel π M K hMK
  have hle (A B : Subgroup E) (hB : B.map π=⊤)
      (hAK : A⊓π.ker=K) (hBK : B⊓π.ker=K)
      (hAN : A≤Subgroup.normalizer (K : Set E))
      (hBN : B≤Subgroup.normalizer (K : Set E)) : A≤B := by
    intro a ha
    have hpa : π a∈B.map π := by rw [hB]; trivial
    obtain ⟨b,hb,he⟩ := hpa
    have hd : a*b⁻¹∈π.ker := by
      change π (a*b⁻¹)=1
      rw [map_mul,map_inv,he,mul_inv_cancel]
    have hdN : a*b⁻¹∈Subgroup.normalizer (K : Set E) :=
      (Subgroup.normalizer (K : Set E)).mul_mem (hAN ha)
        ((Subgroup.normalizer (K : Set E)).inv_mem (hBN hb))
    have hdK := hself (a*b⁻¹) hd hdN
    have hdB : a*b⁻¹∈B := by rw [←hBK] at hdK; exact hdK.1
    have hh := B.mul_mem hdB hb
    simpa only [inv_mul_cancel_right] using hh
  exact le_antisymm (hle L M hM hLK hMK hLN hMN) (hle M L hL hMK hLK hMN hLN)

theorem subsingleton_fullImage_fixedKernel (π : E →* Q) (K : Subgroup E)
    (hself : ∀ g : E,g∈π.ker → g∈Subgroup.normalizer (K : Set E) → g∈K) :
    Subsingleton {L : Subgroup E // L.map π=⊤ ∧ L⊓π.ker=K} := by
  constructor
  intro L M
  exact Subtype.ext (eq_of_self_normalizing_intersection π K L.val M.val
    L.property.1 M.property.1 L.property.2 M.property.2 hself)

end SymmetricSubgroupAsymptotics.FiniteExtensionSelfNormalizingKernelLift
