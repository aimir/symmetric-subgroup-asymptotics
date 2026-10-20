import SymmetricSubgroupAsymptotics.PGroupKernelCentralMonolith
import SymmetricSubgroupAsymptotics.NaturalA4ScalarFourHead

/-! In a binary-by-C3 group, a noncentral minimal normal containing the
binary kernel's center is the actual monolith. No normal lattice is listed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

private theorem cubic_nonidentity_powers : ∀ (u t : CyclicThree), u≠1 →
    ∃ r : Fin 3, u^r.val=t := by decide +kernel

theorem normal_cover_of_cubic_kernel_central_monolith
    {G : Type} [Group G] [Finite G]
    (pi : G →* CyclicThree) (hK : IsPGroup 2 pi.ker)
    (D : Subgroup G) (hD : IsMinimalNormalSubgroup D) (hDK : D≤pi.ker)
    (hcenter : ∀ x : pi.ker, x∈Subgroup.center pi.ker → (x : G)∈D)
    (hnoncentral : ∃ a d : G, d∈D ∧ a*d≠d*a)
    (N : Subgroup G) (hN : N.Normal) (hne : N≠⊥) : D≤N := by
  letI : D.Normal := hD.1
  have hKne : pi.ker≠⊥ := by
    intro hb
    exact hD.2.1 (le_antisymm (hDK.trans hb.le) bot_le)
  letI : Nontrivial pi.ker := (Subgroup.nontrivial_iff_ne_bot pi.ker).mpr hKne
  let Z : Subgroup G := (Subgroup.center pi.ker).map pi.ker.subtype
  letI : Z.Normal := by dsimp only [Z]; infer_instance
  have hZne : Z≠⊥ := by
    letI : Nontrivial (Subgroup.center pi.ker) := hK.center_nontrivial
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    obtain ⟨z,hz⟩ := exists_ne (1 : Subgroup.center pi.ker)
    refine ⟨⟨(z.1.1 : G),⟨z.1,z.2,rfl⟩⟩,?_⟩
    intro hz1
    apply hz
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun q : Z => (q.1 : G)) hz1
  have hZD : Z≤D := by
    rintro _ ⟨x,hx,rfl⟩
    exact hcenter x hx
  have hZe : Z=D := hD.2.2 Z inferInstance hZne hZD
  have hdcomm : ∀ d∈D, ∀ k∈pi.ker, Commute d k := by
    intro d hd k hk
    have hdz : d∈Z := hZe.symm ▸ hd
    obtain ⟨x,hx,hxd⟩ := hdz
    rw [←hxd]
    exact (congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hx (⟨k,hk⟩ : pi.ker))).symm
  have hcentralizer : Subgroup.centralizer (pi.ker : Set G)≤pi.ker := by
    intro c hc
    by_contra hcK
    have hcp : pi c≠1 := hcK
    have hglobal : ∀ g : G, ∀ d∈D, Commute d g := by
      intro g d hd
      obtain ⟨r,hr⟩ := cubic_nonidentity_powers (pi c) (pi g) hcp
      let k := (c^r.val)⁻¹*g
      have hk : k∈pi.ker := by
        change pi ((c^r.val)⁻¹*g)=1
        rw [map_mul,map_inv,map_pow,hr,inv_mul_cancel]
      have hdc : Commute d c := Subgroup.mem_centralizer_iff.mp hc d (hDK hd)
      have hdk : Commute d k := hdcomm d hd k hk
      have he : g=c^r.val*k := by dsimp only [k]; simp
      rw [he]
      exact (hdc.pow_right r.val).mul_right hdk
    obtain ⟨a,d,hd,had⟩ := hnoncentral
    exact had (hglobal a d hd).eq.symm
  exact normal_cover_of_pGroup_kernel_central_monolith 2 pi.ker D hK hcentralizer hcenter hD N hN hne

end SymmetricSubgroupAsymptotics
