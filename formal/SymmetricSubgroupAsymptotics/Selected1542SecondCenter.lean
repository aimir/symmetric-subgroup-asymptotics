import SymmetricSubgroupAsymptotics.Selected1542SecondCenterRows
import SymmetricSubgroupAsymptotics.Selected1542SchreierBridge
import SymmetricSubgroupAsymptotics.Selected1542FirstQuotient

/-! Sparse inverse-free point witnesses exclude every actual original
kernel coset outside N8 from the center modulo the same original Z2. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1542QuotientStructure

private theorem mkFirst_eq_or (a b : Original)
    (hab : QuotientGroup.mk' originalFirstAxis a=QuotientGroup.mk' originalFirstAxis b) :
    a=b ∨ a=originalCentralInvolution*b := by
  have h : QuotientGroup.mk' originalFirstAxis (a*b⁻¹)=1 := by
    rw [map_mul,map_inv,hab,mul_inv_cancel]
  rcases (mkFirst_eq_one_iff _).mp h with h | h
  · exact Or.inl (mul_inv_eq_one.mp h)
  · exact Or.inr (mul_inv_eq_iff_eq_mul.mp h)

theorem original_kernel_center_mod_firstAxis (g : Original) (hg : g∈originalBinaryKernel)
    (hcomm : ∀ k : Original, k∈originalBinaryKernel →
      QuotientGroup.mk' originalFirstAxis g*QuotientGroup.mk' originalFirstAxis k=
        QuotientGroup.mk' originalFirstAxis k*QuotientGroup.mk' originalFirstAxis g) :
    g∈originalNormal := by
  obtain ⟨r,i,hgri⟩ := original_binary_kernel_grid g hg
  let index : Fin 1024 := (finProdFinEquiv : Fin 16 × Fin 64 ≃ Fin 1024) (r,i)
  have hgrid : g.val=secondCenterGrid index :=
    (congrArg Subtype.val hgri).trans (original_kernel_grid_val r i)
  have hrow := secondCenter_all_rows index
  cases hflag : secondCenterInNormal index with
  | true =>
    obtain ⟨n,hn⟩ := hrow.1 hflag
    have he : g=normalOriginal n := by
      apply Subtype.ext
      apply Equiv.ext
      intro p
      exact (congrArg (fun q : Equiv.Perm (Fin 16) => q p) hgrid).trans (hn p)
    rw [he]
    exact (normalTable.chart n).property
  | false =>
    obtain ⟨⟨p,hp⟩,⟨q,hq⟩⟩ := hrow.2 hflag
    let k : Original := firstCenterOriginalGenerator (secondCenterWitness index)
    have hk : k∈originalBinaryKernel := firstCenterOriginalGenerator_mem _
    have hkv : k.val=secondCenterSchreier (secondCenterWitness index) :=
      (firstCenterOriginalGenerator_val _).trans (secondCenterSchreier_eq _).symm
    have he := mkFirst_eq_or (g*k) (k*g) (by simpa only [map_mul] using hcomm k hk)
    rcases he with he | he
    · have hv := congrArg Subtype.val he
      change g.val*k.val=k.val*g.val at hv
      rw [hgrid,hkv] at hv
      exact False.elim (hp (congrArg (fun t : Equiv.Perm (Fin 16) => t p) hv))
    · have hv := congrArg Subtype.val he
      change g.val*k.val=firstCenterZ*(k.val*g.val) at hv
      have hv' : g.val*k.val=secondCenterZ*k.val*g.val := by
        simpa only [secondCenterZ_eq,mul_assoc] using hv
      rw [hgrid,hkv] at hv'
      exact False.elim (hq (congrArg (fun t : Equiv.Perm (Fin 16) => t q) hv'))

theorem firstQuotient_kernel_center_le_secondAxis
    (x : firstQuotientBinaryKernel) (hx : x∈Subgroup.center firstQuotientBinaryKernel) :
    (x : FirstQuotient)∈secondAxis := by
  have hxmap : (x : FirstQuotient)∈originalBinaryKernel.map (QuotientGroup.mk' originalFirstAxis) := by
    rw [←firstQuotientBinaryKernel_image]
    exact x.property
  obtain ⟨g,hg,hgx⟩ := hxmap
  have hc : ∀ k : Original, k∈originalBinaryKernel →
      QuotientGroup.mk' originalFirstAxis g*QuotientGroup.mk' originalFirstAxis k=
        QuotientGroup.mk' originalFirstAxis k*QuotientGroup.mk' originalFirstAxis g := by
    intro k hk
    let y : FirstQuotient := QuotientGroup.mk' originalFirstAxis k
    let xg : FirstQuotient := QuotientGroup.mk' originalFirstAxis g
    have hkm : y∈firstQuotientBinaryKernel := by
      rw [firstQuotientBinaryKernel_image]
      exact ⟨k,hk,rfl⟩
    have he := congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hx (⟨y,hkm⟩ : firstQuotientBinaryKernel))
    change y*(x : FirstQuotient)=(x : FirstQuotient)*y at he
    have hxg : xg=(x : FirstQuotient) := hgx
    change xg*y=y*xg
    rw [hxg]
    exact he.symm
  exact ⟨g,original_kernel_center_mod_firstAxis g hg hc,hgx⟩

end SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
