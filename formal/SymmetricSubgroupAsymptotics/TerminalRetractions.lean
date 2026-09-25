import SymmetricSubgroupAsymptotics.TerminalCentralFibres

/-! Actual subgroup fibres as kernels of quotient-coefficient retractions. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

variable {X Y K : Type*} [Group X] [Group Y] [AddCommGroup K] [Module (ZMod 2) K]
    (π : X →* Y) (e : Multiplicative K ≃* π.ker)

/-- The original kernel intersection W is recorded in its fixed chart. -/
abbrev TerminalLiftFibre (W : Submodule (ZMod 2) K) :=
  {H : Subgroup X // H.map π = ⊤ ∧
    H.comap (terminalKernelInclusion π e) = W.toAddSubgroup.toSubgroup}

/-- Literal group homomorphisms extending the quotient map on the original kernel. -/
abbrev TerminalRetractionFibre (W : Submodule (ZMod 2) K) :=
  {f : Additive X →+ K ⧸ W // terminalVectorRestriction π e f = W.mkQ}

def terminalKernelQuotientHom (W : Submodule (ZMod 2) K) :
    Multiplicative K →* Multiplicative (K ⧸ W) :=
  AddMonoidHom.toMultiplicative W.mkQ.toAddMonoidHom

theorem terminalKernelQuotientHom_surjective (W : Submodule (ZMod 2) K) :
    Function.Surjective (terminalKernelQuotientHom W) := by
  intro x
  obtain ⟨k,hk⟩ := W.mkQ_surjective x.toAdd
  exact ⟨Multiplicative.ofAdd k,congrArg Multiplicative.ofAdd hk⟩

@[simp] theorem terminalKernelQuotientHom_ker (W : Submodule (ZMod 2) K) :
    (terminalKernelQuotientHom W).ker = W.toAddSubgroup.toSubgroup := by
  ext k
  change W.mkQ k.toAdd = 0 ↔ k.toAdd ∈ W
  exact Submodule.Quotient.mk_eq_zero W

/-- Full image plus a central kernel forces the whole subgroup to be normal. -/
theorem terminalLift_normal (hcentral : π.ker ≤ Subgroup.center X)
    (H : Subgroup X) (hfull : H.map π = ⊤) : H.Normal := by
  have ht : H ⊔ π.ker = ⊤ := by rw [← Subgroup.comap_map_eq,hfull,Subgroup.comap_top]
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  rw [← ht]
  exact sup_le H.le_normalizer (hcentral.trans (Subgroup.center_le_normalizer _))

omit [Module (ZMod 2) K] in
/-- Every quotient class modulo a full-image subgroup is represented by an
actual element of the original kernel. -/
theorem terminalKernelToQuotient_surjective
    (H : Subgroup X) [H.Normal] (hfull : H.map π = ⊤) :
    Function.Surjective ((QuotientGroup.mk' H).comp (terminalKernelInclusion π e)) := by
  intro z
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective H z
  have hx : π x ∈ H.map π := by rw [hfull]; trivial
  obtain ⟨h,hh,he⟩ := Subgroup.mem_map.mp hx
  have hk : x*h⁻¹ ∈ π.ker := by simp [he]
  refine ⟨e.symm ⟨x*h⁻¹,hk⟩,?_⟩
  change (QuotientGroup.mk' H) ((e (e.symm ⟨x*h⁻¹,hk⟩)).val) = _
  rw [e.apply_symm_apply]
  have hhh : (QuotientGroup.mk' H) h = 1 := (QuotientGroup.eq_one_iff h).mpr hh
  rw [map_mul,map_inv,hhh,inv_one,mul_one]

/-- The kernel of a quotient-coefficient retraction has full image and
exactly the prescribed original kernel intersection. -/
def terminalRetractionKernel (hπ : Function.Surjective π) (W : Submodule (ZMod 2) K)
    (f : TerminalRetractionFibre π e W) : TerminalLiftFibre π e W := by
  let F : X →* Multiplicative (K ⧸ W) := AddMonoidHom.toMultiplicativeRight f.1
  have hext (k : K) : F (terminalKernelInclusion π e (Multiplicative.ofAdd k)) =
      terminalKernelQuotientHom W (Multiplicative.ofAdd k) := by
    apply Multiplicative.toAdd.injective
    exact LinearMap.congr_fun f.2 k
  refine ⟨F.ker,?_,?_⟩
  · apply top_unique
    intro y _
    obtain ⟨x,hx⟩ := hπ y
    obtain ⟨k,hk⟩ := W.mkQ_surjective (F x).toAdd
    refine Subgroup.mem_map.mpr ⟨terminalKernelInclusion π e (Multiplicative.ofAdd (-k))*x,?_,?_⟩
    · change F (_*_) = 1
      rw [map_mul,hext]
      apply Multiplicative.toAdd.injective
      change W.mkQ (-k)+(F x).toAdd = 0
      rw [map_neg,hk,neg_add_cancel]
    · simpa using hx
  · ext k
    change F (terminalKernelInclusion π e k) = 1 ↔ k.toAdd ∈ W
    rw [show F (terminalKernelInclusion π e k) = terminalKernelQuotientHom W k from hext k.toAdd]
    change W.mkQ k.toAdd = 0 ↔ k.toAdd ∈ W
    exact Submodule.Quotient.mk_eq_zero W

/-- Extension maps are recovered from their actual kernels, since their
restriction to K is the fixed surjective quotient map. -/
theorem terminalRetractionKernel_injective (hπ : Function.Surjective π)
    (W : Submodule (ZMod 2) K) : Function.Injective (terminalRetractionKernel π e hπ W) := by
  intro f g h
  apply Subtype.ext
  apply AddMonoidHom.ext
  intro x
  have hker := congrArg (fun H : TerminalLiftFibre π e W => H.1) h
  change (AddMonoidHom.toMultiplicativeRight f.1).ker =
    (AddMonoidHom.toMultiplicativeRight g.1).ker at hker
  obtain ⟨k,hk⟩ := W.mkQ_surjective (f.1 x)
  have hfext := LinearMap.congr_fun f.2 (-k)
  have hgext := LinearMap.congr_fun g.2 (-k)
  have hz : terminalKernelInclusion π e (Multiplicative.ofAdd (-k))*x.toMul ∈
      (AddMonoidHom.toMultiplicativeRight f.1).ker := by
    change f.1 (Additive.ofMul (terminalKernelInclusion π e (Multiplicative.ofAdd (-k)))+x) = 0
    rw [map_add]
    change f.1 (Additive.ofMul (terminalKernelInclusion π e (Multiplicative.ofAdd (-k)))) = _ at hfext
    rw [hfext,map_neg,hk,neg_add_cancel]
  rw [hker] at hz
  change g.1 (Additive.ofMul (terminalKernelInclusion π e (Multiplicative.ofAdd (-k)))+x) = 0 at hz
  rw [map_add] at hz
  change g.1 (Additive.ofMul (terminalKernelInclusion π e (Multiplicative.ofAdd (-k)))) = _ at hgext
  rw [hgext,map_neg,hk] at hz
  exact neg_add_eq_zero.mp hz

/-- Every actual lift is the kernel of a quotient-coefficient retraction.
The map is built by descent through X/H, not postulated from a count. -/
theorem terminalRetractionKernel_surjective (hπ : Function.Surjective π)
    (hcentral : π.ker ≤ Subgroup.center X) (W : Submodule (ZMod 2) K) :
    Function.Surjective (terminalRetractionKernel π e hπ W) := by
  intro H
  letI := terminalLift_normal π hcentral H.1 H.2.1
  let F := (QuotientGroup.mk' H.1).comp (terminalKernelInclusion π e)
  have hF : Function.Surjective F := terminalKernelToQuotient_surjective π e H.1 H.2.1
  have hFker : F.ker = W.toAddSubgroup.toSubgroup := by
    rw [← MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact H.2.2
  let a : X ⧸ H.1 →* Multiplicative (K ⧸ W) :=
    F.liftOfSurjective hF ⟨terminalKernelQuotientHom W,by rw [hFker,terminalKernelQuotientHom_ker]⟩
  have ha (k : Multiplicative K) : a (F k) = terminalKernelQuotientHom W k := by
    exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ k
  let f : Additive X →+ K ⧸ W :=
    MonoidHom.toAdditiveLeft (a.comp (QuotientGroup.mk' H.1))
  have hf : terminalVectorRestriction π e f = W.mkQ := by
    ext k
    exact congrArg Multiplicative.toAdd (ha (Multiplicative.ofAdd k))
  refine ⟨⟨f,hf⟩,Subtype.ext ?_⟩
  ext x
  change a ((QuotientGroup.mk' H.1) x) = 1 ↔ x ∈ H.1
  constructor
  · intro hx
    obtain ⟨k,hk⟩ := hF ((QuotientGroup.mk' H.1) x)
    have hk0 : terminalKernelQuotientHom W k = 1 := by rw [← ha,hk]; exact hx
    have hkm : k ∈ F.ker := by
      rw [hFker,← terminalKernelQuotientHom_ker W]
      exact hk0
    have hx0 : (QuotientGroup.mk' H.1) x = 1 := hk.symm.trans hkm
    exact (QuotientGroup.eq_one_iff x).mp hx0
  · intro hx
    rw [show (QuotientGroup.mk' H.1) x = 1 from (QuotientGroup.eq_one_iff x).mpr hx,map_one]

/-- Exact equivalence of fixed-intersection actual subgroups and their
quotient-coefficient retractions. -/
def terminalRetractionEquiv (hπ : Function.Surjective π)
    (hcentral : π.ker ≤ Subgroup.center X) (W : Submodule (ZMod 2) K) :
    TerminalRetractionFibre π e W ≃ TerminalLiftFibre π e W :=
  Equiv.ofBijective (terminalRetractionKernel π e hπ W)
    ⟨terminalRetractionKernel_injective π e hπ W,
      terminalRetractionKernel_surjective π e hπ hcentral W⟩

/-- Exact existence criterion retaining W's actual annihilator. -/
theorem terminalLiftFibre_nonempty_iff (hπ : Function.Surjective π)
    (hcentral : π.ker ≤ Subgroup.center X) [FiniteDimensional (ZMod 2) K]
    (W : Submodule (ZMod 2) K) :
    Nonempty (TerminalLiftFibre π e W) ↔
      W.dualAnnihilator ≤ terminalSplittingAnnihilator π e := by
  rw [← (terminalRetractionEquiv π e hπ hcentral W).nonempty_congr]
  rw [nonempty_subtype]
  change (∃ f, terminalVectorRestriction π e f = W.mkQ) ↔ _
  exact terminalKernelQuotientExtension_iff_annihilator π e W

end SymmetricSubgroupAsymptotics
