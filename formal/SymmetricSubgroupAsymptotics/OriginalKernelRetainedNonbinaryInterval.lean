import SymmetricSubgroupAsymptotics.OriginalKernelSectionOddRestriction

/-! Killing the odd layer in an actual binary residual linear quotient
also kills its fixed-free translation section. Therefore every original
axis below the retained odd preimage has a NONBINARY residual linear top.
This leaves all binary quotients to the single retained comparator. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
variable {G B : Type} [Group G] [Group B]
  (pi : G →* B) (A : Rep.{0} (ZMod 2) B) (E : OriginalKernelModuleChart pi A)
  (N : Subgroup G) [N.Normal]

include E in
theorem retained_linear_nonbinary (hpi : Function.Surjective pi)
    (O : Subgroup B) [Finite O] [NeZero (Nat.card O : ZMod 2)]
    (hcubic : ∀ o : O, o^3=1)
    (hfixed : ∀ a : A, (∀ o : O, A.ρ (o : B) a=a) → a=0)
    (hnot : ¬ O.comap pi≤N) : ¬ IsPGroup 2 (G ⧸ (pi.ker ⊔ N)) := by
  intro hbinary
  have htopzero (o : O) : sectionTop pi N hpi (o : B)=1 := by
    apply (hbinary.powEquiv (by decide : Nat.Coprime 2 3)).injective
    have ho : (o : B)^3=1 := congrArg (fun z : O => (z : B)) (hcubic o)
    have hc := congrArg (sectionTop pi N hpi) ho
    simpa only [IsPGroup.powEquiv_apply,map_pow,map_one,one_pow] using hc
  have hsectionzero (v : E.sectionModule pi A N) : v=0 := by
    apply E.sectionFixedFreeOnOdd pi A N hpi O hfixed v
    intro o
    rw [htopzero o,map_one]
    rfl
  have hinj : Function.Injective (base pi N) := by
    apply (base pi N).ker_eq_bot_iff.mp
    apply le_antisymm ?_ bot_le
    intro q hq
    obtain ⟨a,ha⟩ := (E.kernelEquiv pi A N).surjective ⟨q,hq⟩
    have ha1 : a=1 := Multiplicative.toAdd.injective (hsectionzero a.toAdd)
    rw [ha1,map_one] at ha
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val ha.symm)
  apply hnot
  intro g hg
  apply (QuotientGroup.eq_one_iff g).mp
  apply hinj
  rw [map_one]
  change QuotientGroup.mk' (pi.ker ⊔ N) g=1
  have he := htopzero (⟨pi g,hg⟩ : O)
  rw [sectionTop_apply] at he
  exact he

end SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
