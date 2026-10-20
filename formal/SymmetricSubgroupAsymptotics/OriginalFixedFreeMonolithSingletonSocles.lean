import SymmetricSubgroupAsymptotics.OriginalKernelMonolithicSocleCoinvariance
import SymmetricSubgroupAsymptotics.OriginalKernelElementaryChart
import SymmetricSubgroupAsymptotics.OriginalKernelSectionUniform
import SymmetricSubgroupAsymptotics.NormalGeneratorQuotientSocles
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalFixedFreeMonolithSingletonSocles
open OriginalKernelModuleChart

theorem quotientSocle {G B : Type} [Group G] [Finite G] [Group B] [Finite B]
    (pi : G →* B) (hpi : Function.Surjective pi)
    (A : Rep.{0} (ZMod 2) B) [FiniteDimensional (ZMod 2) A] (E : OriginalKernelModuleChart pi A)
    (hA : UniformSubrepresentationGeneratorBound A.ρ 1)
    (O : Subgroup B) [Finite O] [NeZero (Nat.card O : ZMod 2)]
    (hmono : ∀ D : Subgroup B,D.Normal → D≠⊥ → O≤D)
    (hfixed : ∀ v : A,(∀ o : O,A.ρ (o : B) v=v) → v=0)
    (hB : ∀ D : Subgroup B,D.Normal →
      ∃ x : Fin 1 → B,Subgroup.normalClosure (Set.range x)=D)
    (N : Subgroup G) [N.Normal] : SocleNormalGeneratorBound (G ⧸ N) 1 := by
  letI : FiniteDimensional (ZMod 2) (E.sectionRepresentation pi A N) := by
    change FiniteDimensional (ZMod 2) (E.sectionModule pi A N)
    infer_instance
  rcases E.retained_monolith_coinvariance pi A N hpi O hmono with hinside | hkill
  · apply (socleNormalGeneratorBound_iff_normalGen_le (G ⧸ N) 1).mpr
    exact (E.quotientChart pi A N).kernel_normalGen_le (base pi N)
      (E.sectionRepresentation pi A N) (base_surjective pi N) 1
      (E.sectionUniform pi A N hpi hA) _ hinside
  have hzero (v : E.sectionModule pi A N) : v=0 := by
    apply E.sectionFixedFreeOnOdd pi A N hpi O hfixed v
    intro o
    have ho := MonoidHom.mem_ker.mp (hkill o.property)
    have hv := congrArg (fun f : (Module.End (ZMod 2) (E.sectionModule pi A N))ˣ =>
      (f : Module.End (ZMod 2) (E.sectionModule pi A N)) v) ho
    exact hv
  have hinj : Function.Injective (base pi N) := by
    apply (base pi N).ker_eq_bot_iff.mp
    apply le_antisymm ?_ bot_le
    intro q hq
    obtain ⟨a,ha⟩ := (E.kernelEquiv pi A N).surjective ⟨q,hq⟩
    have ha1 : a=1 := Multiplicative.toAdd.injective (hzero a.toAdd)
    rw [ha1,map_one] at ha
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val ha.symm)
  let e := MulEquiv.ofBijective (base pi N) ⟨hinj,base_surjective pi N⟩
  have hs : Function.Surjective (sectionTop pi N hpi) := by
    intro y
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (pi.ker ⊔ N) y
    exact ⟨pi g,sectionTop_apply pi N hpi g⟩
  have hd := normal_generating_tuples_of_surjective (sectionTop pi N hpi) hs hB
  have hq := normal_generating_tuples_of_surjective e.symm.toMonoidHom e.symm.surjective hd
  exact hq (finiteGroupSocle (G ⧸ N)) inferInstance
end SymmetricSubgroupAsymptotics.OriginalFixedFreeMonolithSingletonSocles
