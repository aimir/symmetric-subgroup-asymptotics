import SymmetricSubgroupAsymptotics.CubicKernelSocleFromSmallActionKernel
import SymmetricSubgroupAsymptotics.DihedralEightInjectedNormalGenerators
import SymmetricSubgroupAsymptotics.NormalGeneratorAmbientEnlargement

/-! Replace the four-element kernel-card estimate by an actual D8
injection before a surjective acting-group descent. The quotient
nonprimary socle row is pulled back through the SAME acting epimorphism. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CubicKernelSocleFromDihedralActionKernel

theorem socle_two {G B L : Type} [Group G] [Group B] [Group L]
    [Finite G] [Finite B] [Finite L]
    (pi : G →* B) (hpi : Function.Surjective pi)
    (A : Rep.{0} (ZMod 3) B) [FiniteDimensional (ZMod 3) A]
    (E : OriginalKernelModuleChart pi A)
    (hu : UniformSubrepresentationGeneratorBound A.ρ 1)
    (hcop : Nat.Coprime 3 (Nat.card B))
    (f : L →* B) (hf : Function.Surjective f)
    (top : L →* DihedralGroup 4)
    (hinj : Function.Injective
      (top.comp (Representation.asGroupHom (A.ρ.comp f)).ker.subtype)) : SocleNormalGeneratorBound G 2 := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hker : IsPGroup 3 pi.ker :=
    (ZModModule.isPGroup_multiplicative (n := 3) (G := A)).of_surjective
      E.equiv.toMonoidHom E.equiv.surjective
  have hcop' : Nat.Coprime 3 (Nat.card (G ⧸ pi.ker)) := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective pi hpi).toEquiv]
    exact hcop
  have hp := E.kernel_normalGen_le pi A hpi 1 hu
    (minimalNormalSoclePart G (fun M => IsPGroup 3 M))
    (CoprimeCyclicQuotientSocles.primarySocle_le 3 pi.ker hcop')
  let H := minimalNormalSoclePart G (fun M => ¬ IsPGroup 3 M)
  have hinf : H ⊓ pi.ker=⊥ :=
    NonPrimarySocleCoprimeQuotient.nonprimarySocle_inf_kernel_eq_bot 3 pi.ker hker hcop'
  have hle : H.map pi≤A.ρ.asGroupHom.ker :=
    (Subgroup.map_mono (minimalNormalSoclePart_le_finiteGroupSocle _ _)).trans
      (E.socle_map_le_actionKernel pi A)
  letI : (H.map pi).Normal := Subgroup.Normal.map inferInstance pi hpi
  let P := (H.map pi).comap f
  let k : P →* (Representation.asGroupHom (A.ρ.comp f)).ker :=
    P.subtype.codRestrict _ (fun x => by
      change (Representation.asGroupHom (A.ρ.comp f)) (x : L)=1
      apply Units.ext
      change A.ρ (f (x : L))=1
      have hx := MonoidHom.mem_ker.mp (hle x.property)
      exact congrArg (fun u : (Module.End (ZMod 3) A)ˣ =>
        (u : Module.End (ZMod 3) A)) hx)
  have hk : Function.Injective k := by
    intro x y he
    have hv := congrArg (fun z : (Representation.asGroupHom (A.ρ.comp f)).ker =>
      (z : L)) he
    exact Subtype.ext hv
  have hPinj : Function.Injective (top.comp P.subtype) := by
    intro x y he
    apply hk
    apply hinj
    exact he
  have hP : MarkedC4.normalGen P≤2 :=
    DihedralEightInjectedNormalGenerators.normalGen_le_two P (top.comp P.subtype) hPinj
  have hmap : P.map f=H.map pi := Subgroup.map_comap_eq_self_of_surjective hf _
  have hother : MarkedC4.normalGen H≤2 := by
    apply (normalGen_le_image_of_disjoint_kernel pi hpi H hinf).trans
    letI : (P.map f).Normal := Subgroup.Normal.map inferInstance f hf
    have hm := normalGen_map_le_of_normal_image f P hP
    simpa only [hmap] using hm
  apply (socleNormalGeneratorBound_iff_normalGen_le G 2).mpr
  exact (normalGen_finiteGroupSocle_le_max_primePrimaryParts 3 G).trans
    (max_le (hp.trans (by decide : 1≤2)) hother)

end SymmetricSubgroupAsymptotics.CubicKernelSocleFromDihedralActionKernel
