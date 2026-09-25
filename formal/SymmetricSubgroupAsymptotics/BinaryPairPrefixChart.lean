import SymmetricSubgroupAsymptotics.BinaryPairCertificateCapacity
import SymmetricSubgroupAsymptotics.FusionCentralPrefix

/-! The actual quotient tower attached to a literal physical pair certificate.
The first quotient starts on U/N and kills exactly the image of its retained
cut. The second ends at the original U/(K∨N); no extension is split. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics

/-- Two onto charts with the same literal kernel identify their actual targets. -/
def binaryPair_sameKernelEquiv {G A B : Type*} [Group G] [Group A] [Group B]
    (f : G →* A) (g : G →* B) (hf : Function.Surjective f)
    (hg : Function.Surjective g) (hk : f.ker = g.ker) : A ≃* B :=
  (QuotientGroup.liftEquiv f.ker hf rfl).symm.trans
    (QuotientGroup.liftEquiv f.ker hg hk)

@[simp] theorem binaryPair_sameKernelEquiv_apply {G A B : Type*}
    [Group G] [Group A] [Group B] (f : G →* A) (g : G →* B)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hk : f.ker = g.ker) (x : G) :
    binaryPair_sameKernelEquiv f g hf hg hk (f x) = g x := by
  change (QuotientGroup.liftEquiv f.ker hg hk)
    ((QuotientGroup.liftEquiv f.ker hf rfl).symm (f x)) = _
  rw [← QuotientGroup.liftEquiv_mk f.ker hf rfl x, MulEquiv.symm_apply_apply]
  rfl

namespace BinaryPairLocalCertificate
variable {X I ι : Type} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U I) (N : Subgroup U) [N.Normal]
    (generators : ι → U) (hgen : Subgroup.closure (Set.range generators) = ⊤)
    (C : BinaryPairLocalCertificate generators F.top N)

/-- The original cut image in the original quotient. -/
def prefixCut : Subgroup (U ⧸ N) := C.cut.map (QuotientGroup.mk' N)

instance prefixCut_normal : (C.prefixCut (F := F) (N := N) (generators := generators)).Normal :=
  Subgroup.Normal.map C.cut_normal _ (QuotientGroup.mk'_surjective N)

def prefixFirst : (U ⧸ N) →* (U ⧸ N) ⧸ C.prefixCut (F := F) (N := N) (generators := generators) :=
  QuotientGroup.mk' (C.prefixCut (F := F) (N := N) (generators := generators))

def prefixOriginal : U →* (U ⧸ N) ⧸ C.prefixCut (F := F) (N := N) (generators := generators) :=
  (C.prefixFirst (F := F) (N := N) (generators := generators)).comp (QuotientGroup.mk' N)

theorem prefixOriginal_surjective : Function.Surjective (C.prefixOriginal (F := F) (N := N) (generators := generators)) :=
  (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective N)

theorem prefixOriginal_ker : (C.prefixOriginal (F := F) (N := N) (generators := generators)).ker = N ⊔ C.cut := by
  rw [prefixOriginal, ← MonoidHom.comap_ker, prefixFirst, QuotientGroup.ker_mk',
    prefixCut, QuotientGroup.comap_map_mk']

include hgen in
theorem prefixCut_central : C.prefixCut (F := F) (N := N) (generators := generators) ≤ Subgroup.center (U ⧸ N) := by
  rintro q ⟨c,hc,rfl⟩
  rw [binaryPair_quotient_center_iff N generators hgen]
  exact fun j => C.central j ⟨c,hc⟩

include hgen in
theorem prefixFirst_central : FusionCentralKernel (C.prefixFirst (F := F) (N := N) (generators := generators)) :=
  fusionCentralKernel_quotient _ (C.prefixCut_central (F := F) (N := N) (generators := generators) (hgen := hgen))

def prefixBaseBefore : (U ⧸ N) →* U ⧸ (F.top.ker ⊔ N) :=
  QuotientGroup.lift N (QuotientGroup.mk' (F.top.ker ⊔ N)) (by
    rw [QuotientGroup.ker_mk']; exact le_sup_right)

def prefixBase : ((U ⧸ N) ⧸ C.prefixCut (F := F) (N := N) (generators := generators)) →* U ⧸ (F.top.ker ⊔ N) :=
  QuotientGroup.lift (C.prefixCut (F := F) (N := N) (generators := generators)) (prefixBaseBefore F N) (by
    rintro q ⟨c,hc,rfl⟩
    change QuotientGroup.mk' (F.top.ker ⊔ N) c = 1
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_sup_left (C.cut_le_kernel hc)))

@[simp] theorem prefixBase_original (u : U) :
    C.prefixBase (F := F) (N := N) (generators := generators) (C.prefixOriginal (F := F) (N := N) (generators := generators) u) = QuotientGroup.mk' (F.top.ker ⊔ N) u := rfl

theorem prefixBase_surjective : Function.Surjective (C.prefixBase (F := F) (N := N) (generators := generators)) := by
  intro b
  obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (F.top.ker ⊔ N) b
  exact ⟨C.prefixOriginal (F := F) (N := N) (generators := generators) u,rfl⟩

/-- The actual original pair kernel maps onto the second extension kernel. -/
def prefixKernelMap : F.top.ker →* (C.prefixBase (F := F) (N := N) (generators := generators)).ker where
  toFun k := ⟨C.prefixOriginal (F := F) (N := N) (generators := generators) (k:U), by
    rw [MonoidHom.mem_ker, C.prefixBase_original (F := F) (N := N) (generators := generators)]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_sup_left k.property)⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' a b := by apply Subtype.ext; exact map_mul _ _ _

theorem prefixKernelMap_surjective : Function.Surjective (C.prefixKernelMap (F := F) (N := N) (generators := generators)) := by
  intro r
  obtain ⟨u,hu⟩ := C.prefixOriginal_surjective (F := F) (N := N) (generators := generators) r.val
  have hub : QuotientGroup.mk' (F.top.ker ⊔ N) u = 1 := by
    rw [← C.prefixBase_original (F := F) (N := N) (generators := generators), hu]
    exact r.property
  obtain ⟨k,hk,n,hn,hkn⟩ := Subgroup.mem_sup_of_normal_right.mp
    ((QuotientGroup.eq_one_iff _).mp hub)
  refine ⟨⟨k,hk⟩,?_⟩
  apply Subtype.ext
  change C.prefixOriginal (F := F) (N := N) (generators := generators) k = r.val
  rw [←hu,←hkn,map_mul]
  have hn0 : C.prefixOriginal (F := F) (N := N) (generators := generators) n = 1 := by
    change C.prefixFirst (F := F) (N := N) (generators := generators) (QuotientGroup.mk' N n)=1
    have hnq : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff _).mpr hn
    rw [hnq,map_one]
  rw [hn0,mul_one]

theorem prefixKernelMap_ker : (C.prefixKernelMap (F := F) (N := N) (generators := generators)).ker = C.kernelCut F := by
  ext k
  rw [MonoidHom.mem_ker, Subtype.ext_iff]
  change C.prefixOriginal (F := F) (N := N) (generators := generators) (k:U)=1 ↔ (k:U)∈C.cut
  rw [←MonoidHom.mem_ker,C.prefixOriginal_ker (F := F) (N := N) (generators := generators)]
  constructor
  · intro h
    obtain ⟨n,hn,c,hc,he⟩ := Subgroup.mem_sup_of_normal_left.mp h
    have hnK : n∈F.top.ker := by
      have he' : n=(k:U)*c⁻¹ := (eq_mul_inv_iff_mul_eq).mpr he
      rw [he']
      exact F.top.ker.mul_mem k.property (F.top.ker.inv_mem (C.cut_le_kernel hc))
    rw [←he]
    exact C.cut.mul_mem (C.intersection_le_cut ⟨hnK,hn⟩) hc
  · intro hk
    exact Subgroup.mem_sup_right hk

/-- The exact second kernel, in the unchanged physical representation chart. -/
def prefixModule : Rep (ZMod 2) (U ⧸ (F.top.ker ⊔ N)) :=
  Rep.of (C.physicalRepresentation F N generators hgen)

def prefixKernelEquiv : Multiplicative (C.prefixModule (F := F) (N := N) (generators := generators) (hgen := hgen)) ≃*
    (C.prefixBase (F := F) (N := N) (generators := generators)).ker :=
  binaryPair_sameKernelEquiv
    (sectionSubgroupCutMap (p := 2) (F.sectionMap N) (C.kernelCut F))
    (C.prefixKernelMap (F := F) (N := N) (generators := generators))
    (sectionSubgroupCutMap_surjective (F.sectionMap N) (F.sectionMap_surjective N) _)
    (C.prefixKernelMap_surjective (F := F) (N := N) (generators := generators)) (by
      rw [sectionSubgroupCutMap_ker _ _ (C.sectionKernel_le F N),C.prefixKernelMap_ker (F := F) (N := N) (generators := generators)])

@[simp] theorem prefixKernelEquiv_apply (k : F.top.ker) :
    C.prefixKernelEquiv (F := F) (N := N) (generators := generators) (hgen := hgen)
      (sectionSubgroupCutMap (p := 2) (F.sectionMap N) (C.kernelCut F) k) =
    C.prefixKernelMap (F := F) (N := N) (generators := generators) k :=
  binaryPair_sameKernelEquiv_apply _ _ _ _ _ k

def prefixModuleChart : OriginalKernelModuleChart (C.prefixBase (F := F) (N := N) (generators := generators))
    (C.prefixModule (F := F) (N := N) (generators := generators) (hgen := hgen)) where
  equiv := C.prefixKernelEquiv (F := F) (N := N) (generators := generators) (hgen := hgen)
  conjugate r a := by
    obtain ⟨u,rfl⟩ := C.prefixOriginal_surjective (F := F) (N := N) (generators := generators) r
    obtain ⟨k,hk⟩ := sectionSubgroupCutMap_surjective (F.sectionMap N)
      (F.sectionMap_surjective N) (C.kernelCut F) (Multiplicative.ofAdd a)
    have ha : (sectionSubgroupCutMap (p := 2) (F.sectionMap N) (C.kernelCut F) k).toAdd=a :=
      congrArg Multiplicative.toAdd hk
    rw [←ha,C.prefixBase_original (F := F) (N := N) (generators := generators)]
    change (C.prefixKernelEquiv (F := F) (N := N) (generators := generators) (hgen := hgen) (Multiplicative.ofAdd
      (C.physicalRepresentation F N generators hgen _ _)) :
        (U ⧸ N) ⧸ C.prefixCut (F := F) (N := N) (generators := generators)) = _
    unfold physicalRepresentation
    rw [BinaryPairFrame.originalCutRepresentation_apply]
    have he (l : F.top.ker) :
        (C.prefixKernelEquiv (F := F) (N := N) (generators := generators) (hgen := hgen)
          (sectionSubgroupCutMap (p := 2) (F.sectionMap N) (C.kernelCut F) l) :
            (U ⧸ N) ⧸ C.prefixCut (F := F) (N := N) (generators := generators)) =
        C.prefixOriginal (F := F) (N := N) (generators := generators) (l:U) :=
      congrArg Subtype.val (C.prefixKernelEquiv_apply (F := F) (N := N)
        (generators := generators) (hgen := hgen) l)
    calc
      _ = C.prefixOriginal (F := F) (N := N) (generators := generators)
          (MulAut.conjNormal u k : U) := he (MulAut.conjNormal u k)
      _ = C.prefixOriginal (F := F) (N := N) (generators := generators) u *
          C.prefixOriginal (F := F) (N := N) (generators := generators) (k:U) *
          (C.prefixOriginal (F := F) (N := N) (generators := generators) u)⁻¹ := by
        change C.prefixOriginal (F := F) (N := N) (generators := generators) (u*(k:U)*u⁻¹)=_
        simp only [map_mul,map_inv]
      _ = _ := congrArg (fun z : (U ⧸ N) ⧸ C.prefixCut (F := F) (N := N) (generators := generators) =>
        C.prefixOriginal (F := F) (N := N) (generators := generators) u * z *
          (C.prefixOriginal (F := F) (N := N) (generators := generators) u)⁻¹) (he k).symm

/-- The retained central vector space, not a numerical replacement. -/
def prefixCutSpace := sectionSubgroupImage (p := 2) (F.sectionMap N) (C.kernelCut F)

def prefixCutVectorMap : C.kernelCut F →* Multiplicative (C.prefixCutSpace (F := F) (N := N) (generators := generators)) where
  toFun l := Multiplicative.ofAdd ⟨(F.sectionMap N (l:F.top.ker)).toAdd,
    ⟨Additive.ofMul l,rfl⟩⟩
  map_one' := by
    apply congrArg Multiplicative.ofAdd
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (map_one (F.sectionMap N))
  map_mul' a b := by
    apply congrArg Multiplicative.ofAdd
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (map_mul (F.sectionMap N) _ _)

omit [N.Normal] in
theorem prefixCutVectorMap_surjective : Function.Surjective (C.prefixCutVectorMap (F := F) (N := N) (generators := generators)) := by
  intro a
  obtain ⟨l,hl⟩ := a.toAdd.property
  refine ⟨l.toMul,?_⟩
  apply congrArg Multiplicative.ofAdd
  exact Subtype.ext hl

def prefixCutImageMap : C.kernelCut F →* C.prefixCut (F := F) (N := N) (generators := generators) where
  toFun l := ⟨QuotientGroup.mk' N ((l:F.top.ker):U),
    ⟨((l:F.top.ker):U),l.property,rfl⟩⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' a b := by apply Subtype.ext; exact map_mul _ _ _

theorem prefixCutImageMap_surjective : Function.Surjective (C.prefixCutImageMap (F := F) (N := N) (generators := generators)) := by
  rintro ⟨q,c,hc,rfl⟩
  exact ⟨⟨⟨c,C.cut_le_kernel hc⟩,hc⟩,rfl⟩

theorem prefixCutVectorMap_ker :
    (C.prefixCutVectorMap (F := F) (N := N) (generators := generators)).ker = (C.prefixCutImageMap (F := F) (N := N) (generators := generators)).ker := by
  ext l
  change C.prefixCutVectorMap (F := F) (N := N) (generators := generators) l=1 ↔ C.prefixCutImageMap (F := F) (N := N) (generators := generators) l=1
  constructor
  · intro h
    have hv := congrArg (fun a : Multiplicative (C.prefixCutSpace (F := F) (N := N) (generators := generators)) => a.toAdd.val) h
    have hq : F.sectionMap N (l:F.top.ker)=1 := congrArg Multiplicative.ofAdd hv
    have hn : (l:F.top.ker)∈N.subgroupOf F.top.ker := by
      rw [←F.sectionMap_ker N]
      exact hq
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff _).mpr hn
  · intro h
    have hn : ((l:F.top.ker):U)∈N :=
      (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h)
    have hq : F.sectionMap N (l:F.top.ker)=1 := by
      change (l:F.top.ker)∈(F.sectionMap N).ker
      rw [F.sectionMap_ker N]
      exact hn
    apply congrArg Multiplicative.ofAdd
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd hq

def prefixCentralEquiv : (C.prefixFirst (F := F) (N := N) (generators := generators)).ker ≃* Multiplicative (C.prefixCutSpace (F := F) (N := N) (generators := generators)) :=
  (MulEquiv.subgroupCongr (QuotientGroup.ker_mk' (C.prefixCut (F := F) (N := N) (generators := generators)))).trans
    (binaryPair_sameKernelEquiv (C.prefixCutVectorMap (F := F) (N := N) (generators := generators)) (C.prefixCutImageMap (F := F) (N := N) (generators := generators))
      (C.prefixCutVectorMap_surjective (F := F) (N := N) (generators := generators)) (C.prefixCutImageMap_surjective (F := F) (N := N) (generators := generators))
      (C.prefixCutVectorMap_ker (F := F) (N := N) (generators := generators))).symm

/-- The original cover descends faithfully through its exact recorded kernel. -/
def prefixCover : (U ⧸ (F.top.ker ⊔ N)) →* Equiv.Perm (Fin C.coverDegree) :=
  QuotientGroup.lift (F.top.ker ⊔ N) C.cover C.cover_kernel.symm.le

theorem prefixCover_injective : Function.Injective (C.prefixCover (F := F) (N := N) (generators := generators)) := by
  rw [←MonoidHom.ker_eq_bot_iff,prefixCover,QuotientGroup.ker_lift,C.cover_kernel,
    QuotientGroup.map_mk'_self]

@[simp] theorem prefixCover_original (u : U) :
    C.prefixCover (F := F) (N := N) (generators := generators) (QuotientGroup.mk' (F.top.ker ⊔ N) u)=C.cover u := rfl

instance prefixCutSpace_finite [Finite X] :
    Finite (C.prefixCutSpace (F := F) (N := N) (generators := generators)) :=
  Finite.of_surjective (fun l : C.kernelCut F =>
    (C.prefixCutVectorMap (F := F) (N := N) (generators := generators) l).toAdd)
    (Multiplicative.toAdd.surjective.comp
      (C.prefixCutVectorMap_surjective (F := F) (N := N) (generators := generators)))

instance prefixModule_finite [Finite X] :
    Finite (C.prefixModule (F := F) (N := N) (generators := generators) (hgen := hgen)) :=
  Finite.of_surjective (fun k : F.top.ker =>
    (sectionSubgroupCutMap (p := 2) (F.sectionMap N) (C.kernelCut F) k).toAdd)
    (Multiplicative.toAdd.surjective.comp
      (sectionSubgroupCutMap_surjective (F.sectionMap N) (F.sectionMap_surjective N) _))

/-- The actual central-prefix envelope for every surviving original map.
Capacity and marker dimension are conclusions of the finite certificate. -/
theorem prefix_survival_card_le [Finite X] [Finite I]
    {J : Type} [Group J] [Finite J] (hU : IsPGroup 2 U)
    (P : ∀ β : GroupEpimorphism J (U ⧸ (F.top.ker ⊔ N)), Sylow 2 β.1.ker)
    (S : GroupEpimorphism J (U ⧸ N) → Prop) (b : ℝ)
    (hrank : ∀ β : GroupEpimorphism J (U ⧸ (F.top.ker ⊔ N)),
      (Module.finrank (ZMod 2) (PrimeAbelianization 2 (P β : Subgroup β.1.ker)) : ℝ) ≤ b/2) :
    (Nat.card {f : GroupEpimorphism J (U ⧸ N) // S f} : ℝ) ≤
      (Nat.card (C.prefixModule (F := F) (N := N) (generators := generators) (hgen := hgen)) *
        Nat.card (groupCohomology.H1
          (C.prefixModule (F := F) (N := N) (generators := generators) (hgen := hgen))) : ℝ) *
        (2:ℝ)^((C.fixedDimension:ℝ)/2*b) *
        fusionCentralPrefixWeight C.cutDimension J (U ⧸ (F.top.ker ⊔ N)) := by
  have h := fusionCentralPrefix_survival_card_le
    (C.prefixFirst (F := F) (N := N) (generators := generators))
    (QuotientGroup.mk'_surjective _)
    (C.prefixFirst_central (F := F) (N := N) (generators := generators) (hgen := hgen))
    (C.prefixCentralEquiv (F := F) (N := N) (generators := generators))
    (C.prefixBase (F := F) (N := N) (generators := generators))
    (C.prefixBase_surjective (F := F) (N := N) (generators := generators))
    (C.prefixModule (F := F) (N := N) (generators := generators) (hgen := hgen))
    (C.prefixModuleChart (F := F) (N := N) (generators := generators) (hgen := hgen))
    P S b hrank
  have hc : representationSchurCapacity
      (C.prefixModule (F := F) (N := N) (generators := generators) (hgen := hgen)).ρ =
      (C.fixedDimension:ℝ) := C.capacity_eq F N generators hgen hU
  have hd : Module.finrank (ZMod 2)
      (C.prefixCutSpace (F := F) (N := N) (generators := generators)) = C.cutDimension :=
    C.cutDimension_eq F N generators
  simpa only [hc,hd] using h

/-- The same original quotient cover supplies the joint marker moment. -/
theorem prefixWeight_moment_le (b q : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),
      fusionCentralPrefixWeight C.cutDimension J (U ⧸ (F.top.ker ⊔ N))^q) ≤
      (subgroupCount (b+q*(C.coverDegree+2*C.cutDimension)) : ℝ) := by
  exact fusionCentralPrefixWeight_moment_le
    (C.prefixCover (F := F) (N := N) (generators := generators))
    (C.prefixCover_injective (F := F) (N := N) (generators := generators))
    (MonoidHom.id (U ⧸ (F.top.ker ⊔ N))) Function.surjective_id b C.cutDimension q

end BinaryPairLocalCertificate
end SymmetricSubgroupAsymptotics
