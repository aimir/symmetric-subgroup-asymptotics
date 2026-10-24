import SymmetricSubgroupAsymptotics.CFSGRegularElementSylowPreimage

/-! A regular ambient Sylow witness controls every p-subgroup containing
it. In particular an automorphism fixing that witness preserves the whole
injective Sylow preimage, without any selected-generator description. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.CFSGRegularSylowPreimageUniqueness
open CFSGRegularElementSylowPreimage
variable {G H : Type*} [Group G] [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime]

theorem p_subgroup_le_preimage_of_regular_mem (P : Sylow p H) (f : G→*H)
    (r : G)
    (hreg : ∀g : H,g⁻¹*f r*g∈(P : Subgroup H)→g∈Subgroup.normalizer (P : Set H))
    (Q : Subgroup G) (hQ : IsPGroup p Q) (hrQ : r∈Q) :
    Q≤(P : Subgroup H).comap f := by
  obtain ⟨S,hQS⟩ := (hQ.map f).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq H P S
  have he : (P : Subgroup H).map (MulAut.conj g).toMonoidHom=(S : Subgroup H) := by
    have hh := congrArg (fun T : Sylow p H=>(T : Subgroup H)) hg
    simpa only [Sylow.smul_def,Sylow.pointwise_smul_def,Subgroup.pointwise_smul_def] using hh
  have hrS : f r∈(S : Subgroup H) := hQS ⟨r,hrQ,rfl⟩
  rw [←he] at hrS
  obtain ⟨x,hx,hxr⟩ := hrS
  have hgr : g⁻¹*f r*g∈(P : Subgroup H) := by
    have hx' : g⁻¹*f r*g=x := by
      rw [←hxr]
      change g⁻¹*(g*x*g⁻¹)*g=x
      group
    rw [hx']
    exact hx
  have hgN := hreg g hgr
  intro y hy
  have hyS := hQS (show f y∈Q.map f from ⟨y,hy,rfl⟩)
  rw [←he] at hyS
  obtain ⟨z,hz,hzy⟩ := hyS
  change f y∈(P : Subgroup H)
  rw [←hzy]
  exact (Subgroup.mem_normalizer_iff.mp hgN z).mp hz

theorem sylow_eq_preimage_of_regular_mem (P : Sylow p H) (f : G→*H)
    (hf : Function.Injective f) (r : G) (hrP : f r∈(P : Subgroup H))
    (hreg : ∀g : H,g⁻¹*f r*g∈(P : Subgroup H)→g∈Subgroup.normalizer (P : Set H))
    (Q : Sylow p G) (hrQ : r∈Q) :
    Q=preimageSylow P f hf r hrP hreg := by
  apply Sylow.ext
  let R := preimageSylow P f hf r hrP hreg
  have hQR : (Q : Subgroup G)≤(R : Subgroup G) :=
    p_subgroup_le_preimage_of_regular_mem P f r hreg Q Q.isPGroup' hrQ
  exact (Q.is_maximal' R.isPGroup' hQR).symm

theorem automorphism_preserves_regular_preimage (P : Sylow p H) (f : G→*H)
    (hf : Function.Injective f) (r : G) (hrP : f r∈(P : Subgroup H))
    (hreg : ∀g : H,g⁻¹*f r*g∈(P : Subgroup H)→g∈Subgroup.normalizer (P : Set H))
    (a : MulAut G) (ha : a r=r) :
    ((P : Subgroup H).comap f).map a.toMonoidHom=(P : Subgroup H).comap f := by
  letI : Finite G := Finite.of_injective f hf
  let R := preimageSylow P f hf r hrP hreg
  let Q : Sylow p G := R.mapSurjective (f:=a.toMonoidHom) a.surjective
  have hrQ : r∈Q := ⟨r,hrP,ha⟩
  have he := sylow_eq_preimage_of_regular_mem P f hf r hrP hreg Q hrQ
  exact congrArg (fun S : Sylow p G=>(S : Subgroup G)) he

end SymmetricSubgroupAsymptotics.CFSGRegularSylowPreimageUniqueness
