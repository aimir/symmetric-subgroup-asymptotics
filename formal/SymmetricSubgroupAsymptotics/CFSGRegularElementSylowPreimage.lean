import SymmetricSubgroupAsymptotics.CFSGRegularElementSylowIntersection

/-! A regular Sylow witness in the image of an injective group map
makes the literal Sylow preimage a Sylow. Its normalizer maps into the
ambient Sylow normalizer. No surjectivity or group recognition is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.CFSGRegularElementSylowPreimage
variable {G H : Type*} [Group G] [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime]

def preimageSylow (P : Sylow p H) (f : G→*H) (hf : Function.Injective f)
    (r : G) (hrP : f r∈(P : Subgroup H))
    (hreg : ∀g : H,g⁻¹*f r*g∈(P : Subgroup H)→
      g∈Subgroup.normalizer (P : Set H)) : Sylow p G where
  toSubgroup := (P : Subgroup H).comap f
  isPGroup' := by
    apply P.isPGroup'.of_injective (f.subgroupComap (P : Subgroup H))
    intro x y he
    apply Subtype.ext
    apply hf
    exact congrArg (fun z : (P : Subgroup H)=>z.val) he
  is_maximal' := by
    intro Q hQ hUQ
    have hmapQ : IsPGroup p (Q.map f) := hQ.map f
    obtain ⟨S,hQS⟩ := hmapQ.exists_le_sylow
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq H P S
    have he : (P : Subgroup H).map (MulAut.conj g).toMonoidHom=(S : Subgroup H) := by
      have hh := congrArg (fun T : Sylow p H=>(T : Subgroup H)) hg
      simpa only [Sylow.smul_def,Sylow.pointwise_smul_def,Subgroup.pointwise_smul_def] using hh
    have hrS : f r∈(S : Subgroup H) := hQS ⟨r,hUQ hrP,rfl⟩
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
    apply le_antisymm _ hUQ
    intro y hy
    have hyS := hQS (show f y∈Q.map f from ⟨y,hy,rfl⟩)
    rw [←he] at hyS
    obtain ⟨z,hz,hzy⟩ := hyS
    change f y∈(P : Subgroup H)
    rw [←hzy]
    exact (Subgroup.mem_normalizer_iff.mp hgN z).mp hz

theorem preimageSylow_coe (P : Sylow p H) (f : G→*H) (hf : Function.Injective f)
    (r : G) (hrP : f r∈(P : Subgroup H))
    (hreg : ∀g : H,g⁻¹*f r*g∈(P : Subgroup H)→
      g∈Subgroup.normalizer (P : Set H)) :
    (preimageSylow P f hf r hrP hreg : Subgroup G)=(P : Subgroup H).comap f := rfl

omit [Finite H] [Fact p.Prime] in
theorem preimage_normalizer_le_comap_normalizer (P : Sylow p H) (f : G→*H)
    (r : G) (hrP : f r∈(P : Subgroup H))
    (hreg : ∀g : H,g⁻¹*f r*g∈(P : Subgroup H)→
      g∈Subgroup.normalizer (P : Set H)) :
    Subgroup.normalizer (((P : Subgroup H).comap f : Subgroup G) : Set G)≤
      (Subgroup.normalizer (P : Set H)).comap f := by
  intro x hx
  apply hreg
  have hxinv := (Subgroup.normalizer (((P : Subgroup H).comap f : Subgroup G) : Set G)).inv_mem hx
  have hrU : r∈(P : Subgroup H).comap f := hrP
  have hh := (Subgroup.mem_normalizer_iff.mp hxinv r).mp hrU
  have hh' : x⁻¹*r*x∈(P : Subgroup H).comap f := by
    simpa only [inv_inv] using hh
  change f (x⁻¹*r*x)∈(P : Subgroup H) at hh'
  simpa only [map_mul,map_inv] using hh'

omit [Finite H] [Fact p.Prime] in
theorem preimage_normalizer_soluble (P : Sylow p H) (f : G→*H)
    (hf : Function.Injective f) (r : G) (hrP : f r∈(P : Subgroup H))
    (hreg : ∀g : H,g⁻¹*f r*g∈(P : Subgroup H)→
      g∈Subgroup.normalizer (P : Set H))
    [IsSolvable (Subgroup.normalizer (P : Set H))] :
    IsSolvable (Subgroup.normalizer (((P : Subgroup H).comap f : Subgroup G) : Set G)) := by
  let N := Subgroup.normalizer (((P : Subgroup H).comap f : Subgroup G) : Set G)
  let M := Subgroup.normalizer (P : Set H)
  let phi : N→*M :=
    { toFun := fun x=>⟨f x.val,preimage_normalizer_le_comap_normalizer P f r hrP hreg x.property⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun x y=>Subtype.ext (map_mul f x.val y.val) }
  apply solvable_of_solvable_injective (f:=phi)
  intro x y he
  apply Subtype.ext
  apply hf
  exact congrArg (fun z : M=>z.val) he

end SymmetricSubgroupAsymptotics.CFSGRegularElementSylowPreimage
