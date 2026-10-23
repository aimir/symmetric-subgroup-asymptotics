import SymmetricSubgroupAsymptotics.CFSGCentralCocyclePGroup
import SymmetricSubgroupAsymptotics.CFSGSimpleProjectiveDescent

/-! An actual p-generated central extension with p-prime centre has
no new central lifts. The central difference is a homomorphism on the
whole source and vanishes on its literal p-torsion generators. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPGeneratedCentralLift
variable {G H : Type*} [Group G] [Group H]

theorem central_lift (f : G →* H) (hker : f.ker ≤ Subgroup.center G)
    (p : ℕ) (hcop : p.Coprime (Nat.card (Subgroup.center G)))
    (X : Set G) (hX : Subgroup.closure X = ⊤) (hp : ∀ x ∈ X, x ^ p = 1)
    (z : G) (hz : f z ∈ Subgroup.center H) : z ∈ Subgroup.center G := by
  have hc (x : G) : x⁻¹ * (MulAut.conj z) x ∈ Subgroup.center G := by
    apply hker
    change f (x⁻¹ * (z * x * z⁻¹)) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    have hcomm := Subgroup.mem_center_iff.mp hz (f x)
    rw [← hcomm, mul_assoc (f x) (f z) (f z)⁻¹, mul_inv_cancel, mul_one, inv_mul_cancel]
  let c := CFSGCentralCocyclePGroup.centralDifferenceHom (MulAut.conj z) (⊤ : Subgroup G)
    (fun x => hc x.val)
  let d : G →* Subgroup.center G := c.comp (Subgroup.topEquiv.symm.toMonoidHom)
  have hkill (x : G) (hx : x ∈ X) : d x = 1 := by
    have he : (d x) ^ p = 1 := by rw [← map_pow, hp x hx, map_one]
    exact CFSGCentralCocyclePGroup.central_p_element_eq_one_of_coprime hcop (d x)
      ⟨1, by simpa only [pow_one] using he⟩
  have htop : d.ker = ⊤ := by
    apply top_unique
    rw [← hX]
    exact (Subgroup.closure_le _).mpr hkill
  have hd : d = 1 := MonoidHom.ker_eq_top_iff.mp htop
  apply Subgroup.mem_center_iff.mpr
  intro x
  have he : d x = 1 := by rw [hd]; rfl
  have hh := congrArg (fun a : Subgroup.center G => a.val) he
  change x⁻¹ * (z * x * z⁻¹) = 1 at hh
  have heq : z * x * z⁻¹ = x := (inv_mul_eq_one.mp hh).symm
  have h := congrArg (fun a : G => a * z) heq
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using h.symm

theorem center_comap_eq (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center G)
    (p : ℕ) (hcop : p.Coprime (Nat.card (Subgroup.center G)))
    (X : Set G) (hX : Subgroup.closure X = ⊤) (hp : ∀ x ∈ X, x ^ p = 1) :
    (Subgroup.center H).comap f = Subgroup.center G := by
  apply le_antisymm
  · intro z hz
    exact central_lift f hker p hcop X hX hp z hz
  · exact CFSGSimpleProjectiveDescent.map_mem_center f hf

def projectiveEquiv (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center G)
    (p : ℕ) (hcop : p.Coprime (Nat.card (Subgroup.center G)))
    (X : Set G) (hX : Subgroup.closure X = ⊤) (hp : ∀ x ∈ X, x ^ p = 1) :
    G ⧸ Subgroup.center G ≃* H ⧸ Subgroup.center H := by
  let π := CFSGSimpleProjectiveDescent.projectiveMap f hf
  have hinj : Function.Injective π := by
    apply (MonoidHom.ker_eq_bot_iff π).mp
    apply le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) x
    change (QuotientGroup.mk' (Subgroup.center G)) g = 1
    change (QuotientGroup.mk' (Subgroup.center H)) (f g) = 1 at hx
    exact (QuotientGroup.eq_one_iff g).mpr
      (central_lift f hker p hcop X hX hp g ((QuotientGroup.eq_one_iff (f g)).mp hx))
  exact MulEquiv.ofBijective π ⟨hinj, CFSGSimpleProjectiveDescent.projectiveMap_surjective f hf⟩

end SymmetricSubgroupAsymptotics.CFSGPGeneratedCentralLift
