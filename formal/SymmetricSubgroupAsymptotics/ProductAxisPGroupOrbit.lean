import SymmetricSubgroupAsymptotics.ProductAxisOrbitTransport
import SymmetricSubgroupAsymptotics.FiniteProductPGroup

/-! A product of local p-subgroups fills the same actual product-group
orbit, even with correlated point stabilizers. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ProductAxisPGroupOrbit
variable {J T X : Type*} [Group T] [Fintype J] [DecidableEq J]
  [MulAction (J → T) X]

theorem pi_isPGroup {p : ℕ} (H : J → Subgroup T) (hH : ∀ i,IsPGroup p (H i)) :
    IsPGroup p (Subgroup.pi Set.univ H) := by
  let f : Subgroup.pi Set.univ H →* (∀ i,H i) :=
    { toFun := fun g i => ⟨g.val i,g.property i (Set.mem_univ i)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro g k he
    apply Subtype.ext
    funext i
    exact congrArg (fun z : ∀ i,H i => (z i).val) he
  exact (finitePi_isPGroup (fun i => H i) hH).of_injective f hf

theorem orbit_eq (H : J → Subgroup T)
    (hloc : ∀ (i : J) (g : T) (x : X), ∃ h : H i,
      (Pi.mulSingle i h.val : J → T) • x=(Pi.mulSingle i g : J → T) • x)
    (x : X) : MulAction.orbit (Subgroup.pi Set.univ H) x=MulAction.orbit (J → T) x := by
  apply Set.Subset.antisymm
  · exact MulAction.orbit_subgroup_subset _ _
  · intro y hy
    obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp hy
    obtain ⟨h,hh⟩ := ProductAxisOrbitTransport.exists_product_transporter H hloc g x
    exact MulAction.mem_orbit_iff.mpr ⟨h,hh.trans hg⟩

theorem card_orbit_prime_power [Finite X] {p : ℕ} [Fact p.Prime] (H : J → Subgroup T)
    (hH : ∀ i,IsPGroup p (H i))
    (hloc : ∀ (i : J) (g : T) (x : X), ∃ h : H i,
      (Pi.mulSingle i h.val : J → T) • x=(Pi.mulSingle i g : J → T) • x)
    (x : X) : ∃ r : ℕ,Nat.card (MulAction.orbit (J → T) x)=p^r := by
  obtain ⟨r,hr⟩ := (pi_isPGroup H hH).card_orbit (α:=X) x
  exact ⟨r,by simpa only [orbit_eq H hloc x] using hr⟩

end SymmetricSubgroupAsymptotics.ProductAxisPGroupOrbit
