import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.Group.Subgroup.Finite

/-! Coordinate transport assembles in an arbitrary action of a finite
direct product. The point set is not assumed to be a product, and its
stabilizer may be correlated across all factors. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ProductAxisOrbitTransport
variable {A X : Type*} [Group A] [MulAction A X]

def orbitMovers (H : Subgroup A) : Subgroup A where
  carrier := {g | ∀ x : X, ∃ h : H, (h : A) • x=g • x}
  one_mem' := fun x => ⟨1,rfl⟩
  mul_mem' := by
    intro a b ha hb x
    obtain ⟨v,hv⟩ := hb x
    obtain ⟨u,hu⟩ := ha (b • x)
    refine ⟨u*v,?_⟩
    change ((u : A)*(v : A)) • x=(a*b) • x
    rw [mul_smul,hv,hu,←mul_smul]
  inv_mem' := by
    intro a ha x
    obtain ⟨u,hu⟩ := ha (a⁻¹ • x)
    have hh : (u : A) • (a⁻¹ • x)=x := by simpa only [smul_inv_smul] using hu
    refine ⟨u⁻¹,?_⟩
    change (u : A)⁻¹ • x=a⁻¹ • x
    calc
      (u : A)⁻¹ • x=(u : A)⁻¹ • ((u : A) • (a⁻¹ • x)) :=
        congrArg (fun y : X => (u : A)⁻¹ • y) hh.symm
      _=a⁻¹ • x := inv_smul_smul (u : A) (a⁻¹ • x)

variable {J T : Type*} [Group T] [Finite J] [DecidableEq J]
  [MulAction (J → T) X]

/-- Each local replacement is allowed to depend on the current ORIGINAL
point. This is precisely what makes the proof valid for correlated actions. -/
theorem exists_product_transporter (H : J → Subgroup T)
    (hloc : ∀ (i : J) (g : T) (x : X), ∃ h : H i,
      (Pi.mulSingle i h.val : J → T) • x=(Pi.mulSingle i g : J → T) • x)
    (g : J → T) (x : X) :
    ∃ h : Subgroup.pi Set.univ H, (h : J → T) • x=g • x := by
  let N := Subgroup.pi Set.univ H
  have hall : Subgroup.pi Set.univ (fun _ : J => (⊤ : Subgroup T)) ≤ orbitMovers (X:=X) N := by
    apply Subgroup.pi_le_iff.mpr
    intro i
    rintro a ⟨t,_,rfl⟩ y
    obtain ⟨h,hh⟩ := hloc i t y
    have hmem : Pi.mulSingle i h.val ∈ Subgroup.pi Set.univ H :=
      (Subgroup.mulSingle_mem_pi (I:=Set.univ) (H:=H) i h.val).mpr (fun _ => h.property)
    exact ⟨⟨Pi.mulSingle i h.val,hmem⟩,hh⟩
  rw [Subgroup.pi_top] at hall
  exact hall (Subgroup.mem_top g) x

end SymmetricSubgroupAsymptotics.ProductAxisOrbitTransport
