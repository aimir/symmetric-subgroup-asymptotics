import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Index

/-! Automorphisms preserving a literal subgroup of index two have an
actual faithful affine chart on that subgroup. Restriction is the linear
part and displacement of one outside element is the translation part.
No complement, splitting, or classification of the acting group is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AutomorphismIndexTwoAffineChart

variable {N G : Type*} [CommGroup N] [Group G]

def restrictionAction (K : Subgroup N) (φ : G →* MulAut N)
    (hstable : ∀ (g : G) (n : N), φ g n ∈ K ↔ n ∈ K) : G →* MulAut K where
  toFun g := {
    toFun := fun n => ⟨φ g n.val,(hstable g n.val).2 n.property⟩
    invFun := fun n => ⟨φ g⁻¹ n.val,(hstable g⁻¹ n.val).2 n.property⟩
    left_inv := fun n => Subtype.ext (by
      change φ g⁻¹ (φ g n.val)=n.val
      rw [φ.map_inv]
      exact MulAut.inv_apply_self _ _ _)
    right_inv := fun n => Subtype.ext (by
      change φ g (φ g⁻¹ n.val)=n.val
      rw [φ.map_inv]
      exact MulAut.apply_inv_self _ _ _)
    map_mul' := fun n m => Subtype.ext ((φ g).map_mul n.val m.val) }
  map_one' := by
    apply MulEquiv.ext
    intro n
    apply Subtype.ext
    change φ 1 n.val=n.val
    rw [φ.map_one]
    rfl
  map_mul' g h := by
    apply MulEquiv.ext
    intro n
    apply Subtype.ext
    change φ (g*h) n.val=φ g (φ h n.val)
    rw [φ.map_mul]
    rfl

private theorem displacement_mem (K : Subgroup N) (hK : K.index=2)
    (φ : G →* MulAut N)
    (hstable : ∀ (g : G) (n : N), φ g n ∈ K ↔ n ∈ K)
    (a : N) (g : G) : φ g a*a⁻¹ ∈ K := by
  rw [K.mul_mem_iff_of_index_two hK,hstable,K.inv_mem_iff]

def affineHom (K : Subgroup N) (hK : K.index=2)
    (φ : G →* MulAut N)
    (hstable : ∀ (g : G) (n : N), φ g n ∈ K ↔ n ∈ K)
    (a : N) : G →* K ⋊[MonoidHom.id (MulAut K)] MulAut K where
  toFun g := ⟨⟨φ g a*a⁻¹,displacement_mem K hK φ hstable a g⟩,
    restrictionAction K φ hstable g⟩
  map_one' := by
    apply SemidirectProduct.ext
    · apply Subtype.ext
      change φ 1 a*a⁻¹=1
      rw [φ.map_one]
      exact mul_inv_cancel a
    · exact (restrictionAction K φ hstable).map_one
  map_mul' g h := by
    apply SemidirectProduct.ext
    · apply Subtype.ext
      change φ (g*h) a*a⁻¹=(φ g a*a⁻¹)*φ g (φ h a*a⁻¹)
      rw [φ.map_mul]
      change φ g (φ h a)*a⁻¹=(φ g a*a⁻¹)*φ g (φ h a*a⁻¹)
      rw [(φ g).map_mul,(φ g).map_inv]
      simp only [mul_assoc,mul_left_comm,mul_comm,mul_inv_cancel,one_mul]
    · exact (restrictionAction K φ hstable).map_mul g h

theorem affineHom_injective (K : Subgroup N) (hK : K.index=2)
    (φ : G →* MulAut N) (hφ : Function.Injective φ)
    (hstable : ∀ (g : G) (n : N), φ g n ∈ K ↔ n ∈ K)
    (a : N) (ha : a ∉ K) :
    Function.Injective (affineHom K hK φ hstable a) := by
  intro g h he
  have hr : restrictionAction K φ hstable g=restrictionAction K φ hstable h :=
    congrArg SemidirectProduct.right he
  have hd : φ g a*a⁻¹=φ h a*a⁻¹ :=
    congrArg (fun q : K ⋊[MonoidHom.id (MulAut K)] MulAut K => (q.left : N)) he
  have hga : φ g a=φ h a := mul_right_cancel hd
  have hres (k : K) : φ g k.val=φ h k.val :=
    congrArg (fun f : MulAut K => (f k : N)) hr
  apply hφ
  apply MulEquiv.ext
  intro n
  by_cases hn : n ∈ K
  · exact hres ⟨n,hn⟩
  · have hk : a⁻¹*n ∈ K := by
      rw [K.mul_mem_iff_of_index_two hK,K.inv_mem_iff]
      exact iff_of_false ha hn
    have hkn := hres ⟨a⁻¹*n,hk⟩
    calc
      φ g n = φ g (a*(a⁻¹*n)) := congrArg (φ g) (mul_inv_cancel_left a n).symm
      _ = φ g a*φ g (a⁻¹*n) := (φ g).map_mul _ _
      _ = φ h a*φ h (a⁻¹*n) := congrArg₂ (·*·) hga hkn
      _ = φ h (a*(a⁻¹*n)) := ((φ h).map_mul _ _).symm
      _ = φ h n := congrArg (φ h) (mul_inv_cancel_left a n)

end SymmetricSubgroupAsymptotics.AutomorphismIndexTwoAffineChart
