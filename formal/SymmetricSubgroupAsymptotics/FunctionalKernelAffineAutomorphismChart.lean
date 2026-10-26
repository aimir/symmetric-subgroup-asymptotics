import SymmetricSubgroupAsymptotics.AutomorphismIndexTwoAffineChart
import SymmetricSubgroupAsymptotics.BinaryFunctionalStabilizerClassBound

/-! An actual automorphism action fixing a nonzero linear functional
has a faithful affine chart on that functional's literal kernel.
Unlike an index-two shortcut, the trivial quotient action is proved
from the SAME fixed functional. The chart works over every field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FunctionalKernelAffineAutomorphismChart
open BinaryFunctionalStabilizerClassBound AutomorphismIndexTwoAffineChart

variable {K : Type*} {N G : Type} [Field K] [CommGroup N] [Group G]
    [Module K (Additive N)]

variable (φ : G →* MulAut N) (ρ : G →* (Additive N ≃ₗ[K] Additive N))
    (hcompat : ∀ (g : G) (n : N), ρ g (Additive.ofMul n)=Additive.ofMul (φ g n))
    (ℓ : Module.Dual K (Additive N))
    (hfix : ∀ (g : G) (v : Additive N), ℓ (ρ g v)=ℓ v)

include ρ hcompat hfix

theorem functionalKernel_stable (g : G) (n : N) :
    φ g n∈functionalKernel ℓ ↔ n∈functionalKernel ℓ := by
  change ℓ (Additive.ofMul (φ g n))=0 ↔ ℓ (Additive.ofMul n)=0
  rw [←hcompat,hfix]

theorem displacement_mem (a : N) (g : G) : φ g a*a⁻¹∈functionalKernel ℓ := by
  change ℓ (Additive.ofMul (φ g a*a⁻¹))=0
  rw [ofMul_mul,ofMul_inv,map_add,map_neg,←hcompat,hfix,add_neg_cancel]

def affineHom (a : N) :
    G →* (functionalKernel ℓ ⋊[MonoidHom.id (MulAut (functionalKernel ℓ))]
      MulAut (functionalKernel ℓ)) where
  toFun g := ⟨⟨φ g a*a⁻¹,displacement_mem φ ρ hcompat ℓ hfix a g⟩,
    restrictionAction (functionalKernel ℓ) φ
      (functionalKernel_stable φ ρ hcompat ℓ hfix) g⟩
  map_one' := by
    apply SemidirectProduct.ext
    · apply Subtype.ext
      change φ 1 a*a⁻¹=1
      rw [φ.map_one]
      exact mul_inv_cancel a
    · exact (restrictionAction (functionalKernel ℓ) φ
        (functionalKernel_stable φ ρ hcompat ℓ hfix)).map_one
  map_mul' g h := by
    apply SemidirectProduct.ext
    · apply Subtype.ext
      change φ (g*h) a*a⁻¹=(φ g a*a⁻¹)*φ g (φ h a*a⁻¹)
      rw [φ.map_mul]
      change φ g (φ h a)*a⁻¹=(φ g a*a⁻¹)*φ g (φ h a*a⁻¹)
      rw [(φ g).map_mul,(φ g).map_inv]
      simp only [mul_assoc,mul_left_comm,mul_comm,mul_inv_cancel,one_mul]
    · exact (restrictionAction (functionalKernel ℓ) φ
        (functionalKernel_stable φ ρ hcompat ℓ hfix)).map_mul g h

theorem affineHom_injective (hφ : Function.Injective φ)
    (a : N) (ha : ℓ (Additive.ofMul a)=1) :
    Function.Injective (affineHom φ ρ hcompat ℓ hfix a) := by
  intro g h he
  have hr : restrictionAction (functionalKernel ℓ) φ
      (functionalKernel_stable φ ρ hcompat ℓ hfix) g=
    restrictionAction (functionalKernel ℓ) φ
      (functionalKernel_stable φ ρ hcompat ℓ hfix) h :=
    congrArg SemidirectProduct.right he
  have hd : φ g a*a⁻¹=φ h a*a⁻¹ := congrArg
    (fun q : functionalKernel ℓ ⋊[MonoidHom.id (MulAut (functionalKernel ℓ))]
      MulAut (functionalKernel ℓ) => (q.left : N)) he
  have hga : φ g a=φ h a := mul_right_cancel hd
  have hres (k : functionalKernel ℓ) : φ g k.val=φ h k.val :=
    congrArg (fun f : MulAut (functionalKernel ℓ) => (f k : N)) hr
  have hlin_a : ρ g (Additive.ofMul a)=ρ h (Additive.ofMul a) := by
    rw [hcompat,hcompat,hga]
  apply hφ
  apply MulEquiv.ext
  intro n
  apply Additive.ofMul.injective
  rw [←hcompat,←hcompat]
  let v : Additive N := Additive.ofMul n-ℓ (Additive.ofMul n) • Additive.ofMul a
  have hv : ℓ v=0 := by
    dsimp only [v]
    rw [map_sub,map_smul,ha,smul_eq_mul,mul_one,sub_self]
  have hlin_v : ρ g v=ρ h v := by
    have hh := congrArg Additive.ofMul (hres ⟨v.toMul,hv⟩)
    simpa only [←hcompat] using hh
  have hn : v+ℓ (Additive.ofMul n) • Additive.ofMul a=Additive.ofMul n :=
    sub_add_cancel _ _
  calc
    ρ g (Additive.ofMul n)=ρ g (v+ℓ (Additive.ofMul n) • Additive.ofMul a) :=
      congrArg (ρ g) hn.symm
    _=ρ g v+ℓ (Additive.ofMul n) • ρ g (Additive.ofMul a) := by rw [map_add,map_smul]
    _=ρ h v+ℓ (Additive.ofMul n) • ρ h (Additive.ofMul a) := by rw [hlin_v,hlin_a]
    _=ρ h (v+ℓ (Additive.ofMul n) • Additive.ofMul a) := by rw [map_add,map_smul]
    _=ρ h (Additive.ofMul n) := congrArg (ρ h) hn

theorem exists_injective_affineHom (hφ : Function.Injective φ) (hℓ : ℓ≠0) :
    ∃ a : N, Function.Injective (affineHom φ ρ hcompat ℓ hfix a) := by
  obtain ⟨v,hv⟩ := DFunLike.ne_iff.mp hℓ
  let a : N := ((ℓ v)⁻¹ • v).toMul
  have ha : ℓ (Additive.ofMul a)=1 := by
    change ℓ ((ℓ v)⁻¹ • v)=1
    rw [map_smul,smul_eq_mul,inv_mul_cancel₀ hv]
  exact ⟨a,affineHom_injective φ ρ hcompat ℓ hfix hφ a ha⟩

end SymmetricSubgroupAsymptotics.FunctionalKernelAffineAutomorphismChart
