import SymmetricSubgroupAsymptotics.TwistedMonomialCocycleFrame
import Mathlib.Algebra.Group.Subgroup.Ker

/-! Construct the actual coordinate twists from an automorphism action
which transports coordinate kernels. No independent theta or untwisted
action is assumed; inverse coordinate maps use the SAME inverse action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CoordinateDependencyMonomialAction

variable {Q X A : Type*} [Group Q] [Group A] [MulAction Q X]
variable (rho : Q →* MulAut (X → A))

def Depends : Prop := ∀ (q : Q) (f g : X → A) (x : X),
  f x=g x → (rho q f) (q • x)=(rho q g) (q • x)

def coordinateValue (q : Q) (x : X) (a : A) : A :=
  (rho q (fun _ : X => a)) (q • x)

theorem coordinate_formula (hdep : Depends rho) (q : Q) (f : X → A) (x : X) :
    (rho q f) (q • x)=coordinateValue rho q x (f x) :=
  hdep q f (fun _ : X => f x) x rfl

private theorem inverse_value (hdep : Depends rho) (q : Q) (x : X) (a : A) :
    coordinateValue rho q⁻¹ (q • x) (coordinateValue rho q x a)=a := by
  have hinv : rho q⁻¹ (rho q (fun _ : X => a))=(fun _ : X => a) := by
    change (rho q⁻¹*rho q) (fun _ : X => a)=(fun _ : X => a)
    rw [←map_mul,inv_mul_cancel,map_one,MulAut.one_apply]
  calc
    _=(rho q⁻¹ (rho q (fun _ : X => a))) (q⁻¹ • (q • x)) :=
      (coordinate_formula rho hdep q⁻¹ (rho q (fun _ : X => a)) (q • x)).symm
    _=a := congrFun hinv (q⁻¹ • (q • x))

/-- Each twist is derived by actual evaluation of a constant-coordinate
section; its inverse is derived from rho(q^-1), never guessed. -/
def twist (hdep : Depends rho) (q : Q) (x : X) : MulAut A where
  toFun := coordinateValue rho q x
  invFun := coordinateValue rho q⁻¹ (q • x)
  left_inv := inverse_value rho hdep q x
  right_inv a := by
    simpa only [inv_inv,inv_smul_smul] using inverse_value rho hdep q⁻¹ (q • x) a
  map_mul' a b := congrFun ((rho q).map_mul (fun _ : X => a) (fun _ : X => b)) (q • x)

theorem monomial_law (hdep : Depends rho) (q : Q) (f : X → A) (x : X) :
    (rho q f) (q • x)=twist rho hdep q x (f x) :=
  coordinate_formula rho hdep q f x

def coordinateKernel (x : X) : Subgroup (X → A) :=
  (Pi.evalMonoidHom (fun _ : X => A) x).ker

/-- Kernel transport suffices; both forward and inverse coordinates are
then supplied by the same actual group action. -/
theorem depends_of_coordinate_kernel_transport
    (hker : ∀ (q : Q) (x : X),
      (coordinateKernel (A := A) x).map (rho q).toMonoidHom ≤
        coordinateKernel (A := A) (q • x)) : Depends rho := by
  intro q f g x hfg
  have hd : f⁻¹*g∈coordinateKernel (A := A) x := by
    change (f x)⁻¹*g x=1
    rw [hfg,inv_mul_cancel]
  have he := hker q x (Subgroup.mem_map.mpr ⟨f⁻¹*g,hd,rfl⟩)
  change (rho q (f⁻¹*g)) (q • x)=1 at he
  rw [map_mul,map_inv] at he
  change ((rho q f) (q • x))⁻¹*(rho q g) (q • x)=1 at he
  exact inv_mul_eq_one.mp he

end SymmetricSubgroupAsymptotics.CoordinateDependencyMonomialAction
