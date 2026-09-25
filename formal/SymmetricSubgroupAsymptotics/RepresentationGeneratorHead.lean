import SymmetricSubgroupAsymptotics.PrimeEquivariantCharacters
import SymmetricSubgroupAsymptotics.SchurRepresentation
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Span.Basic

/-! A module-generator bound controls the actual invariant character
head of that same module. This is the algebraic interface needed before
applying an induced-module generator theorem to actual chief layers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra
namespace SymmetricSubgroupAsymptotics

theorem moduleHom_finrank_le_generators {k R M A ι : Type*}
    [Field k] [Ring R] [Algebra k R]
    [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
    [AddCommGroup A] [Module R A] [Module k A] [IsScalarTower k R A]
    [Fintype ι] [FiniteDimensional k A] (v : ι→M)
    (hv : Submodule.span R (Set.range v)=⊤) :
    Module.finrank k (M→ₗ[R]A)≤Fintype.card ι*Module.finrank k A := by
  let ev : (M→ₗ[R]A)→ₗ[k](ι→A) := {
    toFun f i := f (v i)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have hinj : Function.Injective ev := by
    intro f g h
    exact LinearMap.ext_on_range hv (fun i => congrFun h i)
  have h := ev.finrank_le_finrank_of_injective hinj
  simpa only [Module.finrank_pi_fintype,Finset.sum_const,Finset.card_univ,Nat.nsmul_eq_mul] using h

theorem representationHead_finrank_le_generators {k G V : Type*}
    [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) {n : ℕ} (v : Fin n→ρ.asModule)
    (hv : Submodule.span k[G] (Set.range v)=⊤) :
    Module.finrank k (ρ.IntertwiningMap (Representation.trivial k G k))≤n := by
  letI : Module k[G] ρ.asModule := Representation.instModuleMonoidAlgebraAsModule ρ
  letI : Module k[G] (Representation.trivial k G k).asModule :=
    Representation.instModuleMonoidAlgebraAsModule (Representation.trivial k G k)
  rw [(Representation.IntertwiningMap.equivLinearMapAsModule ρ
    (Representation.trivial k G k)).finrank_eq]
  have h := moduleHom_finrank_le_generators (k := k) (R := k[G])
    (M := ρ.asModule) (A := (Representation.trivial k G k).asModule) v hv
  have hd : Module.finrank k (Representation.trivial k G k).asModule=1 :=
    (Representation.trivial k G k).asModuleEquiv.finrank_eq.trans (Module.finrank_self k)
  simpa only [Fintype.card_fin,hd,mul_one] using h

variable {p : ℕ} [Fact p.Prime] {G V : Type*}
    [Group G] [AddCommGroup V] [Module (ZMod p) V]

def representationGroupAction (ρ : Representation (ZMod p) G V) :
    G→*MulAut (Multiplicative V) where
  toFun g := {
    toFun x := Multiplicative.ofAdd (ρ g x.toAdd)
    invFun x := Multiplicative.ofAdd (ρ g⁻¹ x.toAdd)
    left_inv x := by
      apply Multiplicative.toAdd.injective
      change ρ g⁻¹ (ρ g x.toAdd)=x.toAdd
      change (ρ g⁻¹*ρ g) x.toAdd=x.toAdd
      rw [←map_mul,inv_mul_cancel,map_one]
      rfl
    right_inv x := by
      apply Multiplicative.toAdd.injective
      change (ρ g*ρ g⁻¹) x.toAdd=x.toAdd
      rw [←map_mul,mul_inv_cancel,map_one]
      rfl
    map_mul' x y := congrArg Multiplicative.ofAdd (map_add (ρ g) x.toAdd y.toAdd) }
  map_one' := by ext x; change Multiplicative.ofAdd (ρ 1 x.toAdd)=x; rw [map_one]; rfl
  map_mul' g h := by ext x; change Multiplicative.ofAdd (ρ (g*h) x.toAdd)=_; rw [map_mul]; rfl

/-- Relative characters of the actual elementary layer are exactly the
equivariant linear maps from its original representation to the trivial line. -/
def representationCharacterHeadEquiv (ρ : Representation (ZMod p) G V) :
    primeActionCharacters p (representationGroupAction ρ) ≃ₗ[ZMod p]
      ρ.IntertwiningMap (Representation.trivial (ZMod p) G (ZMod p)) where
  toFun χ := {
    toLinearMap := (show V→+ZMod p from {
      toFun v := χ.1 (Additive.ofMul (Multiplicative.ofAdd v))
      map_zero' := χ.1.map_zero
      map_add' x y := χ.1.map_add _ _ }).toZModLinearMap p
    isIntertwining' g := by
      ext v
      change χ.1 (Additive.ofMul (Multiplicative.ofAdd (ρ g v)))=
        χ.1 (Additive.ofMul (Multiplicative.ofAdd v))
      exact χ.2 g (Multiplicative.ofAdd v) }
  invFun f := ⟨{
    toFun v := f v.toMul.toAdd
    map_zero' := f.toLinearMap.map_zero
    map_add' x y := f.toLinearMap.map_add _ _ },by
      intro g v
      exact Representation.IntertwiningMap.isIntertwining _ _ f g v.toAdd⟩
  left_inv χ := by apply Subtype.ext; rfl
  right_inv f := by ext v; rfl
  map_add' _ _ := by ext v; rfl
  map_smul' _ _ := by ext v; rfl

theorem representationCharacterHead_le_generators
    (ρ : Representation (ZMod p) G V) {n : ℕ} (v : Fin n→ρ.asModule)
    (hv : Submodule.span (ZMod p)[G] (Set.range v)=⊤) :
    Module.finrank (ZMod p) (primeActionCharacters p (representationGroupAction ρ))≤n := by
  rw [(representationCharacterHeadEquiv ρ).finrank_eq]
  exact representationHead_finrank_le_generators ρ v hv

end SymmetricSubgroupAsymptotics
