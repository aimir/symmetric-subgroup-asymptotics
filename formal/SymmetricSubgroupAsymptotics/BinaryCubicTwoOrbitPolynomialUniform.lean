import SymmetricSubgroupAsymptotics.RepresentationPolynomialGeneratorBound
import SymmetricSubgroupAsymptotics.RepresentationDualSubquotientGenerators
import Mathlib.LinearAlgebra.Pi

/-! Two binary polynomial chains for an actual commuting cubic and
involution on four local planes. Only the explicit diagonal cubic branch
is covered; no common cubic element is asserted for a larger odd group. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical Polynomial BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryCubicTwoOrbitPolynomialUniform

abbrev Bit := ZMod 2
abbrev Plane := Fin 2 → Bit
abbrev Index := Fin 2 × Fin 2
abbrev Vector := Index → Plane
def e0 : Plane := ![1,0]
def e1 : Plane := ![0,1]
def flip (i : Index) : Index := (i.1,Equiv.swap 0 1 i.2)

private theorem plane_alternative (v : Plane) (hn : v≠0) (he : v≠e0) :
    ∃ c : Bit, v=e1+c • e0 := by
  revert v
  decide +kernel

private theorem plane_decomposition (v : Plane) : v=v 0 • e0+v 1 • e1 := by
  funext i
  fin_cases i <;> simp [e0,e1]

variable {H : Type} [Group H] (rho : Representation Bit H Vector)
  (k s : H) (hk : k^3=1) (hs : s^2=1) (hcomm : Commute k s)
  (K L : Index → Plane ≃ₗ[Bit] Plane)
  (hK : ∀ i v, rho k (Pi.single i v)=Pi.single i (K i v))
  (hL : ∀ i v, rho s (Pi.single i v)=Pi.single (flip i) (L i v))
  (hfixed : ∀ i v, K i v=v → v=0)

include hk hs hcomm in
private theorem product_four : (k*s)^4=k := by
  rw [hcomm.mul_pow]
  have hk4 : k^4=k := by rw [show (4 : ℕ)=3+1 by decide,pow_add,hk,pow_one,one_mul]
  have hs4 : s^4=1 := by rw [show (4 : ℕ)=2*2 by decide,pow_mul,hs,one_pow]
  rw [hk4,hs4,mul_one]

include hk hs hcomm in
private theorem product_three : (k*s)^3=s := by
  rw [hcomm.mul_pow,hk,one_mul]
  rw [show (3 : ℕ)=2+1 by decide,pow_add,hs,pow_one,one_mul]

include hk hs hcomm hK hL hfixed in
/-- Two actual seeds generate the polynomial module for T=k*s. Local
involution transports are arbitrary invertible maps, not pure swaps. -/
theorem polynomial_span :
    Submodule.span Bit[X] (Set.range (fun j : Fin 2 =>
      Module.AEval'.of (rho (k*s)) (Pi.single (j,0) e0)))=⊤ := by
  let T := k*s
  let e := Module.AEval'.of (rho T)
  let P : Submodule Bit[X] (Module.AEval' (rho T)) :=
    Submodule.span Bit[X] (Set.range (fun j : Fin 2 => e (Pi.single (j,0) e0)))
  have hpow (n : ℕ) (v : Vector) (hv : e v∈P) : e (rho (T^n) v)∈P := by
    have hm := P.smul_mem ((Polynomial.X : Bit[X])^n) hv
    have he : ((Polynomial.X : Bit[X])^n) • e v=e (rho (T^n) v) := by
      dsimp only [e]
      rw [Module.AEval'.X_pow_smul_of,map_pow]
      rfl
    rwa [he] at hm
  have hseed (j : Fin 2) : e (Pi.single (j,0) e0)∈P :=
    Submodule.subset_span ⟨j,rfl⟩
  have hfirst (j : Fin 2) (v : Plane) : e (Pi.single (j,0) v)∈P := by
    let i : Index := (j,0)
    have hn : K i e0≠0 := by
      intro h
      have he := (K i).injective (h.trans (map_zero (K i)).symm)
      exact (by decide +kernel : e0≠0) he
    have he : K i e0≠e0 := by
      intro h
      exact (by decide +kernel : e0≠0) (hfixed i e0 h)
    obtain ⟨c,hc⟩ := plane_alternative (K i e0) hn he
    have hke : e (Pi.single i (K i e0))∈P := by
      have hm := hpow 4 (Pi.single i e0) (hseed j)
      rw [product_four k s hk hs hcomm,hK] at hm
      exact hm
    have hsecond : e (Pi.single i e1)∈P := by
      have hm := P.sub_mem hke (P.smul_of_tower_mem c (hseed j))
      have hc' : K i e0-c • e0=e1 := by rw [hc,add_sub_cancel_right]
      rw [← map_smul,← map_sub,← Pi.single_smul,← Pi.single_sub,hc'] at hm
      exact hm
    have hm := P.add_mem (P.smul_of_tower_mem (v 0) (hseed j))
      (P.smul_of_tower_mem (v 1) hsecond)
    rw [← map_smul,← map_smul,← map_add,← Pi.single_smul,← Pi.single_smul,
      ← Pi.single_add,← plane_decomposition v] at hm
    exact hm
  have hall (i : Index) (v : Plane) : e (Pi.single i v)∈P := by
    rcases i with ⟨j,b⟩
    fin_cases b
    · exact hfirst j v
    · have hm := hpow 3 (Pi.single (j,0) ((L (j,0)).symm v))
        (hfirst j ((L (j,0)).symm v))
      rw [product_three k s hk hs hcomm,hL,LinearEquiv.apply_symm_apply] at hm
      exact hm
  have hfull (v : Vector) : e v∈P := by
    have hm := P.sum_mem (fun i (_ : i∈Finset.univ) => hall i (v i))
    rw [← map_sum,LinearMap.sum_single_apply] at hm
    exact hm
  apply top_unique
  intro v _
  exact (e.apply_symm_apply v) ▸ hfull (e.symm v)

include hk hs hcomm hK hL hfixed in
/-- All actual invariant binary subspaces cost two; the polynomial/PID
step is valid despite the involution having order divisible by two. -/
theorem uniform : UniformSubrepresentationGeneratorBound rho 2 :=
  uniformSubrepresentationGeneratorBound_of_polynomial rho (k*s) _
    (polynomial_span rho k s hk hs hcomm K L hK hL hfixed)

include hk hs hcomm hK hL hfixed in
/-- The original subspace and quotient map are retained; no averaging or
semisimplicity is required to pass to an actual section. -/
theorem section_uniform {W : Type} [AddCommGroup W] [Module Bit W]
    (S : Subrepresentation rho) (sigma : Representation Bit H W)
    (q : Representation.IntertwiningMap S.toRepresentation sigma)
    (hq : Function.Surjective q) : UniformSubrepresentationGeneratorBound sigma 2 := by
  let inclusion : Representation.IntertwiningMap S.toRepresentation rho :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' _ := rfl }
  exact ((uniform rho k s hk hs hcomm K L hK hL hfixed).of_injective
    inclusion Subtype.val_injective).of_surjective q hq

end SymmetricSubgroupAsymptotics.BinaryCubicTwoOrbitPolynomialUniform
