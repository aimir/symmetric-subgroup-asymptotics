import SymmetricSubgroupAsymptotics.MonomialPolynomialOrbitGenerators
import Mathlib.Logic.Equiv.Fin.Basic

/-! Vector-valued block monomial representations. Local transport can be
any invertible linear map on the fiber, varying with both the group element
and the block. A cyclic orbit costs only the fiber dimension as a polynomial
module. The PID submodule theorem therefore bounds every invariant subspace,
in arbitrary characteristic, without a splitting or scalar-field shortcut.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical Polynomial BigOperators
namespace SymmetricSubgroupAsymptotics.BlockMonomialPolynomialOrbitGenerators

variable {k G X W : Type} [Field k] [Group G] [Fintype X] [MulAction G X]
    [AddCommGroup W] [Module k W] (rho : Representation k G (X→W))
    (hdelta : ∀g:G,∀x:X,∃u:W≃ₗ[k]W,∀w:W,
      rho g (Pi.single x w)=Pi.single (g • x) (u w))

include hdelta

theorem polynomial_span_orbitCover {d n : ℕ} (basis : Module.Basis (Fin d) k W)
    (g:G) (representative:Fin n→X)
    (hcover:∀x:X,∃j:Fin n,∃m:ℕ,g^m • representative j=x) :
    Submodule.span k[X] (Set.range (fun j:Fin n×Fin d=>
      Module.AEval'.of (rho g) (Pi.single (representative j.1) (basis j.2))))=⊤ := by
  let polyEquiv := Module.AEval'.of (rho g)
  let code : (Fin n×Fin d)→Module.AEval' (rho g) :=
    fun j=>polyEquiv (Pi.single (representative j.1) (basis j.2))
  let P : Submodule k[X] (Module.AEval' (rho g)) :=
    Submodule.span k[X] (Set.range code)
  have hbase (j:Fin n) (w:W) : polyEquiv (Pi.single (representative j) w)∈P := by
    let L : W→ₗ[k]Module.AEval' (rho g) :=
      polyEquiv.toLinearMap.comp (LinearMap.single k (fun _:X=>W) (representative j))
    have hle : Submodule.span k (Set.range basis) ≤ (P.restrictScalars k).comap L := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact Submodule.subset_span ⟨(j,i),rfl⟩
    have hw : w∈Submodule.span k (Set.range basis) := by
      rw [basis.span_eq]
      trivial
    exact hle hw
  have hpoint (x:X) (w:W) : polyEquiv (Pi.single x w)∈P := by
    obtain ⟨j,m,hm⟩ := hcover x
    obtain ⟨u,hu⟩ := hdelta (g^m) (representative j)
    have hpow := P.smul_mem ((Polynomial.X:k[X])^m) (hbase j (u.symm w))
    have he : ((Polynomial.X:k[X])^m) • polyEquiv (Pi.single (representative j) (u.symm w))=
        polyEquiv (rho (g^m) (Pi.single (representative j) (u.symm w))) := by
      dsimp only [polyEquiv]
      rw [Module.AEval'.X_pow_smul_of,map_pow]
      rfl
    rw [he,hu,hm,LinearEquiv.apply_symm_apply] at hpow
    exact hpow
  have hall (v:X→W) : polyEquiv v∈P := by
    have hs := P.sum_mem (fun i (_:i∈Finset.univ)=>hpoint i (v i))
    have he : (∑i,polyEquiv (Pi.single i (v i)))=polyEquiv v := by
      rw [←map_sum,LinearMap.sum_single_apply]
    exact he ▸ hs
  apply top_unique
  intro x _
  simpa only [LinearEquiv.apply_symm_apply] using hall (polyEquiv.symm x)

theorem uniform_of_derangement_with_basis [Finite G] [Nonempty X]
    {d:ℕ} (basis:Module.Basis (Fin d) k W) (g:G)
    (hfree:MulAction.fixedBy X g=∅) :
    UniformSubrepresentationGeneratorBound rho (d*(Nat.card X/2)) := by
  obtain ⟨representative,hcover⟩ :=
    TransitivePermutationModuleGenerators.cyclic_orbit_cover (X:=X) g
  let O := MulAction.orbitRel.Quotient (Subgroup.zpowers g) X
  have hc : Nat.card O ≤ Nat.card X/2 := by
    have h := cyclicOrbitCount_mul_two_le_of_fixedBy_eq_empty g hfree
    change Nat.card O*2≤Nat.card X at h
    omega
  let e : Fin (Nat.card O)↪Fin (Nat.card X/2) := Fin.castLEEmb hc
  let padded : Fin (Nat.card X/2)→X :=
    Function.extend e representative (fun _=>Classical.choice inferInstance)
  have hpadded : ∀x:X,∃j:Fin (Nat.card X/2),∃m:ℕ,g^m • padded j=x := by
    intro x
    obtain ⟨j,m,hm⟩ := hcover x
    refine ⟨e j,m,?_⟩
    change g^m • Function.extend e representative _ (e j)=x
    rw [e.injective.extend_apply]
    exact hm
  let tuple : (Fin (Nat.card X/2)×Fin d)→Module.AEval' (rho g) :=
    fun j=>Module.AEval'.of (rho g) (Pi.single (padded j.1) (basis j.2))
  let E : (Fin (Nat.card X/2)×Fin d) ≃ Fin ((Nat.card X/2)*d) := finProdFinEquiv
  have hrange : Set.range (tuple ∘ E.symm)=Set.range tuple := by
    ext v
    constructor
    · rintro ⟨j,rfl⟩
      exact ⟨E.symm j,rfl⟩
    · rintro ⟨j,rfl⟩
      exact ⟨E j,by simp only [Function.comp_apply,Equiv.symm_apply_apply]⟩
  have hpoly : Submodule.span k[X] (Set.range (tuple ∘ E.symm))=⊤ := by
    rw [hrange]
    exact polynomial_span_orbitCover rho hdelta basis g padded hpadded
  simpa only [Nat.mul_comm] using
    uniformSubrepresentationGeneratorBound_of_polynomial rho g (tuple ∘ E.symm) hpoly

theorem uniform_of_transitive [Finite G] [Nontrivial X] [Module.Finite k W]
    [MulAction.IsPretransitive G X] :
    UniformSubrepresentationGeneratorBound rho (Module.finrank k W*(Nat.card X/2)) := by
  obtain ⟨g,hg⟩ := exists_fixedBy_eq_empty_of_pretransitive G X
  exact uniform_of_derangement_with_basis rho hdelta (Module.finBasis k W) g hg

end SymmetricSubgroupAsymptotics.BlockMonomialPolynomialOrbitGenerators
