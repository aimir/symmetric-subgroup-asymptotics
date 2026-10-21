import SymmetricSubgroupAsymptotics.CFSGSerreFieldDiagram
import SymmetricSubgroupAsymptotics.CFSGSerreTwistGraphProjection
import Mathlib.FieldTheory.Perfect

/-! The literal diagram-and-field twist graph is the graph of an actual
model automorphism when its parameter power is an actual field automorphism.
Finite-field Frobenius powers are supplied concretely at the end. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSerreFieldDiagram
open CFSG.Models.Chevalley CFSGSerreLocalNilpotence
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (K : Type) [Field K]
    (p : Equiv.Perm (Fin n)) (hA : ∀ i j, A (p i) (p j) = A i j) (σ : K ≃+* K)
include hA

def automorphismGraph : Subgroup (Ambient A K × Ambient A K) where
  carrier := {gh | gh.2 = ambientAutomorphism A K p hA σ gh.1}
  one_mem' := (map_one _).symm
  mul_mem' := by
    intro x y hx hy
    change x.2 * y.2 = ambientAutomorphism A K p hA σ (x.1 * y.1)
    rw [hx, hy, map_mul]
  inv_mem' := by
    intro x hx
    change x.2⁻¹ = ambientAutomorphism A K p hA σ x.1⁻¹
    rw [hx, map_inv]

variable (q : ℕ) (hσ : ∀ t : K, σ t = t ^ q)
include hσ

theorem twistGraph_le_automorphismGraph :
    twistGraph A K p (fun _ => q) ≤ automorphismGraph A K p hA σ := by
  apply (Subgroup.closure_le _).mpr
  rintro gh ⟨negative, i, t, h1, h2⟩
  change gh.2 = ambientAutomorphism A K p hA σ gh.1
  apply LinearEquiv.toLinearMap_injective
  have hc := ambientAutomorphism_isRootElement A K p hA σ negative i t gh.1 h1
  have h2' : gh.2.toLinearMap = rootOperator A K negative (p i) (σ t) := by
    rw [hσ]
    exact h2
  exact h2'.trans hc.symm

theorem mem_twistGraph_iff (gh : Ambient A K × Ambient A K) :
    gh ∈ twistGraph A K p (fun _ => q) ↔
      gh.1 ∈ subgroup A K ∧ gh.2 = ambientAutomorphism A K p hA σ gh.1 := by
  constructor
  · intro hg
    exact ⟨(twistGraph_le_model_prod A K p (fun _ => q) hg).1,
      twistGraph_le_automorphismGraph A K p hA σ q hσ hg⟩
  · rintro ⟨h1, h2⟩
    have hm : gh.1 ∈ (twistGraph A K p (fun _ => q)).map
        (MonoidHom.fst (Ambient A K) (Ambient A K)) := by
      rw [twistGraph_fst_image_eq_model]
      exact h1
    obtain ⟨x, hx, he⟩ := hm
    have hx2 := twistGraph_le_automorphismGraph A K p hA σ q hσ hx
    change x.2 = ambientAutomorphism A K p hA σ x.1 at hx2
    have he1 : x.1 = gh.1 := he
    have heq : x = gh := Prod.ext he1 (hx2.trans ((congrArg
      (ambientAutomorphism A K p hA σ) he1).trans h2.symm))
    exact heq ▸ hx

theorem twistGraphFirstProjection_injective :
    Function.Injective (twistGraphFirstProjection A K p (fun _ => q)) := by
  intro x y hxy
  have h1 : x.val.1 = y.val.1 := congrArg Subtype.val hxy
  apply Subtype.ext
  apply Prod.ext h1
  have hx := (mem_twistGraph_iff A K p hA σ q hσ x.val).mp x.property
  have hy := (mem_twistGraph_iff A K p hA σ q hσ y.val).mp y.property
  exact hx.2.trans ((congrArg (ambientAutomorphism A K p hA σ) h1).trans hy.2.symm)

def twistGraphEquiv : twistGraph A K p (fun _ => q) ≃* Model A K :=
  MulEquiv.ofBijective (twistGraphFirstProjection A K p (fun _ => q))
    ⟨twistGraphFirstProjection_injective A K p hA σ q hσ,
      twistGraphFirstProjection_surjective A K p (fun _ => q)⟩

theorem mem_fixedSubgroup_iff (g : Ambient A K) :
    g ∈ fixedSubgroup A K p (fun _ => q) ↔
      g ∈ subgroup A K ∧ ambientAutomorphism A K p hA σ g = g := by
  change (g ∈ subgroup A K ∧ (g, g) ∈ twistGraph A K p (fun _ => q)) ↔ _
  rw [mem_twistGraph_iff A K p hA σ q hσ]
  constructor
  · rintro ⟨hg, _, he⟩
    exact ⟨hg, he.symm⟩
  · rintro ⟨hg, he⟩
    exact ⟨hg, hg, he.symm⟩

omit σ q hσ in
def frobeniusModelAutomorphism [Finite K] (r s : ℕ) [ExpChar K r] :
    MulAut (Model A K) :=
  modelAutomorphism A K p hA (iterateFrobeniusEquiv K r s)

omit σ q hσ in
theorem finiteField_mem_twistGraph_iff [Finite K] (r s : ℕ) [ExpChar K r]
    (gh : Ambient A K × Ambient A K) :
    gh ∈ twistGraph A K p (fun _ => r ^ s) ↔
      gh.1 ∈ subgroup A K ∧ gh.2 =
        ambientAutomorphism A K p hA (iterateFrobeniusEquiv K r s) gh.1 :=
  mem_twistGraph_iff A K p hA (iterateFrobeniusEquiv K r s) (r ^ s)
    (iterateFrobeniusEquiv_def K r s) gh

end SymmetricSubgroupAsymptotics.CFSGSerreFieldDiagram
