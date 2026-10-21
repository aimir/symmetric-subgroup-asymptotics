import SymmetricSubgroupAsymptotics.CFSGSerreDiagramModel
import SymmetricSubgroupAsymptotics.CFSGSerreTwistGraphProjection

/-! For a Cartan-preserving permutation and exponent one, the literal
generated twist graph is exactly the graph of the actual diagram action.
This does not assert the analogous statement for field powers or isogenies. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSerreDiagram
open CFSG.Models.Chevalley CFSGSerreLocalNilpotence
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (K : Type) [Field K]
    (p : Equiv.Perm (Fin n)) (hA : ∀ i j, A (p i) (p j) = A i j)
include hA

def conjugationGraph : Subgroup (Ambient A K × Ambient A K) where
  carrier := {gh | gh.2 = MulAut.conj (spaceEquiv A K p hA) gh.1}
  one_mem' := (map_one _).symm
  mul_mem' := by
    intro x y hx hy
    change x.2 * y.2 = MulAut.conj (spaceEquiv A K p hA) (x.1 * y.1)
    rw [hx, hy, map_mul]
  inv_mem' := by
    intro x hx
    change x.2⁻¹ = MulAut.conj (spaceEquiv A K p hA) x.1⁻¹
    rw [hx, map_inv]

theorem twistGraph_le_conjugationGraph :
    twistGraph A K p (fun _ => 1) ≤ conjugationGraph A K p hA := by
  apply (Subgroup.closure_le _).mpr
  rintro gh ⟨negative, i, t, h1, h2⟩
  change gh.2 = MulAut.conj (spaceEquiv A K p hA) gh.1
  apply LinearEquiv.toLinearMap_injective
  have hc := conjugate_isRootElement A K p hA negative i t gh.1 h1
  have h2' : gh.2.toLinearMap = rootOperator A K negative (p i) t := by
    simpa only [pow_one] using h2
  exact h2'.trans hc.symm

theorem mem_twistGraph_iff (gh : Ambient A K × Ambient A K) :
    gh ∈ twistGraph A K p (fun _ => 1) ↔
      gh.1 ∈ subgroup A K ∧ gh.2 = MulAut.conj (spaceEquiv A K p hA) gh.1 := by
  constructor
  · intro hg
    exact ⟨(twistGraph_le_model_prod A K p (fun _ => 1) hg).1,
      twistGraph_le_conjugationGraph A K p hA hg⟩
  · rintro ⟨h1, h2⟩
    have hm : gh.1 ∈ (twistGraph A K p (fun _ => 1)).map
        (MonoidHom.fst (Ambient A K) (Ambient A K)) := by
      rw [twistGraph_fst_image_eq_model]
      exact h1
    obtain ⟨x, hx, he⟩ := hm
    have hx2 := twistGraph_le_conjugationGraph A K p hA hx
    change x.2 = MulAut.conj (spaceEquiv A K p hA) x.1 at hx2
    have he1 : x.1 = gh.1 := he
    have heq : x = gh := Prod.ext he1 (hx2.trans ((congrArg
      (MulAut.conj (spaceEquiv A K p hA)) he1).trans h2.symm))
    exact heq ▸ hx

theorem twistGraphFirstProjection_injective :
    Function.Injective (twistGraphFirstProjection A K p (fun _ => 1)) := by
  intro x y hxy
  have h1 : x.val.1 = y.val.1 := congrArg Subtype.val hxy
  apply Subtype.ext
  apply Prod.ext h1
  have hx := (mem_twistGraph_iff A K p hA x.val).mp x.property
  have hy := (mem_twistGraph_iff A K p hA y.val).mp y.property
  exact hx.2.trans ((congrArg (MulAut.conj (spaceEquiv A K p hA)) h1).trans hy.2.symm)

def twistGraphEquiv : twistGraph A K p (fun _ => 1) ≃* Model A K :=
  MulEquiv.ofBijective (twistGraphFirstProjection A K p (fun _ => 1))
    ⟨twistGraphFirstProjection_injective A K p hA,
      twistGraphFirstProjection_surjective A K p (fun _ => 1)⟩

theorem mem_fixedSubgroup_iff (g : Ambient A K) :
    g ∈ fixedSubgroup A K p (fun _ => 1) ↔
      g ∈ subgroup A K ∧ MulAut.conj (spaceEquiv A K p hA) g = g := by
  change (g ∈ subgroup A K ∧ (g, g) ∈ twistGraph A K p (fun _ => 1)) ↔ _
  rw [mem_twistGraph_iff A K p hA]
  constructor
  · rintro ⟨hg, _, he⟩
    exact ⟨hg, he.symm⟩
  · rintro ⟨hg, he⟩
    exact ⟨hg, hg, he.symm⟩

end SymmetricSubgroupAsymptotics.CFSGSerreDiagram
