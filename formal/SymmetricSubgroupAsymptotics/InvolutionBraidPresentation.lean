import SymmetricSubgroupAsymptotics.InvolutionBraidTrace
import Mathlib.GroupTheory.PresentedGroup

/-! Universal involution/commutation/three-braid presentation. A checked
identity in this source maps to ANY actual matching system; no full Y
spider relation, faithfulness, finite Coxeter recognition or whole-target
generation is required. Arbitrary identities proved only in a Y quotient
cannot be transported without a universal-source proof. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.InvolutionBraidPresentation
open InvolutionBraidTrace

variable {ι : Type*}

def relations (adj : ι → ι → Bool) : Set (FreeGroup ι) :=
  {w | (∃ i,w=FreeGroup.of i*FreeGroup.of i) ∨
    (∃ i j,adj i j=false ∧ w=(FreeGroup.of i*FreeGroup.of j)*(FreeGroup.of j*FreeGroup.of i)⁻¹) ∨
    (∃ i j,adj i j=true ∧ w=(FreeGroup.of i*FreeGroup.of j*FreeGroup.of i)*
      (FreeGroup.of j*FreeGroup.of i*FreeGroup.of j)⁻¹)}

abbrev Model (adj : ι → ι → Bool) := PresentedGroup (relations adj)

def generator (adj : ι → ι → Bool) (i : ι) : Model adj := PresentedGroup.of i

structure System (adj : ι → ι → Bool) (G : Type*) [Group G] where
  generator : ι → G
  square : ∀ i,generator i*generator i=1
  commute : ∀ i j,adj i j=false → generator i*generator j=generator j*generator i
  braid : ∀ i j,adj i j=true → generator i*generator j*generator i=generator j*generator i*generator j

 theorem generator_square (adj : ι → ι → Bool) (i : ι) :
    generator adj i*generator adj i=1 := by
  have h := PresentedGroup.one_of_mem (rels := relations adj)
    (x := FreeGroup.of i*FreeGroup.of i) (Or.inl ⟨i,rfl⟩)
  simpa only [map_mul,PresentedGroup.of,generator] using h

 theorem generator_commute (adj : ι → ι → Bool) (i j : ι) (hij : adj i j=false) :
    generator adj i*generator adj j=generator adj j*generator adj i := by
  have h := PresentedGroup.one_of_mem (rels := relations adj)
    (x := (FreeGroup.of i*FreeGroup.of j)*(FreeGroup.of j*FreeGroup.of i)⁻¹)
    (Or.inr (Or.inl ⟨i,j,hij,rfl⟩))
  have he : (generator adj i*generator adj j)*(generator adj j*generator adj i)⁻¹=1 := by
    simpa only [map_mul,map_inv,PresentedGroup.of,generator] using h
  exact mul_inv_eq_one.mp he

 theorem generator_braid (adj : ι → ι → Bool) (i j : ι) (hij : adj i j=true) :
    generator adj i*generator adj j*generator adj i=generator adj j*generator adj i*generator adj j := by
  have h := PresentedGroup.one_of_mem (rels := relations adj)
    (x := (FreeGroup.of i*FreeGroup.of j*FreeGroup.of i)*
      (FreeGroup.of j*FreeGroup.of i*FreeGroup.of j)⁻¹)
    (Or.inr (Or.inr ⟨i,j,hij,rfl⟩))
  have he : (generator adj i*generator adj j*generator adj i)*
      (generator adj j*generator adj i*generator adj j)⁻¹=1 := by
    simpa only [map_mul,map_inv,PresentedGroup.of,generator] using h
  exact mul_inv_eq_one.mp he

private theorem all_relators {adj : ι → ι → Bool} {G : Type*} [Group G]
    (S : System adj G) : ∀ r∈relations adj,FreeGroup.lift S.generator r=1 := by
  intro r hr
  rcases hr with ⟨i,rfl⟩ | ⟨i,j,hij,rfl⟩ | ⟨i,j,hij,rfl⟩
  · simpa only [map_mul,FreeGroup.lift_apply_of] using S.square i
  · simp only [map_mul,map_inv,FreeGroup.lift_apply_of]
    rw [S.commute i j hij,mul_inv_cancel]
  · simp only [map_mul,map_inv,FreeGroup.lift_apply_of]
    rw [S.braid i j hij,mul_inv_cancel]

 def evaluation {adj : ι → ι → Bool} {G : Type*} [Group G]
    (S : System adj G) : Model adj →* G := PresentedGroup.toGroup (all_relators S)

 theorem evaluation_generator {adj : ι → ι → Bool} {G : Type*} [Group G]
    (S : System adj G) (i : ι) : evaluation S (generator adj i)=S.generator i := by
  simp [evaluation,generator]

 theorem evaluation_value {adj : ι → ι → Bool} {G : Type*} [Group G]
    (S : System adj G) (w : List ι) :
    evaluation S (value (generator adj) w)=value S.generator w := by
  induction w with
  | nil => simp [value]
  | cons i tail ih =>
    change evaluation S (generator adj i*value (generator adj) tail)=S.generator i*value S.generator tail
    rw [map_mul,evaluation_generator,ih]

 theorem transfer_word_identity {adj : ι → ι → Bool} {G : Type*} [Group G]
    (S : System adj G) (u v : List ι)
    (h : value (generator adj) u=value (generator adj) v) : value S.generator u=value S.generator v := by
  simpa only [evaluation_value] using congrArg (evaluation S) h

 theorem universal_word_identity_of_check [DecidableEq ι] (adj : ι → ι → Bool)
    (u : List ι) (trace : List (Step ι)) (v : List ι)
    (h : checkTo adj u trace v=true) : value (generator adj) u=value (generator adj) v :=
  checkTo_sound adj (generator adj) (generator_square adj)
    (generator_commute adj) (generator_braid adj) u trace v h

end SymmetricSubgroupAsymptotics.InvolutionBraidPresentation
