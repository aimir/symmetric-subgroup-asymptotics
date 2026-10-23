import SymmetricSubgroupAsymptotics.CyclicCoordinateCoboundary
import SymmetricSubgroupAsymptotics.PermutationalWreathProduct

/-! Actual base conjugacy over one cyclic top permutation. Equal cycle
products give a literal conjugating element with trivial top. The result
is uniform in the cycle length and the commutative coefficient group. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CyclicWreathBaseConjugacy
open CyclicCoordinateCoboundary
variable {D : Type*} [CommGroup D] {n : ℕ}

abbrev Wreath (D : Type*) [Group D] (n : ℕ) :=
  PermutationalWreathProduct D (Equiv.Perm (Fin (n+1))) (Fin (n+1))

def cyclicElement (f : Fin (n+1) → D) : Wreath D n :=
  ⟨f,(finRotate (n+1))⁻¹⟩

def baseElement (v : Fin (n+1) → D) : Wreath D n := ⟨v,1⟩

theorem base_conjugate_left (v f : Fin (n+1) → D) (i : Fin (n+1)) :
    (baseElement v * cyclicElement f * (baseElement v)⁻¹).left i=
      v i*f i*(v (finRotate (n+1) i))⁻¹ := by
  simp [baseElement,cyclicElement,PermutationalWreathProduct.mul_left,
    PermutationalWreathProduct.mul_right,PermutationalWreathProduct.inv_left]

theorem base_conjugate_eq_iff (v f g : Fin (n+1) → D) :
    baseElement v * cyclicElement f * (baseElement v)⁻¹=cyclicElement g ↔
      ∀i,g i=v i*f i*(v (finRotate (n+1) i))⁻¹ := by
  constructor
  · intro he i
    have hi := congrArg (fun w : Wreath D n => w.left i) he
    dsimp only at hi
    rw [base_conjugate_left] at hi
    exact hi.symm
  · intro he
    apply PermutationalWreathProduct.ext
    · funext i
      exact (base_conjugate_left v f i).trans (he i).symm
    · simp [baseElement,cyclicElement,PermutationalWreathProduct.mul_right,
        PermutationalWreathProduct.inv_right]

theorem product_eq_iff_exists_gauge (f g : Fin (n+1) → D) :
    (∏i,f i)=(∏i,g i) ↔
      ∃v : Fin (n+1) → D,∀i,g i=v i*f i*(v (finRotate (n+1) i))⁻¹ := by
  constructor
  · intro hprod
    have hr : (∏i,f i*(g i)⁻¹)=1 := by
      rw [Finset.prod_mul_distrib,Finset.prod_inv_distrib,hprod,mul_inv_cancel]
    obtain ⟨v,hv⟩ := exists_coboundary_of_product_one (fun i => f i*(g i)⁻¹) hr
    refine ⟨v,fun i => ?_⟩
    have hi := congrArg (fun t : D => v i*t*g i*(v (finRotate (n+1) i))⁻¹) (hv i)
    simpa [mul_assoc,mul_comm,mul_left_comm] using hi.symm
  · rintro ⟨v,hv⟩
    have hg : g=(fun i => v i*f i*(v (finRotate (n+1) i))⁻¹) := funext hv
    rw [hg,Finset.prod_mul_distrib,Finset.prod_mul_distrib,
      Finset.prod_inv_distrib,Equiv.prod_comp (finRotate (n+1)) v]
    simp [mul_assoc,mul_comm]

theorem product_eq_iff_base_conjugate (f g : Fin (n+1) → D) :
    (∏i,f i)=(∏i,g i) ↔
      ∃v : Fin (n+1) → D,
        baseElement v * cyclicElement f * (baseElement v)⁻¹=cyclicElement g := by
  simp only [base_conjugate_eq_iff]
  exact product_eq_iff_exists_gauge f g

end SymmetricSubgroupAsymptotics.CyclicWreathBaseConjugacy
