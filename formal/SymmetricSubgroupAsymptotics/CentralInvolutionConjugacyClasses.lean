import SymmetricSubgroupAsymptotics.FiniteInvolutionQuotientCardinality
import Mathlib.Algebra.Group.Conj
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Tactic.Group

/-! Multiplication by a literal central involution pairs conjugacy
classes. A surjective homomorphism whose kernel is precisely {1,z}
has exactly these pairs as its conjugacy-class fibres. The finite
class-count identity retains the actual homomorphism and kernel. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CentralInvolutionConjugacyClasses
variable {G Q : Type*} [Group G] [Group Q]

def translate (z : G) (hz : z ∈ Subgroup.center G) : ConjClasses G → ConjClasses G :=
  Quotient.lift (fun x : G => ConjClasses.mk (z*x)) (by
    intro x y hxy
    apply ConjClasses.mk_eq_mk_iff_isConj.mpr
    obtain ⟨g,hg⟩ := isConj_iff.mp hxy
    refine isConj_iff.mpr ⟨g,?_⟩
    calc
      g*(z*x)*g⁻¹=(g*z)*(x*g⁻¹) := by group
      _ =(z*g)*(x*g⁻¹) := by rw [Subgroup.mem_center_iff.mp hz g]
      _ =z*(g*x*g⁻¹) := by group
      _ =z*y := by rw [hg])

theorem translate_mk (z : G) (hz : z ∈ Subgroup.center G) (x : G) :
    translate z hz (ConjClasses.mk x)=ConjClasses.mk (z*x) := rfl

theorem translate_involutive (z : G) (hz : z ∈ Subgroup.center G) (hzz : z*z=1) :
    Function.Involutive (translate z hz) := by
  intro c
  obtain ⟨x,rfl⟩ := ConjClasses.mk_surjective c
  change ConjClasses.mk (z*(z*x))=ConjClasses.mk x
  rw [← mul_assoc,hzz,one_mul]

theorem map_translate (f : G →* Q) (z : G) (hz : z ∈ Subgroup.center G)
    (hfz : f z=1) (c : ConjClasses G) :
    ConjClasses.map f (translate z hz c)=ConjClasses.map f c := by
  obtain ⟨x,rfl⟩ := ConjClasses.mk_surjective c
  change ConjClasses.mk (f (z*x))=ConjClasses.mk (f x)
  rw [map_mul,hfz,one_mul]

theorem map_eq_iff (f : G →* Q) (hf : Function.Surjective f)
    (z : G) (hz : z ∈ Subgroup.center G)
    (hker : ∀ g : G, f g=1 ↔ g=1 ∨ g=z) (c d : ConjClasses G) :
    ConjClasses.map f c=ConjClasses.map f d ↔ c=d ∨ c=translate z hz d := by
  obtain ⟨x,rfl⟩ := ConjClasses.mk_surjective c
  obtain ⟨y,rfl⟩ := ConjClasses.mk_surjective d
  constructor
  · intro he
    have hc : IsConj (f x) (f y) := ConjClasses.mk_eq_mk_iff_isConj.mp he
    obtain ⟨q,hq⟩ := isConj_iff.mp hc
    obtain ⟨g,hg⟩ := hf q
    have hm : f ((g*x*g⁻¹)*y⁻¹)=1 := by
      rw [map_mul,map_mul,map_mul,map_inv,map_inv,hg,hq,mul_inv_cancel]
    rcases (hker _).mp hm with h | h
    · left
      exact ConjClasses.mk_eq_mk_iff_isConj.mpr
        (isConj_iff.mpr ⟨g,mul_inv_eq_one.mp h⟩)
    · right
      change ConjClasses.mk x=ConjClasses.mk (z*y)
      exact ConjClasses.mk_eq_mk_iff_isConj.mpr
        (isConj_iff.mpr ⟨g,mul_inv_eq_iff_eq_mul.mp h⟩)
  · rintro (he | he)
    · exact congrArg (ConjClasses.map f) he
    · rw [he]
      exact map_translate f z hz ((hker z).mpr (Or.inr rfl)) _

theorem twice_class_card_eq [Finite G] (f : G →* Q) (hf : Function.Surjective f)
    (z : G) (hz : z ∈ Subgroup.center G) (hzz : z*z=1)
    (hker : ∀ g : G, f g=1 ↔ g=1 ∨ g=z) :
    2*Nat.card (ConjClasses Q)=Nat.card (ConjClasses G)+
      Nat.card {c : ConjClasses G // translate z hz c=c} := by
  letI : Finite Q := Finite.of_surjective f hf
  letI : Finite (ConjClasses G) :=
    Finite.of_surjective (@ConjClasses.mk G _) ConjClasses.mk_surjective
  letI : Finite (ConjClasses Q) :=
    Finite.of_surjective (@ConjClasses.mk Q _) ConjClasses.mk_surjective
  exact FiniteInvolutionQuotientCardinality.twice_card_eq (ConjClasses.map f)
    (ConjClasses.map_surjective hf) (translate z hz) (translate_involutive z hz hzz)
    (map_translate f z hz ((hker z).mpr (Or.inr rfl)))
    (fun c d he => (map_eq_iff f hf z hz hker c d).mp he)

end SymmetricSubgroupAsymptotics.CentralInvolutionConjugacyClasses
