import SymmetricSubgroupAsymptotics.InvolutionBraidTrace
import SymmetricSubgroupAsymptotics.ConnectedInvolutionDerivedGeneration

/-! Even words in an involution family belong to the ACTUAL ambient
commutator once their abelianization images agree. The family need not
generate the ambient group. In particular this applies inside an actual
node centralizer without claiming to generate that entire centralizer. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.InvolutionEvenWordDerived

 theorem abelianization_eq_of_product_cube {G : Type*} [Group G] (x y : G)
    (hx : x^2=1) (hy : y^2=1) (hxy : (x*y)^3=1) :
    Abelianization.of x=Abelianization.of y := by
  apply CFSGGeneration.commutative_involutions_eq_of_product_cube
  · rw [←map_pow,hx,map_one]
  · rw [←map_pow,hy,map_one]
  · rw [←map_mul,←map_pow,hxy,map_one]

 theorem abelianization_value {G : Type*} [Group G] {ι : Type*}
    (g : ι → G) (base : ι)
    (hsame : ∀ i,Abelianization.of (g i)=Abelianization.of (g base))
    (w : List ι) : Abelianization.of (InvolutionBraidTrace.value g w)=
      Abelianization.of (g base)^w.length := by
  induction w with
  | nil => simp [InvolutionBraidTrace.value]
  | cons i tail ih =>
    change Abelianization.of (g i*InvolutionBraidTrace.value g tail)=_
    rw [map_mul,ih,hsame i]
    exact (pow_succ' (Abelianization.of (g base)) tail.length).symm

 theorem value_mem_commutator {G : Type*} [Group G] {ι : Type*}
    (g : ι → G) (base : ι) (hsq : g base^2=1)
    (hsame : ∀ i,Abelianization.of (g i)=Abelianization.of (g base))
    (w : List ι) (hlen : Even w.length) :
    InvolutionBraidTrace.value g w∈commutator G := by
  rw [←Abelianization.ker_of G]
  change Abelianization.of (InvolutionBraidTrace.value g w)=1
  rw [abelianization_value g base hsame]
  obtain ⟨k,hk⟩ := hlen
  have hs : Abelianization.of (g base)^2=1 := by rw [←map_pow,hsq,map_one]
  rw [hk,←two_mul,pow_mul,hs,one_pow]

end SymmetricSubgroupAsymptotics.InvolutionEvenWordDerived
