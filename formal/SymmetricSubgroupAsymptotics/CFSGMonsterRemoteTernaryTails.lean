import SymmetricSubgroupAsymptotics.CFSGMonsterE6ActualNormalizerIndex
import SymmetricSubgroupAsymptotics.TernaryCubePowerHom
import SymmetricSubgroupAsymptotics.TernaryPairedInversionIndependence
import Mathlib.GroupTheory.NoncommCoprod

/-! Two independent actual ternary tail elements commuting with the
selected E6 reflection image. They belong to the original derived node
centralizer. No statement about generating that full centralizer is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMonsterRemoteTernaryTails
open CFSG.Models.MonsterConstruction CFSGMonsterSelectedDerivedInvolution

def armNode (i : Fin 3) (d : Fin 5) : Node := some (i,d)

private theorem commute_of_nonadjacent (i j : Node) (hne : i≠j) (hn : ¬Adjacent i j) :
    Commute (generator i) (generator j) := by
  have hi : (generator i)⁻¹=generator i :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using generator_square i)
  have hj : (generator j)⁻¹=generator j :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using generator_square j)
  have hp : (generator i*generator j)⁻¹=generator i*generator j :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using nonadjacent_square i j hne hn)
  have hh : generator j*generator i=generator i*generator j := by
    simpa only [mul_inv_rev,hi,hj] using hp
  exact hh.symm

private theorem equal_of_square_cube {H : Type*} [Group H] (x y : H)
    (hy : y^2=1) (h2 : (x*y)^2=1) (h3 : (x*y)^3=1) : x=y := by
  have hp : x*y=1 := by
    have hh : (x*y)^2*(x*y)=1 := by simpa only [pow_succ] using h3
    simpa only [h2,one_mul] using hh
  calc
    x=x*(y*y) := by rw [←pow_two,hy,mul_one]
    _=(x*y)*y := (mul_assoc _ _ _).symm
    _=y := by rw [hp,one_mul]

private theorem collapse (i j k : Node) (he : generator i=generator j)
    (hjk : Adjacent j k) (hne : i≠k) (hik : ¬Adjacent i k) : generator j=generator k := by
  apply equal_of_square_cube _ _ (generator_square k)
  · rw [←he]
    exact nonadjacent_square i k hne hik
  · exact adjacent_cube j k hjk

private theorem commutative_of_base_eq (i : Fin 3)
    (h : generator (armNode i 0)=generator none) : IsMulCommutative Bimonster := by
  have h0 : generator (armNode 0 0)=generator none := by
    by_cases hi : i=0
    · subst i
      exact h
    · have hh := collapse (armNode i 0) none (armNode 0 0) h
        (by simp [armNode,Adjacent]) (by simp [armNode,hi]) (by simp [armNode,Adjacent,hi])
      exact hh.symm
  have h01 : generator (armNode 0 0)=generator (armNode 0 1) :=
    collapse none (armNode 0 0) (armNode 0 1) h0.symm
      (by simp [armNode,Adjacent]) (by simp [armNode]) (by simp [armNode,Adjacent])
  have h12 : generator (armNode 0 1)=generator (armNode 0 2) :=
    collapse none (armNode 0 1) (armNode 0 2) (h0.symm.trans h01)
      (by simp [armNode,Adjacent]) (by simp [armNode]) (by simp [armNode,Adjacent])
  have h23 : generator (armNode 0 2)=generator (armNode 0 3) :=
    collapse none (armNode 0 2) (armNode 0 3) ((h0.symm.trans h01).trans h12)
      (by simp [armNode,Adjacent]) (by simp [armNode]) (by simp [armNode,Adjacent])
  exact bimonster_commutative_of_c_eq_e (h12.trans h23)

private theorem commutative_of_depth_one_two_eq (i : Fin 3)
    (h : generator (armNode i 1)=generator (armNode i 2)) : IsMulCommutative Bimonster := by
  have h10 : generator (armNode i 1)=generator (armNode i 0) :=
    collapse (armNode i 2) (armNode i 1) (armNode i 0) h.symm
      (by simp [armNode,Adjacent]) (by simp [armNode]) (by simp [armNode,Adjacent])
  have h0a : generator (armNode i 0)=generator none :=
    collapse (armNode i 1) (armNode i 0) none h10
      (by simp [armNode,Adjacent]) (by simp [armNode]) (by simp [armNode,Adjacent])
  exact commutative_of_base_eq i h0a

private theorem commutative_of_depth_two_three_eq (i : Fin 3)
    (h : generator (armNode i 2)=generator (armNode i 3)) : IsMulCommutative Bimonster := by
  have h21 : generator (armNode i 2)=generator (armNode i 1) :=
    collapse (armNode i 3) (armNode i 2) (armNode i 1) h.symm
      (by simp [armNode,Adjacent]) (by simp [armNode]) (by simp [armNode,Adjacent])
  exact commutative_of_depth_one_two_eq i h21.symm

private theorem commutative_of_depth_three_four_eq (i : Fin 3)
    (h : generator (armNode i 3)=generator (armNode i 4)) : IsMulCommutative Bimonster := by
  have h32 : generator (armNode i 3)=generator (armNode i 2) :=
    collapse (armNode i 4) (armNode i 3) (armNode i 2) h.symm
      (by simp [armNode,Adjacent]) (by simp [armNode]) (by simp [armNode,Adjacent])
  exact commutative_of_depth_two_three_eq i h32.symm

def centralNode (i : Fin 3) (d : Fin 4) : Node := some (i,⟨d.val+1,by omega⟩)

def centralGenerator (i : Fin 3) (d : Fin 4) : nodeCentralizer := by
  refine ⟨generator (centralNode i d),?_⟩
  change generator (centralNode i d)∈Subgroup.centralizer {generator none}
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  exact (commute_of_nonadjacent _ _ (by simp [centralNode])
    (by simp [centralNode,Adjacent])).eq

private theorem central_square (i : Fin 3) (d : Fin 4) : centralGenerator i d^2=1 := by
  apply Subtype.ext
  exact generator_square _

private theorem central_pair_cube (i : Fin 3) (d e : Fin 4) (h : d.val+1=e.val) :
    (centralGenerator i d*centralGenerator i e)^3=1 := by
  apply Subtype.ext
  apply adjacent_cube
  dsimp only [centralNode,Adjacent]
  exact ⟨rfl,Or.inl (by omega)⟩

private theorem tail_mem_derived (i : Fin 3) (d e : Fin 4) (h : d.val+1=e.val) :
    centralGenerator i d*centralGenerator i e∈commutator nodeCentralizer := by
  have he : Abelianization.of (centralGenerator i d)=Abelianization.of (centralGenerator i e) :=
    InvolutionEvenWordDerived.abelianization_eq_of_product_cube _ _
      (central_square i d) (central_square i e) (central_pair_cube i d e h)
  rw [←Abelianization.ker_of nodeCentralizer]
  change Abelianization.of (centralGenerator i d*centralGenerator i e)=1
  rw [map_mul,he,←map_mul,←pow_two,central_square,map_one]

def firstTail : CFSG.Models.Monster :=
  ⟨centralGenerator 1 2*centralGenerator 1 3,tail_mem_derived 1 2 3 (by decide)⟩
def secondTail : CFSG.Models.Monster :=
  ⟨centralGenerator 2 1*centralGenerator 2 2,tail_mem_derived 2 1 2 (by decide)⟩

theorem first_cube : firstTail^3=1 := by
  apply Subtype.ext
  exact central_pair_cube 1 2 3 (by decide)
theorem second_cube : secondTail^3=1 := by
  apply Subtype.ext
  exact central_pair_cube 2 1 2 (by decide)

theorem first_ne_one (hn : ¬IsMulCommutative CFSG.Models.Monster) : firstTail≠1 := by
  intro he
  have hh := congrArg (fun z : CFSG.Models.Monster => z.val.val) he
  change generator (armNode 1 3)*generator (armNode 1 4)=1 at hh
  have heq : generator (armNode 1 3)=generator (armNode 1 4) :=
    equal_of_square_cube _ _ (generator_square _)
      (by rw [hh,one_pow]) (by rw [hh,one_pow])
  letI : IsMulCommutative Bimonster := commutative_of_depth_three_four_eq 1 heq
  exact hn inferInstance

theorem second_ne_one (hn : ¬IsMulCommutative CFSG.Models.Monster) : secondTail≠1 := by
  intro he
  have hh := congrArg (fun z : CFSG.Models.Monster => z.val.val) he
  change generator (armNode 2 2)*generator (armNode 2 3)=1 at hh
  have heq : generator (armNode 2 2)=generator (armNode 2 3) :=
    equal_of_square_cube _ _ (generator_square _)
      (by rw [hh,one_pow]) (by rw [hh,one_pow])
  letI : IsMulCommutative Bimonster := commutative_of_depth_two_three_eq 2 heq
  exact hn inferInstance

private theorem cross_commute (d e : Fin 4) :
    Commute (centralGenerator 1 d) (centralGenerator 2 e) := by
  apply Subtype.ext
  exact (commute_of_nonadjacent _ _ (by simp [centralNode])
    (by simp [centralNode,Adjacent])).eq

theorem tails_commute : Commute firstTail secondTail := by
  apply Subtype.ext
  exact ((cross_commute 2 1).mul_right (cross_commute 2 2)).mul_left
    ((cross_commute 3 1).mul_right (cross_commute 3 2))

/-- Inner conjugation in the original node centralizer restricts to its
actual derived subgroup; it need not be conjugation by a derived element. -/
def firstInverter : CFSG.Models.Monster →* CFSG.Models.Monster where
  toFun z := ⟨centralGenerator 1 2*z.val*(centralGenerator 1 2)⁻¹,
    (inferInstance : (commutator nodeCentralizer).Normal).conj_mem z.val z.property _⟩
  map_one' := by
    apply Subtype.ext
    change centralGenerator 1 2*1*(centralGenerator 1 2)⁻¹=1
    group
  map_mul' x y := by
    apply Subtype.ext
    change centralGenerator 1 2*(x.val*y.val)*(centralGenerator 1 2)⁻¹=
      (centralGenerator 1 2*x.val*(centralGenerator 1 2)⁻¹)*
        (centralGenerator 1 2*y.val*(centralGenerator 1 2)⁻¹)
    group

theorem firstInverter_first : firstInverter firstTail=firstTail⁻¹ := by
  apply Subtype.ext
  change centralGenerator 1 2*(centralGenerator 1 2*centralGenerator 1 3)*
    (centralGenerator 1 2)⁻¹=(centralGenerator 1 2*centralGenerator 1 3)⁻¹
  have hi : (centralGenerator 1 2)⁻¹=centralGenerator 1 2 :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using central_square 1 2)
  have hj : (centralGenerator 1 3)⁻¹=centralGenerator 1 3 :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using central_square 1 3)
  rw [mul_inv_rev,hi,hj]
  have hs : centralGenerator 1 2*centralGenerator 1 2=1 := by
    simpa only [pow_two] using central_square 1 2
  calc
    _=(centralGenerator 1 2*centralGenerator 1 2)*centralGenerator 1 3*centralGenerator 1 2 := by group
    _=_ := by rw [hs,one_mul]

theorem firstInverter_second : firstInverter secondTail=secondTail := by
  apply Subtype.ext
  change centralGenerator 1 2*(centralGenerator 2 1*centralGenerator 2 2)*
    (centralGenerator 1 2)⁻¹=centralGenerator 2 1*centralGenerator 2 2
  rw [((cross_commute 2 1).mul_right (cross_commute 2 2)).eq]
  group

private theorem first_commutes_eight (j : Fin 8) :
    Commute firstTail.val.val (CFSGMonsterE8BraidBinding.generator j) := by
  have h (d : Fin 5) (hd : d=3 ∨ d=4) :
      Commute (generator (armNode 1 d)) (CFSGMonsterE8BraidBinding.generator j) := by
    apply commute_of_nonadjacent
    · fin_cases j <;> rcases hd with rfl | rfl <;>
        norm_num [armNode,CFSGMonsterE8BraidBinding.node,Adjacent] <;> decide
    · fin_cases j <;> rcases hd with rfl | rfl <;>
        norm_num [armNode,CFSGMonsterE8BraidBinding.node,Adjacent] <;> decide
  exact (h 3 (Or.inl rfl)).mul_left (h 4 (Or.inr rfl))

private theorem second_commutes_eight (j : Fin 8) :
    Commute secondTail.val.val (CFSGMonsterE8BraidBinding.generator j) := by
  have h (d : Fin 5) (hd : d=2 ∨ d=3) :
      Commute (generator (armNode 2 d)) (CFSGMonsterE8BraidBinding.generator j) := by
    apply commute_of_nonadjacent
    · fin_cases j <;> rcases hd with rfl | rfl <;>
        norm_num [armNode,CFSGMonsterE8BraidBinding.node,Adjacent] <;> decide
    · fin_cases j <;> rcases hd with rfl | rfl <;>
        norm_num [armNode,CFSGMonsterE8BraidBinding.node,Adjacent] <;> decide
  exact (h 2 (Or.inl rfl)).mul_left (h 3 (Or.inr rfl))

private theorem commute_value (g : Bimonster)
    (h : ∀ j : Fin 8,Commute g (CFSGMonsterE8BraidBinding.generator j))
    (w : List (Fin 8)) : Commute g (InvolutionBraidTrace.value CFSGMonsterE8BraidBinding.generator w) := by
  induction w with
  | nil => exact Commute.one_right _
  | cons j w ih => exact (h j).mul_right ih

theorem first_commutes_reflection (i : Fin 6) :
    Commute firstTail.val (CFSGMonsterE6ActualNormalizerIndex.centralReflection i) := by
  apply Subtype.ext
  exact (commute_value _ first_commutes_eight (CFSGMonsterE6SelectedReflectionWords.word i)).eq

theorem second_commutes_reflection (i : Fin 6) :
    Commute secondTail.val (CFSGMonsterE6ActualNormalizerIndex.centralReflection i) := by
  apply Subtype.ext
  exact (commute_value _ second_commutes_eight (CFSGMonsterE6SelectedReflectionWords.word i)).eq

end SymmetricSubgroupAsymptotics.CFSGMonsterRemoteTernaryTails
