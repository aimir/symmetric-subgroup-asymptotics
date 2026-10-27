import SymmetricSubgroupAsymptotics.External.CFSG.Models.Monster
import SymmetricSubgroupAsymptotics.CFSGInvolutionOrder
import SymmetricSubgroupAsymptotics.ConnectedInvolutionDerivedGeneration

/-! A genuine involution in the ACTUAL derived centralizer defining Monster.
On arm0, c,d,e,f (depths1,2,3,4) centralize nodeA. The adjacent cubes
give c=e in the abelianization of that centralizer, so c*e belongs to its
derived subgroup; the far-node square gives (c*e)^2=1. If c*e=1, c=e;
the Coxeter relations propagate this collapse to all16 bimonster nodes.
The bimonster would be cyclic, contradicting noncommutativity of the
actual derived centralizer. No model identification, finite order,
simplicity, centralizer generation or inverse-coordinate input is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGMonsterSelectedDerivedInvolution
open CFSG.Models.MonsterConstruction

def generator (i : Node) : Bimonster := PresentedGroup.of i
def arm (d : Fin 5) : Node := some (0,d)

theorem generator_square (i : Node) : generator i ^ 2 = 1 := by
  have h := PresentedGroup.one_of_mem (rels := relations)
    (x := FreeGroup.of i ^ 2) (Or.inl ⟨i,rfl⟩)
  simpa only [map_pow,PresentedGroup.of,generator] using h

private theorem adjacent_irrefl (i : Node) : ¬Adjacent i i := by
  cases i with
  | none => exact not_false
  | some q =>
    rcases q with ⟨a,d⟩
    dsimp only [Adjacent]
    omega

theorem adjacent_cube (i j : Node) (hij : Adjacent i j) :
    (generator i * generator j)^3 = 1 := by
  have hne : i ≠ j := by
    intro he
    subst j
    exact adjacent_irrefl i hij
  have h := PresentedGroup.one_of_mem (rels := relations)
    (x := (FreeGroup.of i * FreeGroup.of j)^3)
    (Or.inr (Or.inl ⟨i,j,hne,hij,rfl⟩))
  simpa only [map_pow,map_mul,PresentedGroup.of,generator] using h

theorem nonadjacent_square (i j : Node) (hne : i ≠ j) (hij : ¬Adjacent i j) :
    (generator i * generator j)^2 = 1 := by
  have h := PresentedGroup.one_of_mem (rels := relations)
    (x := (FreeGroup.of i * FreeGroup.of j)^2)
    (Or.inr (Or.inr (Or.inl ⟨i,j,hne,hij,rfl⟩)))
  simpa only [map_pow,map_mul,PresentedGroup.of,generator] using h

private theorem nonadjacent_commute (i j : Node) (hne : i ≠ j)
    (hij : ¬Adjacent i j) : Commute (generator i) (generator j) := by
  have hi : (generator i)⁻¹ = generator i :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using generator_square i)
  have hj : (generator j)⁻¹ = generator j :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using generator_square j)
  have hp : (generator i * generator j)⁻¹ = generator i * generator j :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using nonadjacent_square i j hne hij)
  have he : generator j * generator i = generator i * generator j := by
    simpa only [mul_inv_rev,hi,hj] using hp
  exact he.symm

private theorem eq_of_product_square_cube {G : Type*} [Group G] (x y : G)
    (hy : y^2=1) (h2 : (x*y)^2=1) (h3 : (x*y)^3=1) : x=y := by
  have hp : x*y=1 := by
    have h : (x*y)^2*(x*y)=1 := by simpa only [pow_succ] using h3
    rwa [h2,one_mul] at h
  calc
    x = x*1 := (mul_one x).symm
    _ = x*(y*y) := by rw [←pow_two,hy]
    _ = (x*y)*y := (mul_assoc x y y).symm
    _ = y := by rw [hp,one_mul]

private theorem collapse (i j k : Node) (he : generator i = generator j)
    (hjk : Adjacent j k) (hne : i ≠ k) (hik : ¬Adjacent i k) :
    generator j = generator k := by
  apply eq_of_product_square_cube _ _ (generator_square k)
  · rw [←he]
    exact nonadjacent_square i k hne hik
  · exact adjacent_cube j k hjk

theorem bimonster_commutative_of_c_eq_e (hce : generator (arm 1) = generator (arm 3)) :
    IsMulCommutative Bimonster := by
  have h34 : generator (arm 3) = generator (arm 4) :=
    collapse (arm 1) (arm 3) (arm 4) hce
      (by simp [arm,Adjacent]) (by decide) (by simp [arm,Adjacent])
  have h32 : generator (arm 3) = generator (arm 2) :=
    collapse (arm 4) (arm 3) (arm 2) h34.symm
      (by simp [arm,Adjacent]) (by decide) (by simp [arm,Adjacent])
  have h21 : generator (arm 2) = generator (arm 1) :=
    collapse (arm 3) (arm 2) (arm 1) h32
      (by simp [arm,Adjacent]) (by decide) (by simp [arm,Adjacent])
  have h10 : generator (arm 1) = generator (arm 0) :=
    collapse (arm 2) (arm 1) (arm 0) h21
      (by simp [arm,Adjacent]) (by decide) (by simp [arm,Adjacent])
  have h0a : generator (arm 0) = generator none :=
    collapse (arm 1) (arm 0) none h10
      (by simp [arm,Adjacent]) (by decide) (by simp [arm,Adjacent])
  have hbase (i : Fin 3) : generator (some (i,0)) = generator none := by
    by_cases hi : i=0
    · subst i
      exact h0a
    · have h := collapse (arm 0) none (some (i,0)) h0a
        (by simp [Adjacent])
        (by simp [arm,hi,Ne.symm hi]) (by simp [arm,Adjacent])
      exact h.symm
  have harm : ∀ (i : Fin 3) (d : ℕ) (hd : d<5),
      generator (some (i,⟨d,hd⟩)) = generator none := by
    intro i d
    induction d with
    | zero =>
      intro hd
      exact hbase i
    | succ d ih =>
      intro hd
      have hd' : d<5 := by omega
      have hp := ih hd'
      have h := collapse none (some (i,⟨d,hd'⟩)) (some (i,⟨d+1,hd⟩)) hp.symm
        (by dsimp only [Adjacent]; exact ⟨rfl,Or.inl rfl⟩)
        (by simp) (by simp [Adjacent])
      exact h.symm.trans hp
  have hall (i : Node) : generator i = generator none := by
    cases i with
    | none => rfl
    | some q => exact harm q.1 q.2.val q.2.isLt
  have hgen : Subgroup.closure (Set.range generator) = ⊤ :=
    PresentedGroup.closure_range_of relations
  have hle : (⊤ : Subgroup Bimonster) ≤ Subgroup.zpowers (generator none) := by
    rw [←hgen]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    rw [hall i]
    exact Subgroup.mem_zpowers _
  letI : IsCyclic Bimonster := isCyclic_iff_exists_zpowers_eq_top.mpr
    ⟨generator none,le_antisymm le_top hle⟩
  infer_instance

def centralNode (d : Fin 4) : Node := some (0,⟨d.val+1,by omega⟩)

def centralArm (d : Fin 4) : nodeCentralizer := by
  refine ⟨generator (centralNode d),?_⟩
  change generator (centralNode d) ∈ Subgroup.centralizer {generator none}
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  exact (nonadjacent_commute (centralNode d) none
    (by simp [centralNode]) (by simp [centralNode,Adjacent])).eq

theorem centralArm_square (d : Fin 4) : centralArm d ^ 2 = 1 := by
  apply Subtype.ext
  change generator (centralNode d)^2=1
  exact generator_square _

theorem centralArm_cube (d e : Fin 4) (hde : d.val+1=e.val) :
    (centralArm d * centralArm e)^3=1 := by
  apply Subtype.ext
  change (generator (centralNode d) * generator (centralNode e))^3=1
  apply adjacent_cube
  dsimp only [centralNode,Adjacent]
  exact ⟨rfl,Or.inl (by omega)⟩

private theorem centralArm_abelian_eq (d e : Fin 4) (hde : d.val+1=e.val) :
    Abelianization.of (centralArm d) = Abelianization.of (centralArm e) := by
  apply CFSGGeneration.commutative_involutions_eq_of_product_cube
  · rw [←map_pow,centralArm_square,map_one]
  · rw [←map_pow,centralArm_square,map_one]
  · rw [←map_mul,←map_pow,centralArm_cube d e hde,map_one]

theorem selected_mem_commutator : centralArm 0 * centralArm 2 ∈ commutator ↥nodeCentralizer := by
  have h02 : Abelianization.of (centralArm 0) = Abelianization.of (centralArm 2) :=
    (centralArm_abelian_eq 0 1 (by decide)).trans (centralArm_abelian_eq 1 2 (by decide))
  rw [←Abelianization.ker_of ↥nodeCentralizer]
  change Abelianization.of (centralArm 0 * centralArm 2) = 1
  rw [map_mul,h02,←map_mul,←pow_two,centralArm_square,map_one]

def selectedInvolution : CFSG.Models.Monster :=
  ⟨centralArm 0 * centralArm 2,selected_mem_commutator⟩

theorem selected_square : selectedInvolution^2=1 := by
  apply Subtype.ext
  apply Subtype.ext
  change (generator (arm 1) * generator (arm 3))^2=1
  exact nonadjacent_square _ _ (by decide) (by simp [arm,Adjacent])

theorem selected_ne_one (hn : ¬IsMulCommutative CFSG.Models.Monster) : selectedInvolution≠1 := by
  intro he
  have hraw := congrArg (fun z : CFSG.Models.Monster => z.val.val) he
  change generator (arm 1) * generator (arm 3) = 1 at hraw
  have hce : generator (arm 1) = generator (arm 3) :=
    eq_of_product_square_cube _ _ (generator_square _)
      (by rw [hraw,one_pow]) (by rw [hraw,one_pow])
  letI : IsMulCommutative Bimonster := bimonster_commutative_of_c_eq_e hce
  exact hn inferInstance

theorem even_card (hn : ¬IsMulCommutative CFSG.Models.Monster) :
    Even (Nat.card CFSG.Models.Monster) := by
  by_contra he
  have hodd : Odd (Nat.card CFSG.Models.Monster) := Nat.not_even_iff_odd.mp he
  exact selected_ne_one hn
    (CFSGReduction.eq_one_of_square_eq_one_of_odd_card hodd selectedInvolution selected_square)

end SymmetricSubgroupAsymptotics.CFSGMonsterSelectedDerivedInvolution
