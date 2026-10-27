import SymmetricSubgroupAsymptotics.CFSGYSectionEvenOrder

/-! A selected adjacent product survives the FULL derived centre.
Another-arm reflection makes a genuine derived inverter. Centrality
would give both square and cube one. The resulting adjacent collapse
propagates through the original Y presentation and makes its actual
derived-centre quotient commutative, contradicting the inherited input.
No parabolic recognition, group order, finiteness or simplicity is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGYAdjacentDerivedNoncentral
open CFSG.Models.YGroups CFSGGeneration CFSGReduction

def generator (arms : Arms) (i : Node arms) : CFSG.Models.YGroups.Group arms :=
  PresentedGroup.of (rels := relations arms) i

private theorem generator_square (arms : Arms) (i : Node arms) :
    generator arms i ^ 2 = 1 := y_generator_sq arms i

private theorem nonadjacent_commute (arms : Arms) (i j : Node arms)
    (hne : i ≠ j) (hij : ¬Adjacent arms i j) :
    Commute (generator arms i) (generator arms j) := by
  have hi : (generator arms i)⁻¹ = generator arms i :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using generator_square arms i)
  have hj : (generator arms j)⁻¹ = generator arms j :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using generator_square arms j)
  have hp : (generator arms i * generator arms j)⁻¹ = generator arms i * generator arms j :=
    inv_eq_of_mul_eq_one_right
      (by simpa only [pow_two] using y_nonadjacent_product_sq arms i j ⟨hne,hij⟩)
  have he : generator arms j * generator arms i = generator arms i * generator arms j := by
    simpa only [mul_inv_rev, hi, hj] using hp
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

private theorem collapse (arms : Arms) (i j k : Node arms)
    (he : generator arms i = generator arms j) (hjk : Adjacent arms j k)
    (hne : i ≠ k) (hik : ¬Adjacent arms i k) : generator arms j = generator arms k := by
  apply eq_of_product_square_cube _ _ (generator_square arms k)
  · rw [←he]
    exact y_nonadjacent_product_sq arms i k ⟨hne,hik⟩
  · exact y_adjacent_product_cube arms j k hjk

theorem source_commutative_of_first_eq_second (arms : Arms) (a : Fin 3)
    (he : generator arms (near arms a 0) = generator arms (near arms a 1)) :
    IsMulCommutative (CFSG.Models.YGroups.Group arms) := by
  have hbaseA : generator arms (near arms a 0) = generator arms none :=
    collapse arms (near arms a 1) (near arms a 0) none he.symm
      (by simp [Adjacent,near]) (by simp [near]) (by simp [Adjacent,near])
  have hbase (b : Fin 3) : generator arms (near arms b 0) = generator arms none := by
    by_cases hba : b=a
    · subst b
      exact hbaseA
    · have h := collapse arms (near arms a 0) none (near arms b 0) hbaseA
        (by simp [Adjacent,near])
        (by simp [near,Ne.symm hba]) (by simp [Adjacent,near])
      exact h.symm
  have harm : ∀ (b : Fin 3) (d : ℕ) (hd : d<arms.length b),
      generator arms (some ⟨b,⟨d,hd⟩⟩) = generator arms none := by
    intro b d
    induction d with
    | zero =>
      intro hd
      exact hbase b
    | succ d ih =>
      intro hd
      have hd' : d<arms.length b := by omega
      have hp := ih hd'
      have h := collapse arms none (some ⟨b,⟨d,hd'⟩⟩) (some ⟨b,⟨d+1,hd⟩⟩) hp.symm
        (by dsimp only [Adjacent]; exact ⟨rfl,Or.inl rfl⟩)
        (by simp) (by simp [Adjacent])
      exact h.symm.trans hp
  have hall (i : Node arms) : generator arms i = generator arms none := by
    cases i with
    | none => rfl
    | some q => exact harm q.1 q.2.val q.2.isLt
  have hgen : Subgroup.closure (Set.range (generator arms)) = ⊤ :=
    PresentedGroup.closure_range_of (relations arms)
  have hle : (⊤ : Subgroup (CFSG.Models.YGroups.Group arms)) ≤
      Subgroup.zpowers (generator arms none) := by
    rw [←hgen]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    rw [hall i]
    exact Subgroup.mem_zpowers _
  letI : IsCyclic (CFSG.Models.YGroups.Group arms) := isCyclic_iff_exists_zpowers_eq_top.mpr
    ⟨generator arms none,le_antisymm le_top hle⟩
  infer_instance

def armCube (arms : Arms) (a : Fin 3) : commutator (CFSG.Models.YGroups.Group arms) :=
  derivedInvolutionProduct (generator arms) none
    (fun i => by simpa only [pow_two] using generator_square arms i)
    (y_abelianization_generators_equal arms) (near arms a 0) (near arms a 1)

def armInverter (arms : Arms) (a b : Fin 3) : commutator (CFSG.Models.YGroups.Group arms) :=
  derivedInvolutionProduct (generator arms) none
    (fun i => by simpa only [pow_two] using generator_square arms i)
    (y_abelianization_generators_equal arms) (near arms a 0) (near arms b 0)

theorem armCube_cube (arms : Arms) (a : Fin 3) : armCube arms a ^ 3 = 1 := by
  apply Subtype.ext
  exact y_adjacent_product_cube arms (near arms a 0) (near arms a 1)
    (by simp [Adjacent,near])

theorem armCube_ne_one (arms : Arms) (a : Fin 3)
    (hn : ¬IsMulCommutative (SimpleSection arms)) : armCube arms a ≠ 1 := by
  intro h
  have hraw := congrArg (fun z : commutator (CFSG.Models.YGroups.Group arms) => z.val) h
  change generator arms (near arms a 0) * generator arms (near arms a 1) = 1 at hraw
  have he : generator arms (near arms a 0) = generator arms (near arms a 1) :=
    eq_of_product_square_cube _ _ (generator_square arms _)
      (by rw [hraw,one_pow]) (by rw [hraw,one_pow])
  letI : IsMulCommutative (CFSG.Models.YGroups.Group arms) :=
    source_commutative_of_first_eq_second arms a he
  apply hn
  refine ⟨⟨fun x y => ?_⟩⟩
  obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center (commutator (CFSG.Models.YGroups.Group arms))) x
  obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center (commutator (CFSG.Models.YGroups.Group arms))) y
  rw [←map_mul,←map_mul]
  congr 1
  apply Subtype.ext
  exact IsMulCommutative.is_comm.comm u.val v.val

private theorem different_arms_commute (arms : Arms) (a b : Fin 3) (hab : a≠b)
    (d e : Fin 2) : Commute (generator arms (near arms a d)) (generator arms (near arms b e)) := by
  apply nonadjacent_commute
  · intro h
    have he : a=b := congrArg (fun q : Node arms =>
      match q with | none => (0 : Fin 3) | some v => v.1) h
    exact hab he
  · intro h
    exact hab h.1

theorem armCube_conjugated_inverse (arms : Arms) (a b : Fin 3) (hab : a≠b) :
    armInverter arms a b * armCube arms a * (armInverter arms a b)⁻¹ =
      (armCube arms a)⁻¹ := by
  let x := generator arms (near arms a 0)
  let y := generator arms (near arms a 1)
  let z := generator arms (near arms b 0)
  have hi : x⁻¹=x := inv_eq_of_mul_eq_one_right
    (by simpa only [pow_two] using generator_square arms (near arms a 0))
  have hj : y⁻¹=y := inv_eq_of_mul_eq_one_right
    (by simpa only [pow_two] using generator_square arms (near arms a 1))
  have hxx : x*x=1 := by simpa only [pow_two] using generator_square arms (near arms a 0)
  have hc : Commute z (x*y) :=
    (different_arms_commute arms b a (Ne.symm hab) 0 0).mul_right
      (different_arms_commute arms b a (Ne.symm hab) 0 1)
  apply Subtype.ext
  change (x*z)*(x*y)*(x*z)⁻¹=(x*y)⁻¹
  calc
    _ = x*(z*(x*y))*z⁻¹*x⁻¹ := by group
    _ = x*((x*y)*z)*z⁻¹*x⁻¹ := by rw [hc.eq]
    _ = (x*x)*y*x⁻¹ := by group
    _ = y*x := by rw [hxx,one_mul,hi]
    _ = _ := by rw [mul_inv_rev,hi,hj]

theorem armCube_not_mem_center (arms : Arms) (a : Fin 3)
    (hn : ¬IsMulCommutative (SimpleSection arms)) :
    armCube arms a ∉ Subgroup.center (commutator (CFSG.Models.YGroups.Group arms)) := by
  intro hcentral
  obtain ⟨b,hba⟩ := exists_ne a
  have hc := Subgroup.mem_center_iff.mp hcentral (armInverter arms a b)
  have hfixed : armInverter arms a b * armCube arms a * (armInverter arms a b)⁻¹ =
      armCube arms a := by rw [hc]; group
  have hinv : (armCube arms a)⁻¹=armCube arms a :=
    (armCube_conjugated_inverse arms a b (Ne.symm hba)).symm.trans hfixed
  have hs : armCube arms a ^ 2=1 := by
    rw [pow_two]
    calc
      _ = (armCube arms a)⁻¹ * armCube arms a :=
        congrArg (fun z => z * armCube arms a) hinv.symm
      _ = 1 := inv_mul_cancel _
  have he : armCube arms a=1 := by
    have h : armCube arms a ^ 2 * armCube arms a=1 := by
      simpa only [pow_succ] using armCube_cube arms a
    rwa [hs,one_mul] at h
  exact armCube_ne_one arms a hn he

def sectionArmCube (arms : Arms) (a : Fin 3) : SimpleSection arms :=
  QuotientGroup.mk' (Subgroup.center (commutator (CFSG.Models.YGroups.Group arms))) (armCube arms a)

theorem sectionArmCube_cube (arms : Arms) (a : Fin 3) : sectionArmCube arms a ^ 3=1 := by
  change (QuotientGroup.mk' _ (armCube arms a)) ^ 3=1
  rw [←map_pow,armCube_cube,map_one]

theorem sectionArmCube_ne_one (arms : Arms) (a : Fin 3)
    (hn : ¬IsMulCommutative (SimpleSection arms)) : sectionArmCube arms a≠1 := by
  intro h
  exact armCube_not_mem_center arms a hn ((QuotientGroup.eq_one_iff _).mp h)

theorem sectionArmCube_order_three (arms : Arms) (a : Fin 3)
    (hn : ¬IsMulCommutative (SimpleSection arms)) : orderOf (sectionArmCube arms a)=3 := by
  have hd := orderOf_dvd_of_pow_eq_one (sectionArmCube_cube arms a)
  have hn1 : orderOf (sectionArmCube arms a)≠1 := by
    intro h
    exact sectionArmCube_ne_one arms a hn (orderOf_eq_one_iff.mp h)
  exact ((Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd).resolve_left hn1

end SymmetricSubgroupAsymptotics.CFSGYAdjacentDerivedNoncentral
