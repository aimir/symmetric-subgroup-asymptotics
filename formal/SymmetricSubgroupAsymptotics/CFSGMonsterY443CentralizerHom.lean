import SymmetricSubgroupAsymptotics.CFSGAxiomMonsterY443ElevenGenerators
import SymmetricSubgroupAsymptotics.CFSGMonsterSelectedDerivedInvolution

/-! An actual map from the literal raw Y443 DERIVED group to the original
Y555 node-centralizer DERIVED group. The natural Y443 subdiagram commutes
with terminal f3; five odd-edge conjugations move f3 to the distinguished
central node. This proves membership, not surjectivity or normal image.
No simplicity, group order, model recognition or image-generation premise.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMonsterY443CentralizerHom
open CFSG.Models.MonsterConstruction
open CFSGMonsterSelectedDerivedInvolution (generator generator_square adjacent_cube nonadjacent_square)
namespace Source
abbrev monsterY443ArmLength := CFSGAxiomMonsterY443ElevenGenerators.monsterY443ArmLength
abbrev MonsterY443Gen := CFSGAxiomMonsterY443ElevenGenerators.MonsterY443Gen
abbrev MonsterY443Adj := CFSGAxiomMonsterY443ElevenGenerators.MonsterY443Adj
abbrev monsterY443Node := CFSGAxiomMonsterY443ElevenGenerators.monsterY443Node
abbrev monsterY443SpiderWord := CFSGAxiomMonsterY443ElevenGenerators.monsterY443SpiderWord
abbrev monsterY443Rels := CFSGAxiomMonsterY443ElevenGenerators.monsterY443Rels
abbrev MonsterY443 := CFSGAxiomMonsterY443ElevenGenerators.MonsterY443
abbrev MonsterY443Derived := CFSGAxiomMonsterY443ElevenGenerators.MonsterY443Derived
end Source

private theorem armLength_le_four (i : Fin 3) : Source.monsterY443ArmLength i ≤ 4 := by
  fin_cases i <;> decide

def includeNode : Source.MonsterY443Gen → Node
  | none => none
  | some ⟨i,d⟩ => some (i,⟨d.val,lt_of_lt_of_le d.isLt
      ((armLength_le_four i).trans (by decide : 4 ≤ 5))⟩)

theorem include_adjacent (i j : Source.MonsterY443Gen) :
    Source.MonsterY443Adj i j ↔ Adjacent (includeNode i) (includeNode j) := by
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some q =>
      rcases q with ⟨a,d⟩
      change d.val=0 ↔ (⟨d.val,lt_of_lt_of_le d.isLt
        ((armLength_le_four a).trans (by decide : 4≤5))⟩ : Fin 5)=0
      constructor
      · intro h
        apply Fin.ext
        exact h
      · intro h
        exact congrArg (Fin.val : Fin 5 → ℕ) h
  | some q =>
    rcases q with ⟨i,d⟩
    cases j with
    | none =>
      change d.val=0 ↔ (⟨d.val,lt_of_lt_of_le d.isLt
        ((armLength_le_four i).trans (by decide : 4≤5))⟩ : Fin 5)=0
      constructor
      · intro h
        apply Fin.ext
        exact h
      · intro h
        exact congrArg (Fin.val : Fin 5 → ℕ) h
    | some q => rcases q with ⟨j,e⟩; rfl

private theorem lift_spider :
    FreeGroup.lift (fun i => generator (includeNode i)) Source.monsterY443SpiderWord =
      PresentedGroup.mk relations spider := by
  simp only [CFSGAxiomMonsterY443ElevenGenerators.monsterY443SpiderWord,
    CFSGAxiomMonsterY443ElevenGenerators.monsterY443Node,includeNode,
    map_mul,FreeGroup.lift_apply_of,spider,generator,PresentedGroup.of]
  rfl

def naturalHom : Source.MonsterY443 →* Bimonster :=
  PresentedGroup.toGroup (f := fun i => generator (includeNode i)) (by
    rintro r (((⟨i,rfl⟩ | ⟨i,j,hij,rfl⟩) | ⟨i,j,hne,hij,rfl⟩) | hspider)
    · simpa only [map_pow,FreeGroup.lift_apply_of] using generator_square (includeNode i)
    · simpa only [map_pow,map_mul,FreeGroup.lift_apply_of] using
        adjacent_cube (includeNode i) (includeNode j) ((include_adjacent i j).mp hij)
    · simp only [map_pow,map_mul,FreeGroup.lift_apply_of]
      by_cases he : includeNode i=includeNode j
      · rw [he,←pow_two,generator_square,one_pow]
      · exact nonadjacent_square _ _ he (fun h => hij ((include_adjacent i j).mpr h))
    · rw [Set.mem_singleton_iff] at hspider
      subst r
      rw [map_pow,lift_spider,←map_pow]
      exact PresentedGroup.one_of_mem (rels := relations)
        (x := spider^10) (Or.inr (Or.inr (Or.inr rfl))))

theorem naturalHom_of (i : Source.MonsterY443Gen) :
    naturalHom (PresentedGroup.of i)=generator (includeNode i) := PresentedGroup.toGroup.of _

def terminalNode : Node := some (2,4)
def terminal : Bimonster := generator terminalNode

private theorem include_ne_terminal (i : Source.MonsterY443Gen) : includeNode i≠terminalNode := by
  cases i with
  | none => simp [includeNode,terminalNode]
  | some q =>
    rcases q with ⟨i,d⟩
    intro h
    have he := congrArg (fun q : Node => q.map (fun p => p.2.val)) h
    have hd : d.val<4 := lt_of_lt_of_le d.isLt (armLength_le_four i)
    simp only [includeNode,terminalNode,Option.map_some,Option.some.injEq] at he
    omega

private theorem include_nonadjacent_terminal (i : Source.MonsterY443Gen) :
    ¬Adjacent (includeNode i) terminalNode := by
  cases i with
  | none => simp [includeNode,terminalNode,Adjacent]
  | some q =>
    rcases q with ⟨i,d⟩
    rintro ⟨hi,he⟩
    subst i
    have hd : d.val<3 := d.isLt
    change d.val+1=4 ∨ 4+1=d.val at he
    omega

theorem generator_commutes_terminal (i : Source.MonsterY443Gen) :
    Commute (generator (includeNode i)) terminal := by
  have hx : (generator (includeNode i))⁻¹=generator (includeNode i) :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using generator_square (includeNode i))
  have ht : terminal⁻¹=terminal :=
    inv_eq_of_mul_eq_one_right (by simpa only [terminal,pow_two] using generator_square terminalNode)
  have hp : (generator (includeNode i)*terminal)⁻¹=generator (includeNode i)*terminal :=
    inv_eq_of_mul_eq_one_right (by simpa only [terminal,pow_two] using
      (nonadjacent_square (includeNode i) terminalNode
        (include_ne_terminal i) (include_nonadjacent_terminal i)))
  exact (show terminal*generator (includeNode i)=generator (includeNode i)*terminal by
    simpa only [mul_inv_rev,hx,ht] using hp).symm

theorem naturalHom_mem_centralizer (g : Source.MonsterY443) :
    naturalHom g ∈ Subgroup.centralizer ({terminal} : Set Bimonster) := by
  have hgen : Subgroup.closure (Set.range
      (fun i : Source.MonsterY443Gen => generator (includeNode i))) ≤
        Subgroup.centralizer ({terminal} : Set Bimonster) := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (generator_commutes_terminal i).eq
  have hf : (naturalHom ∘ (PresentedGroup.of : Source.MonsterY443Gen → Source.MonsterY443))=
      (fun i => generator (includeNode i)) := funext naturalHom_of
  have hr : naturalHom.range=Subgroup.closure (Set.range
      (fun i : Source.MonsterY443Gen => generator (includeNode i))) := by
    rw [MonoidHom.range_eq_map,←PresentedGroup.closure_range_of (rels := Source.monsterY443Rels),
      MonoidHom.map_closure,←Set.range_comp,hf]
  exact hgen (hr ▸ MonoidHom.mem_range.mpr ⟨g,rfl⟩)

private theorem adjacent_conjugation {G : Type*} [Group G] (x y : G)
    (hx : x^2=1) (hy : y^2=1) (hxy : (x*y)^3=1) : (x*y)*x*(x*y)⁻¹=y := by
  have hxinv : x⁻¹=x := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hx)
  have hyinv : y⁻¹=y := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hy)
  rw [mul_inv_rev,hxinv,hyinv]
  calc
    x*y*x*(y*x)=x*y*x*y*x*(y*y) := by
      rw [show y*y=1 by simpa only [pow_two] using hy,mul_one]
      group
    _=(x*y)^3*y := by rw [pow_succ,pow_two]; group
    _=y := by rw [hxy,one_mul]

def path (i : Fin 6) : Node := ![none,some (2,0),some (2,1),some (2,2),some (2,3),some (2,4)] i
def step (i : Fin 5) : Bimonster := generator (path i.succ)*generator (path i.castSucc)

theorem step_conjugation (i : Fin 5) :
    step i*generator (path i.succ)*(step i)⁻¹=generator (path i.castSucc) := by
  apply adjacent_conjugation _ _ (generator_square _) (generator_square _)
  apply adjacent_cube
  fin_cases i <;> simp [path,Adjacent]

def transporter : Bimonster := step 0*step 1*step 2*step 3*step 4

theorem transporter_terminal : transporter*terminal*transporter⁻¹=nodeA := by
  have h4 : step 4*generator (path 5)*(step 4)⁻¹=generator (path 4) := step_conjugation 4
  have h3 : step 3*generator (path 4)*(step 3)⁻¹=generator (path 3) := step_conjugation 3
  have h2 : step 2*generator (path 3)*(step 2)⁻¹=generator (path 2) := step_conjugation 2
  have h1 : step 1*generator (path 2)*(step 1)⁻¹=generator (path 1) := step_conjugation 1
  have h0 : step 0*generator (path 1)*(step 0)⁻¹=generator (path 0) := step_conjugation 0
  change transporter*generator (path 5)*transporter⁻¹=generator (path 0)
  calc
    transporter*generator (path 5)*transporter⁻¹=
      step 0*(step 1*(step 2*(step 3*(step 4*generator (path 5)*(step 4)⁻¹)*
        (step 3)⁻¹)*(step 2)⁻¹)*(step 1)⁻¹)*(step 0)⁻¹ := by unfold transporter; group
    _=generator (path 0) := by
      rw [h4,h3,h2,h1,h0]

def conjugatedHom : Source.MonsterY443 →* Bimonster :=
  (MulAut.conj transporter).toMonoidHom.comp naturalHom

theorem conjugatedHom_mem_nodeCentralizer (g : Source.MonsterY443) :
    conjugatedHom g ∈ nodeCentralizer := by
  have hc := Subgroup.mem_centralizer_singleton_iff.mp (naturalHom_mem_centralizer g)
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  change transporter*naturalHom g*transporter⁻¹*nodeA=
    nodeA*(transporter*naturalHom g*transporter⁻¹)
  rw [←transporter_terminal]
  calc
    _=transporter*(naturalHom g*terminal)*transporter⁻¹ := by group
    _=transporter*(terminal*naturalHom g)*transporter⁻¹ := by rw [hc]
    _=_ := by group

def centralizerHom : Source.MonsterY443 →* nodeCentralizer :=
  conjugatedHom.codRestrict nodeCentralizer conjugatedHom_mem_nodeCentralizer

theorem centralizerHom_coe (g : Source.MonsterY443) :
    (centralizerHom g : Bimonster)=transporter*naturalHom g*transporter⁻¹ := rfl

def derivedHom : Source.MonsterY443Derived →* CFSG.Models.Monster :=
  (centralizerHom.comp (commutator Source.MonsterY443).subtype).codRestrict
    (commutator ↥nodeCentralizer) (by
      intro g
      have hle : (commutator Source.MonsterY443).map centralizerHom ≤
          commutator ↥nodeCentralizer := by
        rw [map_commutator_eq]
        exact Subgroup.commutator_mono le_top le_top
      exact hle ⟨g.val,g.property,rfl⟩)

theorem derivedHom_coe (g : Source.MonsterY443Derived) :
    (derivedHom g).val.val=transporter*naturalHom g.val*transporter⁻¹ := rfl

private def selectedNode (i : Fin 4) : Source.MonsterY443Gen := some ⟨0,i⟩

private theorem selected_abelian_eq (i j : Fin 4) (hij : i.val+1=j.val) :
    Abelianization.of (PresentedGroup.of (selectedNode i) : Source.MonsterY443)=
      Abelianization.of (PresentedGroup.of (selectedNode j)) := by
  apply CFSGGeneration.commutative_involutions_eq_of_product_cube
  · rw [←map_pow,CFSGAxiomMonsterY443ElevenGenerators.generator_square,map_one]
  · rw [←map_pow,CFSGAxiomMonsterY443ElevenGenerators.generator_square,map_one]
  · rw [←map_mul,←map_pow]
    rw [CFSGAxiomMonsterY443ElevenGenerators.adjacent_product_cube,map_one]
    exact ⟨rfl,Or.inl hij⟩

private theorem sourceSelected_mem :
    (PresentedGroup.of (selectedNode 1) : Source.MonsterY443)*
      PresentedGroup.of (selectedNode 3) ∈ commutator Source.MonsterY443 := by
  have he := (selected_abelian_eq 1 2 (by decide)).trans (selected_abelian_eq 2 3 (by decide))
  rw [←Abelianization.ker_of Source.MonsterY443]
  change Abelianization.of ((PresentedGroup.of (selectedNode 1) : Source.MonsterY443)*
    PresentedGroup.of (selectedNode 3))=1
  rw [map_mul,he,←map_mul,←pow_two,
    CFSGAxiomMonsterY443ElevenGenerators.generator_square,map_one]

def sourceSelected : Source.MonsterY443Derived :=
  ⟨PresentedGroup.of (selectedNode 1)*PresentedGroup.of (selectedNode 3),sourceSelected_mem⟩

theorem derivedHom_selected_raw :
    (derivedHom sourceSelected).val.val=transporter*
      CFSGMonsterSelectedDerivedInvolution.selectedInvolution.val.val*transporter⁻¹ := by
  change transporter*naturalHom ((PresentedGroup.of (selectedNode 1) : Source.MonsterY443)*
    PresentedGroup.of (selectedNode 3))*transporter⁻¹=_
  rw [map_mul,naturalHom_of,naturalHom_of]
  rfl

theorem derivedHom_selected_ne_one (hn : ¬IsMulCommutative CFSG.Models.Monster) :
    derivedHom sourceSelected≠1 := by
  intro he
  have hr := congrArg (fun x : CFSG.Models.Monster => x.val.val) he
  change (derivedHom sourceSelected).val.val=(1 : Bimonster) at hr
  rw [derivedHom_selected_raw] at hr
  have hz : CFSGMonsterSelectedDerivedInvolution.selectedInvolution.val.val=1 := by
    apply (MulAut.conj transporter).injective
    change transporter*CFSGMonsterSelectedDerivedInvolution.selectedInvolution.val.val*
      transporter⁻¹=transporter*1*transporter⁻¹
    simpa only [mul_one,mul_inv_cancel] using hr
  apply CFSGMonsterSelectedDerivedInvolution.selected_ne_one hn
  apply Subtype.ext
  apply Subtype.ext
  exact hz

theorem derivedHom_ne_one (hn : ¬IsMulCommutative CFSG.Models.Monster) : derivedHom≠1 := by
  intro he
  exact derivedHom_selected_ne_one hn (DFunLike.congr_fun he sourceSelected)

end SymmetricSubgroupAsymptotics.CFSGMonsterY443CentralizerHom
