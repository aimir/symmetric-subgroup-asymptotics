import SymmetricSubgroupAsymptotics.OriginalMinimalBlock
import SymmetricSubgroupAsymptotics.ActualBlockWreathEmbedding
import SymmetricSubgroupAsymptotics.ActualWreathRangeFamily
import SymmetricSubgroupAsymptotics.FinitePermutationActionRelabel
import SymmetricSubgroupAsymptotics.PermutationalWreathRelabel

/-! Every literal imprimitive transitive subgroup is recovered from a
primitive local permutation subgroup, one actual transitive top subgroup,
one complete full-component wreath subgroup and one point bijection.
This is an actual labelled cover, not a hypothesis or isomorphism census. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.LabelledMinimalBlockWreathCover
open PermutationalWreathProduct

/-- The decoder retains the literal point bijection and whole wreath subgroup. -/
def decodeHom {n r t : ℕ} (R : Subgroup (Equiv.Perm (Fin r)))
    (Q : Subgroup (Equiv.Perm (Fin t))) (e : Fin n ≃ Fin r × Fin t) :
    PermutationalWreathProduct R Q (Fin t) →* Equiv.Perm (Fin n) :=
  e.symm.permCongrHom.toMonoidHom.comp
    (PermutationalWreathProduct.toPerm (D := R) (Q := Q) (I := Fin t) (Lambda := Fin r))

theorem exists_chart {n : ℕ} (hn : 2 ≤ n) (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] (himp : ¬MulAction.IsPreprimitive J (Fin n)) :
    ∃ r t : ℕ,2 ≤ r ∧ 2 ≤ t ∧ r*t=n ∧
      ∃ R : Subgroup (Equiv.Perm (Fin r)),MulAction.IsPreprimitive R (Fin r) ∧
      ∃ Q : Subgroup (Equiv.Perm (Fin t)),MulAction.IsPretransitive Q (Fin t) ∧
      ∃ L : ActualFullWreathFamily.Family R Q (Fin t),
      ∃ e : Fin n ≃ Fin r × Fin t,L.val.map (decodeHom R Q e)=J := by
  letI : Nontrivial (Fin n) := Finite.one_lt_card_iff_nontrivial.mp
    (by simpa only [Nat.card_fin] using (show 1 < n by omega))
  let x0 : Fin n := ⟨0,by omega⟩
  obtain ⟨block⟩ := originalMinimalBlock_nonempty (A := J) x0 himp
  letI : Fintype block.Points := Fintype.ofFinite _
  letI : MulAction.IsPreprimitive block.Component block.Fibre := block.component_preprimitive
  letI : MulAction.IsPretransitive block.Top block.Points := block.top_pretransitive
  let r := Nat.card block.Fibre
  let t := Nat.card block.Points
  let ef := Finite.equivFin block.Fibre
  let ei := Finite.equivFin block.Points
  let R := FinitePermutationActionRelabel.group ef block.Component
  let Q := FinitePermutationActionRelabel.group ei block.Top
  let eD : block.Component ≃* R := FinitePermutationActionRelabel.groupEquiv ef block.Component
  let eQ : block.Top ≃* Q := FinitePermutationActionRelabel.groupEquiv ei block.Top
  have hlocal (d : block.Component) (x : block.Fibre) : ef (d • x)=eD d • ef x :=
    FinitePermutationActionRelabel.equivariant ef block.Component d x
  have htopAction (q : block.Top) (i : block.Points) : ei (q • i)=eQ q • ei i :=
    FinitePermutationActionRelabel.equivariant ei block.Top q i
  let rho : J →* PermutationalWreathProduct block.Component block.Top block.Points :=
    ActualBlockWreathEmbedding.embedding block.map block.map_equivariant block.base
  have htop : Function.Surjective (rightHom.comp rho) := by
    intro q
    obtain ⟨g,hg⟩ := q.property
    exact ⟨g,Subtype.ext hg⟩
  have hfull : Compression.FullComponent rho :=
    ActualBlockWreathEmbedding.fullComponent block.map block.map_equivariant block.base
  let L0 := ActualWreathRangeFamily.ofHom rho htop hfull
  let re := PermutationalWreathRelabel.relabel eD eQ ei htopAction
  let L := PermutationalWreathRelabel.family eD eQ ei htopAction L0
  let e0 : block.Fibre × block.Points ≃ Fin n :=
    ActualBlockWreathEmbedding.productEquiv block.map block.map_equivariant block.base
  let e : Fin n ≃ Fin r × Fin t := e0.symm.trans (Equiv.prodCongr ef ei)
  have hbefore (g : J) (x : Fin n) : e0.symm (g • x)=rho g • e0.symm x := by
    apply e0.injective
    calc
      _=g • x := e0.apply_symm_apply (g • x)
      _=g • e0 (e0.symm x) := congrArg (fun y : Fin n => g • y)
        (e0.apply_symm_apply x).symm
      _=e0 (rho g • e0.symm x) :=
        (ActualBlockWreathEmbedding.productEquiv_equivariant block.map
          block.map_equivariant block.base g (e0.symm x)).symm
  have hact (g : J) (x : Fin n) : e (g • x)=re (rho g) • e x := by
    change (Equiv.prodCongr ef ei) (e0.symm (g • x))=
      re (rho g) • (Equiv.prodCongr ef ei) (e0.symm x)
    rw [hbefore]
    exact PermutationalWreathRelabel.product_equivariant eD eQ ei htopAction ef hlocal
      (rho g) (e0.symm x)
  have hcomp : ((decodeHom R Q e).comp re.toMonoidHom).comp rho=J.subtype := by
    apply MonoidHom.ext
    intro g
    apply Equiv.ext
    intro x
    change e.symm (re (rho g) • e x)=g.val x
    rw [←hact,e.symm_apply_apply]
    rfl
  refine ⟨r,t,block.degrees_ge_two.1,block.degrees_ge_two.2,?_,R,
    FinitePermutationActionRelabel.preprimitive ef block.Component,Q,
    FinitePermutationActionRelabel.pretransitive ei block.Top,L,e,?_⟩
  · simpa only [Nat.card_fin] using block.degree_product
  · change (rho.range.map re.toMonoidHom).map (decodeHom R Q e)=J
    rw [Subgroup.map_map,MonoidHom.map_range,hcomp,Subgroup.range_subtype]

end SymmetricSubgroupAsymptotics.LabelledMinimalBlockWreathCover
