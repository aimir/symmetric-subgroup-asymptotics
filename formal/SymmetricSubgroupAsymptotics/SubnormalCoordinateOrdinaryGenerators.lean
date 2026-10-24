import SymmetricSubgroupAsymptotics.SubnormalCoordinateClassBound
import SymmetricSubgroupAsymptotics.FiniteCoordinateOrdinaryGenerators

/-! Ordinary generator budgets need only subnormal coordinate
subgroups. Every successive kernel is retained as a normal subgroup of
the same original source, so its image in each actual coordinate is
subnormal. Only ordinary kernel/quotient rank subadditivity is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.SubnormalCoordinateOrdinaryGenerators
open SubnormalCoordinateClassBound (map_normal_isSubnormal_of_range)

/-- The filtration keeps normal subgroups of H rather than treating
arbitrary coordinate subgroups as subnormal. -/
theorem normal_subgroup_genRank_le_coordinate_bounds
    {H : Type} [Group H] [Finite H] (n : ℕ)
    (V : Fin n → Type) [∀ i, Group (V i)] [∀ i, Finite (V i)]
    (c : Fin n → ℕ) (f : ∀ i, H →* V i)
    (hc : ∀ i (N : Subgroup H), N.Normal → MarkedC4.genRank (N.map (f i)) ≤ c i)
    (L : Subgroup H) (hL : L.Normal)
    (hinj : Function.Injective (fun x : L => fun i => f i x.val)) :
    MarkedC4.genRank L ≤ ∑ i, c i := by
  induction n generalizing L with
  | zero =>
    letI : Subsingleton L := ⟨fun x y => hinj (funext fun i => Fin.elim0 i)⟩
    have hgen : Subgroup.closure ((∅ : Finset L) : Set L) = ⊤ := by
      rw [Finset.coe_empty,Subgroup.closure_empty]
      apply top_unique
      intro x _
      change x = 1
      exact Subsingleton.elim _ _
    simpa only [Finset.card_empty,Fin.sum_univ_zero] using MarkedC4.genRank_le hgen
  | succ n ih =>
    letI : L.Normal := hL
    let K : Subgroup H := L ⊓ (f 0).ker
    letI : K.Normal := by dsimp only [K]; infer_instance
    have htail : Function.Injective (fun x : K => fun i : Fin n => f i.succ x.val) := by
      intro x y he
      have hxy : (⟨x.val,x.property.1⟩ : L) = ⟨y.val,y.property.1⟩ := by
        apply hinj
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact x.property.2.trans y.property.2.symm
        · exact congrFun he j
      exact Subtype.ext (congrArg (fun z : L => z.val) hxy)
    have hK := ih (fun i : Fin n => V i.succ) (fun i => c i.succ) (fun i => f i.succ)
      (fun i N hN => hc i.succ N hN) K inferInstance htail
    let fL : L →* V 0 := (f 0).comp L.subtype
    let eK : fL.ker ≃* K := {
      toFun x := ⟨x.val.val,⟨x.val.property,x.property⟩⟩
      invFun x := ⟨⟨x.val,x.property.1⟩,x.property.2⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_mul' _ _ := rfl }
    have hker : MarkedC4.genRank fL.ker ≤ ∑ i : Fin n, c i.succ := by
      rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv eK]
      exact hK
    have hrange : fL.range = L.map (f 0) := by
      dsimp only [fL]
      rw [MonoidHom.range_comp,Subgroup.range_subtype]
    let eQ : (L ⧸ fL.ker) ≃* L.map (f 0) :=
      (QuotientGroup.quotientKerEquivRange fL).trans (MulEquiv.subgroupCongr hrange)
    have hquot : MarkedC4.genRank (L ⧸ fL.ker) ≤ c 0 := by
      rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv eQ]
      exact hc 0 L hL
    rw [Fin.sum_univ_succ]
    exact (MarkedC4.genRank_le_of_normal fL.ker).trans
      ((Nat.add_le_add hker hquot).trans_eq (Nat.add_comm _ _))

/-- Subnormality of each original image suffices: every normal
coordinate-kernel image has a proved subnormal chain in that component. -/
theorem genRank_le_subnormal_coordinate_bounds
    {H : Type} [Group H] [Finite H] (n : ℕ)
    (V : Fin n → Type) [∀ i, Group (V i)] [∀ i, Finite (V i)]
    (c : Fin n → ℕ) (f : ∀ i, H →* V i)
    (himage : ∀ i, (f i).range.IsSubnormal)
    (hc : ∀ i (L : Subgroup (V i)), L.IsSubnormal → MarkedC4.genRank L ≤ c i)
    (hinj : Function.Injective (fun x => fun i => f i x)) :
    MarkedC4.genRank H ≤ ∑ i, c i := by
  have ht := normal_subgroup_genRank_le_coordinate_bounds n V c f
    (fun i N hN => hc i (N.map (f i))
      (map_normal_isSubnormal_of_range (f i) (himage i) N hN))
    ⊤ Subgroup.normal_top (fun x y he => Subtype.ext (hinj he))
  calc
    MarkedC4.genRank H = MarkedC4.genRank (⊤ : Subgroup H) :=
      (CoprimeNilpotentProductGenerators.genRank_mulEquiv
        (Subgroup.topEquiv : (⊤ : Subgroup H) ≃* H)).symm
    _ ≤ ∑ i, c i := ht

/-- The original finite index set is retained; no independent product
decomposition of the source is assumed. -/
theorem genRank_le_finite_subnormal_coordinate_bounds
    {ι : Type} [Fintype ι] (V : ι → Type) [∀ i, Group (V i)] [∀ i, Finite (V i)]
    (c : ι → ℕ) (H : Type) [Group H] [Finite H] (f : ∀ i, H →* V i)
    (himage : ∀ i, (f i).range.IsSubnormal)
    (hc : ∀ i (L : Subgroup (V i)), L.IsSubnormal → MarkedC4.genRank L ≤ c i)
    (hinj : Function.Injective (fun x => fun i => f i x)) :
    MarkedC4.genRank H ≤ ∑ i, c i := by
  let e := (Fintype.equivFin ι).symm
  have hi : Function.Injective (fun x => fun j => f (e j) x) := by
    intro x y he
    apply hinj
    funext i
    obtain ⟨j,rfl⟩ := e.surjective i
    exact congrFun he j
  have h := genRank_le_subnormal_coordinate_bounds (Fintype.card ι)
    (fun j => V (e j)) (fun j => c (e j)) (fun j => f (e j))
    (fun j => himage (e j)) (fun j => hc (e j)) hi
  simpa only [e.sum_comp] using h

theorem exists_generating_finset
    {ι : Type} [Fintype ι] (V : ι → Type) [∀ i, Group (V i)] [∀ i, Finite (V i)]
    (c : ι → ℕ) (H : Type) [Group H] [Finite H] (f : ∀ i, H →* V i)
    (himage : ∀ i, (f i).range.IsSubnormal)
    (hc : ∀ i (L : Subgroup (V i)), L.IsSubnormal → MarkedC4.genRank L ≤ c i)
    (hinj : Function.Injective (fun x => fun i => f i x)) :
    ∃ S : Finset H, Subgroup.closure (S : Set H) = ⊤ ∧ S.card ≤ ∑ i, c i := by
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G := H)
  exact ⟨S,hgen,hS.le.trans
    (genRank_le_finite_subnormal_coordinate_bounds V c H f himage hc hinj)⟩

end SymmetricSubgroupAsymptotics.SubnormalCoordinateOrdinaryGenerators
