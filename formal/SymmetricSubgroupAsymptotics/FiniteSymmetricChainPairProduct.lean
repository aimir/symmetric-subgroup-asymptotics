import SymmetricSubgroupAsymptotics.FiniteSymmetricChainProduct

/-! Products of two actual symmetric-chain partitions. Rectangles in the
two old chains are decomposed symmetrically, retaining both original ranks. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.FiniteSymmetricChains

variable {I J : Type} [Preorder I] [Preorder J] {rI : I → ℕ} {rJ : J → ℕ} {K L : ℕ}
    (D : FiniteSymmetricChains I rI K) (E : FiniteSymmetricChains J rJ L)

def PairProductColour :=
  {c : (D.Colour×E.Colour)×Fin (L+1) //
    c.2.val<K+1-2*D.start c.1.1 ∧ c.2.val<L+1-2*E.start c.1.2}

instance pairProductColour_finite : Finite (D.PairProductColour E) := by
  letI : Finite D.Colour := D.finiteColour
  letI : Finite E.Colour := E.finiteColour
  letI : Fintype D.Colour := Fintype.ofFinite _
  letI : Fintype E.Colour := Fintype.ofFinite _
  exact Finite.of_injective (fun c : D.PairProductColour E => c.val) Subtype.val_injective

def pairProductPoint (a : I×J) := (D.position a.1,E.position a.2)

def pairProductColour (a : I×J) : D.PairProductColour E :=
  let h := RectangleSymmetricChains.colour_lt (D.pairProductPoint E a)
  let j := RectangleSymmetricChains.colour (D.pairProductPoint E a)
  ⟨((D.colour a.1,E.colour a.2),⟨j,by have := (lt_min_iff.mp h).2; omega⟩),lt_min_iff.mp h⟩

private theorem pair_colour_equal {a b : I×J}
    (h : D.pairProductColour E a=D.pairProductColour E b) :
    D.colour a.1=D.colour b.1 ∧ E.colour a.2=E.colour b.2 ∧
      RectangleSymmetricChains.colour (D.pairProductPoint E a)=
        RectangleSymmetricChains.colour (D.pairProductPoint E b) := by
  exact ⟨congrArg (fun c : D.PairProductColour E => c.val.1.1) h,
    congrArg (fun c : D.PairProductColour E => c.val.1.2) h,
    congrArg (fun c : D.PairProductColour E => c.val.2.val) h⟩

/-- Symmetric-chain partitions are closed under the actual product order. -/
def pairProduct : FiniteSymmetricChains (I×J) (fun a => rI a.1+rJ a.2) (K+L) where
  Colour := D.PairProductColour E
  finiteColour := inferInstance
  colour := D.pairProductColour E
  start := fun c => D.start c.val.1.1+E.start c.val.1.2+c.val.2.val
  start_bound := by
    intro c
    have h1 := c.property.1
    have h2 := c.property.2
    have hs1 := D.start_bound c.val.1.1
    have hs2 := E.start_bound c.val.1.2
    omega
  rank_bounds := by
    intro a
    have h := RectangleSymmetricChains.rank_bounds (D.pairProductPoint E a)
    have h1 := D.rank_eq_start_add_position a.1
    have h2 := E.rank_eq_start_add_position a.2
    have hs1 := D.start_bound (D.colour a.1)
    have hs2 := E.start_bound (E.colour a.2)
    change D.start (D.colour a.1)+E.start (E.colour a.2)+
        RectangleSymmetricChains.colour (D.pairProductPoint E a)≤rI a.1+rJ a.2 ∧
      rI a.1+rJ a.2+(D.start (D.colour a.1)+E.start (E.colour a.2)+
        RectangleSymmetricChains.colour (D.pairProductPoint E a))≤K+L
    change RectangleSymmetricChains.colour (D.pairProductPoint E a)≤
        (D.position a.1).val+(E.position a.2).val ∧
      (D.position a.1).val+(E.position a.2).val+
        RectangleSymmetricChains.colour (D.pairProductPoint E a)≤
        (K+1-2*D.start (D.colour a.1))+(L+1-2*E.start (E.colour a.2))-2 at h
    omega
  rank_unique := by
    intro a b hc hr
    obtain ⟨hc1,hc2,hcj⟩ := D.pair_colour_equal E hc
    have ha1 := D.rank_eq_start_add_position a.1
    have ha2 := E.rank_eq_start_add_position a.2
    have hb1 := D.rank_eq_start_add_position b.1
    have hb2 := E.rank_eq_start_add_position b.2
    have hstart1 := congrArg D.start hc1
    have hstart2 := congrArg E.start hc2
    let pa : Fin (K+1-2*D.start (D.colour b.1))×Fin (L+1-2*E.start (E.colour b.2)) :=
      (⟨(D.position a.1).val,by have hpos := (D.position a.1).isLt; omega⟩,
       ⟨(E.position a.2).val,by have hpos := (E.position a.2).isLt; omega⟩)
    have hcjPa : RectangleSymmetricChains.colour pa =
        RectangleSymmetricChains.colour (D.pairProductPoint E b) := by
      change min (D.position a.1).val
        ((L+1-2*E.start (E.colour b.2))-1-(E.position a.2).val) = _
      have hn : (L+1-2*E.start (E.colour b.2))-1-(E.position a.2).val =
          (L+1-2*E.start (E.colour a.2))-1-(E.position a.2).val := by omega
      rw [hn]
      exact hcj
    have hp := RectangleSymmetricChains.same_colour_rank_injective pa (D.pairProductPoint E b)
      hcjPa (by change (D.position a.1).val+(E.position a.2).val=
        (D.position b.1).val+(E.position b.2).val; omega)
    have hp1 := congrArg (fun z => z.1.val) hp
    have hp2 := congrArg (fun z => z.2.val) hp
    change (D.position a.1).val=(D.position b.1).val at hp1
    change (E.position a.2).val=(E.position b.2).val at hp2
    exact Prod.ext (D.rank_unique _ _ hc1 (by omega)) (E.rank_unique _ _ hc2 (by omega))
  rank_surjective := by
    intro c t hlo hhi
    let s1 := D.start c.val.1.1
    let s2 := E.start c.val.1.2
    let j := c.val.2.val
    have hs1 := D.start_bound c.val.1.1
    have hs2 := E.start_bound c.val.1.2
    have hj1 := c.property.1
    have hj2 := c.property.2
    have hct : j<min (K+1-2*s1) (L+1-2*s2) := lt_min_iff.mpr ⟨hj1,hj2⟩
    obtain ⟨b,hb,hbr⟩ := RectangleSymmetricChains.rank_surjective hct
      (r := t-s1-s2) (by change s1+s2+j≤t at hlo; omega)
      (by change t+(s1+s2+j)≤K+L at hhi; omega)
    obtain ⟨x,hxc,hxr⟩ := D.rank_surjective c.val.1.1 (s1+b.1.val)
      (by dsimp [s1]; omega) (by have := b.1.isLt; dsimp [s1] at *; omega)
    obtain ⟨y,hyc,hyr⟩ := E.rank_surjective c.val.1.2 (s2+b.2.val)
      (by dsimp [s2]; omega) (by have := b.2.isLt; dsimp [s2] at *; omega)
    have hpx : (D.position x).val=b.1.val := by
      have h := D.rank_eq_start_add_position x
      have hstart := congrArg D.start hxc
      dsimp [s1] at hxr
      omega
    have hpy : (E.position y).val=b.2.val := by
      have h := E.rank_eq_start_add_position y
      have hstart := congrArg E.start hyc
      dsimp [s2] at hyr
      omega
    have hpc : RectangleSymmetricChains.colour (D.pairProductPoint E (x,y))=j := by
      change min (D.position x).val ((L+1-2*E.start (E.colour y))-1-(E.position y).val)=j
      rw [hpx,hpy,hyc]
      exact hb
    have hac : D.pairProductColour E (x,y)=c := by
      apply Subtype.ext
      apply Prod.ext (Prod.ext hxc hyc)
      exact Fin.ext hpc
    refine ⟨(x,y),hac,?_⟩
    change rI x+rJ y=t
    have hlow : s1+s2≤t := by change s1+s2+j≤t at hlo; omega
    dsimp [s1] at hxr
    dsimp [s2] at hyr
    omega
  chain_le := by
    intro a b hc hr
    obtain ⟨hc1,hc2,hcj⟩ := D.pair_colour_equal E hc
    have ha1 := D.rank_eq_start_add_position a.1
    have ha2 := E.rank_eq_start_add_position a.2
    have hb1 := D.rank_eq_start_add_position b.1
    have hb2 := E.rank_eq_start_add_position b.2
    have hstart1 := congrArg D.start hc1
    have hstart2 := congrArg E.start hc2
    let pa : Fin (K+1-2*D.start (D.colour b.1))×Fin (L+1-2*E.start (E.colour b.2)) :=
      (⟨(D.position a.1).val,by have hpos := (D.position a.1).isLt; omega⟩,
       ⟨(E.position a.2).val,by have hpos := (E.position a.2).isLt; omega⟩)
    have hcjPa : RectangleSymmetricChains.colour pa =
        RectangleSymmetricChains.colour (D.pairProductPoint E b) := by
      change min (D.position a.1).val
        ((L+1-2*E.start (E.colour b.2))-1-(E.position a.2).val) = _
      have hn : (L+1-2*E.start (E.colour b.2))-1-(E.position a.2).val =
          (L+1-2*E.start (E.colour a.2))-1-(E.position a.2).val := by omega
      rw [hn]
      exact hcj
    have hsum : (D.position a.1).val+(E.position a.2).val≤
        (D.position b.1).val+(E.position b.2).val := by omega
    have hp : (D.position a.1).val≤(D.position b.1).val ∧
        (E.position a.2).val≤(E.position b.2).val := by
      rcases RectangleSymmetricChains.same_colour_comparable pa (D.pairProductPoint E b) hcjPa with h|h
      · exact ⟨h.1,h.2⟩
      · have h1 := h.1
        have h2 := h.2
        change (D.position b.1).val≤(D.position a.1).val at h1
        change (E.position b.2).val≤(E.position a.2).val at h2
        constructor <;> omega
    exact ⟨D.chain_le _ _ hc1 (by omega),E.chain_le _ _ hc2 (by omega)⟩

end SymmetricSubgroupAsymptotics.FiniteSymmetricChains
