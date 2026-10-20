import SymmetricSubgroupAsymptotics.FiniteSymmetricChains

/-! A constructive symmetric-chain partition survives adjoining one
finite chain. This iterates to every mixed-prime coset grid. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.FiniteSymmetricChains

variable {I : Type} [Preorder I] {rank : I → ℕ} {K : ℕ}
    (D : FiniteSymmetricChains I rank K)

def position (x : I) : Fin (K+1-2*D.start (D.colour x)) :=
  ⟨rank x-D.start (D.colour x),by
    have h := D.rank_bounds x
    have hs := D.start_bound (D.colour x)
    omega⟩

theorem rank_eq_start_add_position (x : I) :
    rank x=D.start (D.colour x)+(D.position x).val := by
  have h := (D.rank_bounds x).1
  change rank x=D.start (D.colour x)+(rank x-D.start (D.colour x))
  omega

def ProductColour (n : ℕ) :=
  {c : D.Colour×Fin n // c.2.val<K+1-2*D.start c.1}

instance productColour_finite (n : ℕ) : Finite (D.ProductColour n) := by
  letI : Finite D.Colour := D.finiteColour
  letI : Fintype D.Colour := Fintype.ofFinite _
  exact Finite.of_injective (fun c : D.ProductColour n => c.val) Subtype.val_injective

def productPoint {n : ℕ} (a : I×Fin n) := (D.position a.1,a.2)

def productColour {n : ℕ} (a : I×Fin n) : D.ProductColour n :=
  let h := RectangleSymmetricChains.colour_lt (D.productPoint a)
  ⟨(D.colour a.1,⟨RectangleSymmetricChains.colour (D.productPoint a),(lt_min_iff.mp h).2⟩),
    (lt_min_iff.mp h).1⟩

private theorem product_colour_equal {n : ℕ} {a b : I×Fin n}
    (h : D.productColour a=D.productColour b) :
    D.colour a.1=D.colour b.1 ∧
      RectangleSymmetricChains.colour (D.productPoint a)=
        RectangleSymmetricChains.colour (D.productPoint b) := by
  exact ⟨congrArg (fun c : D.ProductColour n => c.val.1) h,
    congrArg (fun c : D.ProductColour n => c.val.2.val) h⟩

/-- Adjoining the chain Fin n preserves a genuine ranked symmetric-chain
partition, including exact coverage of every rank in every new chain. -/
def product (n : ℕ) (hn : 0<n) :
    FiniteSymmetricChains (I×Fin n) (fun a => rank a.1+a.2.val) (K+n-1) where
  Colour := D.ProductColour n
  finiteColour := inferInstance
  colour := D.productColour
  start := fun c => D.start c.val.1+c.val.2.val
  start_bound := by
    intro c
    have hj := c.property
    have hjn := c.val.2.isLt
    have hs := D.start_bound c.val.1
    omega
  rank_bounds := by
    intro a
    have h := RectangleSymmetricChains.rank_bounds (D.productPoint a)
    have hr := D.rank_eq_start_add_position a.1
    have hs := D.start_bound (D.colour a.1)
    change D.start (D.colour a.1)+RectangleSymmetricChains.colour (D.productPoint a)≤
      rank a.1+a.2.val ∧ rank a.1+a.2.val+
        (D.start (D.colour a.1)+RectangleSymmetricChains.colour (D.productPoint a))≤K+n-1
    change RectangleSymmetricChains.colour (D.productPoint a)≤(D.position a.1).val+a.2.val ∧
      (D.position a.1).val+a.2.val+RectangleSymmetricChains.colour (D.productPoint a)≤
        (K+1-2*D.start (D.colour a.1))+n-2 at h
    omega
  rank_unique := by
    intro a b hc hr
    obtain ⟨hc0,hc1⟩ := D.product_colour_equal hc
    have hra := D.rank_eq_start_add_position a.1
    have hrb := D.rank_eq_start_add_position b.1
    have hstart := congrArg D.start hc0
    have he : (D.position a.1).val+a.2.val=(D.position b.1).val+b.2.val := by
      omega
    let pa : Fin (K+1-2*D.start (D.colour b.1))×Fin n :=
      (⟨(D.position a.1).val,by have hpos := (D.position a.1).isLt; omega⟩,a.2)
    have hp := RectangleSymmetricChains.same_colour_rank_injective
      pa (D.productPoint b) hc1 he
    have hp0 := congrArg (fun z => z.1.val) hp
    have hp1 := congrArg Prod.snd hp
    change (D.position a.1).val=(D.position b.1).val at hp0
    change a.2=b.2 at hp1
    exact Prod.ext (D.rank_unique _ _ hc0 (by omega)) hp1
  rank_surjective := by
    intro c t hlo hhi
    let s := D.start c.val.1
    let j := c.val.2.val
    have hs := D.start_bound c.val.1
    have hj := c.property
    have hjn := c.val.2.isLt
    have hct : j<min (K+1-2*s) n := lt_min_iff.mpr ⟨hj,hjn⟩
    obtain ⟨b,hb,hbr⟩ := RectangleSymmetricChains.rank_surjective hct
      (r := t-s) (by change s+j≤t at hlo; omega) (by change t+(s+j)≤K+n-1 at hhi; omega)
    obtain ⟨x,hxc,hxr⟩ := D.rank_surjective c.val.1 (s+b.1.val)
      (by dsimp [s]; omega) (by have := b.1.isLt; dsimp [s] at *; omega)
    let a : I×Fin n := (x,b.2)
    have hpx : (D.position x).val=b.1.val := by
      have h := D.rank_eq_start_add_position x
      have hstart := congrArg D.start hxc
      dsimp [s] at hxr
      omega
    have hpc : RectangleSymmetricChains.colour (D.productPoint a)=j := by
      change min (D.position x).val (n-1-b.2.val)=j
      rw [hpx]
      exact hb
    have hac : D.productColour a=c := by
      apply Subtype.ext
      apply Prod.ext hxc
      exact Fin.ext hpc
    refine ⟨a,hac,?_⟩
    change rank x+b.2.val=t
    dsimp [s] at hxr
    have hlow : s≤t := by change s+j≤t at hlo; omega
    omega
  chain_le := by
    intro a b hc hr
    obtain ⟨hc0,hc1⟩ := D.product_colour_equal hc
    have hra := D.rank_eq_start_add_position a.1
    have hrb := D.rank_eq_start_add_position b.1
    have hstart := congrArg D.start hc0
    have hp : (D.position a.1).val+a.2.val≤(D.position b.1).val+b.2.val := by
      omega
    let pa : Fin (K+1-2*D.start (D.colour b.1))×Fin n :=
      (⟨(D.position a.1).val,by have hpos := (D.position a.1).isLt; omega⟩,a.2)
    have hrect : (D.position a.1).val≤(D.position b.1).val ∧ a.2≤b.2 := by
      rcases RectangleSymmetricChains.same_colour_comparable
        pa (D.productPoint b) hc1 with h|h
      · exact ⟨h.1,h.2⟩
      · have h0 := h.1
        have h1 := h.2
        change (D.position b.1).val≤(D.position a.1).val at h0
        change b.2.val≤a.2.val at h1
        constructor
        · change (D.position a.1).val≤(D.position b.1).val
          omega
        · change a.2.val≤b.2.val
          omega
    exact ⟨D.chain_le _ _ hc0 (by have := hrect.1; omega),hrect.2⟩

end SymmetricSubgroupAsymptotics.FiniteSymmetricChains
