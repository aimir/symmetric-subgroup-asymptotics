import SymmetricSubgroupAsymptotics.CyclicOrbitBinarySignNormalGenerators

/-! Literal coordinates of the FULL binary sign wreath over regular V4.
The full translation module is essential: augmentation-only subgroups need
not satisfy the same normal-generator bound. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryRegularKleinWreath
open LinearSemidirectCoprimeSocleBounds
open SemidirectProduct
open scoped BigOperators

abbrev R := Multiplicative (Fin 2 → ZMod 2)
local instance rFintype : Fintype R :=
  Fintype.ofEquiv (Fin 2 → ZMod 2) Multiplicative.ofAdd
local instance rDecidableEq : DecidableEq R :=
  inferInstanceAs (DecidableEq (Fin 2 → ZMod 2))
abbrev M := R → ZMod 2
local instance mFintype : Fintype M := inferInstanceAs (Fintype (R → ZMod 2))
local instance mDecidableEq : DecidableEq M := inferInstanceAs (DecidableEq (R → ZMod 2))
def a : R := Multiplicative.ofAdd ![1,0]
def b : R := Multiplicative.ofAdd ![0,1]

def rho : R →* (M ≃ₗ[ZMod 2] M) where
  toFun r :=
    { toFun := fun v i => v (r⁻¹*i)
      invFun := fun v i => v (r*i)
      left_inv := by intro v; funext i; simp [mul_assoc]
      right_inv := by intro v; funext i; simp [mul_assoc]
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by apply LinearEquiv.ext; intro v; funext i; simp
  map_mul' r s := by
    apply LinearEquiv.ext
    intro v
    funext i
    change v ((r*s)⁻¹*i)=v (s⁻¹*(r⁻¹*i))
    rw [mul_inv_rev,mul_assoc]

abbrev G := Model rho
local instance gDecidableEq : DecidableEq G :=
  inferInstanceAs (DecidableEq (Multiplicative M ⋊[linearAction rho] R))
abbrev top : G →* R := rightHom
abbrev E := translationKernel rho

def lift (v : M) (r : R) : G := ⟨Multiplicative.ofAdd v,r⟩
def t (v : M) : G := lift v 1

def parity (v : M) : ZMod 2 := v 1+v a+v b+v (a*b)
private def regularLabel : Fin 4 ≃ R where
  toFun := ![1,a,b,a*b]
  invFun r := ⟨(r.toAdd 0).val+2*(r.toAdd 1).val,by
    have h0 := (r.toAdd 0).val_lt
    have h1 := (r.toAdd 1).val_lt
    omega⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem parity_eq_sum (v : M) : parity v=∑ i : R, v i := by
  simpa [regularLabel,parity,Fin.sum_univ_succ,add_assoc] using
    (Equiv.sum_comp regularLabel v)

private theorem parity_add (v w : M) : parity (v+w)=parity v+parity w := by
  simp only [parity_eq_sum,Pi.add_apply,Finset.sum_add_distrib]

private theorem parity_permute (r : R) (v : M) :
    parity (fun i => v (r⁻¹*i))=parity v := by
  rw [parity_eq_sum,parity_eq_sum]
  exact Equiv.sum_comp (Equiv.mulLeft r⁻¹) v

def beta : G →* Multiplicative (Fin 3 → ZMod 2) where
  toFun g := Multiplicative.ofAdd ![parity g.left.toAdd,g.right.toAdd 0,g.right.toAdd 1]
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> norm_num [parity]
  map_mul' g h := by
    rcases g with ⟨v,r⟩
    rcases h with ⟨w,s⟩
    apply Multiplicative.toAdd.injective
    funext i
    change ![parity (fun j => v.toAdd j + w.toAdd (r⁻¹*j)),
      r.toAdd 0+s.toAdd 0,r.toAdd 1+s.toAdd 1] i =
      (![parity v.toAdd,r.toAdd 0,r.toAdd 1] i +
        ![parity w.toAdd,s.toAdd 0,s.toAdd 1] i)
    fin_cases i
    · change parity (v.toAdd+(fun j => w.toAdd (r⁻¹*j)))=
        parity v.toAdd+parity w.toAdd
      rw [parity_add,parity_permute]
    · rfl
    · rfl

abbrev D : Subgroup G := beta.ker

theorem beta_kernel_iff (v : M) (r : R) :
    beta (lift v r)=1 ↔ r=1 ∧ parity v=0 := by
  constructor
  · intro h
    have h0 := congrArg (fun x : Multiplicative (Fin 3 → ZMod 2) => x.toAdd 0) h
    have h1 := congrArg (fun x : Multiplicative (Fin 3 → ZMod 2) => x.toAdd 1) h
    have h2 := congrArg (fun x : Multiplicative (Fin 3 → ZMod 2) => x.toAdd 2) h
    change parity v=0 at h0
    change r.toAdd 0=0 at h1
    change r.toAdd 1=0 at h2
    refine ⟨?_,h0⟩
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i
    · exact h1
    · exact h2
  · rintro ⟨rfl,hv⟩
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i
    · exact hv
    · rfl
    · rfl

theorem D_le_E : D ≤ E := by
  intro x hx
  exact (beta_kernel_iff x.left.toAdd x.right).mp hx |>.1

def delta : M := fun r => if r=1 then 1 else 0
def edgeA : M := fun r => if r=1 ∨ r=a then 1 else 0
def edgeB : M := fun r => if r=1 ∨ r=b then 1 else 0
def edgeC : M := fun r => if r=a ∨ r=a*b then 1 else 0

private theorem t_add (v w : M) : t (v+w)=t v*t w :=
  (inl : Multiplicative M →* G).map_mul _ _

private theorem t_neg (v : M) : t (-v)=(t v)⁻¹ :=
  (inl : Multiplicative M →* G).map_inv _

private theorem conjugate_t (v w : M) (r : R) :
    lift v r*t w*(lift v r)⁻¹=t (fun i => w (r⁻¹*i)) :=
  conjugate_translation rho (lift v r) (Multiplicative.ofAdd w)

private theorem comm_translation (v w : M) (r : R) :
    t w*lift v r*(t w)⁻¹*(lift v r)⁻¹=
      t (w+(fun i => -(w (r⁻¹*i)))) := by
  calc
    _=t w*(lift v r*t (-w)*(lift v r)⁻¹) := by rw [t_neg]; group
    _=t w*t (fun i => -(w (r⁻¹*i))) := by
      rw [conjugate_t]
      simp only [Pi.neg_apply]
    _=_ := (t_add _ _).symm

theorem comm_a (v : M) :
    t delta * lift v a * (t delta)⁻¹ * (lift v a)⁻¹ = t edgeA := by
  rw [comm_translation]
  apply congrArg t
  funext i
  change delta i + -(delta (a⁻¹*i))=edgeA i
  unfold delta edgeA
  revert i
  decide +kernel

theorem comm_b (v : M) :
    t delta * lift v b * (t delta)⁻¹ * (lift v b)⁻¹ = t edgeB := by
  rw [comm_translation]
  apply congrArg t
  funext i
  change delta i + -(delta (b⁻¹*i))=edgeB i
  unfold delta edgeB
  revert i
  decide +kernel

theorem conjugate_edgeB (v : M) :
    lift v a * t edgeB * (lift v a)⁻¹ = t edgeC := by
  rw [conjugate_t]
  apply congrArg t
  funext i
  change edgeB (a⁻¹*i)=edgeC i
  unfold edgeB edgeC
  revert i
  decide +kernel

private theorem t_pow (v : M) (n : ℕ) : t v^n=t (n • v) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ,ih,add_nsmul,one_nsmul,t_add]

private theorem regular_exhaustion (i : R) : i=1 ∨ i=a ∨ i=b ∨ i=a*b := by
  revert i
  decide +kernel

private theorem edge_values :
    edgeA 1=1 ∧ edgeA a=1 ∧ edgeA b=0 ∧ edgeA (a*b)=0 ∧
    edgeB 1=1 ∧ edgeB a=0 ∧ edgeB b=1 ∧ edgeB (a*b)=0 ∧
    edgeC 1=0 ∧ edgeC a=1 ∧ edgeC b=0 ∧ edgeC (a*b)=1 := by
  unfold edgeA edgeB edgeC
  decide +kernel

theorem even_decomposition (v : M) (hv : parity v=0) :
    t v = t edgeA ^ (v a+v (a*b)).val *
      t edgeB ^ (v b).val * t edgeC ^ (v (a*b)).val := by
  rw [t_pow,t_pow,t_pow,← t_add,← t_add]
  apply congrArg t
  have hscalar : ∀ (x0 xa xb xc : ZMod 2), x0+xa+xb+xc=0 →
      x0=(xa+xc).val • (1 : ZMod 2)+xb.val • (1 : ZMod 2) ∧
      xa=(xa+xc).val • (1 : ZMod 2)+xc.val • (1 : ZMod 2) ∧
      xb=xb.val • (1 : ZMod 2) ∧ xc=xc.val • (1 : ZMod 2) := by
    decide +kernel
  have hh := hscalar (v 1) (v a) (v b) (v (a*b)) hv
  rcases edge_values with ⟨hA0,hAa,hAb,hAc,hB0,hBa,hBb,hBc,hC0,hCa,hCb,hCc⟩
  funext i
  rcases regular_exhaustion i with rfl | rfl | rfl | rfl
  · simpa only [Pi.add_apply,Pi.smul_apply,hA0,hB0,hC0,smul_zero,add_zero] using hh.1
  · simpa only [Pi.add_apply,Pi.smul_apply,hAa,hBa,hCa,smul_zero,add_zero] using hh.2.1
  · simpa only [Pi.add_apply,Pi.smul_apply,hAb,hBb,hCb,smul_zero,zero_add,add_zero] using hh.2.2.1
  · simpa only [Pi.add_apply,Pi.smul_apply,hAc,hBc,hCc,smul_zero,zero_add] using hh.2.2.2

/-- Every actual normal subgroup with full block image contains the
augmentation kernel. This is where the FULL translation module is used. -/
theorem D_le_of_full_projection (N : Subgroup G) [N.Normal]
    (hfull : Function.Surjective (top.comp N.subtype)) : D ≤ N := by
  obtain ⟨x,hx⟩ := hfull a
  obtain ⟨y,hy⟩ := hfull b
  have hx' : (x : G)=lift (x : G).left.toAdd a := by
    apply SemidirectProduct.ext
    · rfl
    · exact hx
  have hy' : (y : G)=lift (y : G).left.toAdd b := by
    apply SemidirectProduct.ext
    · rfl
    · exact hy
  have hA : t edgeA ∈ N := by
    have h := N.mul_mem ((inferInstance : N.Normal).conj_mem (x : G) x.2 (t delta))
      (N.inv_mem x.2)
    rwa [hx',comm_a] at h
  have hB : t edgeB ∈ N := by
    have h := N.mul_mem ((inferInstance : N.Normal).conj_mem (y : G) y.2 (t delta))
      (N.inv_mem y.2)
    rwa [hy',comm_b] at h
  have hC : t edgeC ∈ N := by
    have h := (inferInstance : N.Normal).conj_mem (t edgeB) hB (x : G)
    rwa [hx',conjugate_edgeB] at h
  intro z hz
  obtain ⟨hzr,hzv⟩ := (beta_kernel_iff z.left.toAdd z.right).mp hz
  have hzt : z=t z.left.toAdd := by
    apply SemidirectProduct.ext
    · rfl
    · exact hzr
  rw [hzt,even_decomposition z.left.toAdd hzv]
  exact N.mul_mem (N.mul_mem (N.pow_mem hA _) (N.pow_mem hB _)) (N.pow_mem hC _)

theorem kernel_uniform_two :
    UniformSubrepresentationGeneratorBound (linearRepresentation rho) 2 := by
  change UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) R R) 2
  apply permutationFunctionRepresentation_uniform_of_polynomial_orbitCover a ![1,b]
  intro i
  obtain ⟨j,n,hn⟩ := (by decide +kernel :
    ∀ i : R, ∃ j : Fin 2, ∃ n : Fin 2, a^n.val * (![1,b] j)=i) i
  exact ⟨j,n.val,hn⟩

theorem quotient_card_le_eight : Nat.card (G ⧸ D) ≤ 8 := by
  calc
    Nat.card (G ⧸ D) = Nat.card beta.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange beta).toEquiv
    _ ≤ Nat.card (Multiplicative (Fin 3 → ZMod 2)) :=
      Subgroup.card_le_card_group beta.range
    _ = 8 := by
      rw [Nat.card_congr Multiplicative.toAdd,Nat.card_fun,Nat.card_zmod,Nat.card_fin]
      norm_num

theorem span_two_distinct : ∀ (r s : R), r≠1 → s≠1 → s≠r →
    ∀ u : R, u=1 ∨ u=r ∨ u=s ∨ u=r*s := by decide +kernel

/-- Proper subgroups of the regular Klein top are cyclic. -/
theorem proper_isCyclic (L : Subgroup R) (hL : L≠⊤) : IsCyclic L := by
  classical
  by_cases hb : L=⊥
  · subst L
    infer_instance
  obtain ⟨r,hr,hr1⟩ := L.bot_or_exists_ne_one.resolve_left hb
  have hle : L ≤ Subgroup.zpowers r := by
    intro s hs
    by_cases hs1 : s=1
    · subst s; exact Subgroup.one_mem _
    by_cases hsr : s=r
    · subst s; exact Subgroup.mem_zpowers _
    exfalso
    apply hL
    apply top_unique
    intro u _
    rcases span_two_distinct r s hr1 hs1 hsr u with h|h|h|h
    · subst u; exact L.one_mem
    · subst u; exact hr
    · subst u; exact hs
    · rw [h]; exact L.mul_mem hr hs
  exact Subgroup.isCyclic_of_le hle

end SymmetricSubgroupAsymptotics.BinaryRegularKleinWreath
end
