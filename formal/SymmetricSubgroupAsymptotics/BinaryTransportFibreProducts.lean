import SymmetricSubgroupAsymptotics.BinaryTransport

/-!
# Proper nonabelian fibre-product carriers

These structural tests cover all literal fibre-product cores. In particular,
a common quotient relation is retained even though both projections are full,
and noncommutativity survives every full projection onto a nonabelian factor.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {A B Q : Type*} [Group A] [Group B] [Group Q]

/-- A literal proper-subdirect candidate over one specified common quotient. -/
def carrierFibreProduct (f : A →* Q) (g : B →* Q) : Subgroup (A × B) where
  carrier := {p | f p.1 = g p.2}
  one_mem' := by simp
  mul_mem' := by rintro x y hx hy; change f (x.1*y.1)=g (x.2*y.2); rw [map_mul,map_mul,hx,hy]
  inv_mem' := by intro x hx; change f x.1⁻¹=g x.2⁻¹; rw [map_inv,map_inv,hx]

def carrierFibreProductLeft (f : A →* Q) (g : B →* Q) : carrierFibreProduct f g →* A :=
  (MonoidHom.fst A B).comp (carrierFibreProduct f g).subtype

def carrierFibreProductRight (f : A →* Q) (g : B →* Q) : carrierFibreProduct f g →* B :=
  (MonoidHom.snd A B).comp (carrierFibreProduct f g).subtype

theorem carrierFibreProductLeft_surjective (f : A →* Q) (g : B →* Q)
    (hg : Function.Surjective g) : Function.Surjective (carrierFibreProductLeft f g) := by
  intro a
  obtain ⟨b,hb⟩ := hg (f a)
  exact ⟨⟨(a,b),hb.symm⟩,rfl⟩

theorem carrierFibreProductRight_surjective (f : A →* Q) (g : B →* Q)
    (hf : Function.Surjective f) : Function.Surjective (carrierFibreProductRight f g) := by
  intro b
  obtain ⟨a,ha⟩ := hf (g b)
  exact ⟨⟨(a,b),ha⟩,rfl⟩

/-- Nontrivial common quotients force the actual carrier to be proper. -/
theorem carrierFibreProduct_ne_top [Nontrivial Q] (f : A →* Q) (g : B →* Q)
    (hf : Function.Surjective f) : carrierFibreProduct f g ≠ ⊤ := by
  obtain ⟨q,hq⟩ := exists_ne (1 : Q)
  obtain ⟨a,ha⟩ := hf q
  intro h
  have hm : (a,1) ∈ carrierFibreProduct f g := by rw [h]; trivial
  change f a = g 1 at hm
  rw [ha,map_one] at hm
  exact hq hm

/-- Proper full-subdirect carriers need not be abelian. Any noncommuting
pair in the first factor has noncommuting simultaneous lifts. -/
theorem carrierFibreProduct_noncommuting (f : A →* Q) (g : B →* Q)
    (hg : Function.Surjective g) {a a' : A} (ha : a*a' ≠ a'*a) :
    ∃ p p' : carrierFibreProduct f g, p*p' ≠ p'*p := by
  obtain ⟨p,hp⟩ := carrierFibreProductLeft_surjective f g hg a
  obtain ⟨p',hp'⟩ := carrierFibreProductLeft_surjective f g hg a'
  refine ⟨p,p',?_⟩
  intro h
  have he := congrArg (carrierFibreProductLeft f g) h
  rw [map_mul,map_mul,hp,hp'] at he
  exact ha he

/-- Exact set coordinates retain the entire common-quotient fibre.
This is deliberately a set equivalence, not an unjustified direct-product
group decomposition of a possibly nonsplit nonabelian carrier. -/
def carrierFibreProductEquiv (f : A →* Q) (g : B →* Q)
    (hg : Function.Surjective g) : carrierFibreProduct f g ≃ A × g.ker := by
  let s : A → B := fun a => (hg (f a)).choose
  have hs (a : A) : g (s a) = f a := (hg (f a)).choose_spec
  exact
    { toFun := fun p => (p.1.1,⟨p.1.2*(s p.1.1)⁻¹,by
        change g (p.1.2*(s p.1.1)⁻¹)=1
        rw [map_mul,map_inv,hs,← p.2,mul_inv_cancel]⟩)
      invFun := fun p => ⟨(p.1,p.2.1*s p.1),by
        change f p.1=g (p.2.1*s p.1)
        rw [map_mul,p.2.2,one_mul,hs]⟩
      left_inv := fun p => by apply Subtype.ext; apply Prod.ext; rfl; simp
      right_inv := fun p => by apply Prod.ext; rfl; apply Subtype.ext; simp }

theorem carrierFibreProduct_card [Finite A] [Finite B] (f : A →* Q) (g : B →* Q)
    (hg : Function.Surjective g) :
    Nat.card (carrierFibreProduct f g) = Nat.card A * Nat.card g.ker := by
  rw [Nat.card_congr (carrierFibreProductEquiv f g hg),Nat.card_prod]

end SymmetricSubgroupAsymptotics

