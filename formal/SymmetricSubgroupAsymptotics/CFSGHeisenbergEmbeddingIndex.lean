import SymmetricSubgroupAsymptotics.CFSGHeisenbergPrimeIndex
import SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree

/-! An injective actual prime-field Heisenberg homomorphism in a simple
group forces every proper subgroup to have large index. The literal
central element moves a coset by simplicity; its stabilizer has the
proper central intersection required by the proved isotropy count. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHeisenbergEmbeddingIndex
open CFSGHeisenbergCoordinateGroup CFSGHeisenbergPrimeIndex

theorem degree_le_of_central_motion (p m:ℕ) [Fact p.Prime]
    {X:Type*}[Finite X][MulAction (Element (ZMod p) m) X]
    (x:X) (c:Multiplicative (ZMod p)) (hc:(central (K:=ZMod p) (m:=m) c) • x≠x) :
    p^(m+1)≤Nat.card X := by
  have hH:¬(central (K:=ZMod p) (m:=m)).range≤MulAction.stabilizer (Element (ZMod p) m) x := by
    intro hh
    exact hc (hh ⟨c,rfl⟩)
  calc
    p^(m+1)≤(MulAction.stabilizer (Element (ZMod p) m) x).index := index_least p m _ hH
    _=(MulAction.orbit (Element (ZMod p) m) x).ncard := MulAction.index_stabilizer _ _
    _≤Nat.card X := Set.ncard_le_card _

theorem proper_index_least (p m:ℕ) [Fact p.Prime]
    {G:Type*}[Group G][Finite G][IsSimpleGroup G]
    (f:Element (ZMod p) m→*G) (hf:Function.Injective f)
    (H:Subgroup G) (hH:H≠⊤) : p^(m+1)≤H.index := by
  let c:Multiplicative (ZMod p):=Multiplicative.ofAdd 1
  have hc:central (m:=m) c≠1 := by
    intro he
    have he' : c=1 := central_injective (he.trans (map_one central).symm)
    exact one_ne_zero (congrArg (fun z:Multiplicative (ZMod p)=>z.toAdd) he')
  have hfc:f (central (m:=m) c)≠1 := by
    intro he
    exact hc (hf (he.trans (map_one f).symm))
  obtain ⟨x,hx⟩ := CFSGConjugateSubgroupDegree.exists_moved_coset_of_ne_one H hH _ hfc
  letI : MulAction (Element (ZMod p) m) (G⧸H) := MulAction.compHom _ f
  have hb := degree_le_of_central_motion p m x c hx
  simpa only [Subgroup.index_eq_card] using hb

end SymmetricSubgroupAsymptotics.CFSGHeisenbergEmbeddingIndex
