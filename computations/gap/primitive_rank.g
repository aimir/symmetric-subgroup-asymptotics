# Literal primitive and relative-rank certificates. JSON transport is external.
RPDegrees := Concatenation([2..23],[25,26,28,29,31,34,37]);;
RPChecks := 0;;
RPCheck := function(b,s) if not b then Error(Concatenation("rank certificate: ",s));fi;RPChecks:=RPChecks+1;end;;
RPJSON := fail;;
RPJSON := function(v)
 local names;
 if IsBool(v) or IsInt(v) then return String(v);fi;
 if IsStringRep(v) then return Concatenation("\"",ReplacedString(ReplacedString(v,"\\","\\\\"),"\"","\\\""),"\"");fi;
 if IsList(v) then return Concatenation("[",JoinStringsWithSeparator(List(v,RPJSON),","),"]");fi;
 if IsRecord(v) then names:=Set(RecNames(v));return Concatenation("{",JoinStringsWithSeparator(List(names,k->Concatenation(RPJSON(k),":",RPJSON(v.(k)))),","),"}");fi;
 Error("unsupported JSON value");
end;;
RPDataStream:=OutputTextUser();;SetPrintFormattingStatus(RPDataStream,false);;
RPEmit := function(v) PrintTo(RPDataStream,"DATA ",RPJSON(v),"\n");end;;
RPImages := function(G,n) local gens;gens:=GeneratorsOfGroup(G);if Length(gens)=0 then gens:=[()];fi;return List(gens,g->List([1..n],x->x^g));end;;
RPGroup := function(rows,n)
 RPCheck(IsList(rows) and Length(rows)>0,"nonempty generator list");
 RPCheck(ForAll(rows,r->IsList(r) and Set(r)=[1..n] and Length(r)=n),"literal permutations");
 return Group(List(rows,PermList));
end;;
RPRank := function(G,N,p)
 return Number(AbelianInvariants(FactorGroup(N,CommutatorSubgroup(N,G))),x->x mod p=0);
end;;
RPVerifyRank := function(G,N,p)
 local R,q;
 R:=Subgroup(N,Concatenation(GeneratorsOfGroup(CommutatorSubgroup(N,G)),List(GeneratorsOfGroup(N),x->x^p)));
 RPCheck(IsNormal(G,R),"relative power subgroup normal in action");
 q:=FactorGroup(N,R);RPCheck(IsElementaryAbelian(q) or Size(q)=1,"elementary relative quotient");
 RPCheck(Size(q)=p^LogInt(Size(q),p),"relative quotient prime power");
 return LogInt(Size(q),p);
end;;
RPSeries := function(G,n) return List(CompositionSeries(G),H->RPImages(H,n));end;;
RPCheckSeries := function(G,rows,n)
 local groups,i,Q,factors;
 groups:=List(rows,x->RPGroup(x,n));
 RPCheck(Length(groups)>=1 and groups[1]=G and Size(groups[Length(groups)])=1,"composition series endpoints");
 factors:=[];
 for i in [1..Length(groups)-1] do
  RPCheck(IsSubgroup(groups[i],groups[i+1]) and IsNormal(groups[i],groups[i+1]),"composition series normal containment");
  Q:=FactorGroup(groups[i],groups[i+1]);RPCheck(IsSimpleGroup(Q),"composition factor simple");Add(factors,Size(Q));
 od;
 RPCheck(Product(factors)=Size(G),"composition order product");return factors;
end;;
RPModule := function(G,n)
 local M,P,v;
 M:=PCore(G,2);P:=SylowSubgroup(G,3);
 v:=First(Elements(M),x->Size(Group(List(Elements(P),g->x^g)))=Size(M));
 RPCheck(v<>fail,"cyclic module witness exists");
 return rec(base:=RPImages(M,n),complement:=RPImages(P,n),vector:=List([1..n],x->x^v));
end;;
RPCheckModule := function(G,n,r)
 local M,P,v;
 M:=RPGroup(r.base,n);P:=RPGroup(r.complement,n);v:=PermList(r.vector);
 RPCheck(IsSubgroup(G,M) and IsNormal(G,M) and IsElementaryAbelian(M) and Size(M)>1 and PrimeDivisors(Size(M))=[2],"binary module base");
 RPCheck(IsSubgroup(G,P) and IsElementaryAbelian(P) and Size(P)>1 and PrimeDivisors(Size(P))=[3],"elementary ternary complement");
 RPCheck(Size(M)*Size(P)=Size(G) and ClosureGroup(M,P)=G,"same actual split module action");
 RPCheck(v in M and Group(List(Elements(P),g->v^g))=M,"one vector generates the module");
end;;
RPOwner := function(G,n,i)
 local W,P,blocks,h,T;
 if n=6 and i in [1,5] then return rec(kind:="odd_index_two",sylow:=RPImages(SylowSubgroup(G,3),n));fi;
 if (n=6 and i in [4,6]) or (n=12 and i in [20,85,164]) then return rec(kind:="cyclic_module",module:=RPModule(G,n));fi;
 if n=12 and i=194 then
  W:=PCore(G,3);blocks:=List(Orbits(W,[1..n]),Set);h:=ActionHomomorphism(G,blocks,OnSets);T:=Image(h);
  return rec(kind:="prime_base",base:=RPImages(W,n),blocks:=blocks,top:=RPImages(T,4),top_images:=List(GeneratorsOfGroup(G),g->List([1..4],x->x^Image(h,g))),top_module:=RPModule(T,4));
 fi;
 W:=PCore(G,2);P:=SylowSubgroup(G,3);
 return rec(kind:="v4_blocks",base:=RPImages(W,n),complement:=RPImages(P,n),blocks:=List(Orbits(W,[1..n]),Set));
end;;
RPRestrict := function(g,B,n) return PermList(List([1..n],function(i) if i in B then return i^g;else return i;fi;end));end;;
RPCheckOwner := function(G,n,r)
 local W,P,blocks,B,locals,V,axes,T,h,loc;
 if r.kind="odd_index_two" then
  P:=RPGroup(r.sylow,n);RPCheck(IsSubgroup(G,P) and IsNormal(G,P) and PrimeDivisors(Size(P))=[3] and Index(G,P)=2,"actual odd index-two predicate");
 elif r.kind="cyclic_module" then RPCheckModule(G,n,r.module);RPCheck(n<>4,"natural A4 excluded from direct module consumer");
 elif r.kind="prime_base" then
  W:=RPGroup(r.base,n);blocks:=r.blocks;RPCheck(IsNormal(G,W) and IsElementaryAbelian(W) and PrimeDivisors(Size(W))=[3],"actual ternary base");
  RPCheck(Set(blocks)=Set(List(Orbits(W,[1..n]),Set)) and Length(blocks)=4 and ForAll(blocks,b->Length(b)=3),"actual prime blocks");
  T:=RPGroup(r.top,4);h:=GroupHomomorphismByImages(G,T,GeneratorsOfGroup(G),List(r.top_images,PermList));
  RPCheck(h<>fail and Image(h)=T and Kernel(h)=W and Size(T)=12,"actual full top quotient");
  RPCheck(ForAll(GeneratorsOfGroup(G),g->ForAll([1..4],j->OnSets(blocks[j],g)=blocks[j^Image(h,g)])),"top action matches blocks");
  RPCheckModule(T,4,r.top_module);
  for B in blocks do loc:=Action(Stabilizer(G,B,OnSets),B);RPCheck(Size(loc)=3,"exact prime local component");od;
 elif r.kind="v4_blocks" then
  W:=RPGroup(r.base,n);P:=RPGroup(r.complement,n);blocks:=r.blocks;
  RPCheck(IsNormal(G,W) and IsElementaryAbelian(W) and Size(W)>1,"V4 base");
  RPCheck(IsSubgroup(G,P) and PrimeDivisors(Size(P))=[3] and ClosureGroup(W,P)=G and Size(W)*Size(P)=Size(G),"actual odd complement");
  RPCheck(Set(blocks)=Set(List(Orbits(W,[1..n]),Set)) and Length(blocks)=3 and ForAll(blocks,b->Length(b)=4),"actual V4 blocks");
  locals:=List(blocks,B->Group(List(GeneratorsOfGroup(W),g->RPRestrict(g,B,n))));
  RPCheck(ForAll(locals,L->Size(L)=4 and IsElementaryAbelian(L)),"local V4 projections");
  V:=Group(Concatenation(List(locals,GeneratorsOfGroup)));RPCheck(Size(V)=64 and IsSubgroup(V,W) and IsNormal(ClosureGroup(V,G),V),"literal ambient V4 product");
  axes:=Concatenation(List(locals,L->Filtered(Elements(L),x->x<>())));
  RPCheck(Length(axes)=9 and IsTransitive(P,axes,OnPoints),"full ternary action on nonzero local vectors");
  h:=ActionHomomorphism(P,axes,OnPoints);RPCheck(Size(Kernel(h))=1,"faithful nine-vector top");
  T:=Action(G,blocks,OnSets);RPCheck(Size(T)=3,"actual three-block top");
 else Error("unknown earlier-owner witness");fi;
end;;
RPNormalScope := function(cat,n)
 if cat="primitive" then if n<=33 then return "all";else return "none";fi;fi;
 if n in [6,9,12,18] then return "all";fi;
 if n in [2,4,8] then return "transitive";fi;
 return "none";
end;;
RPBuild := function(cat,n,i,G)
 local r,p,N,scope,normals,S,h,T,R,x,series;
 r:=rec(kind:="action",catalogue:=cat,degree:=n,index:=i,order:=Size(G),generators:=RPImages(G,n));
 if cat="transitive" then
  r.head2:=RPRank(G,G,2);
  if n=18 then
   r.head3:=RPRank(G,G,3);r.soluble:=IsSolvableGroup(G);
   if not r.soluble then
    x:=First(List(ConjugacyClasses(SylowSubgroup(G,3)),Representative),g->Order(g)=3 and NrMovedPoints(g)=18);
    RPCheck(x<>fail,"semiregular ternary witness");r.semiregular:=List([1..n],j->j^x);
   fi;
  fi;
  if (n=6 and i in [1,4,5,6]) or (n=12 and i in [20,85,164,194,228,229,265]) then r.owner:=RPOwner(G,n,i);fi;
 else
  r.composition:=RPSeries(G,n);
  if n>=5 and n<=29 then
   S:=Socle(G);r.socle:=RPImages(S,n);r.socle_abelian:=IsAbelian(S);r.socle_simple:=IsSimpleGroup(S);
   if not r.socle_abelian and r.socle_simple then
    h:=ActionHomomorphism(G,RightCosets(G,S),OnRight);r.socle_cover_degree:=Index(G,S);r.socle_cover_images:=List(GeneratorsOfGroup(G),g->List([1..Index(G,S)],j->j^Image(h,g)));
   fi;
  fi;
  if n in [8,16,27] then
   S:=Socle(G);R:=Stabilizer(G,1);
   r.nonsoluble_affine:=IsElementaryAbelian(S) and Size(S)=n and not IsSolvableGroup(R);
   if r.nonsoluble_affine then r.affine_socle:=RPImages(S,n);r.stabilizer:=RPImages(R,n);r.stabilizer_composition:=RPSeries(R,n);fi;
  fi;
 fi;
 scope:=RPNormalScope(cat,n);r.normal_scope:=scope;r.normals:=[];
 if scope<>"none" then
  normals:=NormalSubgroups(G);if scope="transitive" then normals:=Filtered(normals,N->IsTransitive(N,[1..n]));fi;
  if scope="transitive" then p:=2;else p:=3;fi;
  for N in normals do Add(r.normals,rec(generators:=RPImages(N,n),order:=Size(N),prime:=p,rank:=RPRank(G,N,p)));od;
 fi;
 return r;
end;;
RPProduce := function()
 local cat,degs,n,i,G,count,normals;
 LoadPackage("transgrp");LoadPackage("primgrp");
 RPCheck(GAPInfo.Version="4.13.1" and PackageInfo("primgrp")[1].Version="3.4.4" and PackageInfo("transgrp")[1].Version="3.6.5","pinned packages");
 RPEmit(rec(kind:="header",schema_version:=1,gap:=GAPInfo.Version,primgrp:="3.4.4",transgrp:="3.6.5",transitive_degrees:=RPDegrees,primitive_degrees:=Concatenation([2..44],[54])));count:=0;normals:=0;
 for cat in ["transitive","primitive"] do
  if cat="transitive" then degs:=RPDegrees;else degs:=Concatenation([2..44],[54]);fi;
  for n in degs do
   if cat="transitive" then G:=NrTransitiveGroups(n);else G:=NrPrimitiveGroups(n);fi;
   for i in [1..G] do
    if cat="transitive" then RPEmit(RPBuild(cat,n,i,TransitiveGroup(n,i)));else RPEmit(RPBuild(cat,n,i,PrimitiveGroup(n,i)));fi;count:=count+1;
   od;
   Print("PROGRESS rank export ",cat," degree ",n," cumulative-actions ",count,"\n");
  od;
 od;
 RPEmit(rec(kind:="footer",schema_version:=1,actions:=count));Print("PASS PRIMITIVE RANK EXPORT: actions=",count,"\n");
end;;
RPSeen:=[];;RPStats:=fail;;
RPInit := function(h)
 RPCheck(h.kind="header" and h.schema_version=1,"header schema");
 RPCheck(h.transitive_degrees=RPDegrees and h.primitive_degrees=Concatenation([2..44],[54]),"exact finite scope");
 LoadPackage("transgrp");LoadPackage("primgrp");
 RPCheck(h.gap=GAPInfo.Version and h.gap="4.13.1" and h.primgrp=PackageInfo("primgrp")[1].Version and h.primgrp="3.4.4" and h.transgrp=PackageInfo("transgrp")[1].Version and h.transgrp="3.6.5","pinned classification correspondence");
 RPSeen:=[];RPStats:=rec(actions:=0,transitive:=0,primitive:=0,normals:=0,critical_pairs:=0,relative_pairs:=0,primitive_pairs:=0,high_c1_pairs:=0,owner_actions:=0,nonsoluble18:=0,nonsoluble18_pairs:=0,nonaffine_simple:=0,nonaffine_other:=0,nonsoluble_affine:=0,composition_factors:=0);
end;;
RPVerify := function(r)
 local G,n,i,E,key,scope,p,rows,N,all,d,x,factors,a3,S,h,R,ab,kap,eta;
 RPCheck(r.kind="action","action tag");n:=r.degree;i:=r.index;
 RPCheck(r.catalogue in ["primitive","transitive"],"catalogue kind");
 key:=[r.catalogue,n,i];RPCheck(not key in RPSeen,"unique action locator");Add(RPSeen,key);
 if r.catalogue="transitive" then
  RPCheck(n in RPDegrees and i>=1 and i<=NrTransitiveGroups(n),"transitive classification scope");E:=TransitiveGroup(n,i);RPStats.transitive:=RPStats.transitive+1;
 else
  RPCheck(n in Concatenation([2..44],[54]) and i>=1 and i<=NrPrimitiveGroups(n),"primitive classification scope");E:=PrimitiveGroup(n,i);RPStats.primitive:=RPStats.primitive+1;
 fi;
 G:=RPGroup(r.generators,n);RPCheck(G=E and Size(G)=r.order and IsTransitive(G,[1..n]),"literal classified action and order");
 if r.catalogue="transitive" then
  d:=RPVerifyRank(G,G,2);RPCheck(d=r.head2 and 2*d<=n,"whole binary head");
  if 8*d>3*n then RPCheck([n,i,d] in [[2,1,1],[4,2,2],[4,3,2],[8,22,4]],"only four critical whole actions");fi;
  if n=18 then
   RPCheck(r.head3=RPVerifyRank(G,G,3) and r.soluble=IsSolvableGroup(G),"degree18 top signature");
   if not r.soluble then
    x:=PermList(r.semiregular);RPCheck(x in G and Order(x)=3 and NrMovedPoints(x)=18,"actual semiregular C3 witness");RPStats.nonsoluble18:=RPStats.nonsoluble18+1;
   fi;
  fi;
  if IsBound(r.owner) then RPCheckOwner(G,n,r.owner);RPStats.owner_actions:=RPStats.owner_actions+1;fi;
 else
  RPCheck(IsPrimitive(G,[1..n]),"primitive action");factors:=RPCheckSeries(G,r.composition,n);a3:=Number(factors,q->q=3);RPStats.composition_factors:=RPStats.composition_factors+Length(factors);
  RPCheck(3*a3<=n,"primitive one-third composition density");
  if 10*a3>=3*n then RPCheck([n,i,Size(G),a3] in [[3,1,3,1],[3,2,6,1],[9,6,216,3],[9,7,432,3]],"four strict composition exceptions");fi;
  if n in [6,18,54] then RPCheck(a3=0,"minimal-block primitive composition seam");fi;
  if n=9 then RPCheck(a3<=3,"degree9 composition seam");fi;
  if n=27 then RPCheck(a3<=7,"degree27 composition seam");fi;
  if n>=5 and n<=29 then
   S:=RPGroup(r.socle,n);RPCheck(S=Socle(G) and r.socle_abelian=IsAbelian(S) and r.socle_simple=IsSimpleGroup(S),"actual primitive socle");
   if not r.socle_abelian then
    if r.socle_simple then
     RPCheck(Size(Centralizer(G,S))=1 and 2*Index(G,S)<=n,"small almost-simple quotient compression");
     RPCheck(r.socle_cover_degree=Index(G,S),"quotient regular cover degree");
     R:=Group(List(r.socle_cover_images,PermList));h:=GroupHomomorphismByImages(G,R,GeneratorsOfGroup(G),List(r.socle_cover_images,PermList));
     RPCheck(h<>fail and Kernel(h)=S and Size(R)=Index(G,S),"actual quotient cover map");RPStats.nonaffine_simple:=RPStats.nonaffine_simple+1;
    else RPStats.nonaffine_other:=RPStats.nonaffine_other+1;fi;
   fi;
  fi;
  if n in [8,16,27] then
   S:=Socle(G);R:=Stabilizer(G,1);
   RPCheck(r.nonsoluble_affine=(IsElementaryAbelian(S) and Size(S)=n and not IsSolvableGroup(R)),"complete affine exceptional predicate");
   if r.nonsoluble_affine then
    RPCheck(RPGroup(r.affine_socle,n)=S and RPGroup(r.stabilizer,n)=R and IsRegular(S,[1..n]) and Centralizer(G,S)=S,"actual affine socle and stabilizer");
    factors:=RPCheckSeries(R,r.stabilizer_composition,n);ab:=Filtered(factors,IsPrime);
    if n=8 then RPCheck(ab=[],"degree8 stabilizer factors");elif n=16 then RPCheck(ForAll(ab,q->q in [2,3]) and Number(ab,q->q=2)<=1 and Number(ab,q->q=3)<=1,"degree16 stabilizer factors");else RPCheck(ForAll(ab,q->q=2) and Length(ab)<=1,"degree27 stabilizer factors");fi;
    kap:=Number(ab,q->q=2)/2+Number(ab,q->q<>2)*17/32;if n in [8,16] then eta:=1/4;else eta:=17/64;fi;
    RPCheck((n-n mod 2)/8-kap-eta>1/4,"strict complete-fibre affine margin");RPStats.nonsoluble_affine:=RPStats.nonsoluble_affine+1;
   fi;
  fi;
 fi;
 scope:=RPNormalScope(r.catalogue,n);RPCheck(r.normal_scope=scope,"normal scope fixed by consumer");rows:=[];
 if scope="none" then RPCheck(r.normals=[],"unused normals omitted");else
  all:=NormalSubgroups(G);if scope="transitive" then all:=Filtered(all,N->IsTransitive(N,[1..n]));p:=2;else p:=3;fi;
  RPCheck(Length(r.normals)=Length(all),"complete normal count");
  for x in r.normals do
   N:=RPGroup(x.generators,n);RPCheck(IsSubgroup(G,N) and IsNormal(G,N) and Size(N)=x.order and x.prime=p,"literal normal and prime");
   RPCheck(not N in rows,"distinct literal normal");Add(rows,N);d:=RPVerifyRank(G,N,p);RPCheck(d=x.rank,"independent relative rank");RPStats.normals:=RPStats.normals+1;
   if scope="transitive" then
    RPCheck(IsTransitive(N,[1..n]),"transitive normal scope");RPStats.critical_pairs:=RPStats.critical_pairs+1;
    if 8*d>3*n then RPCheck(G=N and [n,i,d] in [[2,1,1],[4,2,2],[4,3,2],[8,22,4]],"critical relative exceptions whole");fi;
   elif r.catalogue="primitive" then
    RPStats.primitive_pairs:=RPStats.primitive_pairs+1;
    if 20*d>=3*n then RPCheck(G=N and [n,i,d] in [[3,1,1],[4,1,1]],"primitive strict 3/20 exceptions");fi;
   else
    RPStats.relative_pairs:=RPStats.relative_pairs+1;
    if n in [9,18] then RPCheck(9*d<=2*n,"ternary two-ninth bound");if 9*d=2*n then RPCheck(n=9 and i in [2,6,7,17] and G=N,"exact two-ninth equalities");fi;fi;
    if not (n=9 and i in [2,6,7,17] and G=N) then RPCheck(27*d<=5*n,"relative one-third stability");fi;
    if n in [6,12,18] and 20*d>3*n then RPCheck(IsBound(r.owner),"every high c1 action has actual acceptance witness");RPStats.high_c1_pairs:=RPStats.high_c1_pairs+1;fi;
    if n=18 and not r.soluble then RPCheck(d<=1,"nonsoluble degree18 relative head");RPStats.nonsoluble18_pairs:=RPStats.nonsoluble18_pairs+1;fi;
   fi;
  od;
  RPCheck(ForAll(all,N->Number(rows,M->M=N)=1),"every computed normal has unique literal record");
 fi;
 RPStats.actions:=RPStats.actions+1;
 if RPStats.actions mod 250=0 then Print("PROGRESS rank replay actions ",RPStats.actions," normals ",RPStats.normals,"\n");fi;
end;;
RPFinish := function(f)
 local expected,cat,n,i,degs,k;
 RPCheck(f.kind="footer" and f.schema_version=1 and f.actions=RPStats.actions,"final footer count");expected:=[];
 for cat in ["transitive","primitive"] do
  if cat="transitive" then degs:=RPDegrees;else degs:=Concatenation([2..44],[54]);fi;
  for n in degs do
   if cat="transitive" then k:=NrTransitiveGroups(n);else k:=NrPrimitiveGroups(n);fi;
   for i in [1..k] do Add(expected,[cat,n,i]);od;
  od;
 od;
 RPCheck(Set(expected)=Set(RPSeen),"exact classification slice coverage");
 RPCheck(RPStats.transitive=7259 and RPStats.primitive=340 and RPStats.actions=7599,"action totals");
 RPCheck(RPStats.critical_pairs=233 and RPStats.relative_pairs=20628 and RPStats.primitive_pairs=945 and RPStats.normals=21806,"normal totals");
 RPCheck(RPStats.high_c1_pairs=15 and RPStats.owner_actions=11 and RPStats.nonsoluble18=91 and RPStats.nonsoluble18_pairs=521,"c1 seam totals");
 RPCheck(RPStats.nonaffine_simple=116 and RPStats.nonaffine_other=4 and RPStats.nonsoluble_affine=13,"primitive auxiliary scopes");
 Print("PASS PRIMITIVE RANK VERIFY: ",RPJSON(RPStats)," assertions=",RPChecks,"\n");
end;;
