# Constructive two-affine-block coverage; no transitive catalogue is queried.
ASChecks:=0;;ASJSON:=fail;;
ASCheck:=function(b,s)if not b then Error(Concatenation("affine-nine structure: ",s));fi;ASChecks:=ASChecks+1;end;;
ASJSON:=function(v)
 local names;
 if IsBool(v) or IsInt(v) then return String(v);fi;
 if IsStringRep(v) then return Concatenation("\"",ReplacedString(ReplacedString(v,"\\","\\\\"),"\"","\\\""),"\"");fi;
 if IsList(v) then return Concatenation("[",JoinStringsWithSeparator(List(v,ASJSON),","),"]");fi;
 if IsRecord(v) then names:=Set(RecNames(v));return Concatenation("{",JoinStringsWithSeparator(List(names,k->Concatenation(ASJSON(k),":",ASJSON(v.(k)))),","),"}");fi;
 Error("unsupported JSON value");
end;;
ASStream:=OutputTextUser();;SetPrintFormattingStatus(ASStream,false);;
ASImages:=function(G,n)local gs;gs:=GeneratorsOfGroup(G);if Length(gs)=0 then gs:=[()];fi;return List(gs,g->List([1..n],i->i^g));end;;
ASPerm:=function(g,n)return List([1..n],i->i^g);end;;
ASGroup:=function(rows,n)ASCheck(Length(rows)>0 and ForAll(rows,r->Length(r)=n and Set(r)=[1..n]),"literal permutation rows");return Group(List(rows,PermList));end;;
ASGeometry:=function()
 local f,vs,mats,G,trans,i,t,lines,v;
 f:=GF(3);vs:=Tuples(Elements(f),2);mats:=Elements(GL(2,3));ASCheck(Length(mats)=48,"all invertible two-dimensional matrices");
 G:=Group(List(mats,g->PermList(List(vs,v->Position(vs,v*g)))));trans:=[];
 for i in [1..2] do t:=List([1..2],j->Zero(f));t[i]:=One(f);Add(trans,PermList(List(vs,v->Position(vs,v+t))));od;
 lines:=Set(List(Filtered(vs,v->v<>[Zero(f),Zero(f)]),v->Set(List(Elements(f),a->Position(vs,a*v)))));
 ASCheck(Size(G)=48 and Length(lines)=4,"faithful natural matrix action and four lines");
 return rec(matrix:=G,translations:=Group(trans),lines:=lines,swap:=Product(List([1..9],i->(i,i+9))));
end;;
ASIrreducible:=function(R,geom)return not ForAny(geom.lines,B->ForAll(GeneratorsOfGroup(R),g->OnSets(B,g)=B));end;;
ASConjugator:=function(A,H,K)local c;c:=RepresentativeAction(A,H,K);ASCheck(c<>fail,"actual conjugator exists");return c;end;;
ASGraph:=function(L,N,pi,phi,sw)
 local gs,g,x;
 gs:=Concatenation(GeneratorsOfGroup(N),List(GeneratorsOfGroup(N),g->g^sw));
 for g in GeneratorsOfGroup(L) do x:=PreImagesRepresentative(pi,Image(phi,Image(pi,g)));Add(gs,g*x^sw);od;
 return Group(gs);
end;;
ASProduce:=function(alphabet)
 local geom,M,reps,data,i,j,H,g,J,c,idx,edges,locals,localData,entry,R,L,base,W,N,nr,pi,Q,A,I,co,phi,K,D,np,P,P0,cand,reduced,U,ext,iv,gr,x,h,target,targets,targetids,S,nonsplit,orderphi,counts;
 geom:=ASGeometry();M:=geom.matrix;S:=SymmetricGroup(18);
 targets:=List(alphabet.actions,r->ASGroup(r.generators,18));targetids:=List(alphabet.actions,r->r.action_id);
 ASCheck(Length(targets)=98 and Length(Set(targetids))=98,"shared literal action alphabet");
 reps:=List(ConjugacyClassesSubgroups(M),Representative);ASCheck(Length(reps)=16,"sixteen matrix subgroup representatives");
 data:=rec(kind:="affine9_structure",schema_version:=1,subgroups:=[],locals:=[]);
 counts:=rec(adjoining_edges:=0,graphs:=0,extensions:=0,involutions:=0,nonsplit:=0,higher_order_automorphisms:=0);
 for i in [1..Length(reps)] do
  H:=reps[i];edges:=[];
  for g in Elements(M) do
   J:=ClosureGroup(H,Group(g));idx:=First([1..Length(reps)],j->Size(reps[j])=Size(J) and IsConjugate(M,J,reps[j]));ASCheck(idx<>fail,"adjoining closure target");c:=ASConjugator(M,J,reps[idx]);
   Add(edges,rec(element:=ASPerm(g,9),target:=idx,conjugator:=ASPerm(c,9)));counts.adjoining_edges:=counts.adjoining_edges+1;
  od;
  Add(data.subgroups,rec(generators:=ASImages(H,9),irreducible:=ASIrreducible(H,geom),edges:=edges));
 od;
 locals:=Filtered([1..Length(reps)],i->ASIrreducible(reps[i],geom));
 Sort(locals,function(i,j)local L1,L2;L1:=ClosureGroup(geom.translations,reps[i]);L2:=ClosureGroup(geom.translations,reps[j]);if Size(L1)<>Size(L2) then return Size(L1)<Size(L2);fi;return StructureDescription(L1)<StructureDescription(L2);end);
 for i in locals do
  R:=reps[i];L:=ClosureGroup(geom.translations,R);localData:=rec(stabilizer:=i,generators:=ASImages(L,9),normals:=[]);
  base:=Group(Concatenation(GeneratorsOfGroup(L),List(GeneratorsOfGroup(L),g->g^geom.swap)));W:=ClosureGroup(base,Group(geom.swap));
  for N in NormalSubgroups(L) do
   nr:=rec(generators:=ASImages(N,9),graphs:=[]);pi:=NaturalHomomorphismByNormalSubgroup(L,N);Q:=Image(pi);A:=AutomorphismGroup(Q);I:=Subgroup(A,List(GeneratorsOfGroup(Q),g->ConjugatorAutomorphism(Q,g)));
   for co in RightCosets(A,I) do
    phi:=Representative(co);if not phi^2 in I then continue;fi;
    K:=ASGraph(L,N,pi,phi,geom.swap);D:=Normalizer(W,K);np:=NaturalHomomorphismByNormalSubgroup(D,K);P:=Image(np);P0:=Image(np,Intersection(D,base));cand:=Filtered(Elements(P),x->Order(x)=2 and not x in P0);
    gr:=rec(phi_lifts:=List(GeneratorsOfGroup(L),g->ASPerm(PreImagesRepresentative(pi,Image(phi,Image(pi,g))),9)),kernel:=ASImages(K,18),automorphism_order:=Order(phi),extensions:=[],involutions:=[]);
    reduced:=[];
    for x in cand do
     U:=PreImage(np,Subgroup(P,[x]));idx:=First([1..Length(reduced)],j->IsConjugate(W,U,reduced[j]));
     if idx=fail then
      Add(reduced,U);idx:=Length(reduced);target:=First([1..Length(targets)],j->Size(U)=Size(targets[j]) and IsConjugate(S,U,targets[j]));ASCheck(target<>fail,"target in shared action alphabet");
      c:=ASConjugator(S,U,targets[target]);nonsplit:=not ForAny(ConjugacyClasses(U),h->Order(Representative(h))=2 and not Representative(h) in K);
      ext:=rec(generators:=ASImages(U,18),target:=targetids[target],conjugator:=ASPerm(c,18),nonsplit:=nonsplit);Add(gr.extensions,ext);counts.extensions:=counts.extensions+1;if nonsplit then counts.nonsplit:=counts.nonsplit+1;fi;
     fi;
     c:=ASConjugator(W,U,reduced[idx]);Add(gr.involutions,rec(lift:=ASPerm(PreImagesRepresentative(np,x),18),extension:=idx,conjugator:=ASPerm(c,18)));counts.involutions:=counts.involutions+1;
    od;
    counts.graphs:=counts.graphs+1;if Order(phi)>2 then counts.higher_order_automorphisms:=counts.higher_order_automorphisms+1;fi;Add(nr.graphs,gr);
   od;
   Add(localData.normals,nr);
  od;
  Add(data.locals,localData);Print("PROGRESS affine-nine local ",Length(data.locals)," graphs ",counts.graphs," extensions ",counts.extensions,"\n");
 od;
 data.counts:=counts;
 PrintTo(ASStream,"DATA ",ASJSON(data),"\n");Print("PASS AFFINE9 STRUCTURE EXPORT: ",ASJSON(counts),"\n");
end;;
ASVerify:=function(data,alphabet)
 local geom,M,reps,i,j,H,edge,g,J,c,irred,locals,localData,L,base,W,N,nr,normalList,pi,Q,A,I,cosets,phis,phi,gr,images,K,D,np,P,P0,cand,seen,reduced,U,ex,idx,x,h,target,targets,targetids,S,hit,nonsplit,counts,allV;
 ASCheck(data.kind="affine9_structure" and data.schema_version=1,"schema");geom:=ASGeometry();M:=geom.matrix;S:=SymmetricGroup(18);
 targets:=List(alphabet.actions,r->ASGroup(r.generators,18));targetids:=List(alphabet.actions,r->r.action_id);
 ASCheck(Length(targets)=98 and Length(Set(targetids))=98,"shared alphabet size and IDs");
 for i in [1..Length(targets)] do
  ASCheck(IsTransitive(targets[i],[1..18]) and Size(targets[i])=alphabet.actions[i].order,"shared original action");
  for j in [1..i-1] do if Size(targets[i])=Size(targets[j]) then ASCheck(not IsConjugate(S,targets[i],targets[j]),"shared actions pairwise nonconjugate");fi;od;
 od;
 reps:=List(data.subgroups,r->ASGroup(r.generators,9));ASCheck(Length(reps)=16 and Number(reps,IsTrivial)=1,"sixteen matrix representatives including trivial");
 counts:=rec(adjoining_edges:=0,graphs:=0,extensions:=0,involutions:=0,nonsplit:=0,higher_order_automorphisms:=0);
 for i in [1..Length(reps)] do
  H:=reps[i];ASCheck(IsSubgroup(M,H),"actual matrix subgroup");ASCheck(data.subgroups[i].irreducible=ASIrreducible(H,geom),"natural-module irreducibility");
  for j in [1..i-1] do if Size(H)=Size(reps[j]) then ASCheck(not IsConjugate(M,H,reps[j]),"matrix representatives pairwise nonconjugate");fi;od;
  seen:=[];
  for edge in data.subgroups[i].edges do
   g:=PermList(edge.element);c:=PermList(edge.conjugator);ASCheck(g in M and c in M and edge.target in [1..Length(reps)],"adjoining edge domain");
   ASCheck(not g in seen,"adjoining elements unique");Add(seen,g);J:=ClosureGroup(H,Group(g));ASCheck(J^c=reps[edge.target],"actual adjoining conjugator");counts.adjoining_edges:=counts.adjoining_edges+1;
  od;
  ASCheck(Set(seen)=Set(Elements(M)),"every matrix element adjoined");
 od;
 irred:=Filtered([1..Length(reps)],i->ASIrreducible(reps[i],geom));ASCheck(Length(irred)=7,"seven irreducible local stabilizers");
 ASCheck(Set(List(data.locals,r->r.stabilizer))=Set(irred) and Length(data.locals)=7,"all local stabilizers exactly once");hit:=[];
 allV:=Group(Concatenation(GeneratorsOfGroup(geom.translations),List(GeneratorsOfGroup(geom.translations),g->g^geom.swap)));
 for localData in data.locals do
  L:=ASGroup(localData.generators,9);ASCheck(L=ClosureGroup(geom.translations,reps[localData.stabilizer]) and IsPrimitive(L,[1..9]),"exact primitive affine local action");
  base:=Group(Concatenation(GeneratorsOfGroup(L),List(GeneratorsOfGroup(L),g->g^geom.swap)));W:=ClosureGroup(base,Group(geom.swap));normalList:=[];
  for nr in localData.normals do
   N:=ASGroup(nr.generators,9);ASCheck(IsNormal(L,N) and not N in normalList,"distinct actual local normal");Add(normalList,N);
   pi:=NaturalHomomorphismByNormalSubgroup(L,N);Q:=Image(pi);A:=AutomorphismGroup(Q);I:=Subgroup(A,List(GeneratorsOfGroup(Q),g->ConjugatorAutomorphism(Q,g)));cosets:=Filtered(RightCosets(A,I),co->Representative(co)^2 in I);phis:=[];
   for gr in nr.graphs do
    images:=List(gr.phi_lifts,PermList);ASCheck(Length(images)=Length(GeneratorsOfGroup(L)) and ForAll(images,g->g in L),"actual automorphism lift rows");
    phi:=GroupHomomorphismByImages(Q,Q,List(GeneratorsOfGroup(L),g->Image(pi,g)),List(images,g->Image(pi,g)));
    ASCheck(phi<>fail and IsBijective(phi) and phi in A and phi^2 in I,"actual qualifying outer automorphism");ASCheck(Order(phi)=gr.automorphism_order,"automorphism order");Add(phis,phi);
    K:=ASGroup(gr.kernel,18);ASCheck(K=ASGraph(L,N,pi,phi,geom.swap) and Size(K)*Size(Q)=Size(L)^2,"literal full Goursat kernel");
    D:=Normalizer(W,K);np:=NaturalHomomorphismByNormalSubgroup(D,K);P:=Image(np);P0:=Image(np,Intersection(D,base));cand:=Filtered(Elements(P),x->Order(x)=2 and not x in P0);seen:=[];reduced:=[];
    for ex in gr.extensions do
     U:=ASGroup(ex.generators,18);ASCheck(IsSubgroup(W,U) and IsTransitive(U,[1..18]) and Intersection(U,base)=K and Index(U,K)=2,"actual extension and its block kernel");
     ASCheck(Size(Action(K,[1..9]))=Size(L) and Size(Action(K,[10..18]))=Size(L),"exact local projections");
     ASCheck(Size(Intersection(U,allV)) in [9,81],"diagonal or full translation intersection");
     ASCheck(ForAll(reduced,J->not IsConjugate(W,U,J)),"wreath extension representatives distinct");Add(reduced,U);
     idx:=Position(targetids,ex.target);ASCheck(idx<>fail,"shared target ID");c:=PermList(ex.conjugator);ASCheck(c in S and U^c=targets[idx],"literal S18 identification");AddSet(hit,idx);
     nonsplit:=not ForAny(ConjugacyClasses(U),h->Order(Representative(h))=2 and not Representative(h) in K);ASCheck(ex.nonsplit=nonsplit,"involutory swap existence checked in actual extension");
     counts.extensions:=counts.extensions+1;if nonsplit then counts.nonsplit:=counts.nonsplit+1;fi;
    od;
    for edge in gr.involutions do
     g:=PermList(edge.lift);ASCheck(g in D,"actual normalizer lift");x:=Image(np,g);ASCheck(x in cand and not x in seen,"distinct nonbase quotient involution");Add(seen,x);
     idx:=edge.extension;ASCheck(idx in [1..Length(reduced)],"chosen extension index");U:=PreImage(np,Subgroup(P,[x]));c:=PermList(edge.conjugator);ASCheck(c in W and U^c=reduced[idx],"full preimage transported by actual wreath conjugator");counts.involutions:=counts.involutions+1;
    od;
    ASCheck(Set(seen)=Set(cand),"every nonbase quotient involution retained");ASCheck(Set(List(gr.involutions,e->e.extension))=[1..Length(reduced)],"every extension hit by a lift");
    counts.graphs:=counts.graphs+1;if Order(phi)>2 then counts.higher_order_automorphisms:=counts.higher_order_automorphisms+1;fi;
   od;
   ASCheck(Length(phis)=Length(cosets) and ForAll(cosets,co->Number(phis,phi->phi in co)=1),"every square-inner outer coset exactly once");
  od;
  ASCheck(Length(normalList)=Length(NormalSubgroups(L)) and ForAll(NormalSubgroups(L),N->N in normalList),"complete local normal list");
  Print("PROGRESS affine-nine replay graphs ",counts.graphs," extensions ",counts.extensions,"\n");
 od;
 ASCheck(hit=[1..98],"every shared action reached");ASCheck(counts=data.counts,"recorded structural counts");
 ASCheck(counts.adjoining_edges=768 and counts.graphs=75 and counts.extensions=116 and counts.nonsplit=36,"complete structural totals");
 Print("PASS AFFINE9 STRUCTURE VERIFY: ",ASJSON(counts)," actions=98 assertions=",ASChecks,"\n");
end;;
