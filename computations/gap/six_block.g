# Constructive six-pair action coverage and complete literal normal witnesses.
# Discovery may use subgroup/complement enumeration; replay checks closure,
# relator cocycles, actual permutation conjugacy and normal joins independently.
SBCheck:=FCRequire;;
SBRows:=FCPerms;;
SBGroup:=FEWGroup;;
SBLift:=function(g) return PermList(List([1..12],i->2*((QuoInt(i+1,2))^g)-(i mod 2)));end;;
SBBase:=function() return Group(List([1..6],i->(2*i-1,2*i)));end;;
SBTargets:=function()
 local V,q32,q48;
 V:=Group((1,2)(3,4),(1,3)(2,4),(5,6)(7,8),(5,7)(6,8));
 q32:=Group(Concatenation(GeneratorsOfGroup(V),[(2,3)(6,7)]));
 q48:=Group(Concatenation(GeneratorsOfGroup(V),[(1,2,3)(5,6,7)]));
 return [Group((1,2),(3,4),(5,6)),q32,q48,
   DirectProduct(Group((1,2)),q48),DirectProduct(Group((1,2),(3,4)),q48)];
end;;

# Exact graph-class count from defining relators on the original generators.
SBH1:=function(T,E,W,M)
 local gs,iso,fp,fg,rels,phi,Q,Mb,pc,d,top,columns,j,k,values,col,rel,g,rank,z,f;
 gs:=GeneratorsOfGroup(T);iso:=IsomorphismFpGroupByGenerators(T,gs);fp:=Image(iso);
 fg:=FreeGeneratorsOfFpGroup(fp);rels:=RelatorsOfFpGroup(fp);
 SBCheck(Length(fg)=Length(gs) and Size(fp)=Size(T),"exact top presentation");
 SBCheck(ForAll(rels,r->MappedWord(r,fg,gs)=One(T)),"presentation relators hold on the declared actual generators");
 phi:=NaturalHomomorphismByNormalSubgroup(W,E);Q:=Image(phi);Mb:=Image(phi,M);
 pc:=Pcgs(Mb);d:=Length(pc);top:=List(gs,g->Image(phi,SBLift(g)));columns:=[];
 for j in [1..Length(gs)] do for k in [1..d] do
  values:=ShallowCopy(top);values[j]:=pc[k]*values[j];col:=[];
  for rel in rels do
   g:=MappedWord(rel,fg,values);SBCheck(g in Mb,"relator has zero top");
   Append(col,ExponentsOfPcElement(pc,g));
  od;
  Add(columns,List(col,x->x*One(GF(2))));
 od;od;
 if Length(columns)=0 or Length(columns[1])=0 then rank:=0;else rank:=RankMat(columns);fi;
 z:=Length(gs)*d-rank;f:=LogInt(Size(Centralizer(Mb,Group(top))),2);
 SBCheck(z-d+f>=0,"nonnegative H1 dimension");
 return rec(phi:=phi,Q:=Q,base:=Mb,dimensions:=[d,z,f,z-d+f]);
end;;

SBNormals:=function(U,produce,data)
 local normals,classes,reps,atoms,atom,joins,j,k,N,H,chars,charrows,kn,entry,
   found,a,b,map,Q,target,iso,targets,out,actual,cc,seen,i;
 if produce then
  normals:=NormalSubgroups(U);classes:=ConjugacyClasses(U);
  reps:=List(classes,Representative);
 else
  normals:=List(data.normals,n->SBGroup(n.generators,12));
  reps:=FEWPerms(data.class_representatives,12);
  SBCheck(ForAll(reps,x->x in U),"literal conjugacy representatives belong to U");
  for j in [1..Length(reps)] do for k in [j+1..Length(reps)] do
   SBCheck(not IsConjugate(U,reps[j],reps[k]),"distinct conjugacy classes");
  od;od;
  SBCheck(Sum(reps,x->Index(U,Centralizer(U,x)))=Size(U),"all conjugacy classes covered");
 fi;
 atoms:=[];
 for a in reps do
  atom:=NormalClosure(U,Subgroup(U,[a]));if not atom in atoms then Add(atoms,atom);fi;
 od;
 SBCheck(TrivialSubgroup(U) in normals,"normal closure starts at 1");
 for j in [1..Length(normals)] do
  SBCheck(IsSubgroup(U,normals[j]) and IsNormal(U,normals[j]),"actual original normal");
  SBCheck(not normals[j] in normals{[1..j-1]},"distinct original normals");
 od;
 chars:=Irr(U);charrows:=[];
 for a in chars do
  kn:=Position(normals,KernelOfCharacter(a));SBCheck(kn<>fail,"irreducible kernel retained");
  AddSet(charrows,[kn,a[1]]);
 od;
 if not produce then SBCheck(data.character_kernels=charrows,"exact irreducible kernel-degree pairs");fi;
 targets:=SBTargets();out:=[];
 for j in [1..Length(normals)] do
  N:=normals[j];joins:=[];
  for atom in atoms do
   H:=ClosureGroup(N,atom);k:=Position(normals,H);
   SBCheck(k<>fail,"normal list closed under all class-normal joins");Add(joins,k);
  od;
  if produce then
   entry:=rec(generators:=SBRows(SmallGeneratingSet(N),12),order:=Size(N),joins:=joins);
   if N=U then entry.kind:="characters";entry.characters:=[];
   else
    found:=First([1..Length(charrows)],i->charrows[i][1]=j);
    if found<>fail then entry.kind:="characters";entry.characters:=[found];
    else
     found:=fail;
     for a in [1..Length(charrows)] do
      if charrows[a][2]<>1 then continue;fi;
      for b in [1..Length(charrows)] do
       if Intersection(normals[charrows[a][1]],normals[charrows[b][1]])=N then found:=[a,b];break;fi;
      od;
      if found<>fail then break;fi;
     od;
     if found<>fail then entry.kind:="characters";entry.characters:=found;
     else
      map:=NaturalHomomorphismByNormalSubgroup(U,N);Q:=Image(map);
      target:=First([1..5],i->Size(Q)=Size(targets[i]) and IsomorphismGroups(Q,targets[i])<>fail);
      SBCheck(target<>fail,"every noncharacter quotient has prescribed exact model");
      iso:=IsomorphismGroups(Q,targets[target]);entry.kind:="target";entry.target:=target;
      entry.images:=SBRows(List(GeneratorsOfGroup(U),g->Image(iso,Image(map,g))),LargestMovedPoint(targets[target]));
     fi;
    fi;
   fi;
  else
   entry:=data.normals[j];SBCheck(entry.order=Size(N) and entry.joins=joins,"normal order and complete join edges");
   if entry.kind="characters" then
    SBCheck(Length(entry.characters)<=2 and ForAll(entry.characters,i->i in [1..Length(charrows)]),"character positions");
    if Length(entry.characters)=0 then SBCheck(N=U,"empty cover only for trivial quotient");
    else
     if Length(entry.characters)=2 then SBCheck(charrows[entry.characters[1]][2]=1,"designated linear character");fi;
     H:=U;for i in entry.characters do H:=Intersection(H,normals[charrows[i][1]]);od;
     SBCheck(H=N,"character cover has exact original kernel");
    fi;
   else
    SBCheck(entry.kind="target" and entry.target in [1..5],"fixed exceptional quotient model");
    Q:=targets[entry.target];map:=GroupHomomorphismByImages(U,Q,GeneratorsOfGroup(U),FEWPerms(entry.images,LargestMovedPoint(Q)));
    SBCheck(map<>fail and Image(map)=Q and Kernel(map)=N,"literal original-source target map");
   fi;
  fi;
  Add(out,entry);
 od;
 return rec(normals:=out,class_representatives:=SBRows(reps,12),character_kernels:=charrows);
end;;

SBProduce:=function()
 local S,reps,record,H,edges,dc,x,K,j,c,tops,M,spaces,data,i,T,W,E,ctx,cs,comp,U,
       classes,interface,block,act,normal,total,certs,edge,k;
 S:=SymmetricGroup(6);reps:=List(ConjugacyClassesSubgroups(S),Representative);data:=rec(schema_version:=1,subgroups:=[],subspaces:=[],interfaces:=[],actions:=[]);
 for H in reps do
  edges:=[];
  for dc in DoubleCosets(S,H,H) do
   x:=Representative(dc);K:=ClosureGroup(H,x);j:=First([1..Length(reps)],i->Size(reps[i])=Size(K) and IsConjugate(S,K,reps[i]));
   c:=RepresentativeAction(S,K,reps[j]);
   Add(edges,rec(element:=SBRows([x],6)[1],target:=j,conjugator:=SBRows([c],6)[1]));
  od;
  Add(data.subgroups,rec(generators:=SBRows(GeneratorsOfGroup(H),6),order:=Size(H),edges:=edges));
 od;
 M:=SBBase();spaces:=AllSubgroups(M);data.subspaces:=List(spaces,E->SBRows(SmallGeneratingSet(E),12));
 classes:=[];certs:=0;
 for i in [1..Length(reps)] do
  T:=reps[i];if not IsTransitive(T,[1..6]) then continue;fi;
  W:=Group(Concatenation(GeneratorsOfGroup(M),List(GeneratorsOfGroup(T),SBLift)));
  for j in [1..Length(spaces)] do
   E:=spaces[j];if not IsNormal(W,E) then continue;fi;
   ctx:=SBH1(T,E,W,M);
   if Size(ctx.base)=1 then cs:=[ctx.Q];else cs:=ComplementClassesRepresentatives(ctx.Q,ctx.base);fi;
   interface:=rec(top:=i,space:=j,dimensions:=ctx.dimensions,complements:=[]);
   for comp in cs do
    U:=PreImage(ctx.phi,comp);block:=rec(generators:=SBRows(GeneratorsOfGroup(U),12),action:=0,conjugator:=[]);
    if IsTransitive(U,[1..12]) then
     certs:=certs+1;k:=First([1..Length(classes)],k->Size(classes[k])=Size(U) and IsConjugate(SymmetricGroup(12),U,classes[k]));
     if k=fail then Add(classes,U);k:=Length(classes);fi;
     c:=RepresentativeAction(SymmetricGroup(12),U,classes[k]);block.action:=k;block.conjugator:=SBRows([c],12)[1];
    fi;
    Add(interface.complements,block);
   od;
   Add(data.interfaces,interface);
  od;
 od;
 total:=0;
 for U in classes do
  normal:=Normalizer(SymmetricGroup(12),U);act:=SBNormals(U,true,fail);
  act.generators:=SBRows(GeneratorsOfGroup(U),12);act.order:=Size(U);
  act.normalizer_generators:=SBRows(SmallGeneratingSet(normal),12);act.normalizer_order:=Size(normal);
  total:=total+Length(act.normals);Add(data.actions,act);
  if Length(data.actions) mod 20=0 then Print("PROGRESS six-block export ",Length(data.actions)," actions\n");fi;
 od;
 data.counts:=rec(subgroup_classes:=Length(reps),subspaces:=Length(spaces),interfaces:=Length(data.interfaces),block_certificates:=certs,actions:=Length(classes),normals:=total);
 FCEmit(data);Print("PASS SIX BLOCK EXPORT: ",data.counts,"\n");
end;;

SBVerify:=function(data)
 local S,reps,i,j,H,e,x,c,K,cover,dc,M,spaces,T,W,E,expected,seen,ctx,comps,block,U,
       actions,normal,act,total,certs,reached,k,counts;
 SBCheck(data.schema_version=1,"six-block schema");S:=SymmetricGroup(6);
 reps:=List(data.subgroups,r->SBGroup(r.generators,6));
 SBCheck(TrivialSubgroup(S) in reps,"subgroup coverage starts at identity");
 for i in [1..Length(reps)] do
  H:=reps[i];SBCheck(Size(H)=data.subgroups[i].order,"subgroup order");cover:=[];
  for j in [i+1..Length(reps)] do
   if Size(H)=Size(reps[j]) then SBCheck(not IsConjugate(S,H,reps[j]),"distinct subgroup classes");fi;
  od;
  for e in data.subgroups[i].edges do
   x:=FEWPerms([e.element],6)[1];c:=FEWPerms([e.conjugator],6)[1];
   SBCheck(e.target in [1..Length(reps)] and ClosureGroup(H,x)^c=reps[e.target],"every adjoin edge has literal conjugator");
   UniteSet(cover,Set(Elements(DoubleCoset(H,x,H))));
  od;
  SBCheck(Length(cover)=720,"double cosets cover every possible adjoining element");
 od;
 SBCheck(Length(reps)=56 and Number(reps,H->IsTransitive(H,[1..6]))=16,"complete S6 classification");
 M:=SBBase();spaces:=List(data.subspaces,s->SBGroup(s,12));
 SBCheck(Length(spaces)=2825 and Length(Set(spaces))=2825 and ForAll(spaces,E->IsSubgroup(M,E)),"every binary subspace by exact Gaussian count");
 expected:=[];
 for i in [1..Length(reps)] do
  T:=reps[i];if not IsTransitive(T,[1..6]) then continue;fi;
  W:=Group(Concatenation(GeneratorsOfGroup(M),List(GeneratorsOfGroup(T),SBLift)));
  for j in [1..Length(spaces)] do if IsNormal(W,spaces[j]) then Add(expected,[i,j]);fi;od;
 od;
 SBCheck(List(data.interfaces,x->[x.top,x.space])=expected,"every invariant top/module interface");
 actions:=List(data.actions,a->SBGroup(a.generators,12));certs:=0;reached:=[];
 for e in data.interfaces do
  T:=reps[e.top];E:=spaces[e.space];W:=Group(Concatenation(GeneratorsOfGroup(M),List(GeneratorsOfGroup(T),SBLift)));
  ctx:=SBH1(T,E,W,M);SBCheck(e.dimensions=ctx.dimensions,"exact relator cocycle dimensions");comps:=[];
  for block in e.complements do
   U:=SBGroup(block.generators,12);SBCheck(IsSubgroup(W,U) and Intersection(U,M)=E and Size(U)=Size(E)*Size(T),"full original block projection with exact kernel");
   H:=Image(ctx.phi,U);SBCheck(Size(Intersection(H,ctx.base))=1 and Size(H)*Size(ctx.base)=Size(ctx.Q),"full quotient complement");
   SBCheck(ForAll(comps,K->not IsConjugate(ctx.Q,H,K)),"distinct graph classes");Add(comps,H);
   if IsTransitive(U,[1..12]) then
    SBCheck(block.action in [1..Length(actions)],"physical action target");c:=FEWPerms([block.conjugator],12)[1];
    SBCheck(U^c=actions[block.action],"literal physical conjugacy transport");
    SBCheck(Size(Action(Stabilizer(U,[1,2],OnSets),[1,2]))=2,"exact local binary component");
    AddSet(reached,block.action);certs:=certs+1;
   else SBCheck(block.action=0 and block.conjugator=[],"intransitive graph excluded explicitly");fi;
  od;
  SBCheck(Length(comps)=2^ctx.dimensions[4],"complete graph count from H1");
 od;
 SBCheck(reached=[1..Length(actions)],"all physical nodes reached");total:=0;
 for i in [1..Length(actions)] do
  U:=actions[i];act:=data.actions[i];SBCheck(IsTransitive(U,[1..12]) and Size(U)=act.order,"literal degree12 action");
  for j in [i+1..Length(actions)] do
   if Size(U)=Size(actions[j]) then SBCheck(not IsConjugate(SymmetricGroup(12),U,actions[j]),"distinct physical actions");fi;
  od;
  normal:=SBGroup(act.normalizer_generators,12);
  SBCheck(normal=Normalizer(SymmetricGroup(12),U) and Size(normal)=act.normalizer_order,"exact original symmetric normalizer");
  SBNormals(U,false,act);total:=total+Length(act.normals);
  if i mod 20=0 then Print("PROGRESS six-block verify ",i," actions\n");fi;
 od;
 counts:=rec(subgroup_classes:=56,subspaces:=2825,interfaces:=Length(expected),block_certificates:=certs,actions:=Length(actions),normals:=total);
 SBCheck(counts=data.counts and Length(expected)=112 and certs=224 and Length(actions)=182 and total=2476,"exact full-domain counts");
 Print("PASS SIX BLOCK VERIFY: ",counts,"\n");
end;;
