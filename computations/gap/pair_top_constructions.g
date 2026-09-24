# Constructive pair-top coverage from actual kernels, quotient graphs and lifts.
# Primitive classification is a separate mathematical input.
PTConstructFourPairs:=function()
  local sw,models,L,base,W,N,pi,Q,aut,inn,cs,phi,gs,g,x,K,nor,qpi,
    qbase,cand,U;
  sw:=(1,5)(2,6)(3,7)(4,8);models:=[];
  for L in [AlternatingGroup(4),SymmetricGroup(4)] do
    base:=Group(Concatenation(GeneratorsOfGroup(L),List(GeneratorsOfGroup(L),g->g^sw)));
    W:=ClosureGroup(base,Group(sw));
    for N in PTMenu(L).normals do
      pi:=NaturalHomomorphismByNormalSubgroup(L,N);Q:=Image(pi);aut:=AutomorphismGroup(Q);
      inn:=Subgroup(aut,List(GeneratorsOfGroup(Q),g->ConjugatorAutomorphism(Q,g)));
      for cs in RightCosets(aut,inn) do
        phi:=Representative(cs);gs:=Concatenation(GeneratorsOfGroup(N),List(GeneratorsOfGroup(N),g->g^sw));
        for g in GeneratorsOfGroup(L) do
          x:=PreImagesRepresentative(pi,Image(phi,Image(pi,g)));Add(gs,g*x^sw);
        od;
        K:=Group(gs);nor:=Normalizer(W,K);qpi:=NaturalHomomorphismByNormalSubgroup(nor,K);
        qbase:=Image(qpi,Intersection(nor,base));
        cand:=Filtered(Elements(Image(qpi)),g->Order(g)=2 and not g in qbase);
        for g in cand do
          U:=PreImage(qpi,Subgroup(Image(qpi),[g]));
          PTRequire(Intersection(U,base)=K and Index(U,K)=2 and IsTransitive(U,[1..8]),"actual four-block graph and swap");
          PTRequire(Size(Action(K,[1..4]))=Size(L) and Size(Action(K,[5..8]))=Size(L),"full two-four local projections");
          if not ForAny(models,T->IsConjugate(SymmetricGroup(8),T,U)) then Add(models,U);fi;
        od;
      od;
    od;
  od;
  PTRequire(Length(models)=10,"all ten actual two-four graph/swap classes");
  return models;
end;;

PTConstructEight:=function(actions)
 local checks,Check,tops,labels,AddTop,M4,models,U,flips,C,A,Es,gens,
       top,T,E,x,y,reps,j,i,expected,primrows,es,cursor,F;
 checks:=0;tops:=[];labels:=[];
 Check:=function(ok,msg)if not ok then Error(msg);fi;checks:=checks+1;end;
 AddTop:=function(U,label)if not ForAny(tops,T->IsConjugate(SymmetricGroup(8),U,T)) then Add(tops,U);Add(labels,label);fi;end;
 models:=PTConstructFourPairs();
 for i in [1..Length(models)] do AddTop(models[i],Concatenation("two-four-",String(i)));od;
 Check(Length(tops)=10,"ten Goursat/swap constructions remain distinct");
 flips:=[(1,2),(3,4),(5,6),(7,8)];M4:=Group(flips);C:=Group(Product(flips));A:=Group(flips[1]*flips[2],flips[2]*flips[3],flips[3]*flips[4]);Es:=[Group(()),C,A,M4];
 gens:=[[(1,3,5)(2,4,6),(1,3)(2,4)(5,7)(6,8)],[(1,3,5,7)(2,4,6,8),(1,3)(2,4)]];
 models:=[];
 for j in [1..2] do top:=gens[j];
  Check(Size(Group(top))=[12,24][j] and Size(Intersection(Group(top),M4))=1,"actual split four-pair top");
  es:=[Group(())];cursor:=1;
  while cursor<=Length(es) do
   for x in Elements(M4) do F:=NormalClosure(ClosureGroup(M4,Group(top)),ClosureGroup(es[cursor],x));
    if not F in es then Add(es,F);fi;
   od;cursor:=cursor+1;
  od;
  Check(Set(es)=Set(Es),"cyclic closure proves all four invariant binary kernels");
  for E in Es do reps:=[];
  for x in Elements(M4) do for y in Elements(M4) do
   U:=Group(Concatenation(GeneratorsOfGroup(E),[x*top[1],y*top[2]]));
   if Intersection(U,M4)=E and IsTransitive(U,[1..8]) and not ForAny(reps,T->IsConjugate(M4,U,T)) then Add(reps,U);fi;
  od;od;
  Append(models,reps);
 od;od;
 Check(Length(models)=10,"ten complete binary lift constructions");
 for i in [1..10] do AddTop(models[i],Concatenation("binary-four-",String(i)));od;
 Check(Length(tops)=17,"seventeen distinct imprimitive tops, exactly three overlaps");
 # The seven primitive classifications are external mathematical inputs.
 primrows:=[];
 expected:=[[56,8,7],[168,8,21],[1344,8,168],[168,168,1],[336,168,2],[20160,20160,1],[40320,20160,2]];
 for i in [1..7] do T:=PTGroup(First(actions,a->a.family="paired8" and a.index=i+17).generators);Check(IsPrimitive(T,[1..8]) and [Size(T),Size(Socle(T)),Index(T,Socle(T))]=expected[i],"exact primitive socle/quotient interface");AddTop(T,Concatenation("primitive-",String(i)));Add(primrows,expected[i]);od;
 Check(Length(tops)=24,"seventeen constructive imprimitive and seven licensed primitive tops");
return tops;
end;;
PTConstructTwoAffine:=function()
  local field,vs,mat,trans,i,t,V,R,G,P7,N7,locals,sw,models,
    localidx,L,base,W,nsL,N,pi,Q,aut,inn,cs,phi,gs,g,x,K,nor,qpi,
    qg,qbase,cand,lifts,reps,U,E;
  field:=GF(2);vs:=Tuples(Elements(field),3);mat:=GL(3,2);trans:=[];
  for i in [1..3] do t:=[0,0,0]*One(field);t[i]:=One(field);
    Add(trans,PermList(List(vs,v->Position(vs,v+t))));od;
  V:=Group(trans);R:=Group(List(GeneratorsOfGroup(mat),g->PermList(List(vs,v->Position(vs,v*g)))));
  G:=ClosureGroup(V,R);P7:=SylowSubgroup(R,7);N7:=Normalizer(R,P7);
  locals:=[ClosureGroup(V,P7),ClosureGroup(V,N7),G];
  PTRequire(List(locals,Size)=[56,168,1344],"three actual affine local actions");
  sw:=Product(List([1..8],i->(i,i+8)));models:=[];
  for localidx in [1..3] do
    L:=locals[localidx];PTRequire(IsPrimitive(L,[1..8]) and Socle(L)=V,"affine primitive local socle");
    PTRequire(Size(AutomorphismGroup(L))/Size(L)=[3,1,2][localidx],"complete local automorphisms include affine cocycle");
    base:=Group(Concatenation(GeneratorsOfGroup(L),List(GeneratorsOfGroup(L),g->g^sw)));
    W:=ClosureGroup(base,Group(sw));nsL:=PTMenu(L).normals;
    PTRequire(Set(List(nsL,Size))=[[1,8,56],[1,8,56,168],[1,8,1344]][localidx],"all local normal kernels");
    for N in nsL do
      pi:=NaturalHomomorphismByNormalSubgroup(L,N);Q:=Image(pi);aut:=AutomorphismGroup(Q);
      inn:=Subgroup(aut,List(GeneratorsOfGroup(Q),g->ConjugatorAutomorphism(Q,g)));
      for cs in RightCosets(aut,inn) do
        phi:=Representative(cs);if not phi^2 in inn then continue;fi;
        phi:=First(Elements(cs),h->h^2=One(aut));
        PTRequire(phi<>fail,"all admissible outer classes admit literal involutory representatives");
        gs:=Concatenation(GeneratorsOfGroup(N),List(GeneratorsOfGroup(N),g->g^sw));
        for g in GeneratorsOfGroup(L) do
          x:=PreImagesRepresentative(pi,Image(phi,Image(pi,g)));Add(gs,g*x^sw);
        od;
        K:=Group(gs);nor:=Normalizer(W,K);qpi:=NaturalHomomorphismByNormalSubgroup(nor,K);
        qg:=Image(qpi);qbase:=Image(qpi,Intersection(nor,base));
        cand:=Filtered(Elements(qg),g->Order(g)=2 and not g in qbase);
        lifts:=List(cand,g->PreImage(qpi,Subgroup(qg,[g])));reps:=[];
        for U in lifts do if ForAll(reps,h->not IsConjugate(W,U,h)) then Add(reps,U);fi;od;
        PTRequire(Length(reps)=1,"all actual swap lifts covered for this full quotient graph");
        for U in reps do
          PTRequire(IsTransitive(U,[1..16]) and Intersection(U,base)=K and Index(U,K)=2,
            "actual complete block stabilizer and swap extension");
          PTRequire(Size(Action(K,[1..8]))=Size(L) and Size(Action(K,[9..16]))=Size(L),"both full local projections");
          E:=Intersection(U,Group(Concatenation(GeneratorsOfGroup(V),List(GeneratorsOfGroup(V),g->g^sw))));
          PTRequire(Size(E) in [8,64],"actual diagonal or full binary kernel");Add(models,U);
        od;
      od;
    od;
  od;
  PTRequire(Length(models)=15,"four plus six plus five complete graph/swap classes");
  return models;
end;;

PTConstructZero:=function()
  local S4,alltops,a,b,H,g,F,tops,T,R0,onto,toprows,frames,lift,M,blocks,
    which,cosets,reps,hom,induced,R,Rinv,flip,hs,W,classes,frame,rg,
    es,cursor,E,fp,fg,rels,phi,Q,Mb,pc,d,top,cs,columns,j,k,values,col,
    rel,x,rankZ,zdim,fixdim,h1dim,C,U,interfaces,certs,pos,normals;
  S4:=SymmetricGroup(4);alltops:=List(ConjugacyClassesSubgroups(S4),Representative);
  PTRequire(Length(alltops)=11 and ForAny(alltops,H->Size(H)=1),"eleven candidate four-point subgroup classes");
  for a in [1..Length(alltops)] do
    for b in [a+1..Length(alltops)] do PTRequire(not IsConjugate(S4,alltops[a],alltops[b]),"distinct four-point subgroup classes");od;
    H:=alltops[a];for g in Elements(S4) do F:=ClosureGroup(H,g);
      PTRequire(ForAny(alltops,T->Size(T)=Size(F) and IsConjugate(S4,T,F)),"adjoining every element proves all four-point subgroups");
    od;
  od;
  tops:=Filtered(alltops,T->IsTransitive(T,[1..4]));PTRequire(Length(tops)=5,"complete five transitive four-point actions");
  for T in tops do H:=Stabilizer(T,1);
    for R0 in [Group((1,2,3)),Group((1,2,3),(1,2))] do
      onto:=Filtered(AllHomomorphisms(H,R0),hom->Size(Image(hom))=Size(R0));
      PTRequire((Length(onto)>0)=(Size(T)=4*Size(R0)),"only A4/C3 and S4/S3 stabilizer epimorphisms");
    od;
  od;
  lift:=function(g,i)local p,j;p:=[1..16];for j in [1..4] do p[4*i+j]:=4*i+j^g;od;return PermList(p);end;
  M:=Group(Concatenation(List([0..3],i->[lift((1,2)(3,4),i),lift((1,3)(2,4),i)])));
  blocks:=List([0..3],i->[4*i+1..4*i+4]);frames:=[];
  for which in [1,2] do
    if which=1 then T:=AlternatingGroup(4);else T:=S4;fi;
    H:=Stabilizer(T,4);cosets:=RightCosets(T,H);reps:=List(cosets,Representative);hom:=IdentityMapping(H);
    induced:=function(g)local p,i,j,h,k;p:=[1..16];for i in [1..4] do
      j:=Position(cosets,cosets[i]*g);h:=reps[i]*g*reps[j]^-1;
      for k in [1..4] do p[4*(i-1)+k]:=4*(j-1)+k^Image(hom,h);od;od;return PermList(p);end;
    R:=Group(List(GeneratorsOfGroup(T),induced));
    PTRequire(Size(R)=Size(T) and Size(Kernel(ActionHomomorphism(R,blocks,OnSets)))=1,"actual faithful linear frame");
    PTRequire(Size(Action(Stabilizer(R,blocks[1],OnSets),blocks[1]))=Size(H),"exact local linear image");
    if which=1 then
      hs:=GeneratorsOfGroup(H);hom:=GroupHomomorphismByImages(H,H,hs,List(hs,h->h^-1));
      Rinv:=Group(List(GeneratorsOfGroup(T),induced));flip:=Product(List([0..3],i->lift((1,2),i)));
      PTRequire(R^flip=Rinv and M^flip=M,"actual conjugacy fuses both C3 orientations");
    else
      onto:=Filtered(AllHomomorphisms(H,H),hom->Size(Image(hom))=6);
      PTRequire(Length(onto)=6 and ForAll(onto,hom->ForAny(Elements(H),g->ForAll(GeneratorsOfGroup(H),h->Image(hom,h)=h^g))),"all six S3 maps are inner");
    fi;
    Add(frames,[R,ClosureGroup(M,R)]);
  od;
  classes:=[];interfaces:=0;certs:=0;
  for frame in frames do
    R:=frame[1];W:=frame[2];rg:=GeneratorsOfGroup(R);es:=[TrivialSubgroup(M)];cursor:=1;
    while cursor<=Length(es) do E:=es[cursor];
      for g in RightTransversal(M,E) do if g in E then continue;fi;
        F:=NormalClosure(W,ClosureGroup(E,g));if not F in es then Add(es,F);fi;
      od;cursor:=cursor+1;
    od;
    # Every invariant kernel is generated by cyclic invariant kernels of its vectors.
    SortBy(es,Size);fp:=Image(IsomorphismFpGroupByGenerators(R,rg));
    fg:=FreeGeneratorsOfFpGroup(fp);rels:=RelatorsOfFpGroup(fp);
    PTRequire(Size(fp)=Size(R) and Length(fg)=Length(rg) and ForAll(rels,rel->MappedWord(rel,fg,rg)=One(R)),"exact presentation on original frame generators");
    for E in es do
      phi:=NaturalHomomorphismByNormalSubgroup(W,E);Q:=Image(phi);Mb:=Image(phi,M);
      PTRequire(IsElementaryAbelian(Mb),"actual binary quotient module");
      pc:=Pcgs(Mb);d:=Length(pc);top:=List(rg,g->Image(phi,g));
      if d=0 then cs:=[Q];else cs:=ComplementClassesRepresentatives(Q,Mb);fi;
      columns:=[];
      for j in [1..Length(rg)] do for k in [1..d] do
        values:=ShallowCopy(top);values[j]:=pc[k]*values[j];col:=[];
        for rel in rels do x:=MappedWord(rel,fg,values);PTRequire(x in Mb,"actual relator error in binary module");
          Append(col,ExponentsOfPcElement(pc,x));od;
        Add(columns,List(col,x->x*One(GF(2))));
      od;od;
      if Length(columns)=0 or Length(columns[1])=0 then rankZ:=0;else rankZ:=RankMat(columns);fi;
      zdim:=Length(rg)*d-rankZ;fixdim:=LogInt(Size(Centralizer(Mb,Group(top))),2);h1dim:=zdim-d+fixdim;
      PTRequire(h1dim>=0 and Length(cs)=2^h1dim,"all complement classes by exact Z1/B1 dimension");
      for a in [1..Length(cs)] do for b in [a+1..Length(cs)] do PTRequire(not IsConjugate(Q,cs[a],cs[b]),"distinct actual complement classes");od;od;
      interfaces:=interfaces+1;
      for C in cs do
        PTRequire(Size(C)*Size(Mb)=Size(Q) and Size(Intersection(C,Mb))=1,"literal full complement");U:=PreImage(phi,C);
        PTRequire(Intersection(U,M)=E and Size(U)/Size(E)=Size(R),"exact original kernel and full top");
        if Size(E)=1 then PTRequire(not IsTransitive(U,[1..16]),"zero base is outside transitive scope");continue;fi;
        PTRequire(IsTransitive(U,[1..16]) and Size(Action(Stabilizer(U,blocks[1],OnSets),blocks[1]))=4*Size(Stabilizer(R,blocks[1],OnSets)),"actual primitive-four local action");
        if not ForAny(classes,T->Size(T)=Size(U) and IsConjugate(SymmetricGroup(16),T,U)) then Add(classes,U);fi;
        certs:=certs+1;
      od;
    od;
  od;
  PTRequire(Length(classes)=29,"complete zero-ternary 29-class domain");
  Print("PASS PAIR TOP ZERO CONSTRUCTION: ",interfaces," kernel/complement interfaces; ",certs," transitive lifts\n");
  return classes;
end;;

PTBindConstruction:=function(actions,family,models)
  local records,degree,used,U,i,c,rows;
  records:=Filtered(actions,a->a.family=family);degree:=records[1].degree;used:=[];rows:=[];
  PTRequire(Length(models)=Length(records),"exact constructed domain size");
  for U in models do
    i:=First([1..Length(records)],j->Size(U)=records[j].order and IsConjugate(SymmetricGroup(degree),U,PTGroup(records[j].generators)));
    PTRequire(i<>fail and not i in used,"each constructed class binds one distinct literal action");Add(used,i);
    c:=RepresentativeAction(SymmetricGroup(degree),U,PTGroup(records[i].generators));
    PTRequire(c<>fail and U^c=PTGroup(records[i].generators),"literal permutation conjugacy transports action and all its normals");
    Add(rows,rec(id:=records[i].id,generators:=PTPerms(U,degree),conjugator:=List([1..degree],j->j^c)));
  od;
  PTRequire(Set(used)=[1..Length(records)],"every committed literal action reached");return rows;
end;;

PTConstructions:=function(actions)
  local result;
  result:=rec(paired8:=PTBindConstruction(actions,"paired8",PTConstructEight(actions)),
    two_affine16:=PTBindConstruction(actions,"two_affine16",PTConstructTwoAffine()),
    zero16:=PTBindConstruction(actions,"zero16",PTConstructZero()));
  Print("PASS PAIR TOP CONSTRUCTIONS: 24 outer-eight; 15 two-affine; 29 zero-ternary classes\n");
  return result;
end;;

PTCheckConstructionWitnesses:=function(actions,data)
  local family,records,entry,a,c,U;
  for family in ["paired8","zero16","two_affine16"] do
    records:=Filtered(actions,a->a.family=family);
    PTRequire(Length(data.(family))=Length(records) and
      Set(List(data.(family),x->x.id))=Set(List(records,x->x.id)),"exact construction witness domain");
    for entry in data.(family) do
      a:=First(records,a->a.id=entry.id);U:=PTGroup(entry.generators);c:=PermList(entry.conjugator);
      PTRequire(U^c=PTGroup(a.generators),"retained literal construction transporter");
    od;
  od;
  Print("PASS PAIR TOP CONSTRUCTION WITNESSES: 68 actual permutation transporters\n");
end;;
