# Literal pair-top actions and complete complex-character kernel menus.
# No NormalSubgroups or catalogue call is used by PTCheck.
PTChecks:=0;;
PTRequire:=function(ok,why)
  PTChecks:=PTChecks+1;if not ok then Error(Concatenation("PAIR TOP: ",why));fi;
end;;
PTGroup:=function(rows)
  if Length(rows)=0 then return Group(());fi;
  return Group(List(rows,PermList));
end;;
PTPerms:=function(G,n) return List(GeneratorsOfGroup(G),g->List([1..n],i->i^g));end;;
PTBinaryOrder:=function(n) return n>0 and n=2^LogInt(n,2);end;;
PTJSON:=fail;;
PTJSON:=function(x)
  local ks;
  if IsInt(x) then return String(x);fi;
  if IsStringRep(x) then return Concatenation("\"",x,"\"");fi;
  if IsList(x) then return Concatenation("[",JoinStringsWithSeparator(List(x,PTJSON),","),"]");fi;
  if IsRecord(x) then ks:=SortedList(RecNames(x));
    return Concatenation("{",JoinStringsWithSeparator(List(ks,k->Concatenation(PTJSON(k),":",PTJSON(x.(k)))),","),"}");fi;
  Error("unsupported pair-top data");
end;;

PTStructure:=function(a,T)
  local P,C,parts,pi,S,expected,i,V,localgroup,conj;
  PTRequire(IsTransitive(T,[1..a.degree]) and Size(T)=a.order,"literal degree/order/transitivity");
  PTRequire(not IsPGroup(T),"nonbinary top");
  if a.family="twelve" then
    PTRequire(a.degree=12 and a.original_width=24,"original width24");
    P:=PCore(T,2);C:=PCore(T,3);
    if a.branch="core" then
      S:=T/P;PTRequire(Size(S)=3 or (Size(S)=6 and not IsAbelian(S)),"exact C3/S3 core quotient");
    elif a.branch="ternary" then
      parts:=SortedList(List(Orbits(C,[1..12]),Set));
      PTRequire(IsElementaryAbelian(C) and Size(C)>=9 and SortedList(List(parts,Length))=[3,3,3,3]
        and Size(P)<=2 and PTBinaryOrder(Index(T,C)),"four actual ternary orbits and binary quotient");
      return rec(ternary_blocks:=parts,averaging_rows:=List([1..12],i->Sum(First(parts,b->i in b),j->2^(j-1))));
    elif a.branch="paired" then
      parts:=First(SortedList(List(AllBlocks(T),Set)),b->Length(b)=2);PTRequire(parts<>fail,"actual pair block");
      parts:=SortedList(Orbit(T,Set(parts),OnSets));pi:=ActionHomomorphism(T,parts,OnSets);S:=Image(pi);
      if a.index=195 then expected:=Group((1,2,4),(2,4)(5,6),(1,3)(2,5)(4,6));
      else PTRequire(a.index=236,"paired top index");expected:=Group((1,2,4),(2,4),(1,3)(2,5)(4,6));fi;
      PTRequire(IsConjugate(SymmetricGroup(6),S,expected),"actual S36/S72 quotient representation");
      conj:=RepresentativeAction(SymmetricGroup(6),S,expected);
      return rec(pair_blocks:=parts,top_images:=List(List(a.generators,PermList),g->List([1..6],i->i^Image(pi,g))),
        kernel_generators:=PTPerms(Kernel(pi),12),top_conjugator:=List([1..6],i->i^conj));
    else PTRequire(a.branch="joint","known degree12 branch");fi;
  elif a.family="zero16" then
    P:=PCore(T,2);
    PTRequire(IsTransitive(P,[1..16]) and Index(T,P) in [3,6] and Size(SylowSubgroup(T,3))=3,
      "zero-ternary binary-core hypotheses");
    C:=First(SortedList(Elements(P)),g->ForAll([1..16],i->i^g<>i));
    PTRequire(C<>fail and Length(Orbits(Group(C),[1..16]))<=8,"actual binary-core derangement");
    return rec(derangement:=List([1..16],i->i^C));
  elif a.family="primitive16" then
    V:=Socle(T);PTRequire(IsPrimitive(T,[1..16]) and IsElementaryAbelian(V) and Size(V)=16
      and IsTransitive(V,[1..16]),"original affine primitive16 representation");
  elif a.family="two_affine16" then
    PTRequire(Set(Orbit(T,[1..8],OnSets))=Set([[1..8],[9..16]]),"two actual eight-point blocks");
    localgroup:=Action(Stabilizer(T,[1..8],OnSets),[1..8]);
    PTRequire(IsPrimitive(localgroup,[1..8]) and Size(localgroup) in [56,168,1344],"exact affine local-eight family");
  elif a.family="paired8" then PTRequire(a.degree=8 and a.original_width=32,"original width32 paired branch");
  elif a.family="paired6" then
    if a.index=1 then expected:=Group((1,2,4),(2,4)(5,6),(1,3)(2,5)(4,6));
    else PTRequire(a.index=2,"second paired-six action");expected:=Group((1,2,4),(2,4),(1,3)(2,5)(4,6));fi;
    PTRequire(a.degree=6 and a.original_width=24 and T=expected,"exact six-point module and prefix action");
  else Error("unknown pair-top family");fi;
  return rec();
end;;

# Every normal subgroup is an intersection of irreducible-character kernels,
# by decomposing the faithful regular representation of its quotient.
PTMenu:=function(T)
  local ir,kernels,degrees,c,K,i,states,words,queue,j,N,p;
  ir:=Irr(T);kernels:=[];degrees:=[];
  for c in ir do
    K:=KernelOfCharacter(c);i:=Position(kernels,K);
    if i=fail then Add(kernels,K);Add(degrees,c[1]);
    else degrees[i]:=Minimum(degrees[i],c[1]);fi;
  od;
  states:=[T];words:=[[]];queue:=[1];
  i:=1;while i<=Length(states) do for j in [1..Length(kernels)] do
    N:=Intersection(states[i],kernels[j]);p:=Position(states,N);
    if p=fail then Add(states,N);Add(words,Concatenation(words[i],[j]));Add(queue,Length(states));fi;
  od;i:=i+1;od;
  return rec(kernels:=kernels,degrees:=degrees,normals:=states,words:=words);
end;;

PTProduce:=function(a)
  local T,M,record,i;
  T:=PTGroup(a.generators);M:=PTMenu(T);
  record:=rec(id:=a.id,generators:=a.generators,structure:=PTStructure(a,T),characters:=[],normals:=[]);
  for i in [1..Length(M.kernels)] do
    Add(record.characters,rec(degree:=M.degrees[i],kernel_generators:=PTPerms(M.kernels[i],a.degree)));
  od;
  for i in [1..Length(M.normals)] do
    Add(record.normals,rec(order:=Size(M.normals[i]),generators:=PTPerms(M.normals[i],a.degree),word:=M.words[i]));
  od;
  return record;
end;;

PTCheck:=function(a,record)
  local T,M,ns,ks,c,K,N,i,j,word,meet,cap,extra,P,Q,actual,expected,stored;
  PTRequire(record.id=a.id and record.generators=a.generators,"same action and generator order");
  T:=PTGroup(a.generators);extra:=PTStructure(a,T);
  stored:=ShallowCopy(record.structure);
  if a.family="twelve" and a.branch="paired" then
    if a.index=195 then expected:=Group((1,2,4),(2,4)(5,6),(1,3)(2,5)(4,6));
    else expected:=Group((1,2,4),(2,4),(1,3)(2,5)(4,6));fi;
    PTRequire(PTGroup(stored.top_images)^PermList(stored.top_conjugator)=expected,"actual pair quotient transported to the module action");
    Unbind(extra.top_conjugator);Unbind(stored.top_conjugator);
  fi;
  PTRequire(extra=stored,"literal retained structural maps");
  M:=PTMenu(T);ks:=List(record.characters,c->PTGroup(c.kernel_generators));
  PTRequire(Length(Set(ks))=Length(ks) and Set(ks)=Set(M.kernels),"all distinct irreducible kernels retained");
  for i in [1..Length(ks)] do
    j:=Position(M.kernels,ks[i]);PTRequire(record.characters[i].degree=M.degrees[j],"actual irreducible degree on literal kernel");
  od;
  ns:=List(record.normals,n->PTGroup(n.generators));
  PTRequire(Length(Set(ns))=Length(ns) and Set(ns)=Set(M.normals),"complete distinct normal lattice by character closure");
  cap:=0;
  for i in [1..Length(ns)] do
    N:=ns[i];word:=record.normals[i].word;meet:=T;
    PTRequire(IsNormal(T,N) and Size(N)=record.normals[i].order,"literal normal and exact order");
    for j in word do PTRequire(IsInt(j) and j>=1 and j<=Length(ks),"character index");meet:=Intersection(meet,ks[j]);od;
    PTRequire(meet=N,"exact same-target kernel intersection");
    PTRequire(Length(word)<=a.kappa,"whole-normal prefix cap");cap:=Maximum(cap,Length(word));
    if a.family="paired6" and Length(word)=2 then
      PTRequire(ForAll(word,j->record.characters[j].degree=1 and PTBinaryOrder(Index(T,ks[j]))),
        "two positions are actual binary-primary linear characters");
    fi;
  od;
  Print("PASS PAIR TOP GROUP ",a.id,": ",Length(ns)," normals, prefix ",cap,"\n");
  return Length(ns);
end;;

PTNatural:=function()
  local A,S;
  A:=Group((1,2,3,4,5,6,7,8,9,10,11,12,13,14,15),(14,15,16));
  S:=Group((1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16),(1,2));
  PTRequire(A=AlternatingGroup(16) and S=SymmetricGroup(16),"two actual natural degree16 actions");
  Print("PASS PAIR TOP NATURAL: A16,S16; universal pair-module argument remains mathematical\n");
end;;
