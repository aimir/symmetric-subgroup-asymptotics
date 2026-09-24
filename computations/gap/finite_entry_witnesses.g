# Literal local witnesses for the complete finite binary-entry menu.
# This file performs no catalogue scan and writes no files when loaded.
# API: FEWSetBaseAlphabet(records); FEWSetCharts(d16,d8);
# ctx:=FEWPrepare(U,w); entry:=FEWExport(ctx,N); FEWCheck(U,N,entry);
# Map image rows always follow the exact GeneratorsOfGroup(U) order.
# Group/cut generators are one-based image lists on the ORIGINAL action.
# Each entry retains its own literal normal; quotient cache IDs are never
# evidence consumed by FEWCheck. A pair frame reconstructs the actual top.
# Each transport word retains P itself, not the product of its projections.
# Catalogue-dependent functions are producers only. FEWCheck and
# FEWCheckBaseAlphabet use literal groups, maps and GAP algebra algorithms.

FEWRequire:=function(ok,msg)
 if not ok then Error(Concatenation("finite entry witness: ",msg));fi;
end;;
FEWRows:=function(gs,w) return List(gs,g->ListPerm(g,w));end;;
FEWPerms:=function(rows,w)
 FEWRequire(IsInt(w) and w>=0 and IsList(rows) and ForAll(rows,r->IsList(r) and Length(r)=w
   and Set(r)=[1..w]),"invalid literal permutation rows");
 return List(rows,PermList);
end;;
FEWGroup:=function(rows,w)
 local gs;gs:=FEWPerms(rows,w);
 if Length(gs)=0 then return Group(());fi;
 return Group(gs);
end;;
FEWGens:=function(G,w) return FEWRows(SmallGeneratingSet(G),w);end;;
FEWMap:=function(A,gs,rows,v)
 local ims,R,f;
 FEWRequire(Length(gs)=Length(rows),"map image count");
 ims:=FEWPerms(rows,v);R:=Group(Concatenation(ims,[()]));
 f:=GroupHomomorphismByImages(A,R,gs,ims);
 FEWRequire(f<>fail and IsGroupHomomorphism(f) and IsSurjective(f),"actual onto map");
 return f;
end;;
FEWLog2:=function(n)
 local d;FEWRequire(IsInt(n) and n>0,"positive binary order");
 d:=LogInt(n,2);FEWRequire(2^d=n,"order is a power of two");return d;
end;;
FEWCoverCache:=[];;
FEWCover:=function(B)
 local id,pos,item,f,iso,moved,rename;
 if Size(B)=1 then
   f:=GroupHomomorphismByImages(B,Group(()),GeneratorsOfGroup(B),List(GeneratorsOfGroup(B),x->()));
   return rec(map:=f,degree:=0);
 fi;
 id:=IdGroup(B);pos:=PositionProperty(FEWCoverCache,x->x.id=id);
 if pos=fail then
   f:=MinimalFaithfulPermutationRepresentation(B);
   moved:=MovedPoints(Image(f));
   rename:=ActionHomomorphism(Image(f),moved,OnPoints);
   f:=CompositionMapping(rename,f);
   FEWRequire(IsInjective(f) and Size(Image(f))=Size(B),"faithful producer cover");
   item:=rec(id:=id,source:=B,map:=f,degree:=Length(moved));Add(FEWCoverCache,item);
 else
   item:=FEWCoverCache[pos];iso:=IsomorphismGroups(B,item.source);
   FEWRequire(iso<>fail and IsBijective(iso),"actual cached-cover transporter");
   f:=CompositionMapping(item.map,iso);
 fi;
 FEWRequire(IsInjective(f) and NrMovedPoints(Image(f))=item.degree,"transported faithful cover");
 return rec(map:=f,degree:=item.degree);
end;;

# The base alphabet is defined by the supplied literal actions, not by their
# catalogue names. All normalizers are recomputed by the checker.
FEWBaseRecords:=[];;FEWBaseGroups:=[];;
FEWCheckBaseAlphabet:=fail;;FEWCheck:=fail;;
FEWSetBaseAlphabet:=function(records)
 FEWBaseRecords:=records;
 FEWBaseGroups:=List(records,e->FEWGroup(e.generators,e.degree));
end;;
FEWBuildBaseAlphabet:=function()
 local specs,out,s,U,Z,entry;
 specs:=[[2,1,"critical"],[4,2,"critical"],[4,3,"critical"],
 [8,22,"critical"],[4,1,"cyclic4"],
 [8,18,"carrier"],[8,26,"carrier"],[8,27,"carrier"],
 [8,28,"carrier"],[8,29,"carrier"],[8,31,"carrier"],[8,35,"carrier"],
 [16,1082,"carrier"],[16,1083,"carrier"],[16,1084,"carrier"],
 [16,1332,"carrier"],[16,1547,"carrier"]];out:=[];
 for s in specs do
   U:=TransitiveGroup(s[1],s[2]);Z:=Normalizer(SymmetricGroup(s[1]),U);
   entry:=rec(degree:=s[1],role:=s[3],catalogue_locator:=[s[1],s[2]],
      generators:=FEWGens(U,s[1]),order:=Size(U),
      normalizer_generators:=FEWGens(Z,s[1]),normalizer_order:=Size(Z));
   Add(out,entry);
 od;
 FEWCheckBaseAlphabet(out);FEWSetBaseAlphabet(out);return out;
end;;
FEWCheckBaseAlphabet:=function(records)
 local i,j,e,U,Z,critical,carriers,c4,q8,q16,zeros;
 FEWRequire(Length(records)=17,"seventeen literal base colours");
 critical:=[];carriers:=[];c4:=[];q8:=0;q16:=0;
 for i in [1..Length(records)] do
   e:=records[i];U:=FEWGroup(e.generators,e.degree);
   FEWRequire(e.degree in [2,4,8,16] and IsTransitive(U,[1..e.degree]),"base action transitive");
   FEWLog2(Size(U));FEWRequire(Size(U)=e.order,"base order");
   Z:=FEWGroup(e.normalizer_generators,e.degree);
   FEWRequire(Z=Normalizer(SymmetricGroup(e.degree),U) and Size(Z)=e.normalizer_order,"complete literal symmetric normalizer");
   for j in [1..i-1] do
     if records[j].degree=e.degree then
       FEWRequire(not IsConjugate(SymmetricGroup(e.degree),U,FEWGroup(records[j].generators,e.degree)),"distinct base action colours");
     fi;
   od;
   if e.role="critical" then Add(critical,i);
   elif e.role="cyclic4" then Add(c4,i);FEWRequire(e.degree=4 and IsCyclic(U) and Size(U)=4,"regular C4 colour");
   elif e.role="carrier" then
     Add(carriers,i);FEWRequire(e.degree in [8,16] and Size(U)<=2^(7*e.degree/8),"carrier order budget");
     if e.degree=8 then q8:=q8+1/e.normalizer_order;else q16:=q16+1/e.normalizer_order;fi;
   else Error("finite entry witness: unknown base role");fi;
 od;
 FEWRequire(Length(critical)=4 and Length(c4)=1 and Length(carriers)=12,"base role counts");
 FEWRequire(List(critical,i->records[i].degree)=[2,4,4,8]
    and List(critical,i->records[i].normalizer_order)=[2,24,8,384],"critical degrees and action weights");
 U:=FEWGroup(records[critical[1]].generators,2);FEWRequire(Size(U)=2,"critical C2");
 U:=FEWGroup(records[critical[2]].generators,4);FEWRequire(Size(U)=4 and IsElementaryAbelian(U),"critical regular V4");
 U:=FEWGroup(records[critical[3]].generators,4);FEWRequire(Size(U)=8 and Exponent(U)=4 and not IsAbelian(U),"critical natural D8");
 U:=FEWGroup(records[critical[4]].generators,8);
 zeros:=Number(Elements(U),x->x^2=One(U));
 FEWRequire(Size(U)=32 and Size(Centre(U))=2 and DerivedSubgroup(U)=Centre(U)
   and FrattiniSubgroup(U)=Centre(U) and zeros=20,"critical extraspecial plus type");
 FEWRequire(Length(Filtered(carriers,i->records[i].degree=8))=7
   and Length(Filtered(carriers,i->records[i].degree=16))=5
   and q8=3/64 and q16=65/688128,"exact carrier profile weights");
 return true;
end;;
FEWBaseMatch:=function(U,w)
 local i;
 for i in [1..Length(FEWBaseGroups)] do
   if FEWBaseRecords[i].degree=w and Size(FEWBaseGroups[i])=Size(U)
      and IsConjugate(SymmetricGroup(w),U,FEWBaseGroups[i]) then return i;fi;
 od;
 return fail;
end;;

FEWCharts:=[];;
FEWSetCharts:=function(d16,d8)
 local e,U,Q,P,a,b,gs;
 FEWCharts:=[];
 P:=FEWGroup(d8.cover_generators,8);
 for e in d8.charts do
   U:=FEWGroup(e.source_generators,8);Q:=FEWGroup(e.quotient_generators,16);
   a:=FEWMap(U,FEWPerms(e.source_generators,8),e.alpha_images,16);
   b:=FEWMap(P,FEWPerms(d8.cover_generators,8),e.beta_images,16);
   FEWRequire(Image(a)=Q and Image(b)=Q and Kernel(a)=FEWGroup(e.kernel_generators,8),"literal width8 chart setup");
   Add(FEWCharts,rec(degree:=8,source:=U,target:=Q,quotient_degree:=16,alpha:=a,cover:=P,beta:=b));
 od;
 U:=FEWGroup(d16.source_generators,16);P:=FEWGroup(d16.image_generators,16);
 a:=FEWMap(U,FEWPerms(d16.source_generators,16),d16.image_generators,16);
 FEWRequire(Kernel(a)=FEWGroup(d16.kernel_generators,16),"literal width16 chart setup");
 b:=IdentityMapping(P);
 Add(FEWCharts,rec(degree:=16,source:=U,target:=P,quotient_degree:=16,alpha:=a,cover:=P,beta:=b));
end;;

FEWPrepare:=function(U,w)
 local ctx,j,frame,top,K,kel,gs,comm;
 FEWRequire(w in [2,4,8,16] and IsTransitive(U,[1..w]) and LargestMovedPoint(U)<=w,"literal finite transitive action");
 FEWLog2(Size(U));gs:=GeneratorsOfGroup(U);
 ctx:=rec(group:=U,degree:=w,generators:=gs,frames:=[]);
 for j in [2..w] do
   frame:=Set(Orbit(U,[1,j],OnSets));
   if Length(frame)=w/2 and Length(Set(Concatenation(frame)))=w then
     top:=ActionHomomorphism(U,frame,OnSets);K:=Kernel(top);kel:=Elements(K);
     FEWRequire(IsAbelian(K) and ForAll(kel,x->x^2=One(K)),"elementary pair kernel");
     comm:=List(kel,x->Set(List(gs,g->Position(kel,Comm(x,g)))));
     Add(ctx.frames,rec(frame:=frame,top:=top,K:=K,kel:=kel,comm:=comm,cache:=NewDictionary([1],true)));
   fi;
 od;
 SortBy(ctx.frames,x->Size(x.K));return ctx;
end;;
FEWFixedKey:=function(fr,key)
 local mask;mask:=BlistList([1..Length(fr.kel)],key);
 return Filtered([1..Length(fr.kel)],i->ForAll(fr.comm[i],x->mask[x]));
end;;
FEWCut:=function(fr,M)
 local key,data,sk,t,ell,S,q,C,C0,ck,z,c,r,best;
 key:=Set(List(Elements(M),x->Position(fr.kel,x)));
 data:=LookupDictionary(fr.cache,key);if data<>fail then return data;fi;
 sk:=FEWFixedKey(fr,key);t:=FEWLog2(Length(sk)/Length(key));
 ell:=FEWLog2(Length(FEWFixedKey(fr,sk))/Length(sk));
 S:=Subgroup(fr.K,fr.kel{sk});q:=NaturalHomomorphismByNormalSubgroup(S,M);best:=fail;
 for C in AllSubgroups(Image(q)) do
   C0:=PreImage(q,C);ck:=Set(List(Elements(C0),x->Position(fr.kel,x)));
   z:=FEWFixedKey(fr,ck);c:=FEWLog2(Size(C));r:=FEWLog2(Length(z)/Length(ck));
   if best=fail or 2*c+4*r<best.cost then best:=rec(lift:=C0,c:=c,r:=r,cost:=2*c+4*r);fi;
 od;
 data:=rec(M:=M,t:=t,ell:=ell,dimA:=FEWLog2(Size(fr.K)/Size(M)),cut:=best);
 AddDictionary(fr.cache,key,data);return data;
end;;

FEWTransport:=function(ctx,N)
 local chart,p,a,rows,orbs,word,o,image,index,covergs;
 for chart in FEWCharts do
   if chart.degree=ctx.degree and Size(chart.source)=Size(ctx.group) then
     p:=RepresentativeAction(SymmetricGroup(ctx.degree),ctx.group,chart.source);
     if p<>fail then
       rows:=FEWRows(List(ctx.generators,g->Image(chart.alpha,g^p)),chart.quotient_degree);
       a:=FEWMap(ctx.group,ctx.generators,rows,chart.quotient_degree);
       if Kernel(a)=N then
         orbs:=Orbits(chart.cover,[1..ctx.degree]);word:=[];
         for o in orbs do
           image:=Image(ActionHomomorphism(chart.cover,o,OnPoints));index:=FEWBaseMatch(image,Length(o));
           FEWRequire(index<>fail,"transport projection in literal base alphabet");
           Add(word,rec(block:=o,base_index:=index));
         od;
         covergs:=SmallGeneratingSet(chart.cover);
         return rec(kind:="transport",quotient_degree:=chart.quotient_degree,
           quotient_generators:=FEWGens(chart.target,chart.quotient_degree),
           alpha_images:=rows,cover_generators:=FEWRows(covergs,ctx.degree),
           beta_images:=FEWRows(List(covergs,g->Image(chart.beta,g)),chart.quotient_degree),
           cover_kernel_generators:=FEWGens(Kernel(chart.beta),ctx.degree),word:=word);
       fi;
     fi;
   fi;
 od;
 return fail;
end;;

FEWExport:=function(ctx,N)
 local fr,M,data,topN,q,B,cov,f,e,pi,Q,Z,omega,z,gs;
 FEWRequire(IsSubgroup(ctx.group,N) and IsNormal(ctx.group,N),"literal normal subgroup");e:=fail;
 for fr in ctx.frames do
   M:=Intersection(fr.K,N);data:=FEWCut(fr,M);
   topN:=Image(fr.top,N);q:=NaturalHomomorphismByNormalSubgroup(Image(fr.top),topN);B:=Image(q);
   cov:=FEWCover(B);
   if cov.degree+data.cut.cost<ctx.degree then
     f:=CompositionMapping(cov.map,q,fr.top);
     e:=rec(kind:="pair",frame:=fr.frame,
       top_images:=FEWRows(List(ctx.generators,g->Image(fr.top,g)),ctx.degree/2),
       kernel_generators:=FEWGens(fr.K,ctx.degree),
       intersection_generators:=FEWGens(M,ctx.degree),cut_lift_generators:=FEWGens(data.cut.lift,ctx.degree),
       dimA:=data.dimA,t:=data.t,ell:=data.ell,c:=data.cut.c,r:=data.cut.r,
       cover_degree:=cov.degree,cover_images:=FEWRows(List(ctx.generators,g->Image(f,g)),cov.degree),
       gap:=ctx.degree-cov.degree-data.cut.cost);break;
   fi;
 od;
 if e=fail then
   pi:=NaturalHomomorphismByNormalSubgroup(ctx.group,N);Q:=Image(pi);Z:=Centre(Q);
   omega:=Subgroup(Z,Filtered(Elements(Z),x->x^2=One(Z)));z:=FEWLog2(Size(omega));
   if 38^(8*z)<2^ctx.degree*25^(8*z) then
     e:=rec(kind:="character",quotient_order:=Size(Q),z:=z,
       centre_lift_generators:=FEWRows(List(SmallGeneratingSet(Z),x->PreImagesRepresentative(pi,x)),ctx.degree),
       omega_lift_generators:=FEWRows(List(SmallGeneratingSet(omega),x->PreImagesRepresentative(pi,x)),ctx.degree));
   elif Size(Q)<=128 then
     cov:=FEWCover(Q);
     if cov.degree<ctx.degree then
       f:=CompositionMapping(cov.map,pi);
       e:=rec(kind:="direct",cover_degree:=cov.degree,
          cover_images:=FEWRows(List(ctx.generators,g->Image(f,g)),cov.degree),gap:=ctx.degree-cov.degree);
     fi;
   fi;
 fi;
 if e=fail then e:=FEWTransport(ctx,N);fi;
 FEWRequire(e<>fail,"no sufficient local witness or literal replacement chart");
 e.normal_generators:=FEWGens(N,ctx.degree);e.normal_order:=Size(N);
 FEWCheck(ctx.group,N,e);return e;
end;;

# Checker caches are keyed by the identical literal source object, ordered
# actual frame, and complete element sets of M and C. They never merge
# quotient maps or normals. Every record still reconstructs its own map and
# checks its kernel against its own KN (or N).
FEWCheckSource:=fail;;FEWCheckFrames:=[];;
FEWCheckerFrame:=function(U,gs,frame)
 local pos,top,K,kel,out;
 if FEWCheckSource=fail or not IsIdenticalObj(FEWCheckSource,U) then
   FEWCheckSource:=U;FEWCheckFrames:=[];
 fi;
 pos:=PositionProperty(FEWCheckFrames,x->x.frame=frame);
 if pos<>fail then return FEWCheckFrames[pos];fi;
 top:=ActionHomomorphism(U,frame,OnSets);K:=Kernel(top);kel:=Elements(K);
 out:=rec(frame:=frame,top:=top,K:=K,kel:=kel,
   comm:=List(kel,x->List(gs,g->Comm(x,g))),cells:=NewDictionary([],true));
 Add(FEWCheckFrames,out);return out;
end;;
FEWCheckerCell:=function(fr,M,C)
 local key,cell,fixed,S,second,ck,r;
 key:=Set(Elements(M));cell:=LookupDictionary(fr.cells,key);
 if cell=fail then
   fixed:=Filtered([1..Length(fr.kel)],i->ForAll(fr.comm[i],x->x in M));
   S:=Subgroup(fr.K,fr.kel{fixed});
   second:=Filtered([1..Length(fr.kel)],i->ForAll(fr.comm[i],x->x in S));
   cell:=rec(t:=FEWLog2(Length(fixed)/Size(M)),
     ell:=FEWLog2(Length(second)/Size(S)),dimA:=FEWLog2(Size(fr.K)/Size(M)),
     cuts:=NewDictionary([],true));AddDictionary(fr.cells,key,cell);
 fi;
 ck:=Set(Elements(C));r:=LookupDictionary(cell.cuts,ck);
 if r=fail then
   r:=FEWLog2(Number(fr.comm,row->ForAll(row,x->x in C))/Size(C));
   AddDictionary(cell.cuts,ck,r);
 fi;
 return rec(t:=cell.t,ell:=cell.ell,dimA:=cell.dimA,r:=r);
end;;

FEWCheck:=function(U,N,e)
 local w,gs,K,M,C,frame,top,T,f,KN,kel,fixed,S,second,c,r,t,ell,pi,Q,Z,omega,
       lifted,olift,P,a,b,word,o,image,index,covered,noncritical,fr,cell;
 w:=LargestMovedPoint(U);gs:=GeneratorsOfGroup(U);
 FEWRequire(w in [2,4,8,16] and IsTransitive(U,[1..w]),"checker source action");
 FEWLog2(Size(U));FEWRequire(IsSubgroup(U,N) and IsNormal(U,N),"checker literal normal");
 FEWRequire(FEWGroup(e.normal_generators,w)=N and e.normal_order=Size(N),"record retains exact normal");
 if e.kind="pair" then
   frame:=e.frame;
   FEWRequire(IsList(frame) and Length(frame)=w/2 and ForAll(frame,x->Length(x)=2 and Set(x)=x)
     and Set(Concatenation(frame))=[1..w],"actual pair partition");
   FEWRequire(ForAll(gs,g->Set(List(frame,o->OnSets(o,g)))=Set(frame)),"pair partition invariant");
   fr:=FEWCheckerFrame(U,gs,frame);top:=fr.top;K:=fr.K;M:=Intersection(K,N);
   FEWRequire(e.top_images=FEWRows(List(gs,g->Image(top,g)),w/2),"literal top map image rows");
   FEWRequire(FEWGroup(e.kernel_generators,w)=K and FEWGroup(e.intersection_generators,w)=M,"actual retained pair section");
   FEWRequire(IsAbelian(K) and ForAll(Elements(K),x->x^2=One(K)),"binary elementary section numerator");
   C:=FEWGroup(e.cut_lift_generators,w);
   FEWRequire(IsSubgroup(K,C) and IsSubgroup(C,M) and IsNormal(U,C),"actual lifted central cut");
   FEWRequire(ForAll(GeneratorsOfGroup(C),x->ForAll(gs,g->Comm(x,g) in M)),"cut central modulo original intersection");
   cell:=FEWCheckerCell(fr,M,C);c:=FEWLog2(Size(C)/Size(M));r:=cell.r;
   FEWRequire(e.dimA=cell.dimA and e.t=cell.t and e.ell=cell.ell and e.c=c and e.r=r,"retained section and cut dimensions");
   f:=FEWMap(U,gs,e.cover_images,e.cover_degree);KN:=ClosureGroup(K,N);
   FEWRequire(Kernel(f)=KN and NrMovedPoints(Image(f))=e.cover_degree,"actual faithful B cover with exact kernel KN");
   FEWRequire(e.gap=w-e.cover_degree-2*c-4*r and e.gap>0,"strict original-width central capacity");
 elif e.kind="direct" then
   f:=FEWMap(U,gs,e.cover_images,e.cover_degree);
   FEWRequire(Kernel(f)=N and NrMovedPoints(Image(f))=e.cover_degree
     and e.gap=w-e.cover_degree and e.gap>0,"strict faithful actual quotient cover");
 elif e.kind="character" then
   pi:=NaturalHomomorphismByNormalSubgroup(U,N);Q:=Image(pi);Z:=Centre(Q);
   lifted:=FEWGroup(e.centre_lift_generators,w);olift:=FEWGroup(e.omega_lift_generators,w);
   FEWRequire(IsSubgroup(U,lifted) and IsSubgroup(U,olift),"literal quotient-centre lifts");
   FEWRequire(Image(pi,lifted)=Z,"whole quotient centre, not a selected subgroup");
   omega:=Subgroup(Z,Filtered(Elements(Z),x->x^2=One(Z)));
   FEWRequire(Image(pi,olift)=omega and e.z=FEWLog2(Size(omega)) and e.quotient_order=Size(Q),"complete central involution rank");
   FEWRequire(38^(8*e.z)<2^w*25^(8*e.z),"exact strict character inequality");
 elif e.kind="transport" then
   Q:=FEWGroup(e.quotient_generators,e.quotient_degree);
   a:=FEWMap(U,gs,e.alpha_images,e.quotient_degree);
   P:=FEWGroup(e.cover_generators,w);
   b:=FEWMap(P,FEWPerms(e.cover_generators,w),e.beta_images,e.quotient_degree);
   FEWRequire(Image(a)=Q and Image(b)=Q and Kernel(a)=N,"both maps onto same actual quotient and original exact axis");
   FEWRequire(Kernel(b)=FEWGroup(e.cover_kernel_generators,w),"replacement exact kernel");
   word:=e.word;covered:=[];noncritical:=0;
   FEWRequire(Set(List(word,x->Set(x.block)))=Set(List(Orbits(P,[1..w]),Set)),"whole physical replacement orbit word");
   for o in word do
     index:=o.base_index;
     FEWRequire(IsInt(index) and index>=1 and index<=Length(FEWBaseGroups),"literal base colour reference");
     image:=Image(ActionHomomorphism(P,o.block,OnPoints));
     FEWRequire(FEWBaseRecords[index].degree=Length(o.block) and IsTransitive(image,[1..Length(o.block)])
       and IsConjugate(SymmetricGroup(Length(o.block)),image,FEWBaseGroups[index]),"full actual projection onto base colour");
     Append(covered,o.block);
     if FEWBaseRecords[index].role<>"critical" then noncritical:=noncritical+Length(o.block);fi;
   od;
   FEWRequire(Set(covered)=[1..w] and Length(covered)=w and NrMovedPoints(P)=w,"equal original physical degree with every coordinate retained");
   FEWRequire(4*noncritical>=w,"positive retained noncritical fraction at least one quarter");
 else Error("finite entry witness: unknown branch");fi;
 return true;
end;;
