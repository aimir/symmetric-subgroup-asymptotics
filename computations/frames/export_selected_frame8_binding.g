# Export one literal eight-frame binding as JSON.
#
# Usage is deliberately selected-row only:
#   FRAME8_SELECTED_ROW=1 FRAME8_SELECTED_OUTPUT=/tmp/frame8-row1.json \
#     gap -q export_selected_frame8_binding.g
#
# The one-based row is an entry of FrameEightBindings, hence also the same
# row of frames8.json.  This producer does not invoke Lean and has no bulk
# mode.  The Python consumer rechecks all emitted permutations and words.

FrameSelectedRequire:=function(ok,msg)
 if not ok then Error(Concatenation("SELECTED FRAME8 EXPORT: ",msg));fi;
end;;

FrameSelectedPermutationRow:=function(g,n)
 return List([1..n],i->i^g);
end;;

FrameSelectedPermutationRows:=function(gs,n)
 return List(gs,g->FrameSelectedPermutationRow(g,n));
end;;

FrameSelectedNestedPermutationRows:=function(rows,n)
 return List(rows,gs->FrameSelectedPermutationRows(gs,n));
end;;

FrameSelectedRun:=function()
 local rawRow,output,row,b,T,H,N,normals,classes,normalGenerators,
       classRepresentatives;
 rawRow:=GetEnv("FRAME8_SELECTED_ROW");
 output:=GetEnv("FRAME8_SELECTED_OUTPUT");
 FrameSelectedRequire(rawRow<>fail and output<>fail,
   "FRAME8_SELECTED_ROW and FRAME8_SELECTED_OUTPUT are mandatory");
 row:=Int(rawRow);
 FrameSelectedRequire(row<>fail and 1<=row and row<=30,
   "selected row must lie in [1,30]");
 Read("bindings8.g");
 FrameSelectedRequire(Length(FrameEightTops)=24 and
   Length(FrameEightBindings)=30,"unexpected binding source shape");
 b:=FrameEightBindings[row];T:=FrameEightTops[b[1]];
 H:=Stabilizer(T,1);N:=b[2];
 FrameSelectedRequire(IsNormal(H,N) and Index(H,N) in [3,6],
   "stored point-stabilizer kernel is invalid");
 normals:=NormalSubgroups(T);
 classes:=ConjugacyClasses(T);
 normalGenerators:=List(normals,K->GeneratorsOfGroup(K));
 classRepresentatives:=List(classes,Representative);
 PrintTo(output,
   "{\"schema\":\"frames8-selected-binding-v1\",",
   "\"bindings_sha256\":\"d5a3ef513faa40a10f666478628f5f23f0a156db58e75d8a7be4068c3c2fa3fa\",",
   "\"row\":",row-1,",",
   "\"top_index\":",b[1]-1,",",
   "\"top_order\":",Size(T),",",
   "\"top_generators\":",String(FrameSelectedPermutationRows(
     GeneratorsOfGroup(T),8)),",",
   "\"normal_generators\":",String(FrameSelectedNestedPermutationRows(
     normalGenerators,8)),",",
   "\"normal_orders\":",String(List(normals,Size)),",",
   "\"class_representatives\":",String(FrameSelectedPermutationRows(
     classRepresentatives,8)),",",
   "\"class_sizes\":",String(List(classes,Size)),",",
   "\"stabilizer_generators\":",String(FrameSelectedPermutationRows(
     b[3],8)),",",
   "\"kernel_generators\":",String(FrameSelectedPermutationRows(
     GeneratorsOfGroup(N),8)),",",
   "\"kernel_order\":",Size(N),",",
   "\"local_images\":",String(FrameSelectedPermutationRows(b[4],3)),",",
   "\"coset_representatives\":",String(FrameSelectedPermutationRows(
     b[5],8)),",",
   "\"induced_generators\":",String(FrameSelectedPermutationRows(
     b[6],32)),",",
   "\"binary_basis\":",String(FrameSelectedPermutationRows(b[7],32)),
   "}\n");
 Print("PASS SELECTED FRAME8 BINDING ROW ",row,"; top ",b[1],
   "; order ",Size(T),"; normals ",Length(normals),
   "; classes ",Length(classes),"\n");
end;;

FrameSelectedRun();;
QUIT;
