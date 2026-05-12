AttachSpec("spec");
SetVerbose("ShimuraCurves", 1);

D := 6;
B := QuaternionAlgebra(D);
O := MaximalOrder(B);
for deg in Divisors(D) do
  tr,mu := HasPolarizedElementOfDegree(O,deg);
  if not tr then continue; end if;
  Ns := [1,2,3,4,6];
  print "deg = ", deg;
  X := SemidirectSystem(O, mu);
  time L6 := Lat(X, 6);
  time L4 := Lat(X, 4);
  subs := L6`subs cat [H : H in L4`subs | H`level eq 4];
  //time subs := GenerateDataForGerbiestSurjectiveH(O,mu,Ns);
  WriteHeaderAndSubgroupsDataToFile(subs, O);
end for;
