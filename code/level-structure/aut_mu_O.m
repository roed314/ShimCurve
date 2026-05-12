
function Primitive(x)
    c := Eltseq(x);
    d := LCM([Denominator(r) : r in c]);
    n := [Integers()!(d * r) : r in c];
    return x * (d / GCD(n));
end function;

declare attributes AlgQuatOrd:
  aut_by_mu;

intrinsic Aut(O::AlgQuatOrd,mu::AlgQuatElt) -> Map, SeqEnum
  {return Autmu(O), as a map from D_n or C_n to BxmodQx (which is not a group in Magma)}

  if not assigned O`aut_by_mu then
    O`aut_by_mu := AssociativeArray();
  end if;
  if IsDefined(O`aut_by_mu, mu) then
    pair := O`aut_by_mu[mu];
    return pair[1], pair[2];
  end if;

  t0 := Cputime();
  assert IsScalar(mu^2);
  tr,eta:=IsScalar(mu^2);
  disc:=Discriminant(O);
  Rx<x>:=PolynomialRing(Rationals());
  sqeta,c:=SquarefreeFactorization(eta);
  Em<v>:=NumberField(x^2-sqeta);
  //Rm:=Order([1,v]);
  cyclo,Czeta,zeta:=IsCyclotomic(Em);
  //Zzeta:=Integers(Czeta);

  B:=QuaternionAlgebra(O);
  BxmodQx:=QuaternionAlgebraModuloScalars(B);

  if cyclo then
    //sqeta,c:=SquarefreeFactorization(eta);
    assert sqeta in {-1,-3};
    if sqeta eq -1 then
      cyc_order:=4;
      zeta_n := mu/c;
    elif sqeta eq -3 then
      cyc_order:=6;
      zeta_n := ((mu/c)+1)/2;
    end if;
    a:=B!zeta_n+1;
  else
    cyc_order:=2;
    a:=B!mu;
  end if;

  if IsTwisting(O,mu) then
    tr,muchi:=IsTwisting(O,mu);
    b:=B!(muchi[2]);
    if cyclo then
      Dn<w_chi,w_mu>:=DihedralGroup(GrpPC, cyc_order); // FIXME: there will be another generator for D4 and D6 since magma uses prime relative orders
    else
      Dn<w_chi,w_mu>:=Group("C2^2");
    end if;
    Dngens:=Generators(Dn);
    //assert #Dngens eq 2;
    assert Order(Dn.2) eq #Dn/2;
    assert Order(Dn.1) eq 2;
    elts:= [ <Dn.1^k*Dn.2^l, BxmodQx!(Primitive(b^k*a^l))> : l in [0..cyc_order-1], k in [0..1] ];
    grp_map:=map< Dn -> BxmodQx | elts >;
  else
    if cyclo then
      Cn<w_mu>:=CyclicGroup(GrpPC, cyc_order); // FIXME: this will be a problem for C4 and C6
    else
      Cn<w_mu>:=CyclicGroup(GrpPC, 2);
    end if;
    elts:= [ <Cn.1^k,BxmodQx!(Primitive(a^k))> : k in [0..#Cn-1] ];
    grp_map:=map< Cn -> BxmodQx | elts >;
  end if;

  image := [e[2] : e in elts];
  assert MapIsHomomorphism(grp_map : injective:=true);
  vprint ShimuraCurves, 3: "Aut_mu(O)", Cputime() - t0;
  O`aut_by_mu[mu] := <grp_map, image>;
  return grp_map, image;
end intrinsic;


intrinsic Aut(O::AlgQuatOrd,mu::AlgQuatOrdElt) -> Any
  {return Autmu(O). It will be a map from D_n to  where the codomain 
  is Autmu(O)}
  B:=QuaternionAlgebra(O);
  return Aut(O,B!mu);
end intrinsic;
