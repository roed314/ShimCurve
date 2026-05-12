
declare attributes SubgroupLatElt:
  level, // the minimal integer N from which this subgroup can be pulled back
  X,
  N, // the actual value of N where this subgroup is defined
  index,
  genus,
  shimura_label,
  abstract_label,
  sigma,
  genus,
  H1plusquo,
  i_at_level, // This lattice element may be stored modulo N, where N is a multiple of the level.  In this case, we want to remember which lattice element modulo the level corresponds to this one
  Enh;

declare attributes SubgroupLat:
  LowerLevels;
  // Subgroup lattices, as an associative array indexed by N.
  // Lats[N] only contains subgroups with surjective norm (and currently only the gerbiest ones),
  // but there will be overlap since subgroups of level dividing N will be included (in order to get the containment relations correct)

intrinsic ShimuraLat(G::LMFDBGrp) -> SubgroupLat
{}
    L := New(SubgroupLat);
    L`Grp := G;
    L`outer_equivalence := false; // We want subgroups up to conjugacy, not up to automorphism
    L`inclusions_known := true; // We want to compute inclusion relations
    L`index_bound := 0; // Even though we are restricting subgroups, it's not correctly modeled by an index bound
    // NOTE: you need to set L`subs externally
    return L;
end intrinsic;

intrinsic ShimuraLatElement(L::SubgroupLat, H::Grp, X::AlgQuatEnhSys, level::RngIntElt, N::RngIntElt : i:=false, normalizer:=false, centralizer:=false, normal:=0, normal_closure:=false, gens:=false, subgroup_count:=false, standard:=false, recurse:=0, elt_up:=false, phi_factor:=1) -> SubgroupLatElt
{}
    x := SubgroupLatElement(L, H : i:=i, normalizer:=normalizer, centralizer:=centralizer, normal:=normal, normal_closure:=normal_closure, gens:=gens, subgroup_count:=subgroup_count, standard:=standard, recurse:=recurse);
    x`X := X;
    x`N := N;
    x`Enh := X`Enh[N];
    x`level := level;
    if Type(elt_up) eq BoolElt then
        x`index := #(x`Lat`Grp`MagmaGrp) div (#H * phi_factor);
        x`genus := EnhancedGenus(RamificationData(x));
    else
        x`index := elt_up`index;
        x`genus := elt_up`genus;
        x`shimura_label := elt_up`shimura_label;
        x`abstract_label := elt_up`abstract_label;
        x`i_at_level := elt_up`i;
    end if;
    return x;
end intrinsic;

intrinsic psl2label(x::SubgroupLatElt) -> MonStgElt
{}
    X := x`X;
    N := x`N;
    G1 := G1Perm(X, N);
    L1 := Lat1(X, N);
    j := SubgroupIdentify(L1, x`subgroup meet G1);
    return L1`subs[j]`shimura_label;
end intrinsic;

intrinsic scalar_label(x::SubgroupLatElt) -> MonStgElt
{}
    X := x`X;
    N := x`N;
    G1 := G1Perm(X, N);
    x1 := x`subgroup meet G1;
    scalar_index := Index(x`subgroup, x1);
    // TODO: Fix the trailing 1
    return Sprintf("%o.%o.1", x`level, scalar_index);
end intrinsic;

// This should work for small groups
function GroupLabel(grp)
    if CanIdentifyGroup(#grp) then
        a, b := Explode(IdentifyGroup(grp));
        return Sprintf("%o.%o", a, b);
    end if;
    // For now, we give up.
    return "\\N";
end function;

function getDeterminantImage(H, O, Ahom)
    N := Modulus(BaseRing(H));
    gens := [H.i : i in [1..Ngens(H)]];
    ONparts := [GL4ToPair(h, O, Ahom)[2] : h in gens];
    return sub<GL(1, Integers(N)) | [[[Norm(x)]] : x in ONparts]>;
end function;

function aaa(L, key) // {key: L} in Python
    aa := AssociativeArray(); aa[key] := L; return aa;
end function;

function SortGClass(L)
    ans := [];
    Lat := L[1]`Lat;
    f := func<x|Sort([Lat`subs[y]`shimura_pieces : y in Keys(x, "overs")])>;
    by_supergroups := IndexFibers(L, f);
    for supers in Sort([k : k in Keys(by_supergroups)]) do
        subs := by_supergroups[supers];
        if #subs gt 1 then
            sorter := [sort_key(s, false) : s in subs];
            ParallelSort(~sorter, ~subs);
        end if;
        ans cat:= subs;
    end for;
    return ans;
end function;

intrinsic ComputeLevelsLabels(Lat::SubgroupLat, level::RngIntElt : naive:=false)
{}
    this_level := [H : H in Lat`subs | H`level eq level];
    if #this_level gt 0 then
        X := this_level[1]`X;
        N := this_level[1]`N;
        reduction := Transfer(X, N, level);
    end if;
    by_ig := IndexFibers(this_level, func<x|<x`level, x`index, x`genus>>);
    for ig -> Hs in by_ig do
        if #Hs eq 1 then
            by_gassman := aaa(Hs, 0);
        else
            gcodes := {@ Get(x, "gassman_vec") : x in Hs @};
            Sort(~gcodes);
            by_gassman := IndexFibers(Hs, func<x|Index(gcodes, Get(x, "gassman_vec"))-1>);
        end if;
        for gcode -> gsubs in by_gassman do
            if #gsubs eq 1 or naive then
                by_gnum := gsubs;
            else
                by_gnum := SortGClass(gsubs, false);
            end if;
            for gnum in [1..#by_gnum] do
                H := by_gnum[gnum];
                H`shimura_label := <Sprintf("%o.%o.%o.%o.%o", H`level, H`index, H`genus, CremonaCode(gcode), gnum), gcode, gnum>;
                H`abstract_label := GroupLabel((H`subgroup) @ reduction);
            end for;
        end for;
    end for;
end intrinsic;

intrinsic H1plusquo(H::GrpMat, Enh::AlgQuatEnh) -> GrpPerm
{}
    // Note that this version doesn't cache; the one below does
    G1plus := G1plus(Enh);
    KG := NormalizerKernelGL4(Enh);
    Gmap := G1plusmodKGmap(Enh);

    H1plus := sub< G1plus | H meet G1plus >;
    //H1plusgens := [H1plus.i : i in [1..Ngens(H1plus)]];
    H1plusKG := sub< G1plus | H1plus, KG >;
    H1plusKGmodKG := quo< H1plusKG | KG >;

    H1plusquo := Gmap(H1plus);
    //if not IsIsomorphic(H1plusquo, H1plusKGmodKG) then
    //    Error("This should not happen, something is not right - maybe this subgroup is not coarsest?");
    //end if;
    return H1plusquo;
end intrinsic;

intrinsic H1plusquo(H::SubgroupLatElt) -> GrpPerm
{}
    if not assigned H`H1plusquo then
        X := H`X;
        N := H`N;
        phi := PermHom(X, N);
        H`H1plusquo := H1plusquo(H`subgroup @@ phi, H`Enh);
    end if;
    return H`H1plusquo;
end intrinsic;

intrinsic FuchsianIndex(H::SubgroupLatElt) -> RngIntElt
{Returns the index of H as a fuchsian group acting on the upper half plane.}

    return #G1plusmodKG(H`Enh) / #H1plusquo(H);
end intrinsic;

function RamData(H, Enh)
    G1KG := G1plusmodKG(Enh);
    Gmap := G1plusmodKGmap(Enh);
    ells := EllipticElementsGL4(Enh);
    if Type(H) eq SubgroupLatElt then
        Hpq := H1plusquo(H);
    else
        Hpq := H1plusquo(H, Enh);
    end if;
    T := CosetTable(G1KG, Hpq);
    piH := CosetTableToRepresentation(G1KG, T);

    sigma := [ piH(Gmap(v)) : v in ells ];
    assert &*(sigma) eq Id(Parent(sigma[1]));
    return sigma;
end function;

intrinsic RamificationData(H::SubgroupLatElt) -> SeqEnum[GrpPermElt]
{return the genus of the Shimura curve corresponding to H.}
    if not assigned H`sigma then
        H`sigma := RamData(H, H`Enh);
    end if;
    return H`sigma;
end intrinsic;

intrinsic RamificationData(H::GrpMat, Enh::AlgQuatEnh) -> SeqEnum[GrpPermElt]
{return the genus of the Shimura curve corresponding to H.}
    return RamData(H, Enh);
end intrinsic;

GP_SHIM_RF := recformat< level : Integers(),
			 subgroup,
			 genus,
			 order,
			 index,
			 fuchsian_index,
			 torsion,
			 generators,
			 is_split,
			 galEnd,
			 autmuO_norms,
			 ram_data_elts,
			 discB,
			 discO,
			 deg_mu,
			 order_label,
			 mu_label,
			 label,
			 coarse_label,
			 Glabel,
			 nu2,
			 nu3,
			 nu4,
			 nu6,
			 coarse_class,
			 coarse_class_num,
			 coarse_num,
			 coarse_index,
			 fine_label,
			 gerbiness,
                         aut_gerbiness,
			 is_coarse,
			 psl2label,
                         scalar_label
		       >;

// Minimal record shape for createRecord (needs subgroup + order only).
SUBMEET_RF := recformat<subgroup : GrpMat, order : Integers()>;

function createRecord(H, X)
    s := rec< GP_SHIM_RF | >;
    N := H`N;
    phi := PermHom(X, N);
    Hgp := (H`subgroup) @@ phi;
    order := H`order;
    Enh := H`Enh; // Set in ComputeLevelsLabels
    mu := Enh`mu;
    Ahom := AtoGL4(Enh);
    homtoB := AtoBx(Enh);
    G := GL4sub(Enh);
    KG := NormalizerKernelGL4(Enh);
    O := Enh`quaternionorder;
    AutFull := Aut(O,mu);
    Henhgens := [GL4ToPair(Hgp.i, O, Ahom) : i in [1..Ngens(Hgp)]];
    aut_mu_norms := [Abs(SquarefreeFactorization(Integers()!Norm(homtoB(pair[1])`element))) : pair in Henhgens];

    s`subgroup:=Hgp;
    s`level := H`level;
    s`genus:=H`genus;
    s`order:=order;
    s`index:=Order(G) div order;
    s`coarse_index := s`index;
    s`fuchsian_index:=FuchsianIndex(H);
    s`gerbiness:=#KG;
    s`aut_gerbiness:=#{GL4ToPair(x, O, Ahom)[1] : x in KG};
    s`torsion:=PrimaryAbelianInvariants(FixedSubspace(Hgp));
    s`Glabel := H`abstract_label;
    s`galEnd:=GroupLabel(Domain(Ahom));
    s`autmuO_norms:=aut_mu_norms;
    s`is_split:=(order eq #(Hgp meet Image(Ahom)) * #(Hgp meet ONx(Enh)));
    s`generators:=[<homtoB(g[1]),[Integers()!x mod H`level : x in Eltseq(g[2])]> : g in Henhgens];
    s`generators:= [g : g in Set(s`generators)];
    s`ram_data_elts:=H`sigma;
    s`discO := Discriminant(O);
    s`discB := Discriminant(Algebra(O));
    if IsMaximal(O) then
	s`order_label := Sprintf("%o", s`discO);
    elif IsEichler(O) then
	s`order_label := Sprintf("%o.%o", s`discB, s`discO);
    else
	Error("Not implemented for non-Eichler orders at the moment");
    end if;
    s`deg_mu := Integers()!Norm(mu) div Discriminant(O);
    s`mu_label := Sprintf("%o.%o", s`order_label, s`deg_mu);
    s`coarse_label := H`shimura_label[1];
    s`coarse_class := CremonaCode(H`shimura_label[2]);
    s`coarse_num := H`shimura_label[3];
    s`coarse_class_num := H`shimura_label[2] + 1;
    s`fine_label := s`coarse_label;
    s`label := Sprintf("%o.%o", s`mu_label, s`fine_label);
    s`is_coarse := true;
    s`psl2label := psl2label(H);
    s`scalar_label := scalar_label(H);

    nu := EnhancedEllipticPoints(H`sigma);
    s`nu2 := nu[2];
    s`nu3 := nu[3];
    s`nu4 := nu[4];
    s`nu6 := nu[6];

    // This is testing the genus formula from Gauss-Bonnet, see (39.4.2) in [JV]
    area_term := s`aut_gerbiness * s`fuchsian_index * Area(O) / #Domain(AutFull);
    elliptic_term := 1/2 * &+[Rationals() | nu[e]*(1 - 1/e) : e in [2,3,4,6]];
    assert s`genus eq 1 + area_term - elliptic_term;

    return s;
end function;

function Base26Encode(n)
    strip := "abcdefghijklmnopqrstuvwxyz";
    assert n gt 0;
    x := n - 1;
    s := "";
    repeat
        digit := x mod 26;
        s cat:= strip[digit+1];
        x div:= 26;
    until x eq 0;
    return Reverse(s);
end function;

procedure updateLabels(~subs, G)
    labels := {s`coarse_label : s in subs};
    for label in labels do
	label_subs := [i : i in [1..#subs] | subs[i]`coarse_label eq label];
	perm_chars := [<Eltseq(PermutationCharacter(G,subs[i]`subgroup)),i> : i in label_subs];
	perm_chars_sorted := Sort(perm_chars);
	n := 0;
	idx := 0;
	prev_char := [];
	tiebreaker := 0;
	while idx lt #perm_chars do
	    idx +:= 1;
	    perm_char := perm_chars_sorted[idx][1];
	    if (perm_char ne prev_char) then
		n +:= 1;
		tiebreaker := 0;
	    else
		tiebreaker +:= 1;
	    end if;
	    class := Base26Encode(n);
	    sub_idx := perm_chars_sorted[idx][2];
	    subs[sub_idx]`coarse_label cat:= Sprintf(".%o.%o", class, tiebreaker+1);
	    subs[sub_idx]`coarse_class_num := n;
	    subs[sub_idx]`coarse_class := class;
	    subs[sub_idx]`coarse_num := tiebreaker+1;
	end while;
    end for;
    for i in [1..#subs] do
	subs[i]`label := Sprintf("%o.%o", subs[i]`mu_label, subs[i]`coarse_label);
	subs[i]`fine_label := subs[i]`coarse_label;
    end for;
end procedure;

intrinsic GenerateDataForGerbiestSurjectiveH(O::AlgQuatOrd,mu::AlgQuatElt,Ns::SeqEnum[RngIntElt]) -> SeqEnum[Rec], Assoc
{Returns a list of records, each representing a line to be added to the database gps_shimura_test, together with an updated LatLookup.
If N in Ns, then the every integer m dividing N should be in Ns}

  levels := {N : N in Ns};
  if 2 in Ns and not (6 in Ns) then
    Ns := [6] cat Ns;
  elif Ns eq [1] then
    Ns := [3];
  end if;
  Ns := Reverse(Sort(Ns));
  seen := {};
  records := [];
  X := SemidirectSystem(O, mu);
  for N in Ns do
    print "N =", N;
    if N le 2 then continue; end if;
    L := Lat(X, N);
    L1 := Lat1(X, N);
    print "subs", N, #L;
    Latlevels := {H`level : H in L`subs};
    new_levels := Latlevels diff seen;
    subs := [H : H in L`subs | H`level in new_levels];
    print "#filtered", N, #subs;
    // TODO: Need to fix handling of lower levels, especially with regard to subgroups of G1
    // Also need to set psl2label on the returned records
    t0 := Cputime();
    new_records :=  [createRecord(H, X) : H in subs];

    O1_subs := [H : H in Lat1`subs | H`level in new_levels];

    G := EnhancedImageGL4(X`Enh[N]);
    G1 := EnhancedImageGL4O1(X`Enh[N]);
    ret_O1_subs := [createRecord(H,X) : H in O1_subs];

    for idx->H in new_records do
        H1 := H`subgroup meet G1;
        assert exists(H_O1){H_O1 : H_O1 in ret_O1_subs | IsConjugate(G, H1, H_O1`subgroup)};
        new_records[idx]`psl2label := H_O1`label;
        // checking we are doing the right thing at least once
        if H`label eq "6.1.1.4.0.a.1" then
            assert H_O1`label eq H`label;
        end if;
        scalar_index := Index(H`subgroup, H1);
        // At the moment we are not sure how to label the scalar subgroup, leaving 1 in the end
        new_records[idx]`scalar_label := Sprintf("%o.%o.1", H`level, scalar_index);
    end for;

    records cat:= new_records;
    vprint ShimuraCurves: "createRecord", Cputime() - t0;
    seen join:= Latlevels;
  end for;

  return records;
end intrinsic;

function writeSeqEnum(seq)
    return "{" * Join([Sprint(x) : x in seq], ",") * "}";
end function;

function writeBoolean(b)
    // capitalized for easier regression testing
    return b select "T" else "F";
end function;

function strJoin(char, strings)
    s := "";
    for i->st in strings do
	if (i gt 1) then s cat:=char; end if;
	s cat:= st;
    end for;
    return s;
end function;

/*
List below produced in sage using:

from lmfdb import db
sage: for k in sorted(db.gps_shimura_test.col_type.keys()):
     print('<"%s","%s">,'%(k,db.gps_shimura_test.col_type[k]))

but note that we leave out id and put label first (for update_from_file)
*/
GPS_SHIMURA_FIELDS := [
<"label","text">,
<"Glabel","text">,
<"all_degree1_points_known","boolean">,
<"aut_gerbiness","integer">,
<"autmuO_norms","integer[]">,
<"bad_primes","integer[]">,
<"cm_discriminants","integer[]">,
<"coarse_class","text">,
<"coarse_class_num","integer">,
<"coarse_index","integer">,
<"coarse_label","text">,
<"coarse_num","integer">,
<"conductor","integer[]">,
<"curve_label","text">,
<"deg_mu","integer">,
<"dims","integer[]">,
<"discB","integer">,
<"discO","integer">,
<"fine_label","text">,
<"fine_num","integer">,
<"fuchsian_index","integer">,
<"galEnd","text">,
<"generators","integer[]">,
<"genus","integer">,
<"genus_minus_rank","integer">,
<"gerbiness","integer">,
<"has_obstruction","smallint">,
<"index","integer">,
<"is_coarse","boolean">,
<"is_split","boolean">,
<"lattice_labels","text[]">,
<"lattice_x","integer[]">,
<"level","integer">,
<"level_is_squarefree","boolean">,
<"level_radical","integer">,
<"log_conductor","numeric">,
<"models","smallint">,
<"mu_label","text">,
<"mults","integer[]">,
<"name","text">,
<"newforms","text[]">,
<"nu2","integer">,
<"nu3","integer">,
<"nu4","integer">,
<"nu6","integer">,
<"num_bad_primes","integer">,
<"num_known_degree1_noncm_points","integer">,
<"num_known_degree1_points","integer">,
<"obstructions","integer[]">,
<"order_label","text">,
<"parents","text[]">,
<"parents_conj","integer[]">,
<"pointless","boolean">,
<"power","boolean">,
<"psl2label","text">,
<"q_gonality","integer">,
<"q_gonality_bounds","integer[]">,
<"qbar_gonality","integer">,
<"qbar_gonality_bounds","integer[]">,
<"ram_data_elts","numeric[]">,
<"rank","integer">,
<"reductions","text[]">,
<"scalar_label","text">,
<"simple","boolean">,
<"squarefree","boolean">,
<"torsion","integer[]">,
<"trace_hash","bigint">,
<"traces","integer[]">
];

intrinsic WriteHeaderToFile(file::IO)
{Write the header to a file.}
    fields := [x[1] : x in GPS_SHIMURA_FIELDS];
    types := [x[2] : x in GPS_SHIMURA_FIELDS];

    labels_header := strJoin("|", fields) cat "\n";

    fprintf file, labels_header;

    types_header := strJoin("|", types) cat "\n\n";

    fprintf file, types_header;

    return;
end intrinsic;

intrinsic WriteSubgroupsDataToFile(file::IO, subs::SeqEnum[Rec], O::AlgQuatOrd)
{Write the list of subgroup records to a file, without the header}
    // sorting for consistency
    labels := [H`label : H in subs];
    ParallelSort(~labels, ~subs);
    for s in subs do
      gens_readable:= [ writeSeqEnum(Eltseq(O!g[1]`element) cat Eltseq(O!g[2])) : g in s`generators ];
      perms_readable:=[ EncodePerm(p):  p in s`ram_data_elts];

      bad_primes := PrimeDivisors(s`discO * s`level);

      // TODO: These are naive bounds and should be improved
      if s`genus eq 0 then
          q_gon_bounds := [1, 2];
          qbar_gon_bounds := [1, 1];
      elif s`genus eq 1 then
          q_gon_bounds := [2, 2*s`index];
          qbar_gon_bounds := [2, 2];
      else
          q_gon_bounds := [2, 2*(s`genus - 1)];
          qbar_gon_bounds := [2, (s`genus + 3) div 2];
      end if;
      if q_gon_bounds[1] eq q_gon_bounds[2] then
          q_gon := q_gon_bounds[1];
      else
          q_gon := "\\N";
      end if;
      if qbar_gon_bounds[1] eq qbar_gon_bounds[2] then
          qbar_gon := qbar_gon_bounds[1];
      else
          qbar_gon := "\\N";
      end if;

      s_fields_assoc := AssociativeArray();
      s_fields_assoc["Glabel"] := s`Glabel;
      s_fields_assoc["all_degree1_points_known"] := "F";
      s_fields_assoc["aut_gerbiness"] := s`aut_gerbiness;
      s_fields_assoc["autmuO_norms"] := writeSeqEnum(s`autmuO_norms);
      s_fields_assoc["bad_primes"] := writeSeqEnum(bad_primes);
      s_fields_assoc["cm_discriminants"] := "\\N";
      s_fields_assoc["coarse_class"] := s`coarse_class;
      s_fields_assoc["coarse_class_num"] := s`coarse_class_num;
      s_fields_assoc["coarse_index"] := s`coarse_index;
      s_fields_assoc["coarse_label"] := s`coarse_label;
      s_fields_assoc["coarse_num"] := s`coarse_num;
      s_fields_assoc["conductor"] := "\\N";
      s_fields_assoc["curve_label"] := "\\N";
      s_fields_assoc["deg_mu"] := s`deg_mu;
      s_fields_assoc["dims"] := "\\N";
      s_fields_assoc["discB"] := s`discB;
      s_fields_assoc["discO"] := s`discO;
      s_fields_assoc["fine_label"] := s`fine_label;
      s_fields_assoc["fine_num"] := "\\N";
      s_fields_assoc["fuchsian_index"] := s`fuchsian_index;
      s_fields_assoc["galEnd"] := s`galEnd;
      s_fields_assoc["generators"] := writeSeqEnum(gens_readable);
      s_fields_assoc["genus"] := s`genus;
      s_fields_assoc["genus_minus_rank"] := "\\N";
      s_fields_assoc["gerbiness"] := s`gerbiness;
      s_fields_assoc["has_obstruction"] := "\\N";
      s_fields_assoc["index"] := s`index;
      s_fields_assoc["is_coarse"] := writeBoolean(s`is_coarse);
      s_fields_assoc["is_split"] := writeBoolean(s`is_split);
      s_fields_assoc["label"] := s`label;
      s_fields_assoc["lattice_labels"] := "\\N";
      s_fields_assoc["lattice_x"] := "\\N";
      s_fields_assoc["level"] := s`level;
      s_fields_assoc["level_is_squarefree"] := writeBoolean(IsSquarefree(s`level));
      s_fields_assoc["level_radical"] := &*PrimeDivisors(s`level);
      s_fields_assoc["log_conductor"] := "\\N";
      s_fields_assoc["models"] := "\\N";
      s_fields_assoc["mu_label"] := s`mu_label;
      s_fields_assoc["mults"] := "\\N";
      s_fields_assoc["name"] := "\\N";
      s_fields_assoc["newforms"] := "\\N";
      s_fields_assoc["nu2"] := s`nu2;
      s_fields_assoc["nu3"] := s`nu3;
      s_fields_assoc["nu4"] := s`nu4;
      s_fields_assoc["nu6"] := s`nu6;
      s_fields_assoc["num_bad_primes"] := #bad_primes;
      s_fields_assoc["num_known_degree1_noncm_points"] := "\\N";
      s_fields_assoc["num_known_degree1_points"] := "\\N";
      s_fields_assoc["obstructions"] := "\\N";
      s_fields_assoc["order_label"] := s`order_label;
      s_fields_assoc["parents"] := "{}";
      s_fields_assoc["parents_conj"] := "\\N";
      s_fields_assoc["pointless"] := "\\N";
      s_fields_assoc["power"] := "\\N";
      s_fields_assoc["psl2label"] := s`psl2label;
      s_fields_assoc["q_gonality"] := q_gon;
      s_fields_assoc["q_gonality_bounds"] := writeSeqEnum(q_gon_bounds);
      s_fields_assoc["qbar_gonality"] := qbar_gon;
      s_fields_assoc["qbar_gonality_bounds"] := writeSeqEnum(qbar_gon_bounds);
      s_fields_assoc["ram_data_elts"] := writeSeqEnum(perms_readable);
      s_fields_assoc["rank"] := "\\N";
      s_fields_assoc["reductions"] := "\\N";
      s_fields_assoc["scalar_label"] := s`scalar_label;
      s_fields_assoc["simple"] := "\\N";
      s_fields_assoc["squarefree"] := "\\N";
      s_fields_assoc["torsion"] := writeSeqEnum(s`torsion);
      s_fields_assoc["trace_hash"] := "\\N";
      s_fields_assoc["traces"] := "\\N";

      s_fields := [* s_fields_assoc[fld[1]] : fld in GPS_SHIMURA_FIELDS *];

      assert #s_fields eq 68;
      fprintf file, strJoin("|", [Sprintf("%o", f) : f in s_fields]) cat "\n";
    end for;
    return;
end intrinsic;

intrinsic WriteHeaderAndSubgroupsDataToFile(subs::SeqEnum[Rec], O::AlgQuatOrd)
{Write the list of subgroup records to a file, together with the header.}
    assert #subs gt 0;
    filename:=Sprintf("data/genera-tables/genera-D%o-deg%o.m",subs[1]`discO,subs[1]`deg_mu);
    file := Open(filename, "w");
    WriteHeaderToFile(file);
    WriteSubgroupsDataToFile(file, subs, O);
end intrinsic;

intrinsic WriteHeaderAndSubgroupsDataToFile(subs::SeqEnum[SubgroupLatElt], X::AlgQuatEnhSys)
{}
    O := X`quaternionorder;
    WriteHeaderAndSubgroupsDataToFile([createRecord(H, X) : H in subs], O);
end intrinsic;


intrinsic EnhancedPermutationRepresentationMod2(O::AlgQuatOrd,mu::AlgQuatElt) -> Any
  {return the permutation representation Autmu(O) \ltimes (O/N)^x -> S_n}
  
  Omod2:=quo(O,2);
  Oenh:=EnhancedSemidirectProduct(O : N:=2);

  Omod2_elements := Setseq(Set(Omod2));
  Omod2_units := [ a : a in Omod2_elements | IsUnit(a) ];

  autmuO := Aut(O,mu);
  autmuOelts := [ autmuO(x) : x in Domain(autmuO) ];

  enhanced_elements:= [ Oenh!<a,b> : a in autmuOelts, b in Omod2_units ];
  assert #Set(enhanced_elements) eq #enhanced_elements;
  enhanced_elements := Set(enhanced_elements);
  enhanced_elements := SetToIndexedSet(enhanced_elements);

  n:=#enhanced_elements;
  SymX:=Sym(enhanced_elements);
  permrep := map< enhanced_elements -> SymX | g :-> SymX![ g*x : x in enhanced_elements ] >; 

  permrep_elts:= [ permrep(g) : g in enhanced_elements ];
  Gperm:= sub< SymX | permrep_elts >;

  idG := Oenh!<1, [1,0,0,0]>;
  embedG := map< Oenh -> Gperm | g :-> Gperm!permrep(g), p :-> Image(p,idG) >;

  return embedG;
end intrinsic;


intrinsic Print(elt::AlgQuatOrdResElt)
{.}
  printf "%o", elt`element;
end intrinsic;

intrinsic Print(OmodN::AlgQuatOrdRes)
{.}
  printf "Quotient of %o by %o", OmodN`quaternionorder, OmodN`quaternionideal;
end intrinsic;

intrinsic Print(elt::AlgQuatProjElt)
{.}
  printf "%o", elt`element;
end intrinsic;

intrinsic Print(BxmodFx::AlgQuatProj)
{.}
  printf "Quotient by scalars of %o", BxmodFx`quaternionalgebra;
end intrinsic;





