//Witt Vector Computations
load "gt.m";

/*
Find the leading term of f, where leadingterms are expressions for the leading terms of yn, ... y1, x 
in terms of a uniformizer (also denoted x)
n - level of the tower
f polynomial defining cover y^p -y = f
*/
function find_leadingterm(n,f,leadingterms)

	highest := LeadingTerm(Evaluate(f,leadingterms)) ;

	if highest eq 0 then
		assert(f eq 0); //something went wrong. leadingterms?
		return 0,0;
	end if;
	//return the coefficient and the exponent on the highest order term in the local expansion
	// using the last variable for a uniformizer

 
	return Coefficients(highest)[1], Exponents(highest)[n+1];
end function;

/*
Create a monomial of specific order at level
p - characteristic
level - which level to work at
x, ys[1], ... ys[n] : variables defining tower
ds : ramification invariants at at each level
exponent : the order to use
*/
function create_term(p,level,x,ys,ds,exponent)
	term := Parent(ys[level])!1;
	j := level-1;
	remaining := exponent;

	while remaining gt 0 and j gt 0 do
		newexp:= (Integers()!(remaining/p^(level-1-j)) * Modinv(ds[j],p)) mod p ;
		remaining := remaining - newexp * ds[j] * p^(level-1-j);
		term := term * ys[j]^(newexp);
		j := j-1;
	end while;
	
	//if this assertion fails, we haven't been able to produce the required function using this method
	//we can prove it will never fail for basic towers.  Not entirely sure about more general examples
	assert(remaining mod p^(level-1) eq 0);
	
	term := term * x^(Integers()! (remaining/(p^(level-1))));
	
	return term;
end function;

/*
Normalize the level of the ASW Witt tower to be in standard form
assume previous levels already dealt with
returns the standard form for f_level and the leading term in the expansion of y_level above infinity
p : characteristic
n : largest level in tower
ds : ramification invariants at at each level
x, ys[1], ... ys[n] : variables defining tower
f : polynomial for next level
leadingterms: precomputed leading terms for x, ys
level : level working at now
*/
function normalize_ASW_level(p,n,ds,x,ys,f,leadingterms,simplify,level)
	coeff,deg := find_leadingterm(n,f,leadingterms);
	y_mod :=0 ; //keep track of modifications to y_level
	while deg gt ds[level] do
		//the leading term has degree a multiple of p. Kill it off
		new_term := create_term(p,level,x,ys,ds,Integers()!(deg/p));
		
		newcoeff, newdeg := find_leadingterm(n,new_term^p - new_term,leadingterms);
		assert( newdeg eq deg);
		
		new_term := Root(coeff,p) * newcoeff^(-p) * new_term;
		//cancel out the biggest term		
		f:= simplify(f -  (new_term^p - new_term)) ; 
		y_mod := y_mod - new_term;
		old_deg := deg;
		coeff,deg := find_leadingterm(n,f,leadingterms);
		assert ( deg lt old_deg);
	end while;

	assert(deg eq ds[level]);

	return f, Root(coeff,p) * x^deg , y_mod;
end function;

/*Normalize the ASW tower to put it in Madden's standard form
p : characteristic
n : largest level in tower
P : multivariable polynomial ring in x, ys
ds : ramification invariants at at each level
x, ys[1], ... ys[n] : variables defining tower
fs : polynomials defining each extension (not in standard form yet)
*/
function normalize_ASW(p,n,P,ds,x,ys,fs)
	standard_f := [];
    yList := [];
	leadingterms := [0 : j in [1..n]] cat [x];
	
	for level in [1..n] do
		A,g:= quo<P | [ ys[j]^p - ys[j] - standard_f[j] : j in [1..level-1]]>;
		lift := Inverse(g); //g isn't invertible, but this picks a nice section
	
		//write things in standard forms using Artin-Schreier relations
		simplify := function(poly)
			return lift(g(poly));
		end function;
		
		//make a change of variable ys'[level] = ys[level] + y_mod
		//such that fs[level] + y_mod^p - y_mod is in standard form

		new_f,new_u,y_mod :=normalize_ASW_level(p,n,ds,x,ys,fs[level],leadingterms,simplify,level);
        
		Append(~standard_f,new_f);
		
		//update leading terms for next level
		for j in [n+2-level..n+1] do
            leadingterms[j] := Evaluate( leadingterms[j], x,x^p);
		end for;
	

		leadingterms[n+1-level] := new_u;

		//update later ys's based on change of variables ys[level] = ys'[level] - y_mod
		for j in [ level+1..n] do
			base_fsj := fs[j];
			//The simple thing to do would be to evalute as in the next line
			//fs[j] := simplify(Evaluate(fs[j],ys[level],ys[level] - y_mod));
			//But this involves a huge number of monomials.  Need to rewrite to be more efficient using relations 
			//by working on quotient ring
			coeffs := Coefficients(base_fsj,ys[level]);
			
			power := 0;
			accumulated := A!1;
			fsj_alt := A!0;
			
			while power lt # coeffs do
				fsj_alt := fsj_alt + g(coeffs[power+1]) * accumulated;
				accumulated := accumulated * g(ys[level] - y_mod);
				power +:=1;
			end while;
			
			
			//assert( lift(fsj_alt) eq fs[j]);
			fs[j]  := lift(fsj_alt);
		end for;
	end for;

	return standard_f;	
end function;

computeH1 := function(p, dList, n, varList,lift)

    funcBasis := [];
    diffBasis := [];
    funcExp := [];
    diffExp := [];
    counter := 1;
    funcDict := AssociativeArray();
    diffDict := AssociativeArray();
    
    for a := 0 to p^n-1 do
        yList := Intseq(a,p);
        yList := yList cat [0 : i in [1 .. n-#yList]];
        funcYVar := 1;
        diffYVar := 1;

        for i := 2 to n+1 do
            funcYVar := funcYVar * varList[i]^yList[i-1];
            diffYVar := diffYVar * varList[i]^(p-1-yList[i-1]);
        end for;
        
        b := 0;
        for i := 1 to n do
            b := b - dList[i]*yList[i]/p^(i);
        end for;
        
        b := Ceiling(b);

        for j := b to -1 by 1 do
            func := lift((1/varList[1])^(-j)*funcYVar);
            differential := lift(varList[1]^(-1-j)*diffYVar);
            Append(~funcBasis, func);
            Append(~diffBasis, differential);
            funcDict[func] := counter;
            diffDict[differential] := counter;
            counter := counter + 1;
            Append(~funcExp, [j] cat [yList[k] : k in [1 .. n]]);
            Append(~diffExp, [-1-j] cat [p-1-yList[k] : k in [1 .. n]]);
        end for;
    end for;
    
    return funcBasis, diffBasis, funcDict, diffDict, funcExp, diffExp;
end function;

computeH0 := function(p, dList, n, varList,lift)
    basisList := [];
    counter := 1;
    diffDict := AssociativeArray();
    
    for a := 0 to p^n-1 do
        yList := Intseq(a,p);
        yList := yList cat [0 : i in [1 .. n-#yList]];
        yVar := 1;

        for i := 2 to n+1 do
            yVar := yVar * varList[i]^yList[i-1];
        end for;
        
        b := 0;
        for i := 1 to n do
            b := b + p^(n-i)*dList[i]*(p-1-yList[i]);
        end for;
        
        b := b - p^n - 1;
        b := Floor(b/p^n);

        for j := 0 to b do
            differential := varList[1]^j*yVar;
            Append(~basisList, differential);
            diffDict[differential] := counter;
            counter := counter + 1;
        end for;
    end for;

    return basisList, diffDict;;
end function;

computeDifferential := function(f,dys,varList,n)

    if f eq 0 then
        return 0;
    end if;
    monomials := Monomials(f);
    coeff := Coefficients(f);
    differential := monomials[#monomials]*Derivative(coeff[#coeff]);
    
    if n ne 1 then
    
        differential := differential + &+[Derivative(f,varList[i])*dys[i] : i in [2 .. #varList]];
    else
        differential := differential + Derivative(f)*dys[2];

    end if;
    
    return differential;

end function;

applyFrob := function(F, vec, V, p)
    m := Dimension(V);

    newVec := V!([0 : i in [1 .. m]]);
    
    for i in [1 .. m] do
        if vec[i] ne 0 then
            newVec := newVec + vec[i]^p*F[i];
            
        end if;
    end for;

    return newVec;
end function;

computeTrace := function(k1,k2,varList,p)
    t := 0;
    for i in [1 .. p] do
        for j in [1 .. p] do
            t := t + (varList[2]+i-1)^k1*(varList[3]+j-1)^k2; 
        end for;
    end for;

    return t;

end function;

computeH1dR := function(p, r, n, f)
    k := GF(p^r);
    R<x> := FunctionField(k);
    
    //Witt vector computations don't function correctly for n = 1
    if n eq 1 then
		A<a1,b>:= PolynomialRing(k,2);
		as := [a1];
        ap := [a1^p];
		ASW:=[a1^p -a1];
        
	else
	
        A:= PolynomialRing(k,n+1);
        b := A.(n+1);
        as := [];
	
        AssignNames(~A,[ "a" cat IntegerToString(j) : j in [n..1 by -1]] cat ["b"]);
	
        for index in [n..1 by -1] do
            Append(~as,A.index);
        end for;
	
        ap := [as[i]^p : i in [1..n]];
        epols:=etapols(p,n-1); //characteristic p, length n
        ASW:= WittDiff(ap,as : pols:=epols);
    end if;
    
    if n eq 1 then
		P<y1>:= PolynomialRing(R);

        ys := [y1];
	else
	
        P:= PolynomialRing(R,n);
        ys := [];
	
        AssignNames(~P,[ "y" cat IntegerToString(j) : j in [n..1 by -1]]);
        
        for index in [n..1 by -1] do
            Append(~ys,P.index);
        end for;

    end if;
    
    
    //Break up the terms in the polynomial f.
    xs := Eltseq(f);
    
    //Adds up the witt vectors that are the monomials of f.
    v := [A!0 : j in [1 .. n]];
    
    if n ne 1 then
        v[1] := xs[1];
        for i in [1 .. #xs-1] do
            sumTerm := [A!0 : j in [1 .. n]];
            sumTerm[1] := xs[i+1]*b^i;
            v := WittSum(v,sumTerm : pols := epols);
        end for;
    else
        v[1] := Evaluate(f,b);
    end if;

    //Creates functions using Artin-Schreier-Witt theory with yi^p-yi=fs[i]
    fs := [ap[i] - as[i] - ASW[i] + v[i] : i in [1 .. #ASW]];
    
    print("Witt vector calculations done");

    //Computes ramification invariants up to level n of the tower
    d := Degree(f);
    dList := [d];
    if n gt 1 then
        for i := 2 to n do
            Append(~dList, d*(p^(2*i-1)+1)/(p+1));
        end for;
    end if;

    //List of variables in the tower in Madden's standard form
    if n ne 1 then
        new_fs := normalize_ASW(p, n, A, dList, b, as, fs);
    else
        new_fs := fs;
    end if;
    
    x := P!x;
    varList := [x] cat ys;
    
    
    //gs are the functions defining the tower in terms of x,y1,y2,...
    //dys is a list of functions f_i such that dy_i = f_i dx
    gs := [];
    dys := [1,-1*Evaluate(Derivative(new_fs[1],b), Reverse(varList))];

    for i in [1 .. n] do
        newFunc := Evaluate(new_fs[i], Reverse(varList));
        Append(~gs,newFunc);
    end for;
    
    for i in [2 .. n] do
        newFunc := Evaluate(Derivative(-1*new_fs[i],A.(n+1)), Reverse(varList)) + &+[Evaluate(Derivative(-1*new_fs[i], A.j) ,Reverse(varList)) * dys[n-j+2] : j in [n .. n-i+2 by -1]];
        Append(~dys, newFunc);
    end for;

    print("Tower now in standard form");


    A, h := quo<P | [ys[i]^p - ys[i] - gs[i] : i in [1 .. n]]>;
    lift := Inverse(h);

    
    print("Tower constructed");

  
    //Computes genus
    g := 0.5*(d/(p+1)*p^(2*n) - p^n - (p+1+d)/(p+1))+1;
    g := Integers()!g;
    H1, H0, H1Dict, H0Dict, funcExp, diffExp := computeH1(p, dList, n, varList, lift);

    //dRBasis := H1 cat H0;
    
    print("Bases computed");

    pairing := ZeroMatrix(k,2*g);
    for i in [1 .. g] do
        for j in [Max(i+1,g+1) .. 2*g] do

            firstVal := 0;
            if i le g and j gt g then
                if funcExp[i][1] + diffExp[((j-1) mod g) + 1][1] eq -1 then
                    firstVal := (-1)^(n+1);
                    for k in [2 .. n+1] do
                        yFunc := funcExp[i][k];
                        yDiff := diffExp[((j-1) mod g) + 1][k];
                        
                        if yFunc + yDiff ne p-1 and yFunc + yDiff ne 2*p-2 then
                            firstVal := 0;
                        end if;
                    end for;
                end if;
    
            end if;

            pairing[i][j] := firstVal;
            pairing[j][i] := -1*firstVal;
        end for;
    end for; 

    
    /*
    for i in [1 .. g] do
        entry := [(-1)^(n+1) : j in [1 .. g]];
        for j in [1 .. g] do
            if (funcExp[i][1] + diffExp[j][1]) eq -1 then
                for k in [2 .. n+1] do
                    if (funcExp[i][k] + diffExp[j][k]) ne (p-1) and (funcExp[i][k] + diffExp[j][k]) ne (2*p-2) then
                        entry[j] := 0;
                        break;
                    end if;
                end for;
            else
                entry[j] := 0;
            end if;
        end for;
        Append(~pairing, entry);
    end for;

    funcPairing := Matrix(k,pairing);
    diffPairing := Transpose(funcPairing);
    */

    
    FHN := [];
    psi := [];
    print("Pairing Computed");

    B := RingOfIntegers(R);

    for f in H1 do
        frobf := lift(f^p);
        frobDiff := lift(computeDifferential(f^p, dys,varList,n));
        frobTerms := Terms(frobf);
        frobEntry := [k!0 : i in [1..g]];
        diffEntry := [k!0 : i in [1 .. g]];
        for term in frobTerms do
            coeffList := Coefficients(term);
            xTerm := R!coeffList[#coeffList];

            xDegree := Degree(Denominator(xTerm));

            xPolyTerm := B!(xTerm*x^(xDegree));
            coeffList := Coefficients(xPolyTerm);


            monomialList := Monomials(xPolyTerm);
            for i in [1 .. #monomialList] do
                if coeffList[i] ne 0 then
                    dictTerm := monomialList[i]*term/(xTerm* x^xDegree);
                    if i - 1 - xDegree ge 0 then
                        diffTerm := lift(computeDifferential(lift(dictTerm*coeffList[i]), dys, varList,n));

                        for newTerm in Terms(diffTerm) do
                            newCoeffList := Coefficients(newTerm);
                            newXTerm := R!newCoeffList[#newCoeffList];
                            newXDegree := Degree(Denominator(newXTerm));
                            newXPolyTerm := B!(newXTerm*x^newXDegree);
                            newCoeffList := Coefficients(newXPolyTerm);
                            newMonomialList := Monomials(newXPolyTerm);

                            for j in [1 .. #newMonomialList] do
                                if newCoeffList[j] ne 0 then
                                    newDiffTerm := newMonomialList[j]*newTerm/(newXTerm*x^newXDegree);

                                    if IsDefined(H0Dict, newDiffTerm) then
                                        index := H0Dict[newDiffTerm];

                                        diffEntry[index] := diffEntry[index] + newCoeffList[j];
                                    end if;
                                end if;
                            end for;
                        end for;
                    end if;
    
                    if IsDefined(H1Dict,dictTerm) then
                        index := H1Dict[dictTerm];
                        
                        frobEntry[index] := frobEntry[index]+coeffList[i];
    
                    end if;
                end if;
                
            end for;
        
        end for;

        Append(~FHN, frobEntry);
        Append(~psi, diffEntry);
    end for;
    
    print("Frobenius and psi computed on H1 and H0, resp");
    
    F := Matrix(k, FHN);
    psi := Matrix(k, psi);
    A := KernelMatrix(F);

    a := NumberOfRows(A);
    V := VectorSpace(k,Integers()!g);
    X := ExtendBasis(Rows(A),V);
    B := Matrix(X);
    C := Solution(B,Rows(IdentityMatrix(k,Integers()!g)));


    dRF := [];
    for i in [1 .. #C] do
        psiEntry := V!([0 : j in [1 .. g]]);
        frobEntry := V!([0 : j in [1 .. g]]);
        for j in [1 .. g] do
            if C[i][j] ne 0 then
                if j in [1 .. a] then
                    psiEntry := psiEntry + applyFrob(psi, C[i][j]*B[j], V, p);
                else
                    frobEntry := frobEntry + applyFrob(F, C[i][j]*B[j], V, p);
                end if;
            end if;

            
        end for;

        Append(~dRF, Eltseq(frobEntry) cat Eltseq(psiEntry));
    end for;
    print("F on H1dR Computed");
    for i in [1 .. g] do
        Append(~dRF, [0 : i in [1 .. 2*g]]);
    end for;
    dRF := Matrix(k,dRF);

   /* funcV := [];
    diffV := [];
    zeroVec := [k!0 : i in [1 .. g]];
    for i in [1 .. g] do
        vFuncEntry := [k!0 : j in [1 .. g]];
        vDiffEntry := [k!0 : j in [1 .. g]];
        for j in [1 .. g] do
            Ff := dRF[j];

            vFuncEntry[j] := Root(-1*&+[funcPairing[i][a]*Ff[a+g] : a in [1 .. g]],p);
            vDiffEntry[j] := Root(&+[diffPairing[i][a]*Ff[a] : a in [1 .. g]],p);
            
        end for;
        //vFuncEntry := Eltseq(Solution(funcPairing,V!vFuncEntry));
        //vDiffEntry := Eltseq(Solution(diffPairing, V!vDiffEntry));
        vFuncEntry := Eltseq(V!vFuncEntry * diffPairing);
        vDiffEntry := Eltseq(V!vDiffEntry * diffPairing);
        for j in [1 .. g] do
            vFuncEntry[j] := Root(vFuncEntry[j],p);
            vDiffEntry[j] := Root(vDiffEntry[j],p);
        end for;
        Append(~funcV, zeroVec cat vFuncEntry);
        Append(~diffV, zeroVec cat vDiffEntry);
        
        
    end for; */

    
    dRV := pairing*Transpose(dRF)*pairing^(-1);
    
    
    print("V on H1dR Computed");
    //dRV := VerticalJoin(Matrix(k,funcV),Matrix(k,diffV));


    return dRF,dRV;
end function;