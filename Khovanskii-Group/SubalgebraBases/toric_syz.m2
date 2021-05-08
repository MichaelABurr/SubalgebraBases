-- Returns the variables corresponding to the subalgebra generators in the 
-- tensor ring of a subring instance,
    -- subR is any Subring instance.
genVars = method(TypicalValue => Matrix)
genVars(Subring) := subR ->(
    selectInSubring(1, vars subR#"presentation"#"tensorRing")    
    );


-- Subring equality

isSubalg = method(TypicalValue => Boolean)
isSubalg(Subring, Subring) := (A, B) -> (
    (gens A)%B == 0
    );
subalgEquals = method(TypicalValue => Boolean)
subalgEquals(Subring, Subring) := (A, B) ->(
    isSubalg(A, B) and isSubalg(B, A)
    );
Subring == Subring := (A, B) -> (subalgEquals(A,B));

-- converts exponent vector L to a monomial in vars R.
toMonomial = (R, L) ->(
    variableList := flatten entries vars R;
    m := 1;
    for i from 0 to (length L)-1 do(
	m = m*(variableList_i)^(L#i);
	);
    m	  
    );

-- returns the coefficient of the lead monomial of RingElement f.
leadCoef = method(TypicalValue => Thing)
leadCoef(RingElement) := f ->(
    coefficient(leadMonomial f, f)
    );


-- This is subroutine 11.14 of Sturmfels.
-- There are many simillarities between this calculation and the subduction algorithm.
   -- subR is a subring that contains the ideal generated by the 1-row matrix G.
   -- p is an element of subR#"PresRing"#"TensorRing".
intrinsicReduce = method(TypicalValue => RingElement)
intrinsicReduce(Subring, Matrix, RingElement) := (subR, G, p) -> (
    
    pres := subR#"presentation";
    tense := pres#"tensorRing";
    projInc := pres#"sagbiInclusion";

    if subR#"isSAGBI" == false then(
	error "Can only use IntrinsicReduce on a Subring instance that is a Sagbi basis.";
	);
    
    -- This is one way to guarentee that p is actually an element of subR, but it requires
    -- p to be put into normal form beforehand which is an expensive operation. 
    -- TODO: Look into what happens when p isn't an element of subR.
    --if projInc p != p then(
	--error "p must be a polynomial in the generators of subR."
	--);
    --if projInc G != G then(
        --error "G must contain entries that are polynomials in the generators of subR."
        --);
    
    amb := ambient subR;
    fullSub := pres#"fullSubstitution";
    result := p;
    
    -- If the  === comparison is true, it  does not guarentee that will not throw an error.
    if source fullSub === ring p then(
    	result = fullSub p;
    	);    
    if source fullSub === ring G then(
    	G = fullSub G;
    	);
   
    -- This call to sagbi will not take long.
    KA := subring sagbi subring(leadTerm gens subR);
    tenseKA := KA#"presentation"#"tensorRing";
    Q := (leadTerm G)//KA;
    
    -- This is an ideal inside of the _tensor ring_ of KA.
    I := monomialIdeal(Q);

    loopNum := 0;    	
    while true do (
	if loopNum % 100 == 0 and loopNum > 0 then(
	    --print("reduction step:"|toString(loopNum));
	    );	
	badTerms := result // KA;
	badTerms = badTerms-(badTerms%I);
	badTerms = selectInSubring(1, monomials badTerms);		
	
       	if badTerms == 0 then(
	    break;
	    );
	fullSubKA := KA#"presentation"#"fullSubstitution";
	subMap := KA#"presentation"#"substitution";

	tb := fullSubKA max first entries badTerms;	
	assert(coefficient(tb, result) != 0);
	
	pos := position(first entries Q, gen -> (tb//KA)%(monomialIdeal gen) == 0);
	assert(pos =!= null);
	
	g := fullSubKA (Q_(0,pos));
	v := first ((exponents tb)-(exponents g));
	
	-- mono is supposed to be an element of subR.
	mono := toMonomial(amb,v)//subR;
	mono = fullSub(mono);
	assert(mono%subR == 0);

	-- g is supposed to an element of the subring generated by G.
	g = G_(0,pos);	
	
	-- since an ideal absorbs outside products, we know that diffPoly is an element of ideal G.
	diffPoly := g*mono;
		
	if(diffPoly == 0) then(
	    error "This is not supposed to happen. (Possibly a bug within the function intrinsicReduce.)";
	    );
	
	coef := coefficient(tb, diffPoly);
	assert( (leadTerm diffPoly) == tb*coef);
	assert(coefficient(tb, result) != 0);
	diffPoly = diffPoly * (1/coefficient(tb, diffPoly));
	diffPoly = diffPoly * coefficient(tb, result);
        assert(coefficient(tb, diffPoly) == coefficient(tb, result));
	result = result - diffPoly;	
		
	loopNum = loopNum + 1;
    	);
    assert(result%subR == 0);  
    result
    );

-- applies intrinsicReduce to each entry of the 1-row matrix M.
intrinsicReduce(Subring, Matrix, Matrix) := (subR, G, M) -> (
    matrix({apply(first entries M, ent -> intrinsicReduce(subR, G, ent))})
    );

-- algorithm 11.24
extrinsicBuchberger = method(TypicalValue => Matrix)
extrinsicBuchberger(Subring, Matrix) := (subR, S) -> (
    G := (gens gb (transpose (S//subR)));
    G = subR#"presentation"#"fullSubstitution"(G);
    G = transpose compress G;
    mingensSubring(subR, G)
    );

-- Perform autoreduction on the generators of an intrinsic ideal:
-- I.e., reduce g\in idealGens modulo idealGens-g for all g\in idealGens.   
   -- subR is a Subring (probably has to be a Sagbi basis)
   -- idealGens is a matrix containing generators of an ideal in subR.
autoreduce = method(TypicalValue => Matrix)
autoreduce(Subring, Matrix) := (subR, idealGens) -> (
    noDupes := new MutableList from first entries idealGens;        
    reducedGens := for i from 0 to (numcols idealGens)-1 list(		
	s := idealGens_(0,i);
	notS := submatrix'(matrix({toList noDupes}),,{i});      
	--print("----------- autoreduction step "|toString(i)|"/"|toString(numcols idealGens)|"  --------------");
	answer := intrinsicReduce(subR, notS, s);
       	answer = sub(answer,ring idealGens);	
	if(answer != 0) then ( 
	    answer = answer*(1/leadCoef(answer));
	    );
	noDupes#i = answer;	
	
	answer
	);
    
    -- The extra "matrix entries" is to eliminate the degrees (which are the numbers in curly brackets)
    -- I don't know what they are for and they break the == operator.
    matrix entries (transpose compress (matrix({reducedGens})))
    );

-- Perform autosubduction on the generators of a subring:
-- I.e., reduce g\in G modulo G-g for all g\in G.

-- It is likely that this can be cleaned up a bit.
autosubduce = method(TypicalValue => Matrix)
autosubduce(Matrix) := G -> (
    noDupes := new MutableList from first entries G;        
    reducedGens := for i from 0 to (numcols G)-1 list(		
    	s := G_(0,i);
    	notS := compress submatrix'(matrix({toList noDupes}),,{i});
	if zero notS then return matrix{{s}};	
    presNotS := makePresRing(ring notS,notS);
	answer := presNotS#"fullSubstitution"(internalSubduction(presNotS, s));
    	if(answer != 0) then ( 
	    answer = answer*(1/leadCoef(answer));
	    );
    	noDupes#i = answer;	
    	answer
    	);
        compress matrix{reducedGens}
    );


-- This is subroutine 11.18 of Sturmfels.
-- Assumes M is a matrix of monomials in the toric ring K[A]
-- (for now,  it can be anything in the tensor ring of subR satisfying this condition,
-- involving the generators or the variables.)
toricSyz = method(TypicalValue => Matrix)
toricSyz(Subring, Matrix) := (subR, M) -> (
    
    pres := subR#"presentation";
    tense := pres#"tensorRing";
    projInc := pres#"projectionAmbient";
    fullSub := pres#"fullSubstitution";
    subMap := pres#"substitution";
    incBase := pres#"sagbiInclusion";
    
    amb := ambient subR;
    r := numcols M;
    
    if subR#"isSAGBI" == false then(
	error "Can only use toricSyz on a Subring instance that is a Sagbi basis.";
	);
    if ring M === amb then(
	M = (pres#"inclusionAmbient")(M);
	) else if ring M =!= tense then(
	error "The entries of M must be in either the TensorRing or ambient ring of A.";
	);
    KA := subring leadTerm gens subR;
    tenseKA := KA#"presentation"#"tensorRing";
    M = sub(M, tenseKA);    
    M = (KA#"presentation"#"substitution")(M);
    if leadTerm M != M then(
	error "Expected a 1-row matrix of monomials."; 
	); 
    
    U := M // KA;
    -- If some entry of M is not an element of KA, its normal form is zero.
    -- This will cause the assertion to fail.
    assert(KA#"presentation"#"substitution"(U) == M);

    -- each column of syzU is a relation of U.
    syzU := syz U;
    special := transpose syzU;
    
    -- U is supposed to in the upper variables only. 
    assert(KA#"presentation"#"sagbiInclusion" U == U);
    
    intersection := selectInSubring(1, gens gb intersect(ideal U, KA#"presentation"#"liftedPres"));    
    
    binomials := for i from 0 to (numcols intersection)-1 list(
	ent := intersection_(0,i);
	coefs := apply(first entries U, e -> monoCoef(e, ent));
      	if position(coefs, c -> c != 0) === null then (
	    error "Error: something impossible happened. (This may be a bug in the function toricSyz.)";
	    );
    	coefs 
	);
    binomials = (matrix binomials) || special;
    fullSubKA := KA#"presentation"#"fullSubstitution";
    binomials = transpose compress transpose fullSubKA binomials;
    matrix entries binomials
    );
