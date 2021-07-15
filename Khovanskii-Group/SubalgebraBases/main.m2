debug Core -- gets rid of "raw" error during installation. probably a better way...

-- Performs subduction using matrix of generators, M.
-- currently does not require the generators to be a Sagbi basis.

subduction = method(TypicalValue => RingElement)
subduction(Matrix, RingElement) := (M, f) -> (
    
    -*
    pres := makePresRing(ring M, M);
    result := pres#"fullSubstitution" internalSubduction(pres, f);
    result
    *-
    Q := ring M;
    R := ambient Q;
    
    pres := makePresRing(Q, M);
    liftedPres := makePresRing(R, sub(M, R));
        
    result := topLevelFullSubduction(pres, liftedPres, f);
    result 
    
    );

subduction(Matrix, Matrix) := (M, N) -> (
    
    -*
    pres := makePresRing(ring M, M);	
    ents := for i from 0 to (numcols N)-1 list(
    	pres#"fullSubstitution" internalSubduction(pres, N_(0,i))
	);
    matrix({ents})
    *-
    
    Q := ring M;
    R := ambient Q;
    
    pres := makePresRing(Q, M);
    liftedPres := makePresRing(R, sub(M, R));
    
    ents := for i from 0 to (numcols N)-1 list (
	topLevelFullSubduction(pres, liftedPres, N_(0, i))
	);
    matrix({ents})
    
    );

internalSubduction = method(TypicalValue => RingElement)
internalSubduction(PresRing, RingElement) := (pres, f) -> (
    tense := pres#"tensorRing";
    if ring f === tense then (
	f = (pres#"fullSubstitution")(f);
	)else if ring f =!= source pres#"inclusionAmbient" then (
	error "f must be from ambR or tensorRing.";
	);
        
    -- It is possible for ring f === ambient to be true but f is still from a different ring 
    -- than pres#"tensorRing". In this case, it shouldn't try to prevent an error by using "sub"
    -- or something. Instead, the following line will deliberately throw an error:
    -- (This is done because otherwise there is potential for a segfault.)
    throwError := f - 1_(source pres#"inclusionAmbient");   
    
    -- Use the same pres ring as much as possible.  
    -- M2 will automatically cache the gb calculation 
    -- as long as the pres ring is not reconstructed.
    J := gb (pres#"syzygyIdeal");
        
    F := pres#"substitution";
    M := monoid source pres#"inclusionAmbient";
    numblocks := rawMonoidNumberOfBlocks raw M;
    fMat := matrix({{pres#"inclusionAmbient"(f)}});
    
    
    result := rawSubduction(numblocks, raw fMat, raw F, raw J);
    result = promote(result_(0,0), tense);    
    
    
    result
    );

-- The C++ implementation of rawSubduction could be improved.
-- Here is the code path that it takes:
-- (M2) subduction(Matrix) -> (M2) subduction(RingElement) -> (C++) rawSubduction(Matrix) -> (C++) subduction(RingElement)
-- If we deleted the C++ rawSubduction(Matrix) function and made rawSubduction take a RingElement, we could have:
-- (M2) subduction(Matrix) -> (M2) subduction(RingElement) -> (C++) subduction(RingElement)
internalSubduction(PresRing, Matrix) := (pres, M) -> (	
    ents := for i from 0 to (numcols M)-1 list(
    	internalSubduction(pres, M_(0,i))
	);
    matrix({ents})
    );


-----------------------------------------------------------------
-- subduction which works for quotients
-- Top level code for subduction which can handle quotient rings
-----------------------------------------------------------------

topLevelSubduction = method(
    TypicalValue => RingElement,
    Options => {
	PrintLevel => 0
	})

-- PrintLevels:
--  3+ = displays input and output of subduction
--  4+ = displays rings and ideals used in computation
--  5+ = displays the polynomial g throughout the loop


--------------------------------------------
-- topLevelSubduction
-- 
-- Input:
-- f polynomial in Q = R/I to be subducted
-- P presRing with generators to subduct against
-- S lifted presRing with the generators of S lifted to R
--
-- Output:
-- g subduction of f wrt the generators of S 
--------------------------------------------

topLevelSubduction(PresRing, PresRing, RingElement) := o -> (P, S, f) -> (
     
    if o.PrintLevel > 2 then (
    print("");
    print("--------------------------------");
    print("-- Call to topLevelSubduction");
    print("--------------------------------");
    print("-- PresRing P = ");
    print(peek P);
    print("");
    print("-- Lifted PresRing S = ");
    print(peek S);
    );
    
    -- Setup rings, ideals and maps
    Q := ring f;
    I := ideal Q;
    R := ring I;
    quotientMap := map(Q, R, gens Q);
    LTI := ideal leadTerm I; 
    
    generatorIndices := toList(numgens R .. (numgens P#"tensorRing" - 1));
    G := (matrix P#"fullSubstitution")_generatorIndices;
    liftG := (matrix S#"fullSubstitution")_generatorIndices;
    
    if o.PrintLevel > 3 then (
    print("-- Ambient Ring Q = ");
    print(Q);
    print("");
    print("-- Ideal I = ");
    print(I);
    print("");
    print("-- PolyRing R = ");
    print(R);
    print("");
    print("-- LeadTerm I LTI = ");
    print(LTI);
    print("");
    );
    
    
    -- We work with a subring S of R and, when necessary, take elements mod LT(I)
    syzygyIdeal := S#"syzygyIdeal";
    inclusionAmbient := S#"inclusionAmbient";
    projectionAmbient := S#"projectionAmbient";
    fullSubstitution := S#"fullSubstitution";
    sagbiInclusion := S#"sagbiInclusion";
    
    -- lift LT(I) to the tensorRing
    tensorRingLTI := inclusionAmbient LTI;
    g := f;
    
    while true do (
	
	if o.PrintLevel > 4 then (
	    print("-- Current g = ");
	    print(g);
	    );
	
	-- if g is a constant then exit loop
	if g == 0_Q then break;
	if degree(g) == {0} then break;
		
	liftg := sub(g, R) % I;
	LTg := (leadTerm liftg) % LTI; 
	tensorRingLTg := inclusionAmbient(LTg);
	h := tensorRingLTg % (syzygyIdeal + tensorRingLTI);
	
	projectionh := fullSubstitution sagbiInclusion h;
	-- exit the loop if h does not lie in K[p_1 .. p_r] <- the variables tagging the generators of S
	if projectionh == 0_R then break;
	if degree projectionh == {0} then break;
	
	-- update g
	hSub := quotientMap fullSubstitution h;
	g = g - hSub;
	);
    
    -- if g is a constant subduct to 0_Q
    if g != 0_Q then (
	if degree(g) == {0} then g = 0_Q;
	);
    if o.PrintLevel > 2 then (
    print("-- output = ");
    print(g);
    print("---------------------------------------");
    print("-- End of call to topLevelSubduction");
    print("---------------------------------------");
    print("");
    );
    
    g
    );


topLevelSubduction(PresRing, PresRing, Matrix) := o -> (P, S, M) -> (	
    ents := for i from 0 to (numcols M)-1 list(
    	topLevelSubduction(P, S, M_(0,i), o)
	);
    matrix({ents})
    );

-*
---------------------------------------
-- Old version of topLevelSubduction
-- 
--
---------------------------------------

topLevelSubduction(List, RingElement) := o -> (G, f) -> (
     
    if o.PrintLevel > 2 then (
    print("");
    print("--------------------------------");
    print("-- Call to topLevelSubduction");
    print("--------------------------------");
    print("-- List of polys G = ");
    print(G);
    print("");
    print("-- subducting f = ");
    print(f);
    );
    
    -- Setup rings, ideals and maps
    Q := ring f;
    I := ideal Q;
    R := ring I;
    quotientMap := map(Q, R, gens Q);
    LTI := ideal leadTerm I; 
    
    liftG := for g in G list sub(g, R) % I; -- lift G to R 
    
    if o.PrintLevel > 3 then (
    print("-- Ambient Ring Q = ");
    print(Q);
    print("");
    print("-- Ideal I = ");
    print(I);
    print("");
    print("-- PolyRing R = ");
    print(R);
    print("");
    print("-- LeadTerm I LTI = ");
    print(LTI);
    print("");
    );
    
    
    -- We work with a subring S of R and, when necessary, take elements mod LT(I)
    -------
    -- TODO:
    -- change the input to accept a presentation + ring element 
    -- and we output something in the tensorRing
    --------
    
    S := subring liftG; 
    syzygyIdeal := S#"presentation"#"syzygyIdeal";
    inclusionAmbient := S#"presentation"#"inclusionAmbient";
    projectionAmbient := S#"presentation"#"projectionAmbient";
    fullSubstitution := S#"presentation"#"fullSubstitution";
    sagbiInclusion := S#"presentation"#"sagbiInclusion";
    
    -- lift LT(I) to the tensorRing
    tensorRingLTI := inclusionAmbient LTI;
    g := f;
    
    while true do (
	
	if o.PrintLevel > 4 then (
	    print("-- Current g = ");
	    print(g);
	    );
	
	-- if g is a constant then exit loop
	if g == 0_Q then break;
	if degree(g) == {0} then break;
		
	liftg := sub(g, R) % I;
	LTg := (leadTerm liftg) % LTI; 
	tensorRingLTg := inclusionAmbient(LTg);
	h := tensorRingLTg % (syzygyIdeal + tensorRingLTI);
	
	projectionh := fullSubstitution sagbiInclusion h;
	-- exit the loop if h does not lie in K[p_1 .. p_r] <- the variables tagging the generators of S
	if projectionh == 0_R then break;
	if degree projectionh == {0} then break;
	
	-- update g
	hSub := quotientMap fullSubstitution h;
	g = g - hSub;
	);
    
    -- if g is a constant subduct to 0_Q
    if g != 0_Q then (
	if degree(g) == {0} then g = 0_Q;
	);
    if o.PrintLevel > 2 then (
    print("-- output = ");
    print(g);
    print("---------------------------------------");
    print("-- End of call to topLevelSubduction");
    print("---------------------------------------");
    print("");
    );
    
    g
    );


topLevelSubduction(List, Matrix) := o -> (G, M) -> (	
    ents := for i from 0 to (numcols M)-1 list(
    	topLevelSubduction(G, M_(0,i), o)
	);
    matrix({ents})
    );

-------------------------------------------
*-



--------------------------
-- topLevelFullSubduction
--   applies topLevelSubduction iteratively to a quotient ring element
--------------------------
-- Given a list G and an element f of a quotient ring Q = R/I
--




topLevelFullSubduction = method(TypicalValue => RingElement, Options => {PrintLevel => 0})
topLevelFullSubduction(PresRing, PresRing, RingElement) := o -> (P, S, f) -> (
    Q := ring f;    
    I := ideal Q;
    R := ring I;
    quotientMap := map(Q, R, gens Q);
    result := 0_Q;
    g := f;
    
    if o.PrintLevel > 3 then (
	print("----------------------------");
	print("-- topLevelFullSubduction");
	print("----------------------------");
	print("-- P = ");
	print(peek P);
	print("-- S = ");
	print(peek S);
	print("-- f = ");
	print(f);
	);
    
    while true do (
	
	if o.PrintLevel > 4 then (
	    print("topLevelFullSubduction loop");
	    print("result so far =");
	    print(result);
	    print("g = ");
	    print(g);
	    );
	
	subductedPart := topLevelSubduction(P, S, g, o);
	liftSubductedPart := sub(subductedPart, R) % I;
	LTSubductedPart := quotientMap(leadTerm liftSubductedPart);
	result = result + LTSubductedPart;
	g = subductedPart - LTSubductedPart;
	
	-- exit the loop if g is zero or a constant
	if g == 0_Q then break;
	if degree(g) == {0} then break;
	);
    
    if o.PrintLevel > 3 then (
    	print("exit topLevelFullSubduction loop");
	print("result =");
	print(result);
	print("g = ");
	print(g);
	print("finished topLevelFullSubduction");
	print("--------------------------------")
	);
    
    result
    );


topLevelFullSubduction(PresRing, PresRing, Matrix) := o -> (P, S, M) -> (	
    ents := for i from 0 to (numcols M)-1 list(
    	topLevelFullSubduction(P, S, M_(0,i), o)
	);
    matrix({ents})
    );


-* 
-------------------------------------------
-- Old version of topLevelFullSubduction
--
-- current version uses pres rings
-------------------------------------------

topLevelFullSubduction = method(TypicalValue => RingElement, Options => {PrintLevel => 0})
topLevelFullSubduction(List, RingElement) := o -> (G, f) -> (
    Q := ring f;    
    I := ideal Q;
    R := ring I;
    quotientMap := map(Q, R, gens Q);
    result := 0_Q;
    g := f;
    
    if o.PrintLevel > 3 then (
	print("-- topLevelFullSubduction");
	print("-- G = ");
	print(G);
	print("-- f = ");
	print(f);
	);
    
    while true do (
	
	if o.PrintLevel > 4 then (
	    print("topLevelFullSubduction loop");
	    print("result so far =");
	    print(result);
	    print("g = ");
	    print(g);
	    );
	
	subductedPart := topLevelSubduction(G, g, o);
	liftSubductedPart := sub(subductedPart, R) % I;
	LTSubductedPart := quotientMap(leadTerm liftSubductedPart);
	result = result + LTSubductedPart;
	g = subductedPart - LTSubductedPart;
	
	-- exit the loop if g is a constant
	if g == 0_Q then break;
	if degree(g) == {0} then break;
	);
    
    if o.PrintLevel > 3 then (
    	print("exit topLevelFullSubduction loop");
	print("result =");
	print(result);
	print("g = ");
	print(g);
	print("finished topLevelFullSubduction");
	);
    
    result
    );


topLevelFullSubduction(List, Matrix) := o -> (G, M) -> (	
    ents := for i from 0 to (numcols M)-1 list(
    	topLevelFullSubduction(G, M_(0,i), o)
	);
    matrix({ents})
    );
*-


---------------------------------------------------------------------------------------
-- subalgebraBasis is needed for legacy purposes. It should not be changed or deleted. 
-- New code should use the function "sagbi."
---------------------------------------------------------------------------------------
subalgebraBasis = method(
    TypicalValue => Matrix, 
    Options => {
	Autosubduce => true,
    	Limit => 100,
    	PrintLevel => 0
	}
    );
subalgebraBasis(Matrix) := o -> gensMatrix -> (
    R := subring gensMatrix;
    gens sagbi(R,o)
    );
subalgebraBasis(List) := o -> L -> (
    gens sagbi(o, subring L)
    );
subalgebraBasis(Subring) := o -> subR -> (
    gens sagbi(o, subR)
    );
---------------------------------------------------------------------------------------

sagbi = method(
    TypicalValue => Subring, 
    Options => {
	Autosubduce => true,
    	Limit => 100,
    	PrintLevel => 0,
        storePending => true
    	}
    );

sagbi(Matrix) := o -> gensMatrix -> (
    sagbi(o, subring gensMatrix)
    );

sagbi(List) := o -> L -> (
    sagbi(o, subring L)
    );

sagbi(Subring) := o -> S -> (
    sagbi(o, sagbiBasis S)
    );


-- PrintLevel > 0: Print some information each loop, but don't print any polynomials.
-- PrintLevel > 1: Print new Sagbi gens.
-- PrintLevel > 2: Print the compTable state and show the subductions for each loop
-- PrintLevel > 3: Print more data during each subduction
-- PrintLevel > 4: Print all steps of subduction
sagbi(SAGBIBasis) := o -> S -> (
    if (S#"stoppingData"#"limit" > o.Limit) or S#"sagbiDone" then return S;
    
    compTable := new MutableHashTable from S;
    compTable#"pending" = new MutableHashTable from compTable#"pending";
    compTable#"stoppingData" = new MutableHashTable from compTable#"stoppingData";
    compTable#"stoppingData"#"limit" = max {compTable#"stoppingData"#"limit",o.Limit};
    
    
    ------------------------
    -- Change to autosubduce
    --
    -- note: autosubduce calls internalSubduction
    --       use topLevelAutoSubduce for this now
    --
    -----------------------
    
    --TEMPORARY
    
    if o.Autosubduce then(
	if o.PrintLevel > 0 then (
	    print("Performing initial autosubduction...");
	    );
	
	-- New autosubduce code using top level subduction:
	compTable#"subringGenerators" = topLevelAutoSubduce(compTable#"subringGenerators", PrintLevel => o.PrintLevel);
	
	-- Previous autosubduce routine:
    	-- compTable#"subringGenerators" = autosubduce compTable#"subringGenerators";
	
	if o.PrintLevel > 2 then (
	    print("-- autoSubduced generators = ");
	    print(compTable#"subringGenerators");
	    );
	
    );
    
    ----------------
    
    if (numcols compTable#"sagbiGenerators" == 0) or (not o.storePending) then (
    	insertPending(compTable, compTable#"subringGenerators");
        -- Remove elements of coefficient ring
        remove(compTable#"pending", 0);
        compTable#"stoppingData"#"degree" = processPending(compTable) + 1;
    	);

    local subducted;
    local newElements;
    local pres;
    local sagbiGB;
    local zeroGens;
    local syzygyPairs;
    local terminationCondition0;
    local terminationCondition1;
    local terminationCondition2;
    
    -- TODO: think of a better name:
    -- tempDegree keeps track of the lowest degree of the newly added sagbi generators
    local tempDegree; 

    while compTable#"stoppingData"#"degree" <= o.Limit and not compTable#"sagbiDone" do (  	
	if o.PrintLevel > 0 then (
	    print("---------------------------------------");
	    print("-- Current degree:"|toString(compTable#"stoppingData"#"degree"));
	    print("---------------------------------------");
	    if o.PrintLevel > 2 then ( 
	    	print("-- current state = ");
	    	print(peek compTable);
	    	);
	    );
	
    	if o.PrintLevel > 0 then (
    	    print("-- Computing the kernel of the substitution homomorphism to the initial algebra...");
	    );
        sagbiGB = gb(compTable#"presentation"#"syzygyIdeal", DegreeLimit => compTable#"stoppingData"#"degree");
	terminationCondition1 = rawStatus1 raw sagbiGB == 6;
	zeroGens = submatByDegree(mingens ideal selectInSubring(1, gens sagbiGB), compTable#"stoppingData"#"degree");
	
	-- THIS IS NOT CORRECT IN THE (x^2 - y) QUOTIENT EXAMPLE
	syzygyPairs = compTable#"presentation"#"substitution"(zeroGens);
    	
	
	
	-- Ollie:
	-- 1) I'm not sure what the "mingens ideal" in the definition
	--    of zeroGens is doing. We already have a GB wrt an
	--    elimination order so would it be fine without it?
	-- 
	-- 2) Previous I suggested doing:
	--      zeroGens = submatAtMostDegree(mingens ideal selectInSubring(1, gens sagbiGB), compTable#"stoppingData"#"degree");
	--    however, instead we found that the problem was in the degree update
	--    we now set the degree to be the smallest degree of any new sagbi generator
	
	if o.PrintLevel > 2 then (
	    print("-- syzygyIdeal = ");
	    print(compTable#"presentation"#"syzygyIdeal");
	    print("-- gb calculation DegreeLimit = ");
	    print(compTable#"stoppingData"#"degree");
	    print("-- gens sagbiGB = ");
	    print(gens sagbiGB);
	    );
    
    
    -*
    -- THIS PART IS MOVED INTO THE NEW topLevelSubduction
    
    -- Have we previously found any syzygies of degree currDegree?
        if compTable#"pending"#?(compTable#"stoppingData"#"degree") then (
            syzygyPairs = syzygyPairs |
                compTable#"presentation"#"inclusionAmbient"(matrix{toList compTable#"pending"#(compTable#"stoppingData"#"degree")});
           
	    remove(compTable#"pending", compTable#"stoppingData"#"degree");
	    
	    
	    print("-- more syzygyPairs");
	    print(syzygyPairs);
            );

	if o.PrintLevel > 0 then(
    	    print("-- Performing subduction on S-polys... ");
	        print("-- Num. S-polys before subduction: " | toString(numcols syzygyPairs));
	    );
    *-	
    
    
    
    --------------------------------------------
    -- NEW Subduction using topLevelSubduction
    --------------------------------------------
    -- NOTES:
    -- 1. we avoid using the syzygyPairs, instead we pass zeroGens
    --    into Q
    --
        
     
    G := flatten entries compTable#"sagbiGenerators";
    syzygyAmbient := compTable#"presentation"#"fullSubstitution" zeroGens;
    
    -- Have we previously found any syzygies of degree currDegree?
        if compTable#"pending"#?(compTable#"stoppingData"#"degree") then (
            syzygyPairs = syzygyPairs |
                compTable#"presentation"#"inclusionAmbient"(matrix{toList compTable#"pending"#(compTable#"stoppingData"#"degree")});
            
	    syzygyAmbient = syzygyAmbient | matrix{toList compTable#"pending"#(compTable#"stoppingData"#"degree")};
	    
	    remove(compTable#"pending", compTable#"stoppingData"#"degree");
	    
            );

	if o.PrintLevel > 0 then(
    	    print("-- Performing subduction on S-polys... ");
	        print("-- Num. S-polys before subduction: " | toString(numcols syzygyPairs));
	    );
    
    
    if o.PrintLevel > 2 then (
	print("-- List of elements to be subducted = ");
	print(syzygyAmbient);
	print("-- List of elements to subduct w.r.t. =");
	print(G);
	);
    
    
    presForSubduction := compTable#"presentation";
    liftedPresForSubduction := compTable#"liftedPresentation";
    subducted = topLevelFullSubduction(presForSubduction, liftedPresForSubduction, syzygyAmbient, PrintLevel => o.PrintLevel);
    
    -- put result back into the tensorRing 
    if numcols subducted != 0 then (
    	subducted = compTable#"presentation"#"inclusionAmbient" subducted;
    	);
    
    
    -----------------
    --OLD:
    -- subducted = internalSubduction(compTable#"presentation", syzygyPairs);
    
    --  print out old subduction result
    --print("Old Subduction result:");
    --print(internalSubduction(compTable#"presentation", syzygyPairs));
    ----------------
    
        if numcols subducted != 0 then (
	    newElements = compress ((compTable#"presentation"#"projectionAmbient")(subducted));
            ) else (
	    newElements = subducted;
	    );

	if o.PrintLevel > 0 then(
	    print("-- Num. S-polys after subduction: " | toString(numcols newElements));
	    );

	if o.PrintLevel > 1 then(
	    print("-- New generators:");
	    if(numcols newElements == 0) then(
		-- It has to treat this as a special case because zero matrices are special.
		    print("| 0 |");
		    )else(
		    debugPrintMat(newElements);
		    );
        );

	if numcols newElements > 0 then (
	    
	    if o.PrintLevel > 2 then(
	         print("-- New Elements to be processed");
	         print(newElements);
	         );
	     
	    insertPending(compTable, newElements);
    	    tempDegree = processPending(compTable);
	    
	    -- if not lowestDegree(compTable) == infinity then 
            if not (tempDegree == infinity) then (  
                 compTable#"stoppingData"#"degree" = tempDegree + 1;
                 ) else (
                 compTable#"stoppingData"#"degree" = compTable#"stoppingData"#"degree" + 1;
		 );
        ) else (

        terminationCondition0 = #(compTable#"pending") == 0;
        terminationCondition2 = compTable#"stoppingData"#"degree" > max flatten (degrees compTable#"subringGenerators")_1;

        if o.PrintLevel > 0 then(
		print("-- No new generators found. ");
		print("-- Stopping conditions:");
		print("--    No higher degree candidates: "|toString(terminationCondition0));
		print("--    S-poly ideal GB completed:   "|toString(terminationCondition1));
		print("--    Degree lower bound:          "|toString(terminationCondition2));
		);

        if terminationCondition0 and terminationCondition1 and terminationCondition2 then (
            compTable#"sagbiDone" = true;
            );
	
        compTable#"stoppingData"#"degree" = compTable#"stoppingData"#"degree" + 1;
        );
    
    );
    
    if o.PrintLevel > 0 then(
    	if not compTable#"sagbiDone" then (
            print("-- Limit was reached before a finite SAGBI basis was found.");
    	    )else(
            print("-- Finite Sagbi basis was found.");
            );
    	);
    
    -- We return a new instance of subring instead of the generators themselves so that we can say whether or not a Subring instance
    -- IS a Sagbi basis, not whether or not it HAS a Sagbi basis. (The latter is unacceptable because the cache should not effect 
    -- the value of a function.)
        
    -- If subalgebraBasis is called on a Subring instance with a previously computed Sagbi basis that is not itself a Sagbi basis,
    -- a new subring instance will be constructed from its cached SagbiGens. This is OK because different instances of the same 
    -- subring will still be equal if we calculate equality based on the mathematical equality of the subalgebras they generate.
    -----------------------------------------------------------------------------------------------------
    -- subR.cache.SagbiDone: Indicates whether or not the Subring instance has a cached Sagbi basis. 
    -- subR.isSagbi        : Indicates whether or not (gens subR) itself is a Sagbi basis.
    -----------------------------------------------------------------------------------------------------
    -- The correct way to implement a function that requires a Subring instance that is a Sagbi basis is to check that 
    -- (subR.isSagbi == true). If (subR.isSagbi == false) and (subR.cache.SagbiDone == true), an error should still be thrown.
    
    sagbiBasis(storePending => o.storePending,compTable)
);


-- checks whether or not the generators form a sagbi basis wrt the given term order
verifySagbi = method()
verifySagbi Subring := S -> (
    presS := S#"presentation";
    IA := presS#"syzygyIdeal";
    GBIA := gens gb IA;
    monomialSyzygies := selectInSubring(1, GBIA);
    remainders := compress subduction(gens S, presS#"fullSubstitution" monomialSyzygies);
    HT := new MutableHashTable from S;
    HT#"isSAGBI" = (numcols remainders == 0);
    new Subring from HT
    )
verifySagbi Matrix := M -> verifySagbi subring M
verifySagbi List := L -> verifySagbi subring L
