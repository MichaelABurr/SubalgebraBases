debug Core -- gets rid of "raw" error during installation. probably a better way...

export {
    "subduction",
    "subalgebraBasis",
    "sagbi",
    "PrintLevel",
    "SagbiDegrees",
    "SubalgComputations",
    "SagbiGens",
    "SagbiDone",
    "Autosubduce"
    }

-- Performs subduction using the generators of subR.
-- currently does not require the generators to be a Sagbi basis.

-- Perhaps make this so that you can give it a matrix instead of a subring?
-- If we were to do this, check that the output is used consistently
subduction = method(TypicalValue => RingElement)
subduction(Subring, RingElement) := (subR, f) -> (
    pres := subR#"presentation";
    tense := pres#"tensorRing";
    if ring f === tense then (
	f = (pres#"fullSubstitution")(f);
	)else if ring f =!= ambient subR then (
	error "f must be from the (ambient subR) or subR's TensorRing.";
	);
        
    -- It is possible for ring f === ambient to be true but f is still from a different ring 
    -- than pres#"TensorRing". In this case, it shouldn't try to prevent an error by using "sub"
    -- or something. Instead, the following line will deliberately throw an error:
    -- (This is done because otherwise there is potential for a segfault.)
    throwError := f - 1_(ambient subR);   
    
    -- We no longer store a groebner basis each time
    -- Will this be expensive to recompute a groebner basis each time?
    -*
    if not subR.cache#?"SyzygyIdealGB" then (
	subR.cache#"SyzygyIdealGB" = gb (pres#"SyzygyIdeal");
	);
    J := subR.cache#"SyzygyIdealGB";
    *-
    J := gb (pres#"syzygyIdeal");
        
    F := pres#"substitution";
    numblocks := rawMonoidNumberOfBlocks raw monoid ambient subR;
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
subduction(Subring, Matrix) := (subR, M) -> (	
    ents := for i from 0 to (numcols M)-1 list(
    	subduction(subR, M_(0,i))
	);
    matrix({ents})
    );

---------------------------------------------------------------------------------------
-- subalgebraBasis is needed for legacy purposes. It should not be changed or deleted. 
-- New code should use the function "sagbi."
---------------------------------------------------------------------------------------
subalgebraBasis = method(
    TypicalValue => Matrix, 
    Options => {
	Strategy => null,
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
    	Strategy => null,
	Autosubduce => true,
    	Limit => 100,
    	PrintLevel => 0
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


-- sagbi(Subring) := o -> S -> sagbi(o,sagbiBasis S);

-- PrintLevel > 0: Print some information each loop, but don't print any polynomials.
-- PrintLevel > 1: Print new Sagbi gens.
sagbi(SAGBIBasis) := o -> S -> (
    if S#"sagbiDone" then return S;
    
    compTable := new MutableHashTable from S;
    compTable#"pending" = new MutableHashTable from compTable#"pending";
    compTable#"stoppingData" = new MutableHashTable from compTable#"stoppingData";
    
    if o.Autosubduce then(
	if o.PrintLevel > 0 then (
	    print("Performing initial autosubduction...");
	    );
    	compTable#"subringGenerators" = autosubduce compTable#"subringGenerators";
    );
    
    if #compTable#"pending" == 0 then (
    	insertPending(compTable, compTable#"subringGenerators");
    	);

    -- Remove elements of coefficient ring
    remove(compTable#"pending", 0);
    
    compTable#"stoppingData"#"degree" = processPending(compTable) + 1;
   
    while compTable#"stoppingData"#"degree" <= o.Limit and not compTable#"sagbiDone" do (  	
	if o.PrintLevel > 0 then (
	    print("---------------------------------------");
	    print("-- Current degree:"|toString(compTable#"stoppingData"#"degree"));
	    print("---------------------------------------");
	    );
     
	pres := makePresRing(compTable#"ambientRing", compTable#"sagbiGenerators");
	
    	if o.PrintLevel > 0 then (
    	    print("-- Computing the kernel of the substitution homomorphism to the initial algebra...");
	    );
	sagbiGB = gb(pres#"syzygyIdeal", DegreeLimit => compTable#"stoppingData"#"degree"); 
	zeroGens := submatByDegree(mingens ideal selectInSubring(1, gens sagbiGB), compTable#"stoppingData"#"degree");
	syzygyPairs = pres#"substitution"(zeroGens);
	
	break; 
	);
    	(compTable, sagbiGB, zeroGens, syzygyPairs)
	);
    	
	--this is where we are as of 3/26/21
	
    	end--
	
	-- Have we previously found any syzygies of degree currDegree?
        if subalgComp#"pending"#(compTable#"stoppingData"#"degree") != {} then (
            syzygyPairs = syzygyPairs | pres#"inclusionAmbient"(matrix{subalgComp#"pending"#(compTable#"stoppingData"#"degree")});
            subalgComp#"Pending"#currDegree = {};
            );
	
	if o.PrintLevel > 0 then(
    	    print("-- Performing subduction on S-polys... ");
	    print("-- Num. S-polys before subduction:"|toString(numcols syzygyPairs));
	    );
	
       	subd := subduction(partialSagbi, syzygyPairs);
	
	local newElems;
       	if entries subd != {{}} then (
	    newElems = compress ((pres#"ProjectionBase")(subd));
            ) else (
	    newElems = subd;
	    );
	
	if o.PrintLevel > 0 then(
	    print("-- Num. S-polys after subduction:"|toString(numcols newElems));
	    );	
	
	if o.PrintLevel > 1 then(
	    print("-- New generators:");
	    if(numcols newElems == 0) then(
		-- It has to treat this as a special case because zero matrices are special. 
		print("| 0 |");
		)else(
		debugPrintMat(newElems);
		);
	    );

	if numcols newElems > 0 then (	    
	    insertPending(R, newElems, o.Limit);
    	    processPending(R, o.Limit);
	    currDegree = subalgComp#"CurrentLowest";   
            ) else (
	    
	    C0 := sum toList apply(subalgComp#"Pending", i -> #i) == 0;
	    C1 := rawStatus1 raw sagbiGB == 6;
	    C2 := currDegree > maxGensDeg; 
	    
	    if o.PrintLevel > 0 then(
		print("-- No new generators found. ");
		print("-- Stopping conditions:");
		print("--    No higher degree candidates: "|toString(C0));
		print("--    S-poly ideal GB completed:   "|toString(C1));
		print("--    Degree lower bound:          "|toString(C2));
		);
	    
	    if C0 and C1 and C2 then (
		R.cache.SagbiDone = true;
            	);
	    );
	currDegree = currDegree + 1;
    	);
    
    if currDegree > o.Limit then(
	isPartial = true;
	);
    -- Possibly, it could finish on the same loop that it successfully terminates.
    if R.cache.SagbiDone == true then(
	isPartial = false;
	);
    
    if o.PrintLevel > 0 then(
    	if currDegree > o.Limit then (
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
        
    resultR := ambient R;
    M := R.cache.SagbiGens;
    presRing := makePresRing(resultR, M);
    
    -- It shouldn't directly set (cache => R.cache) because there is a possibility of inhereting outdated information.
    -- (It can't assume that outside sources haven't modified the cache.) 
    cTable := new CacheTable from{
	SubalgComputations => new MutableHashTable from {},
	SagbiGens => M,
	SagbiDegrees => R.cache.SagbiDegrees,
	SagbiDone => R.cache.SagbiDone
	}; 
    new Subring from {
    	"AmbientRing" => resultR,
    	"Generators" => M,
	"PresRing" => presRing,
    	"isSagbi" => R.cache.SagbiDone,
	"isPartialSagbi" => isPartial,
	"partialDegree" => currDegree-1,
	cache => cTable
	}
    );
