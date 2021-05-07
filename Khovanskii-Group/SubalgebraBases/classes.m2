export {
    "Subring",
    "subring",
    "PresRing",
    "makePresRing",
    "getWeight",
    "setWeight",
    "presentationRing",
    "VarBaseName",
    "recordsagbi",
    "sagbidone",
    "sagbigens",
    "sagbiring",
    "storePending",
    "limit",
    "SAGBIBasis",
    "sagbiBasis",
    "isSagbi",
    "sagbiDone"
}

-- Subring data type
-- A subring is meant to be fairly light-weight.
-- Subrings include the ambient ring, their generators
-- a boolean indicating whether the generators are SAGBI and
-- a PresRing (see later)

Subring = new Type of HashTable

-- Make options => true
subring = method(Options => {VarBaseName => "p"})
subring Matrix := opts -> M -> (
    new Subring from{
        "ambientRing" => ring M,
        "generators" => M,
        "presentation" => makePresRing(opts, ring M, M),
        "isSAGBI" => false,
        cache => new CacheTable from {}
    }
)
subring List := opts -> L -> subring(opts, matrix{L})

-- Subring access functions

ambient Subring := A -> A#"ambientRing"
gens Subring := o -> A -> A#"generators"
numgens Subring := A -> (numcols gens A)
net Subring := A -> "subring of " | toString(ambient A)

isSagbi = method()
isSagbi Subring := A -> A#"isSAGBI"

-- SAGBIBasis data type
-- This is a computation object which can hold the intermediate
-- results of a sagbi basis computation.
-- This is similar to the output of a gb calculation

SAGBIBasis = new Type of HashTable

sagbiBasis = method(Options => true)
sagbiBasis Subring := {limit => 100} >> opts -> S -> (
    stopping := new HashTable from {"limit" => opts.limit, "degree" => -1};
    pending := new HashTable;
    new SAGBIBasis from {
        "ambientRing" => ambient S,
        "subringGenerators" => gens S,
        "sagbiGenerators" => matrix(ambient S,{{}}),
        "sagbiDegrees" => matrix(ZZ,{{}}),
        "sagbiDone" => false,
        "stoppingData" => stopping,
        "pending" => pending,
        "presentation" => null
    }
)

sagbiBasis MutableHashTable := {storePending => true, VarBaseName => "p"} >> opts -> H -> (
    stopping := new HashTable from {"limit" => H#"stoppingData"#"limit", "degree" => H#"stoppingData"#"degree"};
    pending := if opts.storePending then new HashTable from H#"pending" else new HashTable;
    new SAGBIBasis from {
        "ambientRing" => H#"ambientRing",
        "subringGenerators" => H#"subringGenerators",
        "sagbiGenerators" => H#"sagbiGenerators",
        "sagbiDegrees" => H#"sagbiDegrees",
        "sagbiDone" => H#"sagbiDone",
        "stoppingData" => stopping,
        "pending" => pending,
        "presentation" => makePresRing(VarBaseName => opts.VarBaseName, H#"ambientRing", H#"sagbiGenerators")
    }
)

gens SAGBIBasis := o -> S -> (
    if #flatten entries S#"sagbiGenerators" == 0 then S#"subringGenerators"
    else if S#"sagbiDone" then (S#"sagbiGenerators")
    else (
        << "The subring generators should be subducted by the sagbi generators.  This is not yet implemented";
        S#"subringGenerators" | S#"sagbiGenerators"
    )
)

subring SAGBIBasis := {} >> opts -> S -> (
    G := gens S;
    if S#"sagbiDone" then new Subring from{
        "ambientRing" => ring S#"sagbiGenerators",
        "generators" => G,
        "presentation" => makePresRing(opts, ring S#"sagbiGenerators", S#"sagbiGenerators"),
        "isSAGBI" => true,
        cache => new CacheTable from {}}
    else subring G
)

sagbiDone = method(Options => {})
sagbiDone SAGBIBasis := opts -> S -> S#"sagbiDone"

-- This type is compatible with internal maps that are generated in the Sagbi algorithm.
-- Originally, this was stored directly in the cache of an instance of Subring.
-- The problem with that solution is there is a need to use these maps outside of the Sagbi algorithm computations.
-- Also, the cache should not be used in a way that causes side effects.
PresRing = new Type of HashTable

net PresRing := pres -> (
    tense := pres#"tensorRing";
    A := numcols vars tense;
    B := numcols selectInSubring(1, vars tense);
    "PresRing instance ("|toString(B)|" generators in "|toString(A-B)|" variables)"
)

-- gensR are elements of R generating some subalgebra.
-- R is a polynomial ring.
makePresRing = method(TypicalValue => PresRing, Options => {VarBaseName => "p"})
makePresRing(Ring, Matrix) := opts -> (R, gensR) -> (
    if(R =!= ring(gensR)) then(
    error "The generators of the subalgebra must be in the ring R.";
    );
    makePresRing(opts, R, first entries gensR)
)

makePresRing(Ring, List) := opts -> (R, gensR) ->(
    gensR = sort gensR;

    if #gensR == 0 then(
        error "List must not be empty.";
    );

    if(ring(matrix({gensR})) =!= R) then(
        error "The generators of the subalgebra must be in the ring R.";
    );

    ambR := R;
    nBaseGens := numgens ambR;
    nSubalgGens := length gensR;

    -- Create a ring with combined generators of base and subalgebra.
    monoidAmbient := monoid ambR;
    coeffField := coefficientRing ambR;

    -- Construct the monoid of a ring with variables corresponding to generators of the ambient ring and the subalgebra.
    -- Has an elimination order that eliminates the generators of the ambient ring.
    -- The degrees of generators are set so that the SyzygyIdeal is homogeneous.
    newOrder := prepend(Eliminate nBaseGens, monoidAmbient.Options.MonomialOrder);

    newVariables := monoid[
    VariableBaseName=> opts.VarBaseName,
    Variables=>nBaseGens+nSubalgGens,
    Degrees=>join(degrees source vars ambR, degrees source matrix({gensR})),
    MonomialOrder => newOrder];

    tensorRing := coeffField newVariables;

    sagbiInclusion := map(tensorRing, tensorRing,
    (matrix {toList(nBaseGens:0_(tensorRing))}) |
    (vars tensorRing)_{nBaseGens .. nBaseGens+nSubalgGens-1});

    projectionAmbient := map(ambR, tensorRing,
    (vars ambR) | matrix {toList(nSubalgGens:0_(ambR))});

    inclusionAmbient := map(tensorRing, ambR,
    (vars tensorRing)_{0..nBaseGens-1});

    substitution := map(tensorRing, tensorRing,
    (vars tensorRing)_{0..nBaseGens-1} | inclusionAmbient(matrix({gensR})));

    genVars := (vars tensorRing)_{numgens ambient R..numgens tensorRing-1};

    syzygyIdeal := ideal(genVars - inclusionAmbient(leadTerm matrix({gensR})));
    

    liftedPres := ideal(substitution(genVars) - genVars);
    fullSubstitution := projectionAmbient*substitution;

    ht := new HashTable from {
    "tensorRing" => tensorRing,
    "sagbiInclusion" => sagbiInclusion,
    "projectionAmbient" => projectionAmbient,
    "inclusionAmbient" => inclusionAmbient,
    "substitution" => substitution,
    "fullSubstitution" => fullSubstitution,
    "syzygyIdeal" => syzygyIdeal,
    "liftedPres" => liftedPres
    };

    new PresRing from ht
);

-- The reason why this is implemented is to prevent incorrect usage of the makePresRing constructor.
-- A subring is already associated with an immutable PresRing instance which should be used instead of
-- constructing a new instance. Don't use makePresRing when you can use the function subring.
makePresRing(Subring) := opts -> subR -> (
    subR#"PresRing"
);

-- Old things, to be edited.

-- f % Subring is never going to be an element of the subalgebra, hence the ouput
-- is in the lower variables of TensorRing.
-- input: f in ambient A or TensorRing of A.
-- output: r in TensorRing of A such that f = a + r w/ a in A, r "minimal"
RingElement % Subring := (f, A) -> (
    pres := A#"PresRing";
    if ring f === ambient A then(
	f = (pres#"InclusionBase")(f);
	) else if ring f =!= pres#"TensorRing" then(
	error "The RingElement f must be in either TensorRing or ambient A.";
	);
    ans := (internalSubduction(A, f));
    ans
    );

-- f // Subring is always going to be inside of the subalgebra, hence the output
-- should be in the upper variables of TensorRing.
-- NOTE: If you want to compute FullSub(f//A), it is a lot faster to compute f-(f%A).
-- input: f in ambient A or TensorRing of A.
-- output: a in TensorRing of A such that f = a + r w/ a in A, r "minimal."
RingElement // Subring := (f, A) -> (
    pres := A#"PresRing";
    tense := pres#"TensorRing";
    if ring f === ambient A then(
	f = (pres#"InclusionBase")(f);
	) else if ring f =!= tense then(
	error "The RingElement f must be in either the TensorRing or ambient ring of A.";
	);
    result := f - (f % A);
    I := pres#"LiftedPres";
    result % I
    );

-- Sends each entry e to e%A
Matrix % Subring := (M, A) -> (
    pres := A#"PresRing";
    ents := for i from 0 to numrows M - 1 list(
	for j from 0 to numcols M - 1 list(M_(i,j) % A)
	);
    matrix(pres#"TensorRing", ents)
    );

-- Sends each entry e to e//A
Matrix // Subring := (M, A) -> (
    pres := A#"PresRing";
    ents := for i from 0 to numrows M - 1 list(
	for j from 0 to numcols M - 1 list(M_(i,j) // A)
	);
    matrix(pres#"TensorRing", ents)
    );

-- Returns the tensor ring because the function ambient returns the ambient ring.
ring Subring := A -> (
A#"PresRing"#"TensorRing"
);

end---Michael

end-- Old classes.m2

export {
    "Subring",
    "subring",
    "PresRing",
    "makePresRing",
    "VarBaseName"
    }


-- Returns M with all constant entries deleted.
deleteConstants := M -> (
    L := first entries M; 
    L = select(L, gen -> not isConstant gen);
    matrix({L})
    );


Subring = new Type of HashTable
subring = method(Options => {VarBaseName => "p"})
subring Matrix := opts -> M -> (
    R := ring M;
    
    M = deleteConstants M;
    
    if zero M then (
	error "Cannot construct an empty subring.";
	);
   
    cTable := new CacheTable from{
	SubalgComputations => new MutableHashTable from {},
	SagbiGens => matrix(R, {{}}),
	SagbiDegrees => {},
	SagbiDone => false
	}; 
    new Subring from {
    	"AmbientRing" => R,
    	"Generators" => M,
	-- The PresRing of a Subring instance is immutable because the generators are immutable.
	"PresRing" => makePresRing(opts, R, M),
	"isSagbi" => false,
	"isPartialSagbi" => false,
	"partialDegree" => 0,
	cache => cTable
	}    
    )
subring List := opts -> L -> subring(opts, matrix{L})

gens Subring := o -> A -> A#"Generators"
numgens Subring := A -> numcols gens A
ambient Subring := A -> A#"AmbientRing"
net Subring := A -> "subring of " | toString(ambient A)

-- This type is compatible with internal maps that are generated in the Sagbi algorithm.
-- Originally, this was stored directly in the cache of an instance of Subring. 
-- The problem with that solution is there is a need to use these maps outside of the Sagbi algorithm computations.
-- Also, the cache should not be used in a way that causes side effects.
PresRing = new Type of HashTable

net PresRing := pres -> (    
    tense := pres#"TensorRing";
    A := numcols vars tense;
    B := numcols selectInSubring(1, vars tense);
    "PresRing instance ("|toString(B)|" generators in "|toString(A-B)|" variables)"
    )

-- gensR are elements of R generating some subalgebra.
-- R is a polynomial ring.
makePresRing = method(TypicalValue => PresRing, Options => {VarBaseName => "p"})  
makePresRing(Ring, Matrix) := opts -> (R, gensR) -> ( 
    if(R =!= ring(gensR)) then(
	error "The generators of the subalgebra must be in the ring R.";
	);
    makePresRing(opts, R, first entries gensR)
    );
  
makePresRing(Ring, List) := opts -> (R, gensR) ->( 
    gensR = sort gensR;
    
    if(ring(matrix({gensR})) =!= R) then(
	error "The generators of the subalgebra must be in the ring R.";
	);
    
    ambR := R;
    nBaseGens := numgens ambR;
    nSubalgGens := length gensR;
    
    -- Create a ring with combined generators of base and subalgebra.  
    MonoidAmbient := monoid ambR;
    CoeffField := coefficientRing ambR;
    
    -- The degrees of generators are set so that the SyzygyIdeal is homogeneous.
    -- (This property is important for subrings of quotient rings. Note that it isn't guarenteed currently
    -- when the order does not agree with the grading on the lead term.)
    newOrder := prepend(Eliminate nBaseGens, MonoidAmbient.Options.MonomialOrder);
        
    NewVariables := monoid[        
	VariableBaseName=> opts.VarBaseName,
	Variables=>nBaseGens+nSubalgGens,
	Degrees=>join(degrees source vars ambR, degrees source matrix({gensR})),
        MonomialOrder => newOrder
	];
        
    TensorRing := CoeffField NewVariables;
    
    assert(heft TensorRing =!= null);	    
        
    ProjectionInclusion := map(TensorRing, TensorRing,
        (matrix {toList(nBaseGens:0_(TensorRing))}) |
	(vars TensorRing)_{nBaseGens .. nBaseGens+nSubalgGens-1});
    
    ProjectionBase := map(ambR, TensorRing,
        (vars ambR) | matrix {toList(nSubalgGens:0_(ambR))});
    
    InclusionBase := map(TensorRing, ambR,
        (vars TensorRing)_{0..nBaseGens-1});
    
    Substitution := map(TensorRing, TensorRing,
        (vars TensorRing)_{0..nBaseGens-1} | InclusionBase(matrix({gensR})));
    	
    SyzygyIdeal := ideal(
        (vars TensorRing)_{nBaseGens..nBaseGens+nSubalgGens-1}-
	InclusionBase(leadTerm matrix({gensR})));
    
    submap := Substitution;
    genVars := (vars TensorRing)_{numgens ambient R..numgens TensorRing-1};
    liftedPres := ideal(submap(genVars) - genVars);
    FullSub := ProjectionBase*Substitution;
     
    ht := new HashTable from {
	"TensorRing" => TensorRing,
	"ProjectionInclusion" => ProjectionInclusion,
	"ProjectionBase" => ProjectionBase,
	"InclusionBase" => InclusionBase,
	"Substitution" => Substitution,
	"FullSub" => FullSub,
	"SyzygyIdeal" => SyzygyIdeal,
	"LiftedPres" => liftedPres
	};

    new PresRing from ht
    );

-- The reason why this is implemented is to prevent incorrect usage of the makePresRing constructor.
-- A subring is already associated with an immutable PresRing instance which should be used instead of
-- constructing a new instance. Don't use makePresRing when you can use the function subring.   
makePresRing(Subring) := opts -> subR -> (
    subR#"PresRing"
    );

end--

