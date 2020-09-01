pathToPackage = "./SubalgebraBases.m2"
installPackage(
    "SubalgebraBases",
    FileName=>pathToPackage,
    RunExamples => false,
    RerunExamples => false
    )
debug Core;

--setRandomSeed("randseed1");
moTest := (subR, n, maxDeg) -> (
    subMap := subR#"PresRing"#"Substitution";
    fullSub := subR#"PresRing"#"FullSub";
    incBase := subR#"PresRing"#"InclusionBase";

    print("-------------------------------------------"); 
    print("-- moTest:");

    for i from 1 to n do(
	
    	testElt :=  sum for deg from 0 to maxDeg list(
	    random(deg, ambient subR)
	    )//subR;
    	print("-------------------------------------------");
    	-- Possible ways to choose a lead term.
    	A := leadTerm testElt;	 
    	B := leadTerm(subR, testElt);
    	C := leadTerm subMap testElt;
    	D := leadTerm fullSub testElt;
	
    	print("LHS:");
    	print(leadTerm fullSub A);
    	print("RHS:");
    	print(leadTerm fullSub B);
	
	-- MO of the upper variables == MO induced by substitution map. 
    	--assert(leadTerm fullSub A == leadTerm fullSub B);
	
	-- If two terms of testElt have the same lead term under the substitution map
	-- and that term happens to be D, this will fail if they happen to cancel out.
	-- The chances of this happening seem to be very low, but we could cherry pick 
	-- examples using the function toricSyz.
	assert(leadTerm fullSub B == D);
    	-- MO of the lower variables == MO of the ambient ring.
    	assert(fullSub C == D);
    	);
    print("-------------------------------------------"); 
    print("-- End moTest"); 
    print("-------------------------------------------"); 
    );


-- The reason I use a finite field is because that's what the original programmers used
-- when they wrote the tests 20 years ago. I assume the reason they did this was so that
-- they wouldn't accidentally write code that relies on an infinite field.  
kk = ZZ/101


-- This function is from the tests, but here it is slightly modified.
genericminors = (minorsize,rowsize,colsize) -> (
    -- (minorsize) by (minorsize) minors of a generic (rowsize) by (colsize) matrix
    matdim := rowsize * colsize;
    x = symbol x;
    R := kk[x_1 .. x_matdim];
    Temp := genericMatrix(R,x_1,rowsize,colsize);
    print(Temp);
    gens minors(minorsize,Temp)
    );

print("toricSyz test (Sturmfels example 11.19)");
t = symbol t;
R = kk[symbol t_1, symbol t_2]
subR = sagbi subring matrix(R, {{t_1^2, t_1*t_2, t_2^2}});
M = matrix(R, {{t_1^2, t_1*t_2}});
M = subR#"PresRing"#"InclusionBase"(M);
ans = matrix(R,{{-t_2^2, t_1*t_2}, {-t_1*t_2, t_1^2}});
--ans = subR#"PresRing"#"InclusionBase"(ans);
time assert (toricSyz(subR, M) == ans);

------------------------------------------
------------------------------------------
-- Sturmfels example 11.22
------------------------------------------
------------------------------------------
i = 2;
R = kk[symbol t_1, symbol t_2, symbol t_3];
A := {t_1*t_2*t_3,
      t_1^2*t_2,
      t_1*t_2^2,
      t_1^2*t_3,
      t_1*t_3^2,
      t_2^2*t_3,
      t_2*t_3^2};
G := matrix {{t_1^(2*i)*t_2^(2*i)*t_3^(2*i), t_1^((3*i)+2)*t_2*t_3^(3*i)}}
subR = sagbi subring A;
assert((set first entries gens subR) === (set A)); 
tsyz := toricSyz(subR, G);
assert(tsyz * (transpose G) == 0);

ans1 = mingensSubring(subR, tsyz);
ans2 = extrinsicBuchberger(subR, tsyz);

-- Subroutine 11.24 is guarenteed to return a (non-reduced) GB but subroutine 11.18 is only 
-- guarenteed to return some set of generators. So, it may be a coincidence that ans1 and ans2
-- coincide for all values of i that I have tried.
-- If tsyz generates syz(G), then it generates in(syz G) because in(syz G) = syz(G)?
assert(ans1 == ans2);

-*
print("i="|toString(i));
print("num syzygies:");
print(numrows ans1);
print("expected of degree "|toString(i+1)|":");
print((2*i)+2);
*-
-- the degree of each row is 3*(i+1) because all the generators have degree 3
degs := apply(entries (ans1//subR), row -> degree sum row)
assert(length (positions(degs, d -> first d == 3*(i+1))) == (2*i)+2);

------------------------------------------
------------------------------------------
-- Sturmfels example 11.25 
------------------------------------------
------------------------------------------

print("Sturmfels chapter 11 example 11.25.");
M = genericminors(2, 2, 5)

-- This monomial order is such that all the 2x2 determinants ab-cd satisfy ab > cd (I.e., the
-- positive term comes first.)
BaseRing := kk[x_1..x_10, MonomialOrder => {Weights=> {1,1,2,4,3,9,4,16,5,25}}]
N = sub(M, BaseRing);
subR := sagbi subring(N);
pres := subR#"PresRing";
tense = pres#"TensorRing";

-- The variables of the ambient ring are the variables of a generic matrix.
-- They are structured as follows, where the entries are subscripts of x,
-- the variable of the ambient ring:
--
-- | 1 3 5 7 9  |
-- | 2 4 6 8 10 |
--
-- The generators are the binomial(5,2)=10 2x2 determinants:
--
-- p_10 = [12]
-- p_11 = [13]
-- p_12 = [23]
-- p_13 = [14]
-- p_14 = [24]
-- p_15 = [34]
-- p_16 = [15]
-- p_17 = [25]
-- p_18 = [35]
-- p_19 = [45]

g1 = ((p_10-p_12)*(p_12-p_15))_tense;
g2 = ((p_11 + p_13 + p_16)*(p_16 + p_17 + p_18))_tense
G = matrix({{g1, g2}})
ltG = leadTerm pres#"Substitution" G;
-- g_3 in Sturmfels.
f = ((p_16*p_18*g1) - (p_12*p_15*g2))_tense

gensSyz := toricSyz(subR, ltG);

-- The result of toricSyz is really a KA module. 
KA = sagbi subring(leadTerm gens subR);
tenseKA = KA#"PresRing"#"TensorRing";

-- ans1 contains ans2. 
ans1 = extrinsicBuchberger(KA, gensSyz);
ans2 = mingensSubring(KA, gensSyz);


------------------------------------------------------------------------------------
-- Screw invariants
------------------------------------------------------------------------------------

-- Invariants the rotation subgroup of SE(3) (see benchmark.m2 for more information)
-- Notice how we need an elimination order on the AMBIENT ring, not the tensor ring.  
R = QQ[(t_1..t_3)|(w_1..w_3)|(v_1..v_3), MonomialOrder => {Eliminate 3, Lex}];

M =  transpose genericMatrix(R, first gens R, 3, 3)
A = (M*(transpose M))-(id_(source M))
B = (det M) - 1 
eqns := (flatten entries A)|{B}
sag1 = sagbi eqns

-- Invariants of the translation subgroup of SE(3) (see benchmark.m2 for more information)
G = vars R;
t = transpose G_{0..2}
w = transpose G_{3..5}
v = transpose G_{6..8}
plucker := w||v
T = genericSkewMatrix(R, G_(0,0), 3);
zed = T-T;  
I = id_(source zed)
translation := matrix({{I, zed},{T, I}})*plucker
sag2 = sagbi transpose translation;

-- This normal form calculation is computing an intersection of subrings.
ans = sag2#"PresRing"#"FullSub"((gens sag1)//sag2)
-- The sagbi call removes the constants/zeros and verifies that it's a sagbi basis. 
-- selectInSubring computes an intersection with a polynomial ring. 
ans = selectInSubring(1, gens sagbi ans)

error "stop"
------------------------------------------------------------------------------------
------------------------------------------------------------------------------------

------------------------------------------
------------------------------------------
-- Example 1, Stillman and Tsai 
-- Falsely succeeds, can we do better?
------------------------------------------
------------------------------------------
gndR = kk[x,y, MonomialOrder => Lex]
I = ideal(x^2 - x*y)
Q = gndR/I
subR = sagbi(subring {x}, PrintLevel => 2)
elt = ((gens subR)_(0,0))^1

J = gens subR#"PresRing"#"SyzygyIdeal"

for j from 0 to (numcols J)-1 do(
    pj := J_(0,j);
    
    --error "stop";
    );

G = lift(gens subR, ambient ambient subR)
subR2 = subring G;
extra = subR2#"PresRing"#"FullSub"((presentation Q)//subR2)
newElts = sub(extra, Q)

subR = sagbi(subring ((gens subR)|newElts), PrintLevel => 0)

error "stop";

------------------------------------------
------------------------------------------
-- attempt to do all of SE(3) at once
------------------------------------------
------------------------------------------
gndR = QQ[(x_1..x_9)|(t_1..t_3)|(w_1..w_3)|(v_1..v_3), MonomialOrder => GRevLex];
G = vars gndR;
x = transpose G_{0..8}
t = transpose G_{9..11}
w = transpose G_{12..14}
v = transpose G_{15..17}
plucker := w||v

T = genericSkewMatrix(gndR, G_(0,8), 3);
zed = T-T;  
I = id_(source zed)

R = genericMatrix(gndR, G_(0,0), 3, 3);
A = (R*(transpose R))-I
B = (det R) - 1 
eqns = (flatten entries A)|{B}

translation := matrix({{I, zed},{T, I}})*plucker
rotation := matrix({{R, zed},{zed, R}})*plucker

rotation = (transpose rotation) | (matrix {eqns});
sag2 = sagbi(rotation,PrintLevel=> 1);

error "stop";

------------------------------------------
------------------------------------------
-- intrinsicBuchberger test
------------------------------------------
------------------------------------------
m1 := map(tenseSagbi, tense, gens tenseSagbi);
G = m1 G;

result = intrinsicBuchberger(subRSagbi, G)

result = result // subRSagbi;
h = intrinsicReduce(subRSagbi, result, f);

ltH = leadTerm(subRSagbi,h);
ltResult = leadTerm(subRSagbi, result);
print("is h zero? - "|toString(h == 0));

------------------------------------------
------------------------------------------
-- Normal form demo
------------------------------------------
------------------------------------------
 
f = f_tense;
print("-- f:");
print(f);
print("-- f % subR:");
output1 := f % subR;
print(output1);
print("-- f // subR:");
output2 := f // subR;
print(output2);

-- Notice how the flags are set when sagbi fails.
R = kk[x, y]
F = matrix{{x, x*y-y^2, x*y^2}}
subR = sagbi(F,Limit=>30) 
peek subR

-- Notice how the flags are set when sagbi succeeds.
R = kk[y, x]
F = matrix{{x, x*y-y^2, x*y^2}}
subR = sagbi(F) 
peek subR

error "stop"