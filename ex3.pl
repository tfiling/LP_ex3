user:file_search_path(sat, '../satsolver').
:- use_module(sat(satsolver)).
% :- use_module(naive_sat).
/* helper funcs */
and(A,B) :- A,B.
or(A,B) :- A;B.
nand(A,B) :- not(and(A,B)).
nor(A,B) :- not(or(A,B)).
xor(A,B) :- or(A,B), nand(A,B).

or( 0, 0, 0).
or( 0, 1, 1).
or( 1, 0, 1).
or( 1, 1, 1).

xor( 0, 0, 0).
xor( 0, 1, 1).
xor( 1, 0, 1).
xor( 1, 1, 0).

and( 0, 0, 0).
and( 0, 1, 0).
and( 1, 0, 0).
and( 1, 1, 1).

dec2bin(0,[0]).
dec2bin(1,[1]).
dec2bin(N,L):- 
    N > 1,
    X is N mod 2,
    Y is N // 2,  
    dec2bin(Y,L1),
    L = [X|L1].

my_flatten([], []).
my_flatten([A|B],L) :- 
    my_flatten(B,B1), !, 
    append(A,B1,L).
my_flatten([A|B],[A|B1]) :- 
    my_flatten(B,B1).

zeroToMinusOne([], []).
zeroToMinusOne([0|Rest], [-1|RestNew]):-
        zeroToMinusOne(Rest, RestNew).
zeroToMinusOne([1|Rest], [1|RestNew]):-
        zeroToMinusOne(Rest, RestNew).
zeroToMinusOne([-1|Rest], [-1|RestNew]):-
        zeroToMinusOne(Rest, RestNew).

fixDoubleMinus([],[]).
fixDoubleMinus([List | RestCNF], [NewCNF | RestNewCNF]):-
    fixDoubleMinusH2(List, NewCNF),
    fixDoubleMinus(RestCNF, RestNewCNF).

fixDoubleMinusH2([H | RestCNF], [NewH | RestNewCNF]) :-
    fixDoubleMinusH(H, NewH),
    fixDoubleMinusH2(RestCNF, RestNewCNF).
fixDoubleMinusH2([], []).

fixDoubleMinusH(- -1, 1):- !.
fixDoubleMinusH(- -X1, X) :-
    nonvar(X1),
    fixDoubleMinusH(X1, X).
fixDoubleMinusH(-1, -1):- !.
fixDoubleMinusH(- -X1, X):- 
    var(X1),
    fixDoubleMinusH(X1, X).
fixDoubleMinusH(-X, -X):-
    var(X),
    !.

fixDoubleMinusH(X, X):-
    var(X),
    !,
    fixDoubleMinusH(CNF, NewCNF).

/* Part A */

/*task 1*/
%sum_equals(+,+,-)
sum_equals(Sum,Numbers,CNF):-
    addVectors(Numbers, CNF, [LastVector]), !,  % ResList is the sum of Numbers in binary representaion, returned wrapped in list
    writeln('Res List is' + LastVector),        % unwrapped the list without using myflatten
    % my_flatten(ResList, LastVector),          % TODO gal make sure that RestList can only be bit vercor wrapped in a list
    dec2bin(Sum, BinSum),
    reverse(BinSum, LsbBinSum),
    setLastVectorValues(LsbBinSum, LastVector), % TODO gal what if len(LsbBinSum) > len(LastVector)? this will mean for sure that the CNF will fail
    writeln('LastVector = ' + LastVector),
    zeroToMinusOne(BinSumFinal, BinSumMinus),
    writeln('CNF before'+CNF),
    writeln(''),
    mapVals(BinSumMinus, LastVector),
    zeroToMinusOne(LastVector, FinalLastVector),
    writeln('CNF after'+CNF),
    writeln(''),
    fixDoubleMinus(CNF, NewCNF),
    writeln('NewCNF after Fixing'+NewCNF),
    sat(CNF),
    writeln('AfterSolver' + CNF).
    

mapVals([],[]).
mapVals([B|BinSumMinus], [X|LastVector]):-
    X = B,
    mapVals(BinSumMinus, LastVector).
   

    
    % sat(CNF).

%addVectors (+,-)
addVectors([_],[],[]).

addVectors([X,Y], CNF, [Sum1|ResList]):-
    length(X, N),
    length(Y, M),
    N > M, 
    abs(N-M, Val),
    length(Block, Val),
    paddZero(Block),
    append(Y,Block, NewY),  
    add(X,NewY,-1,Sum1, CNF1), 
    addVectors([Sum1], CNF2, ResList),
    append(CNF1, CNF2, CNF).

addVectors([X,Y], CNF, [Sum1|ResList]):-
    length(X, N),
    length(Y, M),
    N == M,   
    add(X,Y,-1,Sum1, CNF1),
    %writeln('Sum1 is' + Sum1),
    addVectors([Sum1], CNF2, ResList),
    append(CNF1, CNF2, CNF).

addVectors([X,Y|Numbers], CNF, ResList):-
    length(X, N),
    length(Y, M),
    N > M, 
    abs(N-M, Val),
    length(Block, Val),
    paddZero(Block),
    append(Y,Block, NewY),  
    add(X,NewY,-1,Sum1, CNF1),  
    addVectors([Sum1|Numbers], CNF2, ResList),
    append(CNF1, CNF2, CNF).

addVectors([X,Y|Numbers], CNF, ResList):-
    length(X, N),
    length(Y, M),
    N==M,
    add(X,Y,-1,Sum1,CNF1),
    addVectors([Sum1|Numbers], CNF2, ResList),
    append(CNF1, CNF2, CNF).

    
paddZero([]).    
paddZero([0|Rest]):- 
    paddZero(Rest).


% if_then_else(Condition, Action1, Action2) :- 
%     Condition, !, Action1.  
% if_then_else(Condition, Action1, Action2) :- 
%     Action2.

%we did in class, SUM of 2 Bit Vectors
% add(+, +, -, -, -)
add([], [], C, [C], []).

add([X|Xs], [Y|Ys], C, [S|Sum], CNF):-       
    fullAdder(X,Y,C,S,NextC, CNF1),
    add(Xs, Ys, NextC, Sum, CNF2),
    append(CNF1, CNF2, CNF).

%we did in class, SUM of 2 Bits 
%fullAdder(+,+,+,-,-, -)
% fullAdder(I1, I2, C_in, S, C_out, CNF):-
%     %calc Next C
%     CNF = [[I1,I2,C_in,-S], [I1, I2, -C_in, S], [I1,-I2,C_in,S],[I1,-I2,-C_in,-S],
%     [-S,I2,C_in,S], [-I1,I2,-C_in,-S],[-I1,-I2,C_in,-S],[-I1,-I2,-C_in,S]].
%     %xor(I1, I2, X), 
%     % and( I1, I2, A1), and( X, C_in, A2), or(A1, A2, C_out),
    
fullAdder(X, Y, C, Sum, Carry, Cnf) :-
    Cnf = [[X,Y,C,Sum,Carry],
    [X,Y,C,Sum,-Carry],
    [X,Y,C,-Sum,Carry],
    [X,Y,C,-Sum,-Carry],
    [X,Y,-C,Sum,Carry],
    [X,Y,-C,Sum,-Carry],
    [X,Y,-C,-Sum,-Carry],
    [X,-Y,C,Sum,Carry],
    [X,-Y,C,Sum,-Carry],
    [X,-Y,C,-Sum,-Carry],
    [X,-Y,-C,Sum,Carry],
    [X,-Y,-C,-Sum,Carry],
    [X,-Y,-C,-Sum,-Carry],
    [-X,Y,C,Sum,Carry],
    [-X,Y,C,Sum,-Carry],
    [-X,Y,C,-Sum,-Carry],
    [-X,Y,-C,Sum,Carry],
    [-X,Y,-C,-Sum,-Carry],
    [-X,-Y,C,Sum,Carry],
    [-X,-Y,C,-Sum,-Carry],
    [-X,-Y,-C,Sum,-Carry],
    [-X,-Y,-C,-Sum,Carry]].


% setLastVectorValues(LsbBinSum+, LastVector+)
% will set the values for the variables held in  LastVector
% the extra bits not mentioned in LsbBinSum will be 0s
% setLastVectorValues(LsbBinSum, LastVector) :-
%     length(LsbBinSum, Len),
%     length(LastVector, Len),
%     LastVector = LsbBinSum.

setLastVectorValues(LsbBinSum, LastVector) :-
    length(LastVector, LastVectorLen),
    length(LsbBinSum, LsbBinSumLen),
    LastVectorLen >= LsbBinSumLen,
    RequiredPaddingZeros is LastVectorLen - LsbBinSumLen,
    length(PaddingBlock, RequiredPaddingZeros),
    paddZero(PaddingBlock),
    append(LsbBinSum, PaddingBlock, LastVector).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Task 2 - all_diff(Numbers+, CNF-)

all_diff([X1, X2 | Rest], CNF) :-
    diff(X1, X2, CNF1),
    all_diff([X1 | Rest], CNF2),
    all_diff([X2 | Rest], CNF3),
    append([CNF1, CNF2, CNF3], CNF).

all_diff([_], []).
all_diff([], []).

% note -    preparing to the exam we implemented this one for unary representation
%           the below implementation based on this implementation
diff(Xs,Ys,[[B]|CNF]):-
    diff(B, Xs, Ys, CNF).

diff(B, [X], [Y], CNF):-
        CNF = [[-B, -X, -Y], [-B, X, Y], [B, -X, Y], [B, X, -Y]].

diff(B, [X | Xs], [Y | Ys], CNF):-
    % CNF1 = [[-B, -X, -Y, B1], [-B, X, Y, B1], [B, -X, Y], [B, X, -Y], [B, -B1]], % TODO gal - cosider using the origianl CNF
    CNF1 = [[-B, -X, -Y, B1], [-B, X, Y, B1], [B, -X, Y], [B, X, -Y], [B, X, Y, -B1], [B, -X, -Y, -B1]],
    diff(B1, Xs, Ys, CNF2),
    append(CNF1, CNF2, CNF).

diff(_, [], [], []).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% part 2 - Kakuro
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Task 3

 kakuroVerify([H | Rest]) :-
    verify_assignment(H),
    kakuroVerify(Rest).

kakuroVerify([]).

verify_assignment(Sum = Assignments) :-
    is_sum(Sum, Assignments),
    all_numbers_diff(Assignments).

is_sum(Sum, [H | T]) :-
    Sum1 is Sum - H,
    is_sum(Sum1, T).

is_sum(0, []).

all_numbers_diff([X1, X2 | Rest]) :-
    X1 \= X2,
    all_numbers_diff([X1 | Rest]),
    all_numbers_diff([X2 | Rest]).

all_numbers_diff([_]).
all_numbers_diff([]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Task 4 - TODO GAL

%%%%%%%%%%%%%%%%%%%%%%%%
%%% Utils

% var_list_to_bitvector_list(Vars+, Map+, BitVectors-)
var_list_to_bitvector_list([Var | RestVars], Map, [BitVector | RestBitVectors]) :-
    var_to_bitvector(Var, Map, BitVector),
    var_list_to_bitvector_list(RestVars, Map, RestBitVectors).

var_list_to_bitvector_list([], _, []).

% var_to_bitvector(Var+, Map+, BitVector-) - finds Var in Map and returns it's bitvector.
var_to_bitvector(Var, [Var = BitVector | _], BitVector).    % found Var, stop looking

var_to_bitvector(Var, [Var2 = _ | RestVars], BitVector) :-  % first mapped variable is not the one we are looking for, keep looking
    Var \= Var2,
    var_to_bitvector(Var, RestVars, BitVector).

% no need for halt predicate, we expect it to fail if Var is not mapped

%%%%%%%%%%%%%%%%%%%%%%%%
% map_solution_variables(Instance+, Map-)
% maps each variable in Vars into binary representatin in the form of Var = [Lsbit, Bit2, Bit4, ....]
% when decoding we will have values in the bit varialbes allowing us to assign the Var variable with number
% the Var assignemnt will reflect in instance and therefor in the solution

map_solution_variables([Sum = Vars | Rest], Map) :-
    dec2bin(Sum, BinSum),   % sum binary representation size indicates the max lengeth of each variable
    lengeth(BinSum, Lengeth),
    map_binary_variables(Vars, Map, Lengeth, []),
    map_solution_variables(Rest, Map).

map_solution_variables([], []).

% current variable was not mapped already - map it!
map_binary_variables([Var | RestVars], [Var = BitVector | RestMap], Lengeth, AlreadyMapped) :-
    \member(Var = _, AlreadyMapped),
    lengeth(BitVector, Lengeth),    % Length bits 
    append([Var = BitVector], AlreadyMapped, AlreadyMapped1),
    map_binary_variables(RestVars, RestMap, Lengeth, AlreadyMapped1).

% current variable was mapped already - continue to the next one
map_binary_variables([Var | RestVars], [Var = _ | RestMap], Lengeth, AlreadyMapped) :-
    member(Var = _, AlreadyMapped),
    map_binary_variables(RestVars, RestMap, Lengeth, AlreadyMapped).


map_binary_variables([], [], _).

%%%%%%%%%%%%%%%%%%%%%%%%
% generate_sol_correctness_cnf(Instance+, Map+, CorrectnessCNF-)

generate_sol_correctness_cnf([Sum = Vars | Rest], Map, CorrectnessCNF) :-
    var_list_to_bitvector_list(Vars, Map, BitVectors),
    sum_equals(Sum, BitVectors, CNF1),
    all_diff(BitVectors, CNF2),
    generate_sol_correctness_cnf(Rest, Map, RestCNF),
    append([CNF1, CNF2, RestCNF], CorrectnessCNF).

generate_sol_correctness_cnf([], _, []).


%%%%%%%%%%%%%%%%%%%%%%%%

kakuroEncode(Instance, Map, CNF):-
    map_solution_variables(Instance, Map),
    generate_sol_correctness_cnf(Instance, Map, CNF).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Task 5 - TODO 


%%%%%%%%%%%%%%%%%%%%%%%%
% bit_vector_to_int(Vector+, CurrentIncrement+, Num-)

bit_vector_to_int([1 | Rest], CurrentIncrement, Num) :-
    NextIncrement is CurrentIncrement * 2,
    bit_vector_to_int(Rest, NextIncrement, Num1),
    Num is CurrentIncrement + Num1.

% TODO gal - handle a scenario where we have ---1(unwrapping the -s)
bit_vector_to_int([-1 | Rest], CurrentIncrement, Num) :-
    NextIncrement is CurrentIncrement * 2,
    bit_vector_to_int(Rest, NextIncrement, Num).

bit_vector_to_int([], _, 0).


kakuroDecode([Var = BitVector | Rest], Solution) :-
    bit_vector_to_int(BitVector, 1, Var),
    kakuroDecode(Rest, Solution).

kakuroDecode([], []).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Task 6 - TODO gal

kakuroSolve(Instance,Solution) :-
    kakuroEncode(Instance, Map, CNF),
    sat(CNF),
    kakuroDecode(Map, Solution),
    kakuroVerify(Solution).
