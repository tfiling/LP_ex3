% user:file_search_path(sat, '../satsolver').
% :- use_module(sat(satsolver)).
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
/* Part A */

/*task 1*/
%sum_equals(+,+,-)
sum_equals(Sum,Numbers,CNF):-
    addVectors(Numbers, CNF, ResList), !,
    writeln(ResList),
    my_flatten(ResList, LastVector),
    dec2bin(Sum, BinSum),
    reverse(BinSum, NewBinSum),
    length(LastVector, N),
    length(NewBinSum, M),
    N > M,
    abs(N-M, Val),
    length(Block, Val),
    paddZero(Block),
    append(NewBinSum,Block, BinSumFinal),
    zeroToMinusOne(BinSumFinal, BinSumMinus),
    mapVals(BinSumMinus, LastVector),
    zeroToMinusOne(LastVector, FinalLastVector).
    

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
    add(X,NewY,0,Sum1, CNF1),  
    addVectors([Sum1], CNF2, ResList),
    append(CNF1, CNF2, CNF).

addVectors([X,Y], CNF, [Sum1|ResList]):-
    length(X, N),
    length(Y, M),
    N == M, 
    abs(N-M, Val),
    length(Block, Val),
    paddZero(Block),
    append(Y,Block, NewY),  
    add(X,NewY,0,Sum1, CNF1),  
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
    add(X,NewY,0,Sum1, CNF1),  
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
fullAdder(I1, I2, C_in, S, C_out, CNF):-
    %calc Next C
    CNF = [[I1,I2,C_in,-S], [I1, I2, -C_in, S], [I1,-I2,C_in,S],[I1,-I2,-C_in,-S],
    [-S,I2,C_in,S], [-I1,I2,-C_in,-S],[-I1,-I2,C_in,-S],[-I1,-I2,-C_in,S]].
    %xor(I1, I2, X), 
    % and( I1, I2, A1), and( X, C_in, A2), or(A1, A2, C_out),
   
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

% var_to_bitvector(Var+, Map+, BitVector-)
var_to_bitvector(Var, [Var = BitVector | _], BitVector).

var_to_bitvector(Var, [Var2 = _ | RestVars], BitVector) :-
    Var \= Var2,
    var_to_bitvector(Var, RestVars, BitVector).

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
    generate_sol_correctness_cnf(Instance, Map, CorrectnessCNF).

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
