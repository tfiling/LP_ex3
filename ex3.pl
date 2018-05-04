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
% maps each variable in Vars into binary representatin in the form of Var = [Lsbit, Bit2, Bit4, ....]
% when decoding we will have values in the bit varialbes allowing us to assign the Var variable with number
% the Var assignemnt will reflect in instance and therefor in the solution

map_solution_variables([Sum = Vars | Rest], Map) :-
    dec2bin(Sum, BinSum),   % sum binary representation size indicates the max lengeth of each variable
    lengeth(BinSum, Lengeth),
    map_binary_variables(Vars, Map, Lengeth, []),
    map_solution_variables(Rest, Map).

map_solution_variables([], []) :-

% current variable was not mapped already - map it!
map_binary_variables([Var | RestVars], [Var = BitVector | RestMap], Lengeth, AlreadyMapped) :-
    \member(Var = _, AlreadyMapped),
    lengeth(BitVector, Lengeth),    % Length bits 
    append([Var = BitVector], AlreadyMapped, AlreadyMapped1),
    map_binary_variables(RestVars, RestMap, Lengeth, AlreadyMapped1).

% current variable was mapped already - continue to the next one
map_binary_variables([Var | RestVars], [Var = BitVector | RestMap], Lengeth, AlreadyMapped) :-
    member(Var = _, AlreadyMapped),
    map_binary_variables(RestVars, RestMap, Lengeth, AlreadyMapped).


map_binary_variables([], [], _).

%%%%%%%%%%%%%%%%%%%%%%%%



%%%%%%%%%%%%%%%%%%%%%%%%

kakuroEncode(Instance,Map,CNF):-
    map_solution_variables(Instance, Map),
    kakuroEncode_continued(Instance,Map,CNF-[]).

%%%%%%%%%%%%%%%%%%%%%%%%
kakuroEncode_continued(Instance,Map,[[B]|CNF1]-CNF3):-
    map_integers_to_bit_vectors(Instance,Map),
    orders_to_CNF(Map,B,CNF1-CNF2),            % validates that every bit vector must be as unary ordered
    previous_tasks(Instance,Map,CNF2-CNF3).      % get the CNFs of the sum_equals and all_diff of the previous tasks    
    
% creates the mapping that was asked in the above task	
map_integers_to_bit_vectors([ClueSum=Block|RestInstance],Map):-
    accumulate_bit_vectors([ClueSum=Block|RestInstance], Blocks-[]),
    sort(Blocks, BlocksNoDuplicates),
    map(BlocksNoDuplicates,Map).

% accumulate all the blocks to one big block
accumulate_bit_vectors([], Blocks-Blocks).
accumulate_bit_vectors([_=Block|RestInstance], Blocks1-Blocks3):-
    list_to_continued_list(Block, Blocks1-Blocks2),
    accumulate_bit_vectors(RestInstance, Blocks2-Blocks3).

map([],[]).
map([Var|RestBlock],[Var=Bvs|RestMap]):-
    length(Bvs, 8),
    map(RestBlock,RestMap).
    
% gets the Cnf clauses of the bit vectors
orders_to_cnf([],_,Cnf-Cnf).
orders_to_cnf([_=Bv|RestMap],B,Cnf1-Cnf3):-
    order_to_cnf(Bv,B,Cnf1-Cnf2),
    orders_to_cnf(RestMap,B,Cnf2-Cnf3).
    
% gets the Cnf clauses of the bit vector
order_to_cnf([_],_,Cnf-Cnf).
order_to_cnf([X,Y|RestBv],B,[[B,Y],[-B,X,-Y],[B,-X,-Y]|RestCnf1]-Cnf2):-
    order_to_cnf([Y|RestBv],B,RestCnf1-Cnf2).


% gets the cnf of sum equals for all the blocks
previous_tasks([],_,Cnf-Cnf).
previous_tasks([ClueSum=Block|RestInstance],Map,Cnf1-Cnf4):-
    get_bit_vectors_by_vars(Block,Map,Numbers),
    sum_equals(ClueSum,Numbers,SumCnf),
    list_to_continued_list(SumCnf,Cnf1-Cnf2),
    all_diff(Numbers, AllDiffCnf),
    list_to_continued_list(AllDiffCnf,Cnf2-Cnf3),
    previous_tasks(RestInstance,Map,Cnf3-Cnf4).
   
% given some var, returns his bit vector from the map
get_bit_vectors_by_vars([],_,[]).
get_bit_vectors_by_vars([Var|RestVars],Map,[Number|RestNumbers]):-
    get_bit_vector_by_var(Var,Map,Number),
    get_bit_vectors_by_vars(RestVars,Map,RestNumbers).
    
% also adds 1 at the start so it will be completelly 
get_bit_vector_by_var(Var1,[Var2=Bvs|_],[1|Bvs]):-
    Var1 == Var2.
get_bit_vector_by_var(Var1,[Var2=_|RestMap],FullBvs):-
    Var1 \== Var2,
    get_bit_vector_by_var(Var1, RestMap, FullBvs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Task 5 - TODO gal

/* Task 7 */
kakuroDecode([],[]).
kakuroDecode([Var=Bvs|RestMap],[Var=Num|RestSolution]):-
	bit_vector_to_number([1|Bvs],Num),
    kakuroDecode(RestMap,RestSolution).

bit_vector_to_number([],0).
bit_vector_to_number([-1|_],0).	
bit_vector_to_number([1|RestBvs],Num):-
	bit_vector_to_number(RestBvs,Num1),
	Num is Num1 + 1.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Task 6 - TODO gal

/* Task 8 */
kakuroSolve(Instance, Solution):-
	kakuroEncode(Instance,Map,Cnf),
	sat(Cnf),
	kakuroDecode(Map,MapSolution),
	kakuroBuildSolution(Instance, MapSolution, Solution),
	kakuroVerify(Solution).


/* Tools */ % TODO - GAL
% turns list to continued list
list_to_continued_list([],List-List).
list_to_continued_list([El|RestList],[El|List1]-List2):-
    list_to_continued_list(RestList,List1-List2).