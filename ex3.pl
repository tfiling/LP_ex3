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
%%% TODO REMOVE!!
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% /* Task 3 */
% sum_equals(Sum,Numbers,CNF):-
% 	join_bit_vectors(Numbers, OneBigBv),
% 	length(OneBigBv, Max),
% 	Max >= Sum,
% 	Sum >= 0,
% 	two_completence(OneBigBv, OneBigBvPadded),
% 	length(OneBigBvPadded, N),
% 	sorting_network(N, Cs-[], OneBigBvPadded, Out-[]),
% 	comparators_to_cnf(Cs, CNF),
% 	unify_number_with_bit_vector(Sum, Out).
	
% % joins all bit vectors to a single bit vector
% join_bit_vectors([],[]).
% join_bit_vectors([[]|RestBvs],Sol):-
% 	join_bit_vectors(RestBvs,Sol).
% join_bit_vectors([[Bit|RestVector]|RestBvs],[Bit|RestSol]):-
% 	join_bit_vectors([RestVector|RestBvs],RestSol).

% % the merger must work with 2^n In's, so we must add some padding in case we do not have such numbers
% two_completence(Before, After):-
% 	length(Before, N),
% 	get_top_power_of_two(N, N1, 1),
% 	two_completence_fill(Before, After, N1).
	
% % returns N1 which is the top of N and a power of two.
% get_top_power_of_two(N, N1, Temp):-
% 	N > Temp,
% 	Temp2 is Temp * 2,
% 	get_top_power_of_two(N, N1, Temp2).
% get_top_power_of_two(N, N1, Temp):-
% 	Temp >= N,
% 	N1 is Temp - N.

% % adds padding after the end of the original
% two_completence_fill([], [], 0).
% two_completence_fill([], [-1|RestAfter], N1):-
% 	N1 > 0,
% 	N2 is N1 - 1,
% 	two_completence_fill([], RestAfter, N2).
% two_completence_fill([Var|Before], [Var|After], N1):-
% 	two_completence_fill(Before, After, N1).
	
% /* NOTE: the next part is taken from the previous work - (task 3) and has been modified for our needs (it is stated in the end when it does not) */
% /*
%  * I have divided this based on the batcher even odd merge sort algorithm
%  * Phase 1 is sorting top half and bottom half of the original input recursevly
%  * Phase 2 is sorting the evens and the odds
%  * Phase 3 is sorting the couples
%  * as explained in the algorithm itself
%  */
% sorting_network(2, [comparator(In1, In2, Out1, Out2)|Cs]-Cs, [In1,In2], [Out1,Out2|Out]-Out).
% sorting_network(N, Cs1-Cs4, In, Out1-Out2):-
% 	N > 2,
% 	N1 is N / 2,
% 	% Phase 1
% 	split_list(N1, In, InFirstHalf, InSecondHalf),
% 	sorting_network(N1, Cs1-Cs2, InFirstHalf, Out3-Out4),
% 	sorting_network(N1, Cs2-Cs3, InSecondHalf, Out4-_),
% 	sorting_network_phase_2(N, Cs3-Cs4, Out3, Out1-Out2).
	
% % Phase 2 - Note: be aware of the connection we do with the first and last elements of Out.
% sorting_network_phase_2(2, [comparator(In1, In2, Out1, Out2)|Cs]-Cs, [In1,In2], [Out1,Out2|RestOut]-RestOut).
% sorting_network_phase_2(N, Cs1-Cs4, In, [ElOut|RestOut1]-Out2):-
% 	N > 2,
% 	N1 is N / 2,
% 	split_list_even_odd(In, InOdd, InEven),
% 	sorting_network_phase_2(N1, Cs1-Cs2, InOdd, [ElOut|RestOutOdd]-[]),
% 	sorting_network_phase_2(N1, Cs2-Cs3, InEven, OutEven-[]),
% 	nth1(N1,OutEven,ElLast),
% 	N2 is N - 1,
% 	nth1(N2,RestOut1,ElLast),
% 	% Phase 3
% 	split_list_even_odd([ElOut|RestOutPhase2], [ElOut|RestOutOdd], OutEven),
% 	sorting_network_phase_3(Cs3-Cs4, RestOutPhase2, RestOut1-Out2),
% 	!.
	
% sorting_network_phase_3(Cs-Cs, [_], [_|RestOut]-RestOut).
% sorting_network_phase_3([comparator(In1,In2,Out1,Out2)|RestCs]-Cs , [In1,In2|RestIn], [Out1,Out2|RestOut]-EndOut):-
% 	sorting_network_phase_3(RestCs-Cs, RestIn, RestOut-EndOut).

% % split a list to two 
% split_list(0, SecondHalf, [], SecondHalf).
% split_list(N, [El|RestList], [El|RestFirstHalf], SecondHalf):-
% 	N > 0,
% 	N1 is N - 1,
% 	split_list(N1, RestList, RestFirstHalf, SecondHalf).

% % split a list to even list and odd list
% split_list_even_odd([],[],[]).
% split_list_even_odd([El|RestList], [El|RestList1], List2):-
% 	split_list_even_odd(RestList, List2, RestList1).
	
% /* End of previous work */
	
% % returns all the comparators as cnf.
% % note: I have decided here that all the ones would be at the begining of the out vector
% comparators_to_cnf([], []).
% comparators_to_cnf([comparator(In1,In2,Out1,Out2)|Cs], [[In1,In2,-Out1],[In1,-In2,Out1],[-In1,In2,Out1],[-In1,-In2,Out1],[In1,In2,-Out2],[In1,-In2,-Out2],[-In1,In2,-Out2],[-In1,-In2,Out2]|RestCnf]):-
% 	comparators_to_cnf(Cs, RestCnf).
		
		
% % unifies a given number with bit vector, making sure the Bv is as the unary order.
% unify_number_with_bit_vector(0, []).
% unify_number_with_bit_vector(0, [-1|RestBv]):-
% 	unify_number_with_bit_vector(0, RestBv).	
% unify_number_with_bit_vector(N, [1|RestBv]):-
% 	N > 0,
% 	N1 is N - 1,
% 	unify_number_with_bit_vector(N1, RestBv).	

% /* Task 4 */
% all_diff(Numbers, Cnf):-
%     all_diff_continued(Numbers, Cnf-[]).
% all_diff_continued(Numbers, Cnf1-Cnf3):-
%     all_diff_get_bs_and_cnf(Numbers, BsMatrix, Cnf1-Cnf2),
%     transpose(BsMatrix, BsTMatrix),              
%     one_at_most_matrix(BsTMatrix,Cnf2-Cnf3).     % this line adds the sentence "one at most is allowed to be true" to the cnf
	
% % one at most for list of lists (matrix)
% one_at_most_matrix([],Perms-Perms).
% one_at_most_matrix([List|RestMatrix],Perms1-Perms3):-
%     one_at_most(List,Perms1-Perms2),
%     one_at_most_matrix(RestMatrix,Perms2-Perms3).
	
% % builds cnf when one b at most can be true
% one_at_most([_],Perms-Perms).
% one_at_most([El|RestList],Perms1-Perms3):-
%     one_at_most_build_perm(El,RestList,Perms1-Perms2),
%     one_at_most(RestList,Perms2-Perms3).
% one_at_most_build_perm(_,[],Perms-Perms).
% one_at_most_build_perm(El1,[El2|RestList],[[-El1,-El2]|Perms]-RestPerms):-
%     one_at_most_build_perm(El1,RestList,Perms-RestPerms).
    
% % convert all the numbers to cnf and B tables which indicate in bit vector of [...XY...] there is a case when X=1 and y=0,
% % if it happens, then there would be 1 at the Bs table
% all_diff_get_bs_and_cnf([],[],Cnf-Cnf).
% all_diff_get_bs_and_cnf([[X]|RestNumbers],[[B]|RestBsNumbers],[[B,-X],[-B,X]|Cnf1]-Cnf2):-
%     all_diff_get_bs_and_cnf(RestNumbers,RestBsNumbers,Cnf1-Cnf2).
% all_diff_get_bs_and_cnf([[X,Y|RestVector]|RestNumbers],[[B|RestBsVector]|RestBsNumbers],[[B,-X,Y],[-B,X],[-B,-X,-Y]|RestCnf1]-Cnf2):-
%     all_diff_get_bs_and_cnf([[Y|RestVector]|RestNumbers],[RestBsVector|RestBsNumbers],RestCnf1-Cnf2).

% % transpose a matrix, even if the size of the rows in the matrix do not match.
% transpose([], []):-!.
% transpose(Matrix, TMatrix):-
%     transpose_get_column(Matrix, MatrixWithoutCol,TMatrix-TMatrixWithoutRow),
%     transpose(MatrixWithoutCol, TMatrixWithoutRow).
% % the bit vector we have gathered is meant to be used by its columns
% transpose_get_column([],[],[[]|RestTMatrix]-RestTMatrix).
% transpose_get_column([[El]|RestMatrix], RestMatrixWithoutCol,[[El|TMatrixRow]|RestTMatrix]-RestTMatrix):-
%     length([a],1),
%     transpose_get_column(RestMatrix, RestMatrixWithoutCol,[TMatrixRow|RestTMatrix]-RestTMatrix).
% transpose_get_column([[El|Row]|RestMatrix], [Row|RestMatrixWithoutCol],[[El|TMatrixRow]|RestTMatrix]-RestTMatrix):-
%     length([a,b],2),
%     transpose_get_column(RestMatrix, RestMatrixWithoutCol,[TMatrixRow|RestTMatrix]-RestTMatrix).

   
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

%%%%%%%%%%%%%%%%%%%%%%%%
% % TODO - GAL
% kakuroEncode_continued(Instance,Map,[[B]|CNF1]-CNF3):-
%     map_integers_to_bit_vectors(Instance,Map),
%     orders_to_CNF(Map,B,CNF1-CNF2),            % validates that every bit vector must be as unary ordered
%     previous_tasks(Instance,Map,CNF2-CNF3).      % get the CNFs of the sum_equals and all_diff of the previous tasks    
    
% % creates the mapping that was asked in the above task	
% map_integers_to_bit_vectors([ClueSum=Block|RestInstance],Map):-
%     accumulate_bit_vectors([ClueSum=Block|RestInstance], Blocks-[]),
%     sort(Blocks, BlocksNoDuplicates),
%     map(BlocksNoDuplicates,Map).

% % accumulate all the blocks to one big block
% accumulate_bit_vectors([], Blocks-Blocks).
% accumulate_bit_vectors([_=Block|RestInstance], Blocks1-Blocks3):-
%     list_to_continued_list(Block, Blocks1-Blocks2),
%     accumulate_bit_vectors(RestInstance, Blocks2-Blocks3).

% map([],[]).
% map([Var|RestBlock],[Var=Bvs|RestMap]):-
%     length(Bvs, 8),
%     map(RestBlock,RestMap).
    
% % gets the Cnf clauses of the bit vectors
% orders_to_cnf([],_,Cnf-Cnf).
% orders_to_cnf([_=Bv|RestMap],B,Cnf1-Cnf3):-
%     order_to_cnf(Bv,B,Cnf1-Cnf2),
%     orders_to_cnf(RestMap,B,Cnf2-Cnf3).
    
% % gets the Cnf clauses of the bit vector
% order_to_cnf([_],_,Cnf-Cnf).
% order_to_cnf([X,Y|RestBv],B,[[B,Y],[-B,X,-Y],[B,-X,-Y]|RestCnf1]-Cnf2):-
%     order_to_cnf([Y|RestBv],B,RestCnf1-Cnf2).


% % gets the cnf of sum equals for all the blocks
% previous_tasks([],_,Cnf-Cnf).
% previous_tasks([ClueSum=Block|RestInstance],Map,Cnf1-Cnf4):-
%     get_bit_vectors_by_vars(Block,Map,Numbers),
%     sum_equals(ClueSum,Numbers,SumCnf),
%     list_to_continued_list(SumCnf,Cnf1-Cnf2),
%     all_diff(Numbers, AllDiffCnf),
%     list_to_continued_list(AllDiffCnf,Cnf2-Cnf3),
%     previous_tasks(RestInstance,Map,Cnf3-Cnf4).
   
% % given some var, returns his bit vector from the map
% get_bit_vectors_by_vars([],_,[]).
% get_bit_vectors_by_vars([Var|RestVars],Map,[Number|RestNumbers]):-
%     get_bit_vector_by_var(Var,Map,Number),
%     get_bit_vectors_by_vars(RestVars,Map,RestNumbers).
    
% % also adds 1 at the start so it will be completelly 
% get_bit_vector_by_var(Var1,[Var2=Bvs|_],[1|Bvs]):-
%     Var1 == Var2.
% get_bit_vector_by_var(Var1,[Var2=_|RestMap],FullBvs):-
%     Var1 \== Var2,
%     get_bit_vector_by_var(Var1, RestMap, FullBvs).

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

% % TODO gal
% /* Task 7 */
% kakuroDecode([],[]).
% kakuroDecode([Var=Bvs|RestMap],[Var=Num|RestSolution]):-
% 	bit_vector_to_number([1|Bvs],Num),
%     kakuroDecode(RestMap,RestSolution).

% bit_vector_to_number([],0).
% bit_vector_to_number([-1|_],0).	
% bit_vector_to_number([1|RestBvs],Num):-
% 	bit_vector_to_number(RestBvs,Num1),
% 	Num is Num1 + 1.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Task 6 - TODO gal

kakuroSolve(Instance,Solution) :-
    kakuroEncode(Instance, Map, CNF),
    sat(CNF),
    kakuroDecode(Map, Solution),
    kakuroVerify(Solution).

% % TODO gal
% /* Task 8 */
% kakuroSolve(Instance, Solution):-
% 	kakuroEncode(Instance,Map,Cnf),
% 	sat(Cnf),
% 	kakuroDecode(Map,MapSolution),
% 	kakuroBuildSolution(Instance, MapSolution, Solution),
% 	kakuroVerify(Solution).


% /* Tools */ % TODO - GAL
% % turns list to continued list
% list_to_continued_list([],List-List).
% list_to_continued_list([El|RestList],[El|List1]-List2):-
%     list_to_continued_list(RestList,List1-List2).
