user:file_search_path(sat, '../satsolver').
:- use_module(sat(satsolver)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Task 1 - sum_equals(Sum+,Numbers+,CNF-)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%sum_equals(+,+,-)
sum_equals(Sum,Numbers,CNF):-
    addVectors(Numbers, SumVaribles, CNF),      % SumVaribles is the variable list(bit vector) that will be set with the actual sum bits
    dec2bin(Sum, LsbBinSum),    % converts Sum into binary Lsbit first representation
    zeroToMinusOne(LsbBinSum, LsbBinSumMinus),  % LsbBinSumMinus is LsbBinSum where all 0s were converted to -1
    setLastVectorValues(LsbBinSumMinus, SumVaribles).   % sets all bit variables in SumVaribles according to the values in LsbBinSumMinus
                                                        % pads the MSbits with -1s (0s)


% dec2bin(Decimal+,BinaryRepresentation-) - converts decimal numbers into their binary representation
dec2bin(0,[0]).

dec2bin(1,[1]).

dec2bin(N,L):- 
    N > 1,
    X is N mod 2,
    Y is N // 2,  
    dec2bin(Y,L1),
    L = [X|L1].

% zeroToMinusOne(OriginalBinary+, ConvertedRepresentation-)
% converts binary representation of {0, 1} into binary representation of {-1, 1} 
zeroToMinusOne([], []).

zeroToMinusOne([0|Rest], [-1|RestNew]):-
        zeroToMinusOne(Rest, RestNew).

zeroToMinusOne([1|Rest], [1|RestNew]):-
        zeroToMinusOne(Rest, RestNew).
        

% addVectors(Numbers+, Sum-, CNF-)
% generates a CNF that will statisfy if and only if the numbers(list of numbers in binary representation)
% sums into Sum(binary representation which is at this point is composed from variables)
addVectors([Xs1, Xs2 | RestNumbers], Sum, CNF) :-
    add_binary(Xs1, Xs2, CurrentSum, CNF_CurrentSum),
    addVectors([CurrentSum | RestNumbers], Sum, RestAdditionCNF),
    append(CNF_CurrentSum, RestAdditionCNF, CNF).

addVectors([FinalSum], FinalSum, []).
    
% paddZero(Block+) - set -1 into all of the variables. 
% will not satisfy if one or more elements in the list is not variable
paddZero([]).    
paddZero([-1 | Rest]):- 
    paddZero(Rest).


% add_binary(Xs+, Ys+, Zs-, CNF-)
% wrapper for add(Xs+, Ys+, Cin+, Zs-, CNF-)
% generates a CNF that will statisfy if and only if the Xs and Ys numbers(binary representation)
% sums into Zs(binary representation)
add_binary([], [], [], []).

add_binary(Xs, Ys, Zs, CNF) :-
    add_binary(Xs, Ys, -1, Zs, CNF).    % invoke add_binary that will set a chain of fullAdders over Xs Ys
                                        % initial carry in is -1 (0)

% add_binary(Xs+, Ys+, Cin+, Zs-, CNF-)
% returns Zs the result and a CNF that will satify if and only if Xs and Ys are summed into Zs
% Xs and Ys are binary representation of numbers, Cin is a carry if from the previous addition
% can handle bitvectors on different length

% regular addition of two bits and a carry in
add_binary([X | Xs], [Y | Ys], Cin, [Z | Zs], CNF) :-
    fullAdder(X, Y, Cin, Z, Cout, CNF_bit),
    add_binary(Xs, Ys, Cout, Zs, RestCNF),
    append(CNF_bit, RestCNF, CNF).

% Xs has more bits than Ys, simply add X with -1 (0)
add_binary([X | Xs], [], Cin, [Z | Zs], CNF) :-
    fullAdder(X, -1, Cin, Z, Cout, CNF_bit),
    add_binary(Xs, [], Cout, Zs, RestCNF),
    append(CNF_bit, RestCNF, CNF).

% Ys has more bits than Xs, simply add Y with -1 (0)
add_binary([], [Y | Ys], Cin, [Z | Zs], CNF) :-
    fullAdder(-1, Y, Cin, Z, Cout, CNF_bit),
    add_binary([], Ys, Cout, Zs, RestCNF),
    append(CNF_bit, RestCNF, CNF).

% the last step of the addition where the carry out from the previous addition is set is the MSbit of the sum
add_binary([], [], Cin, [Cin], []).

% fullAdder(+,+,+,-,-, -)
% introduced in the class, returns a S, C_out and CNF which will satisfy on correct bit addition
 fullAdder(I1, I2, C_in, S, C_out, CNF):-
% CNF_S: s <=> I1 Xor I2 Xor C_in
    CNF_S = [   % a CNF that satisfies when S will hold the correct value
        [ I1, I2, C_in,-S], 
        [ I1, I2,-C_in, S], 
        [ I1,-I2, C_in, S],
        [ I1,-I2,-C_in,-S],
        [-I1, I2, C_in, S], 
        [-I1, I2,-C_in,-S],
        [-I1,-I2, C_in,-S],
        [-I1,-I2,-C_in, S]
        ],
% CNF_Cout C_out <=> (I1 ^ I2) V (I1 ^ C_in) V (I2 ^ C_in)
    CNF_Cout = [    % a CNF that satisfies when C_out will hold the correct value
        [ I1, I2, C_in,-C_out],
        [ I1, I2,-C_in,-C_out],
        [ I1,-I2, C_in,-C_out],
        [ I1,-I2,-C_in, C_out],
        [-I1, I2, C_in,-C_out],
        [-I1, I2,-C_in, C_out],
        [-I1,-I2, C_in, C_out],
        [-I1,-I2,-C_in, C_out]
    ],
    append(CNF_S, CNF_Cout, CNF).
    
% setLastVectorValues(LsbBinSum+, SumVaribles+)
% applies values of LsbBinSum into SumVaribles which is a list of variables and padds the MSbits with -1 (0)
setLastVectorValues(LsbBinSum, SumVaribles) :-
    length(SumVaribles, SumVariblesLen),
    length(LsbBinSum, LsbBinSumLen),
    SumVariblesLen >= LsbBinSumLen,     % should not satisfy if LsbBinSum is longer SumVaribles
                                        % if its not longer then it is impossible that the argumented sum 
                                        % can be reached with the given amount of numbers
    RequiredPaddingZeros is SumVariblesLen - LsbBinSumLen,
    length(PaddingBlock, RequiredPaddingZeros),
    paddZero(PaddingBlock),
    append(LsbBinSum, PaddingBlock, SumVaribles).   % LsbBinSum values are appended into -1s padding "creating" SumVaribles.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Task 2 - all_diff(Numbers+, CNF-)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% all_diff(Numbers+, CNF-)
all_diff([X1, X2 | Rest], CNF) :-
    diff(X1, X2, CNF1),             % CNF1 will satisfy if and only if X1 is different from X2
    all_diff([X1 | Rest], CNF2),    % CNF2 will satisfy if and only if X1 is different from the rest on the numbers
    all_diff([X2 | Rest], CNF3),    % CNF3 will satisfy if and only if X2 is different from the rest on the numbers
    append([CNF1, CNF2, CNF3], CNF).    % all 3 should be satisfied!

% a single number or an empty list of numbers is a Vacuous truth
all_diff([_], []).
all_diff([], []).

% note -    preparing to the exam we implemented this one for unary representation
%           the below implementation based on this implementation
diff(Xs,Ys,[[B]|CNF]):-
    diff(B, Xs, Ys, CNF).

diff(B, [X], [Y], CNF):-
% B <=> X != Y
        CNF = [
            [-B, X, Y], 
            [-B, -X, -Y], 
            [B, -X, Y], 
            [B, X, -Y]
            ].

diff(B, [X | Xs], [Y | Ys], CNF):-
% B <=> (X != Y) V B1(at least one of the next bits is not equal)
    CNF1 = [
        [B, -X, Y], 
        [B, X, -Y], 
        [B, -X, -Y, -B1],
        [B, X, Y, -B1], 
        [-B, -X, -Y, B1], 
        [-B, X, Y, B1] 
        ],
    diff(B1, Xs, Ys, CNF2),
    append(CNF1, CNF2, CNF).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% part 2 - Kakuro
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Task 3 - kakuroVerify(Solution+)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% kakuroVerify(Solution+)
 kakuroVerify([H | Rest]) :-
    verify_assignment(H),
    kakuroVerify(Rest).

kakuroVerify([]).

% verify_assignment(Sum+ = Assignments+) - satisfies if and only if the anumbers assigned fit kakuro rules
verify_assignment(Sum = Assignments) :-
    is_sum(Sum, Assignments),
    all_numbers_diff(Assignments).

% is_sum(Sum+, Numbers+) - satisfies if and only if the sum of Numbers is Sum
is_sum(Sum, [H | T]) :-
    Sum1 is Sum - H,
    is_sum(Sum1, T).

% all numbers were substracted from Sum and 0 is remaining -> sum of all given numbers is Sum
is_sum(0, []).

% all_numbers_diff(Numbers+) - satisfies if and only if all numbers are distinct
all_numbers_diff([X1, X2 | Rest]) :-
    X1 \== X2,                      % X1 is different than X2
    all_numbers_diff([X1 | Rest]),  % X1 is different than the rest of the numbers
    all_numbers_diff([X2 | Rest]).  % X2 is different than the rest of the numbers

all_numbers_diff([_]).
all_numbers_diff([]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Task 4 - kakuroEncode(Instance+,Map-,CNF-)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% var_list_to_bitvector_list(Vars+, Map+, BitVectors-)
% returns with BitVectors the binary representation of all Vars according to Map (the mapping of the encoding)
var_list_to_bitvector_list([Var | RestVars], Map, [BitVector | RestBitVectors]) :-
    var_to_bitvector(Var, Map, BitVector),
    var_list_to_bitvector_list(RestVars, Map, RestBitVectors).

var_list_to_bitvector_list([], _, []).

% var_to_bitvector(Var+, Map+, BitVector-) - finds Var in Map and returns it's bitvector.
% first mapped variable is not the one we are looking for, keep looking
var_to_bitvector(Var, [Var2 = _ | RestVars], BitVector) :-  
    Var \== Var2,
    var_to_bitvector(Var, RestVars, BitVector).

% found Var and its representation in Map, stop looking
var_to_bitvector(Var, [Var = BitVector | _], BitVector).    

% no need for halt / base case predicate, we expect it to fail if Var is not mapped
% any Var mentioned in the instance should be present in Map


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% map_solution_variables(Instance+, VarsMap-)
% Map is built in the form of [Instance, VarsMap] and this predicate receives the VarsMap part of the Map
% VarsMap maps each variable into binary representatin in the form of Var = [Bit1, Bit2, Bit4, Bit8]
% when decoding we will have values in the bit varialbes allowing us to assign the Var variable with number
% the Var assignemnt will reflect in instance and therefor in the solution

map_solution_variables(Instance, VarsMap) :-
    accumulateVars(Instance, Vars),
    sort(Vars, VarsNoDuplicates),   % handle duplicated appearances of Vars
    map_binary_variables(VarsNoDuplicates, VarsMap).

% accumulateVars(Instance+, AllVars+)
% appends all variables mentioned in the Instance (may contain duplicates)
accumulateVars([_ = Vars | Rest], AllVars) :-
    accumulateVars(Rest, AccumulatedVars),
    append(Vars, AccumulatedVars, AllVars).

accumulateVars([], []).

% map_binary_variables(Vars+, Map-)
% maps all variables in the form of Var = [Bit1, Bit2, Bit4, Bit8]
map_binary_variables([Var | RestVars], [Var = BitVector | RestMap]) :-
    length(BitVector, 4),   % possible numbers are between 1 and 9 accoring to the instructions
    map_binary_variables(RestVars, RestMap).



map_binary_variables([], []).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% generate_sol_correctness_cnf(Instance+, Map+, CorrectnessCNF-)

% generate_sol_correctness_cnf(Instance+, Map+, CorrectnessCNF-)
generate_sol_correctness_cnf([Sum = Vars | Rest], Map, CorrectnessCNF) :-
    var_list_to_bitvector_list(Vars, Map, BitVectors),  % extract current relevant variables(binary representation)
    sum_equals(Sum, BitVectors, CNF1),                  % CNF1 satisfies when Vars sum into Sum
    all_diff(BitVectors, CNF2),                         % CNF2 satisfies when Vars are distinct from each other
    generate_sol_correctness_cnf(Rest, Map, RestCNF),   % generate the CNF for the rest of instance assignments
    append([CNF1, CNF2, RestCNF], CorrectnessCNF).      % append all 3 CNFs

generate_sol_correctness_cnf([], _, []).


% all_vars_greater_than_0(Map+, CNF-)
% generate CNF that will satisfy if and only if all numbers mapped are greater than 0
% we simply set the bits as a CNF OR component -> at least one bit is not -1 (0)
all_vars_greater_than_0([_ = BitVector | Rest], CNF) :-
    all_vars_greater_than_0(Rest, RestVarsCNF),
    append([BitVector], RestVarsCNF, CNF).

all_vars_greater_than_0([], []).

% all_vars_smaller_than_10(Map+, CNF-)
% generate CNF that will satisfy if and only if all numbers mapped are smaller than 10
% if X3 is 1 then X2 and X3 must be -1 (0)
all_vars_smaller_than_10([_ = [_, X1, X2, X3] | Rest], CNF) :-
% {X3 => !X1 ^ !X2} <=> {!X3 V (!X1 ^ !X2)}
    CurrentVarCNF = [
        [-X1, -X3],
        [-X2, -X3]
    ],
    all_vars_smaller_than_10(Rest, RestCNF),
    append(CurrentVarCNF, RestCNF, CNF).

all_vars_smaller_than_10([], []).


kakuroEncode(Instance, [Instance, VarsMap], CNF):-
    map_solution_variables(Instance, VarsMap),  % map instance
    generate_sol_correctness_cnf(Instance, VarsMap, CNF1),  % generate general solution correctness CNF
    all_vars_greater_than_0(VarsMap, CNF2),     % force all numbers to be greater than 0
    all_vars_smaller_than_10(VarsMap, CNF3),    % force all numbers to be smaller than 10
    append([CNF1, CNF2, CNF3], CNF).        % all 3 combined are the proper CNF expression

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Task 5 - kakuroDecode(Map+, Solution-)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% bit_vector_to_int(Vector+, CurrentIncrement+, Num-)
% converts a binary number into an equivalent decimal number
bit_vector_to_int([1 | Rest], CurrentIncrement, Num) :-
    NextIncrement is CurrentIncrement * 2,
    bit_vector_to_int(Rest, NextIncrement, Num1),
    Num is CurrentIncrement + Num1.

bit_vector_to_int([-1 | Rest], CurrentIncrement, Num) :-
    NextIncrement is CurrentIncrement * 2,
    bit_vector_to_int(Rest, NextIncrement, Num).

bit_vector_to_int([], _, 0).

% kakuroDecode(Map+, Solution-)
kakuroDecode([Solution, VarsMap], Solution) :- 
    kakuroDecodeFillSolution(VarsMap).

% kakuroDecodeFillSolution(Map+) - assignes decimal number into Var accoring to the assignment made by the sat solver
kakuroDecodeFillSolution([Var = BitVector | Rest]) :-
    bit_vector_to_int(BitVector, 1, Var),
    kakuroDecodeFillSolution(Rest).

kakuroDecodeFillSolution([]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Task 6 - kakuroSolve(Instance+,Solution-)

kakuroSolve(Instance,Solution) :-
    kakuroEncode(Instance, Map, CNF),   % incode the instance
    sat(CNF),                           % solve the CNF using the sat solver
    kakuroDecode(Map, Solution),        % decode the solution stored in Map in the form of [... | Var_i = [B_i0, B_i1, B_i2, B_i3] | ....]
                                        % each Var is identical to the one in Solution and Instance.
                                        % assigning them will automatically fill Solution with the resulted solution
    kakuroVerify(Solution).             % validate the solution
