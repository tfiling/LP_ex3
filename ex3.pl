% user:file_search_path(sat, '../satsolver').
% :- use_module(sat(satsolver)).
:- use_module(naive_sat).
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
fixDoubleMinus([List|CNF], NewCNF):-
    fixDoubleMinusH(List, NewCNF),
    fixDoubleMinus(CNF, NewCNF).

fixDoubleMinusH([], []).
fixDoubleMinusH([- -X| CNF], [X| NewCNF]):-
    fixDoubleMinusH(CNF, NewCNF).
fixDoubleMinusH([-X| CNF], [-X| NewCNF]):-
    fixDoubleMinusH(CNF, NewCNF).

fixDoubleMinusH([X| CNF], [X| NewCNF]):-
        fixDoubleMinusH(CNF, NewCNF).
fixDoubleMinusH([- -1| CNF], [1| NewCNF]):-
    fixDoubleMinusH(CNF, NewCNF).
fixDoubleMinusH([-1| CNF], [-1| NewCNF]):-
    fixDoubleMinusH(CNF, NewCNF).

/* Part A */

/*task 1*/
%sum_equals(+,+,-)
sum_equals(Sum,Numbers,CNF):-
    addVectors(Numbers, CNF, ResList), !,
    writeln('Res List is' + ResList),
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
    %writeln('Sum1 is' + Sum1),
 
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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% part 2 - Kakuro
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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

    