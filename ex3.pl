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
/* Part A */

/*task 1*/
%sum_equals(+,+,-)
%for Even vectors case
sum_equals(Sum,Numbers,CNF):-
    addVectors(Numbers, CNF),
    sat(CNF),
    integerRep(CNF, Sum2),
    Sum == Sum2.

addVectors([_],[]).

addVectors([X,Y|Numbers], CNF):-
    add(X,Y,0,Sum1,CNF1),
    addVectors([Sum1|Numbers], CNF2),
    append(CNF1, CNF2, CNF).

%we did in class, SUM of 2 Bit Vectors
add([], [], C, [C], []).

add([X|Xs], [Y|Ys], C, [S|Sum], CNF):-
    fullAdder(X,Y,C,S,NextC, CNF1),
    add(Xs, Ys, NextC, Sum, CNF2),
    append(CNF1, CNF2, CNF).

%we did in class, SUM of 2 Bits 
%fullAdder(+,+,+,-,-, -)
fullAdder(I1, I2, C_in, Out, C_out, CNF):-
    %calc S
    xor(X, I2, X), and( I1, I2, A1), and( X, C_in, A2),
    xor( X, C_in, Out), or( A1, A2, C_out),

    %calc NextC
    xor(X, Y, Res), and(X, Y, A1), and(Res, C, A2), or(A1, A2, NextC),
    CNF = [[X,Y,C,-S], [X, Y, -C, S], [X,-Y,C,S],[X,-Y,-C,-S],[-S,Y,C,S], [-X,Y,-C,-S],[-X,-Y,C,-S],[-X,-Y,-C,S]],

   
