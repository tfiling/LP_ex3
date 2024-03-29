:- include('ex3.pl').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% test kakuroVerify

test1(1,     
            [14 = [5, 1, 6, 2], 
            17 = [9, 2, 1, 5], 
            3 = [2, 1], 
            4 = [3, 1], 
            11 = [9, 2],
            6 = [2, 4], 
            8 = [2, 1, 5], 
            3 = [2, 1], 
            18 = [4, 5, 3, 6], 
            3 = [1, 2]], % board

            1). % should pass

test1(2,     
            % [14 = [5, 1, 6, 2], 
            [14 = [5, 1, 6, 3],     % not 14
            17 = [9, 2, 1, 5], 
            3 = [2, 1], 
            4 = [3, 1], 
            11 = [9, 2],
            6 = [2, 4], 
            8 = [2, 1, 5], 
            3 = [2, 1], 
            18 = [4, 5, 3, 6], 
            3 = [1, 2]], % board

            0). % should pass

test1(3,     
            % [14 = [5, 1, 6, 2], 
            [14 = [5, 1, 2, 2],     % not 14
            17 = [9, 2, 1, 5], 
            3 = [2, 1], 
            4 = [3, 1], 
            11 = [9, 2],
            6 = [2, 4], 
            8 = [2, 1, 5], 
            3 = [2, 1], 
            18 = [4, 5, 3, 6], 
            3 = [1, 2]], % board

            0). % should pass

test1(4,     
            [14 = [5, 1, 6, 2], 
            17 = [9, 2, 1, 5], 
            3 = [2, 1], 
            4 = [2, 2],         % 4 but is identical 
            11 = [9, 2],
            6 = [2, 4], 
            8 = [2, 1, 5], 
            3 = [2, 1], 
            18 = [4, 5, 3, 6], 
            3 = [1, 2]], % board

            0). % should pass

test1(5,     
            [14 = [5, 1, 6, 2], 
            17 = [9, 2, 2, 4], % 17 but is identical
            3 = [2, 1], 
            4 = [3, 1], 
            11 = [9, 2],
            6 = [2, 4], 
            8 = [2, 1, 5], 
            3 = [2, 1], 
            18 = [4, 5, 3, 6], 
            3 = [1, 2]], % board

            0). % should pass

% test1(1,     
%             [14 = [I11, I12, I13, I14], 
%             17 = [I3, I4, I5, I6], 
%             3 = [I7, I8], 
%             4 = [I9, I10], 
%             11 = [I3, I7],
%             6 = [I1, I2], 
%             8 = [I4, I8, I11], 
%             3 = [I1, I5], 
%             18 = [I2, I6, I9, I13], 
%             3 = [I10, I14]], % board

%             1). % should pass            


testKakuroVerify :-
    test1(I, Sol, ShouldPass),
    (ShouldPass is 1 -> 
        (kakuroVerify(Sol) -> writeln(I: ok);writeln(I: failed)) ;
        (kakuroVerify(Sol) -> writeln(I: failed); writeln(I: ok))
    ),
    fail.
testKakuroVerify.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% test fullAdder
% fullAdder(I1, I2, C_in, S, C_out, CNF)
test2(1,
        % fulladder(-1, -1, -1, Z, Cout, CNF),
        fulladder(-1, -1, -1, -1, -1, CNF),
        1).

test2(2,
        fulladder(1, -1, -1, 1, -1, CNF),
        1).

test2(3,
        fulladder(-1, 1, -1, 1, -1, CNF),
        1).

test2(4,
        fulladder(-1, -1, 1, 1, -1, CNF),
        1).

test2(5,
        fulladder(-1, 1, 1, -1, 1, CNF),
        1).

test2(6,
        fulladder(1, -1, 1, -1, 1, CNF),
        1).

test2(7,
        fulladder(1, 1, -1, -1, 1, CNF),
        1).

test2(8,
        fulladder(1, 1, 1, 1, 1, CNF),
        1).


testFullAdder :-
    test2(I, fulladder(X, Y, Cin, Z, Cout, CNF), ShouldPass),
    (ShouldPass is 1 -> 
        (fullAdder(X, Y, Cin, Z, Cout, CNF), sat(CNF) -> writeln(I: ok);writeln(I: failed)) ;
        (fullAdder(X, Y, Cin, Z, Cout, CNF), \sat(CNF) -> writeln(I: failed); writeln(I: ok))
    ),
    fail.
testFullAdder.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% test kakuroSolve

test5(1,
        [14 = [I11, I12, I13, I14],
        17 = [I3, I4, I5, I6], 
        3 = [I7, I8], 
        4 = [I9, I10], 
        11 = [I3, I7],
        6 = [I1, I2], 
        8 = [I4, I8, I11], 
        3 = [I1, I5], 
        18 = [I2, I6, I9, I13], 
        3 = [I10, I14]
        ],        % instance

        [14 = [5, 1, 6, 2],
        17 = [9, 2, 1, 5], 
        3 = [2, 1], 
        4 = [3, 1], 
        11 = [9, 2],
        6 = [2, 4], 
        8 = [2, 1, 5], 
        3 = [2, 1], 
        18 = [4, 5, 3, 6], 
        3 = [1, 2]
        ],            % solution

        1). % are equal

test5(2,
        [
                14 = [X1, X2],
                3 = [X3, X4],
                11 = [X1, X3],
                6 = [X2, X4]
        ],

        [
                14 = [9, 5],
                3 = [2, 1],
                11 = [9, 2],
                6 = [5, 1]
        ],
        1
).

test5(3,
        [
                6 = [X1, X2],
                4 = [X3, X4],
                6 = [X1, X3],
                4 = [X2, X4]
        ],

        [
                6 = [5, 1],
                4 = [1, 3],
                6 = [5, 1],
                4 = [1, 3]
        ],
        1
).

test5(4,
        [
                16 = [X1, X2, X3],
                9 = [X4, X5, X6],
                17 = [X7, X8, X9],
                18 = [X10, X11, X12],
                3 = [X3, X6],
                30 = [X2, X5, X9, X12],
                11 = [X1, X4, X8, X11],
                16 = [X7, X10]
        ],
        [
                16 = [5, 9, 2],
                9 = [2, 6, 1],
                17 = [9, 1, 7],
                18 = [7, 3, 8],
                3 = [2, 1],
                30 = [9, 6, 7, 8],
                11 = [5, 2, 1, 3],
                16 = [9, 7]
        ],
        1
).

testKakuroSolve :-
    test5(I, Instance, Sol, AreEqual),
    (AreEqual is 1 -> 
        (kakuroSolve(Instance, Result), Sol = Result -> writeln(I: ok);writeln(I: failed)) ;
        (kakuroSolve(Instance, Result), Sol \= Result -> writeln(I: failed); writeln(I: ok))
    ),
    fail.
testKakuroSolve.


:- 
    writeln('testKakuroVerify'),
    testKakuroVerify,
    writeln('testFullAdder'),
    testFullAdder,    
    writeln('testKakuroSolve'),
    testKakuroSolve.