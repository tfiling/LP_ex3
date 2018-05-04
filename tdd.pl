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
        3 = [I10, I14]],        % instance

        [14 = [5, 1, 6, 2], 
        17 = [9, 2, 1, 5], 
        3 = [2, 1], 
        4 = [3, 1], 
        11 = [9, 2],
        6 = [2, 4], 
        8 = [2, 1, 5], 
        3 = [2, 1], 
        18 = [4, 5, 3, 6], 
        3 = [1, 2]],            % solution

        1). % are equal

testKakuroSolve :-
    test5(I, Instance, Sol, AreEqual),
    (AreEqual is 1 -> 
        (kakuroSolve(Instance, Result), Sol = Result -> writeln(I: ok);writeln(I: failed)) ;
        (kakuroSolve(Instance, Result), Sol \= Result -> writeln(I: failed); writeln(I: ok))
    ),
    fail.
testKakuroSolve.


:- testKakuroVerify, testKakuroSolve.