#lang forge/froglet

open "connect4.frg"

///////////////////////////
// Helpers for Testing
pred redOrYellowTurn[b: Board] {
    Redturn[b] or Yellowturn[b]
}

pred morePieces[post: Board, pre: Board] {
    #{r, c: Int | some post.board[r][c]}
    =
    add[1, #{r, c: Int | some pre.board[r][c]}]
}
pred allBoardsWellformed {
    all b: Board | wellformed[b]
}

pred noCycles {
    all b: Board | Game.next[b] != Game.first
}


///////////////////////////



test suite for wellformed {
    // assert test
    MovePreservesWellformed: assert all pre, post: Board, col: Int, p: Player | {
        wellformed[pre]
        move[pre, col, p, post]
    } is sufficient for wellformed[post] for exactly 2 Board, 4 Int
     
    
    // Positive tests
    test expect { emptyBoardWellformed: {
    some b: Board {
        wellformed[b] and (all r, c: Int {
            no b.board[r][c]
        })
    }
} is sat }


    test expect { simpleWinRowTest: {
    some b: Board {
        wellformed[b] and
        winRow[b, RED]
    }
} is sat }
    
    test expect { validPiecesWellformed: {
        some b: Board | 
            wellformed[b] and
            b.board[0][0] = RED and
            b.board[1][1] = YELLOW and
            b.board[5][6] = RED
    } is sat }
    
    // Negative tests
        test expect { wellformedBlocksNegativeIndices: {
    some b: Board {
        wellformed[b] and
        some b.board[-8][-8]
    }
} is unsat }
    test expect { outOfBoundsRow: {
        some b: Board | wellformed[b] and some b.board[6][3]
    } is unsat }
    
    test expect { outOfBoundsCol: {
        some b: Board | wellformed[b] and some b.board[3][7]
    } is unsat }
    
    test expect { negativeRow: {
        some b: Board | wellformed[b] and some b.board[-1][3]
    } is unsat }
    
}


test suite for starting {
    // assert tests:
    StartingImpliesRedturn: assert all b: Board |
        starting[b] is sufficient for Redturn[b]
    for exactly 1 Board, 4 Int

    StartingImpliesBalanced: assert all b: Board |
        starting[b] is sufficient for balanced[b]
    for exactly 1 Board, 4 Int
    
    // Positive tests
    test expect { completelyEmpty: {
        some b: Board | starting[b]
    } is sat }
    
    // Negative tests
    test expect { hasOnePiece: {
        some b: Board | starting[b] and some b.board[0][0]
    } is unsat }
    
    test expect { hasManyPieces: {
        some b: Board | 
            starting[b] and
            b.board[0][0] = RED and
            b.board[0][1] = YELLOW
    } is unsat }

    
    //assert starting is sat
}

test suite for gravityHolds {
    // assert test

    MovePreservesGravity: assert all pre, post: Board, col: Int, p: Player | {
        wellformed[pre]
        gravityHolds[pre]
        move[pre, col, p, post]
    } is sufficient for gravityHolds[post] for exactly 2 Board, 4 Int
    
    // Positive tests
    test expect { emptyBoardGravity: {
        some b: Board | gravityHolds[b] and (all r, c: Int | no b.board[r][c])
    } is sat }
    
    test expect { stackedPiecesValid: {
        some b: Board | 
            gravityHolds[b] and
            b.board[0][0] = RED and
            b.board[1][0] = YELLOW and
            b.board[2][0] = RED
    } is sat }
    
    test expect { multipleColumnsValid: {
        some b: Board | 
            gravityHolds[b] and
            b.board[0][0] = RED and
            b.board[1][0] = YELLOW and
            b.board[0][1] = YELLOW and
            b.board[1][1] = RED and
            b.board[2][1] = YELLOW
    } is sat }
    
    // Negative tests
    test expect { floatingPiece: {
        some b: Board | 
            gravityHolds[b] and
            b.board[2][0] = RED and
            no b.board[1][0] and
            no b.board[0][0]
    } is unsat }
    
    test expect { gapInColumn: {
        some b: Board | 
            gravityHolds[b] and
            b.board[0][0] = RED and
            no b.board[1][0] and
            b.board[2][0] = YELLOW
    } is unsat }
    
    // Property tests
   // assert gravityHolds is sat
}

test suite for Redturn {

    // Positive tests
    test expect { emptyBoardRedTurn: {
        some b: Board | Redturn[b] and (all r, c: Int | no b.board[r][c])
    } is sat }
    
    test expect { equalPiecesRedTurn: {
        some b: Board | 
            Redturn[b] and
            b.board[0][0] = RED and
            b.board[0][1] = YELLOW
    } is sat }
    
    test expect { twoPairsRedTurn: {
        some b: Board | 
            Redturn[b] and
            b.board[0][0] = RED and
            b.board[0][1] = YELLOW and
            b.board[0][2] = RED and
            b.board[0][3] = YELLOW
    } is sat }
    
    // Negative tests
    test expect { redAheadNotRedTurn: {
    some b: Board {
        Redturn[b] and
        b.board[0][0] = RED and
        b.board[0][1] = YELLOW and
        b.board[0][2] = RED and
        // All other positions are empty
        (all r, c: Int {
            not ((r = 0 and c = 0) or (r = 0 and c = 1) or (r = 0 and c = 2))
            implies no b.board[r][c]
        })
    }
} is unsat }
    
   test expect { yellowAheadNotRedTurn: {
    some b: Board {
        Redturn[b] and 
        #{r, c: Int | b.board[r][c] = YELLOW} = 1 and
        #{r, c: Int | b.board[r][c] = RED} = 0
    }
} is unsat }
    
    // Property tests
   // assert Redturn is sat
}

test suite for Yellowturn {
    
    // Positive tests
    test expect { redAheadByOneYellowTurn: {
        some b: Board | 
            Yellowturn[b] and
            b.board[0][0] = RED and
            b.board[0][1] = YELLOW and
            b.board[0][2] = RED
    } is sat }
    
    test expect { threePiecesYellowTurn: {
        some b: Board | 
            Yellowturn[b] and
            b.board[0][0] = RED and
            b.board[0][1] = YELLOW and
            b.board[0][2] = RED and
            b.board[0][3] = YELLOW and
            b.board[0][4] = RED
    } is sat }
    
    // Negative tests
    test expect { equalPiecesNotYellowTurn: {
        some b: Board {
            Yellowturn[b] and
            #{r, c: Int | b.board[r][c] = RED} = 1 and
            #{r, c: Int | b.board[r][c] = YELLOW} = 1
        }
    } is unsat }
    
    test expect { emptyBoardNotYellowTurn: {
        some b: Board | Yellowturn[b] and (all r, c: Int | no b.board[r][c])
    } is unsat }
    
    // Property tests
   // assert Yellowturn is sat
    
//     MutuallyExclusiveTurns: assert {
//         all b: Board | not (Redturn[b] and Yellowturn[b])
//     } is necessary for Yellowturn
}

test suite for balanced {
    // assert test
    BalancedMeansExactlyOneTurn: assert all b: Board |
        balanced[b] is sufficient for redOrYellowTurn[b]
    for exactly 1 Board, 4 Int
    
    // Positive tests
    test expect { emptyBoardBalanced: {
        some b: Board | balanced[b] and (all r, c: Int | no b.board[r][c])
    } is sat }
    
    test expect { redTurnBalanced: {
        some b: Board | 
            balanced[b] and
            b.board[0][0] = RED and
            b.board[0][1] = YELLOW
    } is sat }
    
    test expect { yellowTurnBalanced: {
        some b: Board | 
            balanced[b] and
            b.board[0][0] = RED and
            b.board[0][1] = YELLOW and
            b.board[0][2] = RED
    } is sat }
    
    // Negative tests
    test expect { redTwoAhead: {
    some b: Board {
        balanced[b] and
        #{r, c: Int | b.board[r][c] = RED} = 3 and
        #{r, c: Int | b.board[r][c] = YELLOW} = 1
    }
    } is unsat }

    test expect { yellowTwoAhead: {
        some b: Board {
            balanced[b] and
            #{r, c: Int | b.board[r][c] = RED} = 1 and
            #{r, c: Int | b.board[r][c] = YELLOW} = 3
        }
    } is unsat }
    
    // Property tests
    // BalancedIsTurnOrOtherTurn: assert {
    //     all b: Board | balanced[b] implies (Redturn[b] or Yellowturn[b])
    // } is necessary for balanced
    
    // assert balanced is sat
}

test suite for winRow {
    // assert test
    WinRowImpliesWinning: assert all b: Board, p: Player |
        winRow[b, p] is sufficient for winning[b, p]
    for exactly 1 Board, 4 Int
    
    // Positive tests
    test expect { bottomRowWinRed: {
        some b: Board | 
            winRow[b, RED] and
            b.board[0][0] = RED and
            b.board[0][1] = RED and
            b.board[0][2] = RED and
            b.board[0][3] = RED
    } is sat }
    
    test expect { middleRowWinYellow: {
        some b: Board | 
            winRow[b, YELLOW] and
            b.board[3][1] = YELLOW and
            b.board[3][2] = YELLOW and
            b.board[3][3] = YELLOW and
            b.board[3][4] = YELLOW
    } is sat }
    
    test expect { topRowWin: {
        some b: Board | 
            winRow[b, RED] and
            b.board[5][3] = RED and
            b.board[5][4] = RED and
            b.board[5][5] = RED and
            b.board[5][6] = RED
    } is sat }
    
    // Negative tests
   test expect { onlyThreeInRow: {
    some b: Board {
        wellformed[b] and
        winRow[b, RED] and
        b.board[0][0] = RED and
        b.board[0][1] = RED and
        b.board[0][2] = RED and
        // All other positions must be empty
        (all r, c: Int {
            not (r = 0 and (c = 0 or c = 1 or c = 2))
            implies no b.board[r][c]
                })
            }
        } is unsat }
    
    test expect { fourWithGap: {
        some b: Board  {
            wellformed[b] and
            winRow[b, RED] and
            b.board[0][0] = RED and
            b.board[0][1] = RED and
            b.board[0][2] = YELLOW and
            b.board[0][3] = RED and
            b.board[0][4] = RED
            (all r, c: Int {
            not (r = 0 and (c = 0 or c = 1 or c = 2 or c = 3 or c = 4))
            implies no b.board[r][c]
                })
    }
    } is unsat }
    
    // Property tests
    test expect { winRowExists: {
        some b: Board, p: Player | winRow[b, p]
    } is sat }
}

test suite for winCol {
    // assert test
    WinRowImpliesWinning: assert all b: Board, p: Player |
        winCol[b, p] is sufficient for winning[b, p]
    for exactly 1 Board, 4 Int
    
    // Positive tests
    test expect { leftColumnWin: {
        some b: Board | 
            winCol[b, RED] and
            b.board[0][0] = RED and
            b.board[1][0] = RED and
            b.board[2][0] = RED and
            b.board[3][0] = RED
    } is sat }
    
    test expect { middleColumnWin: {
        some b: Board | 
            winCol[b, YELLOW] and
            b.board[2][3] = YELLOW and
            b.board[3][3] = YELLOW and
            b.board[4][3] = YELLOW and
            b.board[5][3] = YELLOW
    } is sat }
    
    test expect { rightColumnWin: {
        some b: Board | 
            winCol[b, RED] and
            b.board[0][6] = RED and
            b.board[1][6] = RED and
            b.board[2][6] = RED and
            b.board[3][6] = RED
    } is sat }
    
    // Negative tests
    test expect { onlyThreeInColumn: {
        some b: Board {
            winCol[b, RED] and
            b.board[0][0] = RED and
            b.board[1][0] = RED and
            b.board[2][0] = RED and
            no b.board[3][0]
            (all r, c: Int {
            not (r = 0 and (c = 0 or c = 1 or c = 2))
            implies no b.board[r][c]
                })
    }
    } is unsat }
    
    test expect { fourWithVerticalGap: {
        some b: Board {
            winCol[b, YELLOW] and
            b.board[0][0] = YELLOW and
            b.board[1][0] = YELLOW and
            b.board[2][0] = RED and
            b.board[3][0] = YELLOW and
            b.board[4][0] = YELLOW
            (all r, c: Int {
            not (c = 0 and (r = 0 or r = 1 or r = 2 or r = 3 or r = 4))
            implies no b.board[r][c]
                })
    }
    } is unsat }
    
    // Property tests
    test expect { winColExists: {
        some b: Board, p: Player | winCol[b, p]
    } is sat }
}

test suite for winDiag {
    // assert test
    WinRowImpliesWinning: assert all b: Board, p: Player |
        winDiag[b, p] is sufficient for winning[b, p]
    for exactly 1 Board, 4 Int

    // Positive tests
    test expect { diagonalUpRightWin: {
        some b: Board | 
            winDiag[b, RED] and
            b.board[0][0] = RED and
            b.board[1][1] = RED and
            b.board[2][2] = RED and
            b.board[3][3] = RED
    } is sat }
    
    test expect { diagonalUpLeftWin: {
        some b: Board | 
            winDiag[b, YELLOW] and
            b.board[0][6] = YELLOW and
            b.board[1][5] = YELLOW and
            b.board[2][4] = YELLOW and
            b.board[3][3] = YELLOW
    } is sat }
    
    test expect { diagonalMiddleUpRight: {
        some b: Board | 
            winDiag[b, RED] and
            b.board[1][1] = RED and
            b.board[2][2] = RED and
            b.board[3][3] = RED and
            b.board[4][4] = RED
    } is sat }
    
    // Negative tests
    test expect { onlyThreeDiagonal: {
    some b: Board {
        wellformed[b] and
        winDiag[b, RED] and
        b.board[0][0] = RED and
        b.board[1][1] = RED and
        b.board[2][2] = RED and
        // All other positions must be empty
        (all r, c: Int {
            not ((r = 0 and c = 0) or (r = 1 and c = 1) or (r = 2 and c = 2))
            implies no b.board[r][c]
            })
        }
    } is unsat }
    
    test expect { fourWithDiagonalGap: {
        some b: Board { 
            winDiag[b, YELLOW] and
            b.board[0][0] = YELLOW and
            b.board[1][1] = YELLOW and
            b.board[2][2] = RED and
            b.board[3][3] = YELLOW
            (all r, c: Int {
            not ((r = 0 and c = 0) or (r = 1 and c = 1) or (r = 2 and c = 2) or (r = 3 and c = 3))
            implies no b.board[r][c]
            })
        }
    } is unsat }
    
    // Property tests
    test expect { winDiagExists: {
        some b: Board, p: Player | winDiag[b, p]
    } is sat }
}

test suite for winning {
    // assert test
    // this logic is done in the prev 4 test suits

    // Positive tests
    test expect { winByRow: {
        some b: Board | 
            winning[b, RED] and
            b.board[0][0] = RED and
            b.board[0][1] = RED and
            b.board[0][2] = RED and
            b.board[0][3] = RED
    } is sat }
    
    test expect { winByColumn: {
        some b: Board | 
            winning[b, YELLOW] and
            b.board[0][0] = YELLOW and
            b.board[1][0] = YELLOW and
            b.board[2][0] = YELLOW and
            b.board[3][0] = YELLOW
    } is sat }
    
    test expect { winByDiagonal: {
        some b: Board | 
            winning[b, RED] and
            b.board[0][0] = RED and
            b.board[1][1] = RED and
            b.board[2][2] = RED and
            b.board[3][3] = RED
    } is sat }
    
    // Negative tests
    test expect { almostWin: {
        some b: Board { 
            winning[b, RED] and
            b.board[0][0] = RED and
            b.board[0][1] = RED and
            b.board[0][2] = RED and
            no b.board[0][3]
            (all r, c: Int {
            not (r = 0 and (c = 0 or  c = 1 or c = 2))
            implies no b.board[r][c]
            })
        }
    } is unsat }
    
    test expect { emptyBoardNotWinning: {
        some b: Board | 
            winning[b, RED] and
            (all r, c: Int | no b.board[r][c])
    } is unsat }
    
    // Property tests
    // WinningIsSomeWinType: assert {
    //     all b: Board, p: Player | 
    //         winning[b, p] implies (winRow[b, p] or winCol[b, p] or winDiag[b, p])
    // } is necessary for winning
    
    test expect { winningExists: {
        some b: Board, p: Player | winning[b, p]
    } is sat }
}

test suite for move {

    // assert test
    MoveIncrementsPieceCount: assert all pre, post: Board, col: Int, p: Player | {
        wellformed[pre]
        gravityHolds[pre]
        move[pre, col, p, post]
    } is sufficient for morePieces[post, pre]
    for exactly 2 Board, 4 Int
    
    // Positive tests
    test expect { movePositiveBottomLanding: {
        some pre, post: Board |
            starting[pre] and gravityHolds[pre] and Redturn[pre] and
            move[pre, 3, RED, post] and
            post.board[0][3] = RED
    } is sat }
    
    test expect { moveOntoExistingPiece: {
        some pre, post: Board |
            pre.board[0][2] = RED and
            gravityHolds[pre] and Yellowturn[pre] and
            move[pre, 2, YELLOW, post] and
            post.board[1][2] = YELLOW
    } is sat }
    
    // Negative tests
    test expect { moveNegativeWrongTurn: {
        some pre, post: Board |
            starting[pre] and gravityHolds[pre] and Redturn[pre] and
            move[pre, 0, YELLOW, post]
    } is unsat }
    
    test expect { moveNegativeOutOfBounds: {
        some pre, post: Board |
            starting[pre] and gravityHolds[pre] and Redturn[pre] and
            move[pre, 7, RED, post]
    } is unsat }
    
    test expect { moveNegativeFullColumn: {
        some pre, post: Board |
            pre.board[0][1] = RED and
            pre.board[1][1] = YELLOW and
            pre.board[2][1] = RED and
            pre.board[3][1] = YELLOW and
            pre.board[4][1] = RED and
            pre.board[5][1] = YELLOW and
            gravityHolds[pre] and Redturn[pre] and
            move[pre, 1, RED, post]
    } is unsat }
    
    test expect { moveNegativeAfterWin: {
        some pre, post: Board |
            pre.board[0][0] = RED and
            pre.board[0][1] = RED and
            pre.board[0][2] = RED and
            pre.board[0][3] = RED and
            gravityHolds[pre] and winning[pre, RED] and
            (move[pre, 4, RED, post] or move[pre, 4, YELLOW, post])
    } is unsat }
    
}

test suite for wellformed_game {
    // assert test
    WellformedGameImpliesAllWellformed: assert
        wellformed_game is sufficient for allBoardsWellformed
    for exactly 8 Board, 4 Int

    // Positive tests
    test expect { wellformedGamePositive: {
        wellformed_game
    } is sat }
    
    // Negative tests
    test expect { wellformedGameNegativeWinnerHasNext: {
    wellformed_game 
    some b: Board {
        (winning[b, RED] or winning[b, YELLOW]) and some Game.next[b]
    }
    } is unsat }
    
    test expect { wellformedGameNegativeNotStarting: {
        wellformed_game and some Game.first.board[0][0]
    } is unsat }
    
    // Property tests
    GameStartsEmpty: assert {
        wellformed_game implies starting[Game.first]
    } is necessary for wellformed_game
    
    AllBoardsWellformed: assert {
        wellformed_game implies (all b: Board | wellformed[b])
    } is necessary for wellformed_game
}


test suite for linear_game {
    // assert tests
    LinearImpliesWellformed: assert
        linear_game is sufficient for wellformed_game
    for exactly 8 Board, 4 Int
        
    // Positive tests
    // test expect { linearGamePositive: {
    //     linear_game and
    //     (some b: Board | {
    //         (b = Game.first or some bPrev: Board | Game.next[bPrev] = b) and
    //         winning[b, RED]
    //     })
    // } is sat }
    test expect { linearGameExists: {
    linear_game
    } is sat }
    // test expect { linearGameYellowWin: {
    //     linear_game 
    //     some b: Board {
    //         winning[b, YELLOW]
    //     }
    // } is sat }
    
    // Negative tests
    test expect { linearGameNegativeCycleToFirst: {
        linear_game 
        some b: Board {
            Game.next[b] = Game.first
        }
    } is unsat }
    
    test expect { linearGameNegativeTwoPredsSameNext: {
        linear_game 
        some b1, b2, b3: Board {
            b1 != b2 and Game.next[b1] = b3 and Game.next[b2] = b3
        }
    } is unsat }
    
    test expect { linearGameNegativeSelfLoop: {
        linear_game 
        some b: Board {
            Game.next[b] = b
        }
    } is unsat }
    
    // Property tests
    LinearImpliesWellformed: assert {
        linear_game implies wellformed_game
    } is necessary for linear_game
    
    NextIsInjective: assert {
        all b1, b2: Board {
            linear_game implies {
                (b1 != b2 and some Game.next[b1] and some Game.next[b2]) 
                implies Game.next[b1] != Game.next[b2]
            }
        }
    } is necessary for linear_game
}
