#lang forge/froglet

// can onl have one red player and one yellow player
abstract sig Player {}
one sig RED, YELLOW extends Player {}

sig Board {
    -- board[row][col] = player who has a piece there
    board: pfunc Int -> Int -> Player
}

-- Valid row/col ranges: rows 0-5, cols 0-6
pred wellformed[b: Board] {
    all row, col: Int | {
        (row < 0 or row > 5 or col < 0 or col > 6) implies
            no b.board[row][col]
    }
}

// starting board has no pieces on it
pred starting[b: Board] {
    all row, col: Int | no b.board[row][col]
}

// all peices are played on the lowest empty row of a column, or on the bottom row
pred gravityHolds[b: Board] {
    all row, col: Int | {
        (row > 0 and row <= 5 and col >= 0 and col <= 6) implies {
            some b.board[row][col] implies some b.board[subtract[row,1]][col]
        }
    }
}

// In every game red goes first
// If red and yellow have played the same amount of pieces, it will alwasy be red's turn
pred Redturn[b: Board] {
    #{row, col: Int | b.board[row][col] = RED}
    =
    #{row, col: Int | b.board[row][col] = YELLOW}
}
// If red has played one more peice than yellow then it will alwasy be yellows turn
pred Yellowturn[b: Board] {
    #{row, col: Int | b.board[row][col] = RED}
    =
    add[1, #{row, col: Int | b.board[row][col] = YELLOW}]
}

// one of the above must always be true to ensure that no players turn is skipped
pred balanced[b: Board] {
    Redturn[b] or Yellowturn[b]
}

// 4 in a row horizonatly anywhere win the game
pred winRow[b: Board, p: Player] {
    some row, col: Int | {
        row >= 0 and row <= 5
        col >= 0 and col <= 3
        b.board[row][col] = p
        b.board[row][add[col,1]] = p
        b.board[row][add[col,2]] = p
        b.board[row][add[col,3]] = p
    }
}

// 4 in a row veritcaly anywhere win the game
pred winCol[b: Board, p: Player] {
    some row, col: Int | {
        row >= 0 and row <= 2
        col >= 0 and col <= 6
        b.board[row][col] = p
        b.board[add[row,1]][col] = p
        b.board[add[row,2]][col] = p
        b.board[add[row,3]][col] = p
    }
}

// 4 in a row either diagonal direction wins the game
pred winDiag[b: Board, p: Player] {
    (some row, col: Int | {
        row >= 0 and row <= 2
        col >= 0 and col <= 3
        b.board[row][col] = p
        b.board[add[row,1]][add[col,1]] = p
        b.board[add[row,2]][add[col,2]] = p
        b.board[add[row,3]][add[col,3]] = p
    })
    or
    (some row, col: Int | {
        row >= 0 and row <= 2
        col >= 3 and col <= 6
        b.board[row][col] = p
        b.board[add[row,1]][subtract[col,1]] = p
        b.board[add[row,2]][subtract[col,2]] = p
        b.board[add[row,3]][subtract[col,3]] = p
    })
}

pred winning[b: Board, p: Player] {
    winRow[b, p] or winCol[b, p] or winDiag[b, p]
}


 // This makes a playes move, must be valid and follow the pred stated above.
pred move[pre: Board, moveCol: Int, p: Player, post: Board] {
    // who every played last must be the opposite player of p
    p = RED implies Redturn[pre]
    p = YELLOW implies Yellowturn[pre]

    moveCol >= 0
    moveCol <= 6

    // a column must be emtpy to play there
    no pre.board[5][moveCol]

    // if someone won the game is over and no move can be made
    not winning[pre, RED]
    not winning[pre, YELLOW]

    // the previuse board must have followed the rules
    gravityHolds[pre]

    // find a spot that is at the lowest empty spot on a column
    some landingRow: Int | {
        landingRow >= 0
        landingRow <= 5
        no pre.board[landingRow][moveCol]
        all rr: Int | (rr >= 0 and rr < landingRow) implies some pre.board[rr][moveCol]

        //make the move on the next board
        post.board[landingRow][moveCol] = p

        // make sure the next board is the same as the pre board other than the piece we just placed above
        all r, c: Int | (r != landingRow or c != moveCol) implies
            post.board[r][c] = pre.board[r][c]
    }
}

/** Find a winning board for X */
// example_win: run {
//     some b: Board | {
//         wellformed[b]
//         balanced[b]
//         gravityHolds[b]
//         winning[b, RED]
//     }
// } for exactly 1 Board, 4 Int

// one_step: run {
//     some b1, b2: Board | {
//         wellformed[b1]
//         balanced[b1]
//         gravityHolds[b1]
//         some c: Int, p: Player | move[b1, c, p, b2]
//     }
// } for exactly 2 Board, 4 Int

///////////////////////////////////////////////////////////
// Full game trace
///////////////////////////////////////////////////////////


// this sig hold the full game.
one sig Game {
    first: one Board,
    next: pfunc Board -> Board
}

// A game to be well formed must have a clean starting state, all baords must follow every rule, the game only ends with a winner
pred wellformed_game {

    //make starting baord
    starting[Game.first]

    // all boards in the game follow the rules of the game
    all b: Board | {
        wellformed[b]
        gravityHolds[b]
        balanced[b]
    }

    all b1, b2: Board |
        Game.next[b1] = b2 implies {
            some c: Int, p: Player |
                move[b1, c, p, b2]
        }

    all b: Board |
        (winning[b, RED] or winning[b, YELLOW]) implies {
            no Game.next[b]
        }

    all b: Board |
        b != Game.first implies {
            one bPrev: Board | Game.next[bPrev] = b
        }
}

// a game is linear if it is well formed and has no cycles
pred linear_game {
    wellformed_game

    // if boards are not the same they do not have the same next baord
    all b1, b2: Board |
        (b1 != b2) implies Game.next[b1] != Game.next[b2]

    // the next board can not be the starting state AKA cant cycle back to the start
    all b: Board | Game.next[b] != Game.first

   /// each baord has a peice count that goes up by one from the pre baord
    all b: Board | some Game.next[b] implies {
        #{r, c: Int | Game.next[b].board[r][c] != none}
        =
        add[1, #{r, c: Int | b.board[r][c] != none}]
    }

    // only baord with no pre is the starting baord
    all b: Board | b != Game.first implies {
        some bPrev: Board | Game.next[bPrev] = b
    }
}


// run a valid isntance of the game for exactly 4 moves for each player since thats how many it takes to win 
a_game: run {
    linear_game
    some b: Board | winning[b, RED]
} for exactly 4 Int, exactly 8 Board
