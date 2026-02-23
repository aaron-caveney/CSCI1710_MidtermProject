#lang forge/froglet

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

pred starting[b: Board] {
    all row, col: Int | no b.board[row][col]
}

/** Gravity: no floating pieces */
pred gravityHolds[b: Board] {
    all row, col: Int | {
        (row > 0 and row <= 5 and col >= 0 and col <= 6) implies {
            some b.board[row][col] implies some b.board[subtract[row,1]][col]
        }
    }
}

/** Red goes first */
pred Redturn[b: Board] {
    #{row, col: Int | b.board[row][col] = RED}
    =
    #{row, col: Int | b.board[row][col] = YELLOW}
}

pred Yellowturn[b: Board] {
    #{row, col: Int | b.board[row][col] = RED}
    =
    add[1, #{row, col: Int | b.board[row][col] = YELLOW}]
}

pred balanced[b: Board] {
    Xturn[b] or Oturn[b]
}

/** Four in a row horizontally */ 
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

/** Four in a column vertically */
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

/** Four in a diagonal */
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

/**
 * Drop player p's piece into column moveCol.
 * Piece lands in the lowest empty row of that column.
 */
pred move[pre: Board, moveCol: Int, p: Player, post: Board] {
    -- GUARD
    p = RED implies Xturn[pre]
    p = YELLOW implies Oturn[pre]

    moveCol >= 0
    moveCol <= 6

    -- Column not full
    no pre.board[5][moveCol]

    -- Game not over
    not winning[pre, RED]
    not winning[pre, YELLOW]

    -- Gravity holds in pre
    gravityHolds[pre]

    -- Find landing row: lowest empty row in moveCol
    some landingRow: Int | {
        landingRow >= 0
        landingRow <= 5
        no pre.board[landingRow][moveCol]
        all rr: Int | (rr >= 0 and rr < landingRow) implies some pre.board[rr][moveCol]

        -- Place piece
        post.board[landingRow][moveCol] = p

        -- Frame condition
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

// /** Single step */
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

one sig Game {
    first: one Board,
    next: pfunc Board -> Board
}



pred wellformed_game {

    starting[Game.first]

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

pred linear_game {
    wellformed_game

    -- next is injective
    all b1, b2: Board |
        (b1 != b2) implies Game.next[b1] != Game.next[b2]

    -- no cycles back to first
    all b: Board | Game.next[b] != Game.first

    -- piece count increases by exactly 1 each step
    all b: Board | some Game.next[b] implies {
        #{r, c: Int | Game.next[b].board[r][c] != none}
        =
        add[1, #{r, c: Int | b.board[r][c] != none}]
    }

    -- Game.first is the ONLY board with no predecessor
    all b: Board | b != Game.first implies {
        some bPrev: Board | Game.next[bPrev] = b
    }
}

a_game: run {
    linear_game
    some b: Board | winning[b, RED]
} for exactly 4 Int, exactly 8 Board
